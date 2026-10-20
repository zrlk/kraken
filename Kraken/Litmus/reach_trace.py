#!/usr/bin/env python3
"""Extract a compact replay trace for `Kraken.Promising.reachRun` (REACH).

Runs `.lake/build/bin/krakenlitmus_<isa> -v <flags> -witness FILE.kl` (flags from
the file's `# flags:` header line), takes the first witness marked
`(of interest)` (for a `Sometimes` example: a final state violating a
`forall`/`~exists` condition, or satisfying an `exists` one), and prints it as
a Lean list of steps `(tid, [timestamps of the step's reads and writes])`,
the input of `reachRun` / `reachCheck` (Kraken/Promising/ReachCore.lean).

  python3 Kraken/Litmus/reach_trace.py [--isa x64|aarch64] [--from OUT] FILE.kl

`--from OUT` reads saved explorer output instead of running the explorer.
Exits non-zero if there is no witness of interest, or if the witness has a
promise step (not supported by `reachRun`).

`--promises` (CERTL) prints the witness as a list of `ReachPStep`s for
`reachPRun` / `reachPCheck` (Kraken/Promising/ReachCertCore.lean) instead:
`.instr tid [stamps]` and `.promise tid addr val`. A promise's location is
resolved to its address from the `.kl` header (untyped scalars, in 256-byte
slots from `0x1000`, as `Litmus.AArch64.symBase`), or `[N]` as printed;
`--sym NAME=ADDR` overrides.
"""
import argparse
import os
import re
import subprocess
import sys

STEP = re.compile(r'^P(\d+): ')
READ = re.compile(r'^\s+read .* @(\d+)\s')
WRITE = re.compile(r'^\s+write .* @(\d+)')
PROMISE = re.compile(r'^P\d+ promises ')
PROMISE_FULL = re.compile(r'^P(\d+) promises (\S+) := (\d+) @\d+')


def explorer_output(isa, path, save=None):
    root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    binary = os.path.join(root, '.lake', 'build', 'bin', f'krakenlitmus_{isa}')
    flags = []
    with open(path) as f:
        for line in f:
            m = re.match(r'^\s*#\s*flags:\s*(.*)$', line)
            if m:
                flags = m.group(1).split()
                break
    if '-fuel' not in flags:
        flags = ['-fuel', '300'] + flags   # as run.sh / run_x64.sh
    if '-witness' not in flags:
        flags.append('-witness')
    out = subprocess.run([binary, '-v'] + flags + [path], capture_output=True, text=True).stdout
    if save:
        with open(save, 'w') as f:
            f.write(out)
    return out


def trace_of(out):
    lines = out.splitlines()
    try:
        start = next(i for i, l in enumerate(lines) if l.startswith('Witness for') and '(of interest)' in l)
    except StopIteration:
        sys.exit('no witness of interest')
    steps = []
    for line in lines[start + 1:]:
        if line.startswith('Witness for'):
            break
        if PROMISE.match(line):
            sys.exit('witness has a promise step; reachRun does not replay promises')
        m = STEP.match(line)
        if m:
            steps.append((int(m.group(1)), []))
            continue
        m = READ.match(line) or WRITE.match(line)
        if m and steps:
            steps[-1][1].append(int(m.group(1)))
    return steps


def header_syms(path, base=0x1000, slot=0x100):
    """Addresses of the untyped scalar locations of a `.kl` header."""
    text = re.sub(r'\(\*.*?\*\)', '', open(path).read(), flags=re.S)
    text = '\n'.join(l for l in text.splitlines() if not l.lstrip().startswith('#'))
    start = text.index('{')
    body = text[start + 1:text.index('}', start)]
    syms = {}
    for item in body.replace('\n', ' ').split(';'):
        item = item.strip()
        if not item or ':' in item.split('=')[0]:
            continue
        name, _, val = (x.strip() for x in item.partition('='))
        if not re.fullmatch(r'[A-Za-z_]\w*', name):
            sys.exit(f'unsupported header item: {item!r} (use --sym)')
        # slots in order of first mention (`head=d` places `d` after `head`)
        for n in [name] + ([val] if re.fullmatch(r'[A-Za-z_]\w*', val) else []):
            if n not in syms:
                syms[n] = base + slot * len(syms)
    return syms


def ptrace_of(out, syms):
    lines = out.splitlines()
    try:
        start = next(i for i, l in enumerate(lines) if l.startswith('Witness for') and '(of interest)' in l)
    except StopIteration:
        sys.exit('no witness of interest')
    steps = []
    for line in lines[start + 1:]:
        if line.startswith('Witness for'):
            break
        m = PROMISE_FULL.match(line)
        if m:
            loc = m.group(2)
            if loc.startswith('[') and loc.endswith(']'):
                addr = int(loc[1:-1])
            elif loc in syms:
                addr = syms[loc]
            else:
                sys.exit(f'unknown location {loc} (use --sym)')
            steps.append(('p', int(m.group(1)), addr, int(m.group(3))))
            continue
        m = STEP.match(line)
        if m:
            steps.append(('i', int(m.group(1)), []))
            continue
        m = READ.match(line) or WRITE.match(line)
        if m and steps and steps[-1][0] == 'i':
            steps[-1][2].append(int(m.group(1)))
    return steps


def plean(steps, per_line=5):
    items = [f'.instr {s[1]} [{", ".join(map(str, s[2]))}]' if s[0] == 'i'
             else f'.promise {s[1]} {hex(s[2])} {s[3]}' for s in steps]
    rows = [', '.join(items[i:i + per_line]) for i in range(0, len(items), per_line)]
    return '[' + ',\n   '.join(rows) + ']'


def lean(steps, per_line=6):
    items = [f'({t}, [{", ".join(map(str, ts))}])' for t, ts in steps]
    rows = [', '.join(items[i:i + per_line]) for i in range(0, len(items), per_line)]
    return '[' + ',\n   '.join(rows) + ']'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--isa', default='x64', choices=['x64', 'aarch64'])
    ap.add_argument('--from', dest='saved')
    ap.add_argument('--save', help='also save the explorer output here')
    ap.add_argument('--promises', action='store_true', help='emit ReachPStep items (reachPRun)')
    ap.add_argument('--sym', action='append', default=[], help='NAME=ADDR for a promise location')
    ap.add_argument('file')
    a = ap.parse_args()
    out = open(a.saved).read() if a.saved else explorer_output(a.isa, a.file, a.save)
    if a.promises:
        syms = header_syms(a.file)
        for kv in a.sym:
            k, v = kv.split('=')
            syms[k] = int(v, 0)
        steps = ptrace_of(out, syms)
        print(f'-- {len(steps)} steps, {sum(s[0] == "p" for s in steps)} promises')
        print(plean(steps))
        return
    steps = trace_of(out)
    print(f'-- {len(steps)} steps')
    print(lean(steps))


if __name__ == '__main__':
    main()
