#!/usr/bin/env python3
"""Split scc's AArch64 listing into blocks of stack accesses, register
operations and a final branch; compute each block's static offsets (sp and
the registers holding a stack address, relative to the entry sp) and each
function's stack region; emit `block_spec` commands (Spike/Lib/A64Flow.lean)
and coverage statistics. At a label the offsets are the meet of all incoming
edges (fall-through and branches), computed to a fixpoint, so that the blocks
of a function compose (Spike/Lib/A64Cfg.lean).

Usage: genblocks_a64.py LISTING.s OUT.lean [MAXLEN]
  LISTING.s  scc's AArch64 listing (scc --arch arm -S prog.w)
  OUT.lean   the block_spec lines (OUT.lean.json: coverage statistics)
  MAXLEN     longest block (default: no limit)
"""
import re, sys, json, collections

src, out = sys.argv[1], sys.argv[2]
lines = open(src).read().split('\n')

REGOPS = {'movz', 'movk', 'add', 'sub', 'adds', 'subs', 'madd', 'msub', 'and', 'orr', 'eor', 'ubfm', 'sbfm',
          'lslv', 'lsrv', 'asrv', 'csel', 'csinc', 'mrs'}
LAB = r'([.A-Za-z_][\w.]*)'
XR = r'(x\d+|xzr)'


def base(r):
    """The register a destination operand names: 'sp', 'xN', or None (zero register)."""
    if r in ('sp', 'wsp'):
        return 'sp'
    m = re.fullmatch(r'[xw](\d+)', r)
    return f'x{m.group(1)}' if m else None


def node(ins):
    """The single-instruction node lemma that covers an instruction outside the block lemma, if any:
    'label' or 'system' (`si_nd`, Spike/Lib/A64Nodes.lean: `adrp Xd, L`, `add Xd, Xs, :lo12:L`,
    `nop`, `msr tpidr_el0, Xs`; general registers only) or 'sys' (`svc_nd`: `svc #0`). Stack switches
    ('switch', `sw_nd`, Spike/Lib/A64Switch.lean) are counted where they are classified (`switch`)."""
    G = r'(x(?:\d|[12]\d|30))'
    if re.fullmatch(r'adrp ' + G + ', ' + LAB, ins):
        return 'label'
    if re.fullmatch(r'add ' + G + ', ' + G + ', :lo12:' + LAB, ins):
        return 'label'
    if ins == 'nop' or re.fullmatch(r'msr tpidr_el0, ' + G, ins):
        return 'system'
    if ins == 'svc #0':
        return 'sys'
    return None


# The system calls whose kernel step has no event (rt_sigaction, exit_group, futex, exit): `svc_nd`
# matches them fully. `write` and `clone` are matched for the thread's control only (`Out.sys`).
SILENT_NRS = {134, 94, 98, 93}

def classify(ins):
    """('slot', n) | ('reg', dst, info) | ('b', L) | ('bcond', L) | ('cb', L) | ('bl', L) | ('ret',) |
    ('x', category)"""
    m = re.fullmatch(r'(ldr|str) ' + XR + r', \[sp(?:, #(-?\d+))?\]', ins)
    if m:
        return ('slot', m.group(1), base(m.group(2)), int(m.group(3) or 0))
    m = re.fullmatch(r'b ' + LAB, ins)
    if m:
        return ('b', m.group(1))
    m = re.fullmatch(r'b\.[a-z]+ ' + LAB, ins)
    if m:
        return ('bcond', m.group(1))
    m = re.fullmatch(r'(cbz|cbnz) ' + XR + ', ' + LAB, ins)
    if m:
        return ('cb', m.group(3))
    m = re.fullmatch(r'bl ' + LAB, ins)
    if m:
        return ('bl', m.group(1))
    if ins == 'ret':
        return ('ret',)
    mn = ins.split()[0]
    ops = ins[len(mn):].strip()
    if mn in ('br', 'blr'):
        return ('x', 'indirect branch')
    if mn in ('ldar', 'stlr', 'swpal', 'ldaddal', 'casal'):
        return ('x', 'shared memory')
    if mn in ('ldr', 'str', 'ldur', 'stur'):
        return ('x', 'non-frame memory')
    if mn == 'adrp' or ':lo12:' in ops:
        return ('x', 'label address')
    if mn in ('svc', 'msr', 'dmb'):
        return ('x', 'system')
    if mn not in REGOPS:
        return ('x', 'other')
    args = [a.strip() for a in ops.split(',')]
    d = base(args[0])
    if mn in ('and', 'orr', 'eor') and '#' in ops:
        return ('x', 'other')
    if mn in ('movz', 'movk') and not re.match(r'#\d+', args[1]):
        return ('x', 'other')
    if mn in ('adds',) and '#' in ops:
        return ('x', 'other')
    if mn in ('add', 'sub') and len(args) == 3 and args[2].startswith('#'):
        s = base(args[1])
        n = int(args[2][1:])
        if args[0].startswith('x') or args[0] == 'sp':
            if args[1].startswith('x') or args[1] == 'sp':
                return ('reg', d, (mn, s, n))
        return ('reg', d, None)
    if d == 'sp':
        return ('x', 'other')
    return ('reg', d, None)


# Static offsets: (sp, ((reg, k), ...), epoch). The epoch counts the stack switches on the way to a
# point: after `add sp, Xs, #n` with Xs of unknown offset (`sw_nd`, Spike/Lib/A64Switch.lean) the code is
# in a new region, based at the new sp (offset 0, no register offsets), with its own [lo, hi).


def so_get(o, r):
    if r == 'sp':
        return o[0]
    return dict(o[1]).get(r)


def so_kill(o, r):
    return (o[0], tuple(e for e in o[1] if e[0] != r)) + o[2:]


def so_set(o, r, k):
    if r == 'sp':
        return (k, o[1]) + o[2:]
    return (o[0], ((r, k),) + so_kill(o, r)[1]) + o[2:]


def step(o, c):
    """(new SO or None if not covered, accessed offset or None)"""
    t = c[0]
    if t == 'slot':
        _, op, r, n = c
        if o[0] % 16 != 0 or n % 8 != 0:
            return None, None
        acc = o[0] + n
        if op == 'ldr' and r is not None:
            return so_kill(o, r), acc
        return o, acc
    if t == 'reg':
        _, d, info = c
        if info:
            mn, s, n = info
            k = so_get(o, s)
            if k is not None:
                return so_set(o, d, k + n if mn == 'add' else k - n), None
        if d is None:
            return o, None
        if d == 'sp':
            return None, None
        return so_kill(o, d), None
    if t in ('b', 'bcond', 'cb', 'ret'):
        return o, None
    if t == 'bl':
        return so_kill(o, 'x30'), None
    return None, None


U = 'unknown'  # an unknown sp (None: no flow reaches the point)


def meet(a, b):
    """The offsets both a and b guarantee: the same sp, the register offsets they agree on."""
    if a is None:
        return b
    if b is None:
        return a
    if a == U or b == U or a[0] != b[0] or a[2:] != b[2:]:
        return U
    d = dict(b[1])
    return (a[0], tuple(e for e in a[1] if d.get(e[0]) == e[1])) + a[2:]


# ---- split into functions
# A function starts at a label the listing declares a function (`.type NAME, %function`),
# or at the first label (`_start` has no `.type` on AArch64). Any other label
# (`.L…`, or a global marker inside a function such as
# `scc_rt_release_site`) is a label of the enclosing function: offsets flow across it.
FUNS = set(re.findall(r'^\s*\.type\s+([A-Za-z_.$][\w.$]*)\s*,\s*[@%]function', '\n'.join(lines), re.M))
funcs = []  # (name, [(lineno, kind, text)])
cur = None
for i, raw in enumerate(lines, 1):
    s = raw.strip()
    if not s or s.startswith('//'):
        continue
    if not raw.startswith('\t') and s.endswith(':'):
        lab = s[:-1]
        if lab in FUNS or cur is None:
            cur = (lab, [])
            funcs.append(cur)
        if cur is not None:
            cur[1].append((i, 'label', lab))
        continue
    if s.startswith('.'):
        continue
    if cur is not None:
        cur[1].append((i, 'ins', s))

user = lambda f: f.startswith('wc_')
total = collections.Counter()
covered = collections.Counter()
uncov = collections.Counter()
nodes = collections.Counter()  # uncovered by blocks, covered by a node lemma (known offsets)
blocks = []  # (fn, startline, lo, hi, so, [ins], endline)
TERMS = ('b', 'bcond', 'cb', 'bl', 'ret')
MAXLEN = int(sys.argv[3]) if len(sys.argv) > 3 else 1000


def switch(c, o):
    """Whether a classified instruction is a stack switch at offsets o: a register operation writing sp
    that the block lemma does not cover (`sw_nd`)."""
    return c[0] == 'reg' and c[1] == 'sp' and o not in (None, U) and step(o, c)[0] is None


def x_dst(text):
    """The register an uncovered instruction may write (its first operand), if any."""
    parts = text.split(None, 1)
    if len(parts) < 2:
        return None
    return base(parts[1].split(',')[0].strip())


for fn, items in funcs:
    key = 'user' if user(fn) else 'runtime'
    # pass 1: static offsets at every instruction, the meet of all incoming edges at each label (to a fixpoint)
    at_label = {}
    so_before = {}

    def flow(lab, o):
        global changed
        new = meet(at_label.get(lab), o)
        if new != at_label.get(lab):
            at_label[lab] = new
            changed = True
        return new

    for sweep in range(100):
        changed = False
        o = (0, (), 0)
        epochs = 0
        for idx, (ln, kind, text) in enumerate(items):
            if kind == 'label':
                o = flow(text, o)
                continue
            so_before[idx] = o
            c = classify(text)
            if o is None:
                continue
            if c[0] in ('b', 'bcond', 'cb'):
                flow(c[1], o)
            if o == U:
                if c[0] in ('b', 'ret'):
                    o = None
                continue
            if c[0] == 'x':
                d = x_dst(text)
                if d == 'sp':
                    o = U
                elif c[1] in ('system', 'shared memory'):
                    o = (o[0], ()) + o[2:]  # may write more than its first operand
                elif d is not None:
                    o = so_kill(o, d)
                continue
            n, _ = step(o, c)
            if switch(c, o):  # a new region at the new sp
                epochs += 1
                n = (0, (), epochs)
            if n is None:  # not covered here: as an uncovered instruction
                d = x_dst(text)
                n = U if d == 'sp' else (so_kill(o, d) if d else o)
            if c[0] in ('b', 'ret'):
                o = None
            elif c[0] == 'bl':
                o = n  # the callee returns with sp restored and keeps only the callee-saved registers
                for r in [f'x{i}' for i in range(19)]:
                    o = so_kill(o, r)
            else:
                o = n
        if not changed:
            break
    else:
        raise SystemExit(f'no fixpoint in {fn}')
    # regions: the accessed offsets, one region per epoch
    region = collections.defaultdict(lambda: [0, 0])
    for idx, (ln, kind, text) in enumerate(items):
        if kind != 'ins' or so_before.get(idx) in (None, U):
            continue
        c = classify(text)
        if c[0] == 'x':
            continue
        n, acc = step(so_before[idx], c)
        if n is not None and acc is not None:
            r = region[so_before[idx][2]]
            r[0] = min(r[0], acc)
            r[1] = max(r[1], acc + 8)
    # pass 2: blocks
    blk = None

    def flush():
        global blk
        if blk and blk[5]:
            blocks.append(blk)
        blk = None

    nr = None  # the system-call number last set in straight-line code
    for idx, (ln, kind, text) in enumerate(items):
        if kind == 'label':
            nr = None
            flush()
            continue
        total[key] += 1
        m = re.fullmatch(r'mov[z]? x8, #(\d+)', text)
        if m:
            nr = int(m.group(1))
        c = classify(text)
        o = so_before.get(idx)
        if c[0] == 'x':
            uncov[(key, c[1])] += 1
            if node(text) and o not in (None, U):
                k = node(text)
                if k == 'sys' and nr is None:
                    k = 'sys, number after a label'  # the call number must come from the node's invariant
                elif k == 'sys' and nr not in SILENT_NRS:
                    k = 'sys, control only'  # write, clone: the kernel step's events are not matched
                nodes[(key, k)] += 1
            flush()
            continue
        if o is None or o == U:
            uncov[(key, 'unknown stack offset')] += 1
            flush()
            continue
        n, acc = step(o, c)
        if n is None:
            uncov[(key, 'stack switch' if c[0] == 'reg' else 'unaligned stack access')] += 1
            if switch(c, o):
                nodes[(key, 'switch')] += 1
            flush()
            continue
        covered[key] += 1
        if blk is not None and len(blk[5]) >= MAXLEN:
            flush()  # long blocks: split on request
        if blk is None:
            blk = [fn, ln, *region[o[2]], o, [], ln]
        blk[5].append(text)
        blk[6] = ln
        if c[0] in TERMS:
            flush()
    flush()


def ident(s):
    return re.sub(r'[^A-Za-z0-9_]', '_', s)


def so_lean(o):
    regs = ', '.join(f'(.X{r[1:]}, {k})' for r, k in o[1])
    return f'⟨{o[0]}, [{regs}]⟩'


names = collections.Counter()
body = []
for f, start, lo, hi, o, ins, end in blocks:
    k = names[f]
    names[f] += 1
    text = '\n'.join(ins)
    body.append(f'-- {f}, listing lines {start}–{end}')
    body.append(f'block_spec {ident(f)}_{k} ({lo}) {hi} {so_lean(o)} parseAArch64("{text}")')
    body.append('')

stats = {
    'total': dict(total), 'covered': dict(covered),
    'uncovered': {f'{k[0]}: {k[1]}': v for k, v in sorted(uncov.items())},
    'nodes': {f'{k[0]}: {k[1]}': v for k, v in sorted(nodes.items())},
    'blocks': len(blocks), 'user_blocks': sum(1 for b in blocks if user(b[0])),
    'max_block': max(len(b[5]) for b in blocks),
    'terminated': sum(1 for b in blocks if classify(b[5][-1])[0] in TERMS),
    'hist': dict(sorted(collections.Counter(len(b[5]) for b in blocks).items())),
}
json.dump(stats, open(out + '.json', 'w'), indent=1)
open(out, 'w').write('\n'.join(body))
print(json.dumps({k: v for k, v in stats.items() if k != 'hist'}, indent=1))
