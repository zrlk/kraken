#!/usr/bin/env python3
"""Split scc's x86-64 listing into blocks of stack accesses, register
operations and a final branch; compute each block's static offsets (rsp and
the registers holding a stack address, relative to the frame base) and each
function's stack region; emit `block_spec` commands and coverage statistics.
At a label the offsets are the meet of all incoming edges (fall-through and
branches), computed to a fixpoint, so that the blocks of a function compose
(Spike/Lib/X64Cfg.lean).

Usage: genblocks_x64.py LISTING.s OUT.lean
  LISTING.s  scc's x64 listing (scc --arch x64 -S prog.w)
  OUT.lean   the block_spec lines (OUT.lean.json: coverage statistics)
"""
import re, sys, json, collections

src, out = sys.argv[1], sys.argv[2]
lines = open(src).read().split('\n')

R64 = ['rax', 'rbx', 'rcx', 'rdx', 'rsi', 'rdi', 'rsp', 'rbp'] + [f'r{i}' for i in range(8, 16)]
BASE = {}
for r in R64:
    BASE[r] = r
for a, b in [('rax', 'eax'), ('rbx', 'ebx'), ('rcx', 'ecx'), ('rdx', 'edx'), ('rsi', 'esi'), ('rdi', 'edi'),
             ('rsp', 'esp'), ('rbp', 'ebp')]:
    BASE[b] = a
    BASE[b[1:]] = a
for a, b in [('rax', 'al'), ('rbx', 'bl'), ('rcx', 'cl'), ('rdx', 'dl'), ('rsi', 'sil'), ('rdi', 'dil'),
             ('rsp', 'spl'), ('rbp', 'bpl')]:
    BASE[b] = a
for a in ['ah', 'bh', 'ch', 'dh']:
    BASE[a] = 'r' + a[0] + 'x'
for i in range(8, 16):
    for suf in ['d', 'w', 'b']:
        BASE[f'r{i}{suf}'] = f'r{i}'

REG = r'%([a-z0-9]+)'
IMM = r'\$(-?\d+)'
MEM = r'(-?\d+)?\(%([a-z0-9]+)\)'
CC = r'(e|z|ne|nz|b|c|nae|ae|nb|nc|a|nbe|be|na|l|nge|le|ng|ge|nl|g|nle)'


def reg(s):
    return BASE.get(s)


def classify(ins):
    """('ld', r, b, n) | ('st', b, n, r) | ('push', r) | ('pop', r) | ('reg', mn, dst, info) |
    ('jmp', L) | ('jcc', L) | ('call', L) | ('ret',) | ('x', category)"""
    m = re.fullmatch(r'movq ' + MEM + r', ' + REG, ins)
    if m:
        return ('ld', BASE[m.group(3)], BASE[m.group(2)], int(m.group(1) or 0))
    m = re.fullmatch(r'movq ' + REG + r', ' + MEM, ins)
    if m:
        return ('st', BASE[m.group(3)], int(m.group(2) or 0), BASE[m.group(1)])
    m = re.fullmatch(r'pushq ' + REG, ins)
    if m and m.group(1) in R64:
        return ('push', m.group(1))
    m = re.fullmatch(r'popq ' + REG, ins)
    if m and m.group(1) in R64:
        return ('pop', m.group(1))
    m = re.fullmatch(r'jmp ([.A-Za-z_][\w.]*)', ins)
    if m:
        return ('jmp', m.group(1))
    m = re.fullmatch(r'j' + CC + r' ([.A-Za-z_][\w.]*)', ins)
    if m:
        return ('jcc', m.group(2))
    m = re.fullmatch(r'call ([.A-Za-z_][\w.]*)', ins)
    if m:
        return ('call', m.group(1))
    if ins == 'ret':
        return ('ret',)
    mn = ins.split()[0]
    ops = ins[len(mn):].strip()
    if '%fs:' in ops:
        return ('x', 'thread pointer')
    if mn in ('syscall', 'ud2', 'mfence', 'lock') or mn.startswith('xchg') or mn.startswith('xadd'):
        return ('x', 'system' if mn in ('syscall', 'ud2') else 'shared memory')
    if re.match(r'(and|or|xor|test|imul|shl|shr|sar)[bwlq]?$', mn):
        return ('x', 'undefined flags')
    if '(%rip)' in ops:
        return ('x', 'label address')
    if '(' in ops and not mn.startswith('lea'):
        return ('x', 'shared memory')
    m = re.fullmatch(r'(mov[bwlq]?|movabsq) (?:' + REG + '|' + IMM + r'), ' + REG, ins)
    if m:
        s, imm, d = m.group(2), m.group(3), m.group(4)
        return ('reg', 'mov', reg(d), ('copy', reg(s)) if s and mn == 'movq' and s in R64 and d in R64 else None)
    m = re.fullmatch(r'(movz|movs)[bwl][wlq] ' + REG + ', ' + REG, ins)
    if m:
        return ('reg', 'movx', reg(m.group(3)), None)
    m = re.fullmatch(r'set' + CC + ' ' + REG, ins)
    if m:
        return ('reg', 'setcc', reg(m.group(2)), None)
    m = re.fullmatch(r'cmov' + CC + r'[wlq]? ' + REG + ', ' + REG, ins)
    if m:
        return ('reg', 'cmov', reg(m.group(3)), None)
    m = re.fullmatch(r'leaq ' + MEM + ', ' + REG, ins)
    if m:
        return ('reg', 'lea', reg(m.group(3)), ('lea', BASE[m.group(2)], int(m.group(1) or 0)))
    m = re.fullmatch(r'(add|adc|sub|sbb|cmp)([bwlq]) (?:' + REG + '|' + IMM + r'), ' + REG, ins)
    if m:
        op, w, s, imm, d = m.groups()
        info = None
        if imm is not None and w == 'q' and op in ('add', 'sub') and d in R64:
            info = (op, int(imm))
        return ('reg', op, None if op == 'cmp' else reg(d), info)
    m = re.fullmatch(r'(inc|dec|neg|not)[bwlq] ' + REG, ins)
    if m:
        return ('reg', m.group(1), reg(m.group(2)), None)
    if mn in ('cqto', 'cqo'):
        return ('reg', 'cqo', 'rdx', None)
    if mn == 'nop':
        return ('reg', 'nop', None, None)
    return ('x', 'other')


def node(ins):
    """The single-instruction node lemma that covers an instruction outside the block lemma, if any:
    'flag' (`flag_nd`, Spike/Lib/X64Flags.lean: the register forms with undefined flags and the
    zeroing `xorl %r32, %r32`), 'label' (`si_nd`, Spike/Lib/X64Nodes.lean: `leaq L(%rip), %r`),
    'sys' (`syscall_nd`, Spike/Lib/X64Nodes.lean: `syscall`), 'thread pointer' (`fsld_nd`, same file:
    `movq %fs:k, %r`) or 'dead' (`dead_nd`, Spike/Lib/X64Dead.lean: `ud2`, a node no run reaches, after
    a call that does not return or after `exit_group`).
    The destination is never `%rsp`."""
    m = re.fullmatch(r'(and|or|xor|test|imul)q ' + REG + ', ' + REG, ins)
    if m and m.group(2) in R64 and m.group(3) in R64 and m.group(3) != 'rsp':
        return 'flag'
    m = re.fullmatch(r'(shl|shr)q %cl, ' + REG, ins)
    if m and m.group(2) in R64 and m.group(2) != 'rsp':
        return 'flag'
    m = re.fullmatch(r'xorl ' + REG + ', ' + REG, ins)
    if m and m.group(1) == m.group(2) and BASE.get(m.group(1)) not in (None, 'rsp') and m.group(1) not in R64:
        return 'flag'
    m = re.fullmatch(r'leaq ([.A-Za-z_][\w.]*)\(%rip\), ' + REG, ins)
    if m and m.group(2) in R64 and m.group(2) != 'rsp':
        return 'label'
    if ins == 'syscall':
        return 'sys'
    m = re.fullmatch(r'movq %fs:(-?\d+), ' + REG, ins)
    if m and m.group(2) in R64 and m.group(2) != 'rsp':
        return 'thread pointer'
    if ins == 'ud2':
        return 'dead'
    return None


# The system calls whose kernel step has no event (rt_sigaction, exit_group, futex, exit): `syscall_nd`
# matches them fully. `write` and `clone` are matched for the thread's control only (`Out.sys`);
# `arch_prctl` (158) sets the thread pointer, which `syscall_nd` does not cover.
SILENT_NRS = {13, 231, 202, 60}
NOT_SYS_NRS = {158}

# Static offsets: (rsp, ((reg, k), ...), epoch). The epoch counts the stack switches on the way to a
# point: after `movq %r, %rsp` with %r of unknown offset (`sw_nd`) or `andq $k, %rsp` (`swand_nd`,
# Spike/Lib/X64Switch.lean) the code is in a new region, based at the new %rsp (offset 0, no register
# offsets), with its own [lo, hi).


def so_get(o, r):
    if r == 'rsp':
        return o[0]
    return dict(o[1]).get(r)


def so_kill(o, r):
    return (o[0], tuple(e for e in o[1] if e[0] != r)) + o[2:]


def so_set(o, r, k):
    if r == 'rsp':
        return (k, o[1]) + o[2:]
    return (o[0], ((r, k),) + so_kill(o, r)[1]) + o[2:]


def step(o, c):
    """(new SO or None if not covered, accessed offset or None)"""
    t = c[0]
    if t == 'ld':
        _, r, b, n = c
        kb = so_get(o, b)
        if kb is None or r == 'rsp':
            return None, None
        return so_kill(o, r), kb + n
    if t == 'st':
        _, b, n, r = c
        kb = so_get(o, b)
        if kb is None:
            return None, None
        return o, kb + n
    if t == 'push':
        return (o[0] - 8, o[1]) + o[2:], o[0] - 8
    if t == 'pop':
        if c[1] == 'rsp':
            return None, None
        return (o[0] + 8, so_kill(o, c[1])[1]) + o[2:], o[0]
    if t == 'reg':
        _, mn, d, info = c
        if info and info[0] == 'copy':
            k = so_get(o, info[1])
            if k is not None:
                return so_set(o, d, k), None
        if info and info[0] == 'lea':
            k = so_get(o, info[1])
            if k is not None:
                return so_set(o, d, k + info[2]), None
        if info and info[0] in ('add', 'sub'):
            k = so_get(o, d)
            if k is not None:
                return so_set(o, d, k + info[1] if info[0] == 'add' else k - info[1]), None
        if d is None:
            return o, None
        if d == 'rsp':
            return None, None
        return so_kill(o, d), None
    if t in ('jmp', 'jcc'):
        return o, None
    if t == 'call':
        return (o[0] - 8, o[1]) + o[2:], o[0] - 8
    if t == 'ret':
        return (o[0] + 8, o[1]) + o[2:], o[0]
    return None, None


U = 'unknown'  # an unknown rsp (None: no flow reaches the point)


def meet(a, b):
    """The offsets both a and b guarantee: the same rsp, the register offsets they agree on."""
    if a is None:
        return b
    if b is None:
        return a
    if a == U or b == U or a[0] != b[0] or a[2:] != b[2:]:
        return U
    d = dict(b[1])
    return (a[0], tuple(e for e in a[1] if d.get(e[0]) == e[1])) + a[2:]


# ---- split into functions
# A function starts at a label the listing declares a function (`.type NAME, @function`),
# or at the first label. Any other label
# (`.L…`, or a global marker inside a function such as
# `scc_rt_release_site`) is a label of the enclosing function: offsets flow across it.
FUNS = set(re.findall(r'^\s*\.type\s+([A-Za-z_.$][\w.$]*)\s*,\s*[@%]function', '\n'.join(lines), re.M))
funcs = []  # (name, [(lineno, kind, text)])
cur = None
for i, raw in enumerate(lines, 1):
    s = raw.strip()
    if not s or s.startswith('#'):
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
blocks = []  # (fn, startline, lo, hi, so, [ins])
TERMS = ('jmp', 'jcc', 'call', 'ret')


def switch(c, o, text):
    """Whether an instruction is a stack switch at offsets o: a register operation writing %rsp that the
    block lemma does not cover (`sw_nd`), or `andq $k, %rsp` (`swand_nd`)."""
    if o in (None, U):
        return False
    if c[0] == 'reg':
        return c[2] == 'rsp' and step(o, c)[0] is None
    return re.fullmatch(r'andq \$-?\d+, %rsp', text) is not None


def x_dst(text):
    """The register an uncovered instruction may write (its last operand), if any."""
    m = re.search(r'%([a-z0-9]+)$', text)
    return BASE.get(m.group(1)) if m else None

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
        o = (8, (), 0)
        epochs = 0
        for idx, (ln, kind, text) in enumerate(items):
            if kind == 'label':
                o = flow(text, o)
                continue
            so_before[idx] = o
            c = classify(text)
            if o is None:
                continue
            if c[0] in ('jmp', 'jcc'):
                flow(c[1], o)
            if o == U:
                if c[0] in ('jmp', 'ret') or text == 'ud2':
                    o = None
                continue
            if switch(c, o, text):  # a new region at the new %rsp
                epochs += 1
                o = (0, (), epochs)
                continue
            if c[0] == 'x':
                d = x_dst(text)
                if text == 'ud2':
                    o = None
                elif d == 'rsp':
                    o = U
                elif text == 'syscall':
                    for r in ('rax', 'rcx', 'r11'):  # the kernel's results and clobbers
                        o = so_kill(o, r)
                elif d is not None:
                    o = so_kill(o, d)
                continue
            n, _ = step(o, c)
            if n is None:  # not covered here: as an uncovered instruction
                d = x_dst(text)
                n = U if d == 'rsp' else (so_kill(o, d) if d else o)
            if c[0] in ('jmp', 'ret'):
                o = None
            elif c[0] == 'call':
                # the callee returns with rsp restored and keeps only the callee-saved registers
                for r in ('rax', 'rcx', 'rdx', 'rsi', 'rdi', 'r8', 'r9', 'r10', 'r11'):
                    o = so_kill(o, r)
            else:
                o = n
        if not changed:
            break
    else:
        raise SystemExit(f'no fixpoint in {fn}')
    # regions: the accessed offsets, one region per epoch; the entry region also holds the saved %rbp
    # and the return address ([0, 16))
    region = collections.defaultdict(lambda: [0, 0])
    region[0] = [0, 16]
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
        m = re.fullmatch(r'mov[lq] \$(\d+), %[er]ax', text)
        if m:
            nr = int(m.group(1))
        c = classify(text)
        o = so_before.get(idx)
        if c[0] == 'x':
            uncov[(key, c[1])] += 1
            if node(text) and o not in (None, U) and not (node(text) == 'sys' and nr in NOT_SYS_NRS):
                k = node(text)
                if k == 'sys' and nr is None:
                    k = 'sys, number after a label'  # the call number must come from the node's invariant
                elif k == 'sys' and nr not in SILENT_NRS:
                    k = 'sys, control only'  # write, clone: the kernel step's events are not matched
                nodes[(key, k)] += 1
            elif switch(c, o, text):
                nodes[(key, 'switch')] += 1
            flush()
            continue
        if o is None or o == U:
            uncov[(key, 'unknown stack offset')] += 1
            flush()
            continue
        n, acc = step(o, c)
        if n is None:
            uncov[(key, 'stack switch' if c[0] == 'reg' else 'non-frame memory')] += 1
            if switch(c, o, text):
                nodes[(key, 'switch')] += 1
            flush()
            continue
        covered[key] += 1
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
    regs = ', '.join(f'(.{r}, {k})' for r, k in o[1])
    return f'⟨{o[0]}, [{regs}]⟩'


names = collections.Counter()
body = []
for f, start, lo, hi, o, ins, end in blocks:
    k = names[f]
    names[f] += 1
    text = '\n'.join(ins)
    body.append(f'-- {f}, listing lines {start}–{end}')
    body.append(f'block_spec {ident(f)}_{k} ({lo}) {hi} {so_lean(o)} parse("{text}")')
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
print(json.dumps(stats, indent=1))
