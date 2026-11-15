#!/usr/bin/env python3
"""Generate the per-step SegP lemmas of the closed hello run (chunks C1..C8)."""
import re, sys, json

import os
GEN_DIR = os.environ.get('FWDGEN_DIR', '/tmp/fwdgen')
SIM = GEN_DIR + '/sim.out'
INS = GEN_DIR + '/insns.txt'
TAB = GEN_DIR + '/tab2.out'
LAST = None  # the counter add: the first `lock xadd` on `scc_rt_heap_use` (found below)
RTK = None  # the take's range (from the TAKE line)
ENT_LO, ENT_HI = 140737488285696, 140737488351232
REGORDER = ['rax', 'rbx', 'rcx', 'rdx', 'rsi', 'rdi', 'rsp', 'rbp', 'r8', 'r9', 'r10', 'r11', 'r12', 'r13', 'r14',
            'r15', 'fsBase']

# ---------- parse ----------
states = {}
for l in open(SIM):
    m = re.match(r'^(\d+) pc=(\d+) \[(.*?)\] F=(⟨.*?⟩) D=(.*)$', l)
    if not m:
        continue
    i = int(m.group(1))
    regs = {}
    if m.group(3).strip():
        for kv in m.group(3).split(', '):
            k, v = kv.split(' := ')
            k = 'fsBase' if k == 'fs' else k
            regs[k] = int(v)
    fl = tuple(x.strip() == 'true' for x in m.group(4)[1:-1].split(','))
    states[i] = dict(pc=int(m.group(2)), regs=regs, fl=fl)

ins = {}
for l in open(INS):
    m = re.match(r'^(\d+) (\d+) \((W\d+)\) (.*)$', l.rstrip('\n'))
    if m:
        ins[int(m.group(1))] = (int(m.group(2)), m.group(3), m.group(4))

for i, (pc_, w_, t_) in sorted(ins.items()):
    mt = re.search(r'TAKE (\d+) (\d+)', t_)
    if mt and RTK is None:
        RTK = (int(mt.group(1)), int(mt.group(2)))
        TAKE_STEP = i
    if 'SYSCALL nr=13' in t_:
        SIG_STEP = i
    if 'SYSCALL nr=158' in t_:
        FS_STEP = i
cells = {}
labels = {}
for l in open(TAB):
    p = l.split()
    if p[0] == 'CELL':
        cells[int(p[2])] = (int(p[1]), int(p[3]))
    elif p[0] == 'LAB':
        name = p[1]
        if p[2] == 'none':
            labels[name] = ('sym', int(re.search(r'\[(\d+)\]', l).group(1)))
        else:
            labels[name] = ('code', int(re.search(r'\(some (\d+)\)', l).group(1)))


HEAP = labels['scc_rt_heap_use'][1]
LAST = next(i for i, (_, _, t_) in sorted(ins.items()) if t_.startswith('(xadd') and f'[rmw {HEAP}/8' in t_)


def labname(s):
    return 'lab_' + s.replace('.', '_')


# ---------- names ----------
def regs_lean(r):
    if not r:
        return '{}'
    return '{ ' + ', '.join(f'{k} := {r[k]}' for k in REGORDER if k in r) + ' }'


def fl_name(f):
    return 'F_' + ''.join('1' if b else '0' for b in f)


def fl_lean(f):
    return '⟨' + ', '.join('true' if b else 'false' for b in f) + '⟩'


SPECIAL_R = {SIG_STEP: 'Rsig', SIG_STEP + 1: "Rsig'", TAKE_STEP: 'Rtk', FS_STEP: 'Rfs', FS_STEP + 1: "Rfs'"}
rname_of = {}  # frozen regs -> name
rdefs = []  # (step, name, lean)
for i in range(0, LAST + 1):
    key = tuple(sorted(states[i]['regs'].items()))
    if i in SPECIAL_R:
        if key in rname_of:
            assert rname_of[key] == SPECIAL_R[i], (i, rname_of[key])
        rname_of[key] = SPECIAL_R[i]
for i in range(0, LAST + 1):
    key = tuple(sorted(states[i]['regs'].items()))
    if key not in rname_of:
        rname_of[key] = f'R{i}'
        rdefs.append((i, f'R{i}', regs_lean(states[i]['regs'])))


def rname(i):
    return rname_of[tuple(sorted(states[i]['regs'].items()))]


fdefs = {}
for i in range(0, LAST + 1):
    n = fl_name(states[i]['fl'])
    if n not in fdefs:
        fdefs[n] = (i, fl_lean(states[i]['fl']))

# ---------- memory tracking ----------
# layers: list of (basename, list name, list of (a,v) latest first)
mem = {}  # step -> D lean term, layers
L = []
N = None  # after take
Llast = None
lists = []  # (step, name, lean)
cur_list_name = 'Lnil'
cur_base = 'Ent'


def look(b, lst):
    for a, v in lst:
        if a == b:
            return v
    return None


def cur_layers():
    if N is None:
        return [('Ent', cur_list_name, L)]
    return [('B2', cur_list_name, N), ('Ent', 'Llast', Llast)]


def D_term():
    base, ln, _ = cur_layers()[0]
    return f'(stores {base} {ln})'


def B_term(base):
    return base


def load_term(b, layers):
    base, ln, lst = layers[0]
    v = look(b, lst)
    if v is not None:
        return (f'(loadInt_look (B := {base}) (L := {ln}) (b := {b}#64) (v := {v}#64) (by decide) (by decide) '
                f'(by decide))'), v
    head = f'(loadInt_look_none (B := {base}) (L := {ln}) (b := {b}#64) (by decide) (by decide) (by decide))'
    if base == 'B2':
        if RTK[0] <= b and b + 8 <= RTK[0] + RTK[1]:
            return f'({head}.trans (copy_in (by decide) (by decide)))', 0
        t, v = load_term(b, layers[1:])
        return f'({head}.trans ((copy_out (by decide) (by decide) (by decide)).trans {t}))', v
    raise Exception(f'load from entry stack, unstored {b}')


def ex_term(b, layers):
    base, ln, lst = layers[0]
    v = look(b, lst)
    if v is not None:
        return f'(ex_look (B := {base}) (L := {ln}) (b := {b}#64) (v := {v}#64) (by decide) (by decide) (by decide))'
    if base == 'Ent':
        assert ENT_LO <= b and b + 8 <= ENT_HI
        return (f'(ex_base (B := {base}) (L := {ln}) (b := {b}#64) (by decide) (by decide) (by decide) '
                f'(stack_some (by decide) (by decide)))')
    head = f'(loadInt_look_none (B := {base}) (L := {ln}) (b := {b}#64) (by decide) (by decide) (by decide))'
    if RTK[0] <= b and b + 8 <= RTK[0] + RTK[1]:
        return f'⟨_, {head}.trans (copy_in (by decide) (by decide))⟩'
    return f'(ex_eq ({head}.trans (copy_out (by decide) (by decide) (by decide))) {ex_term(b, layers[1:])})'


def none_term(b, layers):
    base, ln, lst = layers[0]
    assert look(b, lst) is None
    head = f'(loadInt_look_none (B := {base}) (L := {ln}) (b := {b}#64) (by decide) (by decide) (by decide))'
    if base == 'Ent':
        return f'({head}.trans (ent_none (by decide)))'
    assert not (RTK[0] < b + 8 and b < RTK[0] + RTK[1])
    return f'({head}.trans ((copy_out (by decide) (by decide) (by decide)).trans {none_term(b, layers[1:])}))'


nlist = 0


def push_store(i, a, v):
    global L, N, cur_list_name
    assert a % 8 == 0
    prev = cur_list_name
    if N is None:
        L = [(a, v)] + L
        nm = f'L{i}'
    else:
        N[:] = [(a, v)] + N
        nm = f'N{i}'
    lists.append((i, nm, f'({a}#64, {v}#64) :: {prev}'))
    cur_list_name = nm


# ---------- shared memory ----------
M_name = 'M0'
mdefs = []
shared_vals = {}  # addr -> current value
SHIFT_COUNTS = {}

REG64 = r'\(\((\w+)\) \(W64\)\)'


def reg_val(i, r):
    return states[i]['regs'].get(r, 0)


def lean_reg(r, w='W64'):
    return f'(Reg.low .{r} .{w})'


steps = {}  # i -> (lean statement text, proof text, kind)

MASK = (1 << 64) - 1


def to_s64(x):
    return x - (1 << 64) if x >= (1 << 63) else x


for i in range(0, LAST):
    pc, W, t = ins[i]
    s, s2 = states[i], states[i + 1]
    assert s['pc'] == pc
    cidx, z = cells[pc]
    R, F, D = rname(i), fl_name(s['fl']), D_term()
    R2, F2 = rname(i + 1), fl_name(s2['fl'])
    HC = f'(cellM {cidx} {pc} rfl rfl (by decide +kernel) {R} {F} {D})'
    HS = '(by decide)'
    pre = f'(· = mk {R} {F} {D} {pc})'
    Mi, Xi = 'M', 'X'
    gen = True
    D2 = None
    pc2 = s2['pc']
    proof = None
    kind = 'x'

    def X(inner):
        return f'sgX hparse {HC} (by intro _ _ h; cases h) {HS} {inner}'

    m = None
    if (m := re.match(r'\(xor \(reg \(\((\w+)\) \(W32\)\)\) \(\(reg \(\(\1\) \(W32\)\)\)\)\)\)', t)):
        proof = X(f'(lx_xor32 (exec_xor_rr32_self {HC}) (by decide) (by decide) rfl)')
    elif (m := re.match(r'\((and|or) \(reg ' + REG64 + r'\) \(\(reg ' + REG64 + r'\)\)\)\)', t)):
        lem = {'and': 'exec_and_rr', 'or': 'exec_or_rr'}[m.group(1)]
        proof = X(f'(lx_logic ({lem} {HC}) (by decide) (by decide) rfl)')
    elif (m := re.match(r'\(and \(reg ' + REG64 + r'\) \(imm \(int64', t)):
        proof = X(f'(lx_logic (exec_and_ri {HC}) (by decide) (by decide) rfl)')
    elif t.startswith('(imul none'):
        proof = X(f'(lx_imul (exec_imul_rr {HC}) (by decide) (by decide) rfl)')
    elif (m := re.match(r'\((shl|shr) \(reg ' + REG64 + r'\) \(ShiftCountExpr\.cl\)\)\)', t)):
        proof = X(f'(lx_{m.group(1)} {HC} (by decide) (by decide) (by decide) (by decide) rfl)')
    elif (re.match(r'\(mov \(reg ' + REG64 + r'\) \(\(reg ' + REG64 + r'\)\)\)\)', t)
          or re.match(r'\(mov \(reg \(\((\w+)\) \(W(64|32)\)\)\) \(imm \(int64 \(?-?\d+\)?\)\)\)', t)
          or re.match(r'\((add|cmp) \(reg ' + REG64 + r'\) \(\(reg ' + REG64 + r'\)\)\)\)', t)
          or re.match(r'\(sub \(reg ' + REG64 + r'\) \(imm \(int64 \(?-?\d+\)?\)\)\)\)', t)
          or re.match(r'\(lea \(\((\w+)\) \(W64\)\) \{ base := some \(reg \((\w+)\)\), disp := int64', t)):
        proof = X(f'(lf (hx_reg rfl {HC} (by decide) (by decide) rfl))')
    elif (m := re.match(r'\(mov \(reg ' + REG64 + r'\) \(\(mem \{ base := some \(reg \(rbp\)\), disp := int64 \(?(-?\d+)\)? \}\)\)\)\)', t)):
        r, o = m.group(1), int(m.group(2))
        a = (reg_val(i, 'rbp') + o) & MASK
        lt, v = load_term(a, cur_layers())
        assert reg_val(i + 1, r) == v, (i, r, v, reg_val(i + 1, r))
        proof = X(f'(lf (hx_ld {HC} (a := {a}#64) (by decide) {lt} (by decide) rfl))')
    elif (m := re.match(r'\(mov \(mem \{ base := some \(reg \(rbp\)\), disp := int64 \(?(-?\d+)\)? \}\) \(\(reg ' + REG64 + r'\)\)\)\)', t)):
        o, r = int(m.group(1)), m.group(2)
        a = (reg_val(i, 'rbp') + o) & MASK
        v = reg_val(i, r)
        et = ex_term(a, cur_layers())
        proof = X(f'(lf (hx_st {HC} (a := {a}#64) (v := {v}#64) (by decide) {et} (by decide) rfl))')
        push_store(i, a, v)
    elif (m := re.match(r'\(push \(\(reg ' + REG64 + r'\)\)\)\)', t)):
        r = m.group(1)
        a = (reg_val(i, 'rsp') - 8) & MASK
        v = reg_val(i, r)
        et = ex_term(a, cur_layers())
        proof = X(f'(lf (hx_push {HC} (a := {a}#64) (v := {v}#64) (by decide) {et} (by decide) (by decide) rfl))')
        push_store(i, a, v)
    elif (m := re.match(r'\(pop \(reg ' + REG64 + r'\)\)\)', t)):
        r = m.group(1)
        a = reg_val(i, 'rsp')
        lt, v = load_term(a, cur_layers())
        assert reg_val(i + 1, r) == v
        proof = X(f'(lf (hx_pop {HC} (a := {a}#64) (by decide) {lt} (by decide) rfl))')
    elif (m := re.match(r'\(call \(Relrel \(sub \(label "([^"]+)"\)', t)):
        lab = m.group(1)
        a = (reg_val(i, 'rsp') - 8) & MASK
        v = pc + z
        assert labels[lab][1] == pc2
        et = ex_term(a, cur_layers())
        proof = X(f'(lf (hx_call {HC} {labname(lab)} (a := {a}#64) (v := {v}#64) (by decide) {et} (by decide) '
                  f'(by decide)))')
        push_store(i, a, v)
    elif t.startswith('(ret)'):
        a = reg_val(i, 'rsp')
        lt, v = load_term(a, cur_layers())
        assert v == pc2
        proof = X(f'(lf (hx_ret {HC} (a := {a}#64) (by decide) {lt} (by decide) (by decide)))')
    elif (m := re.match(r'\(jmp \(Relrel \(sub \(label "([^"]+)"\)', t)):
        lab = m.group(1)
        assert labels[lab][1] == pc2
        proof = X(f'(lf (hx_jmp {HC} {labname(lab)}))')
    elif (m := re.match(r'\(jcc \(CondCode\.(\w+)\) "([^"]+)"\)\)', t)):
        lab = m.group(2)
        if pc2 == pc + z:
            proof = X(f'(lf (hx_jccN {HC} (by decide) rfl))')
        else:
            assert labels[lab][1] == pc2
            proof = X(f'(lf (hx_jccT {HC} (by decide) {labname(lab)}))')
    elif (m := re.match(r'\(lea \(\((\w+)\) \(W64\)\) \{ base := some \(rip\), disp := sub \(label "([^"]+)"\)', t)):
        lab = m.group(2)
        proof = X(f'(lf (hx_leaRip {HC} {labname(lab)} (by decide) rfl))')
    elif t.startswith('(syscall)') and i == SIG_STEP:
        proof = f'sg_rtSigaction {D} M X'
        kind = 'k'
    elif t.startswith('(syscall)') and i == FS_STEP:
        proof = f'sg_archSetFs {D} M X'
        kind = 'k'
    elif t.startswith('(nop 1)') and i == TAKE_STEP:
        Llast = list(L)
        lists.append((i, 'Llast', cur_list_name))
        N = []
        cur_list_name = 'Nnil'
        proof = f'sg_take hparse {D} {M_name} rfl (by decide +kernel)'
        kind = 'take'
    elif (m := re.match(r'\((mov|xadd true|xchg)', t)) and '[' in t:
        ev = re.search(r'\[(\w+) (\d+)/8 (.*)\]', t)
        evk, a = ev.group(1), int(ev.group(2))
        if 'movfs' in t:
            r = re.match(r'\(movfs \(reg ' + REG64, t).group(1)
            val = shared_vals.get(a, None)
            nt = none_term(a, cur_layers())
            proof = (f'sgFsSh hparse {HC} {HS} (a := {a}#64) (by decide) {nt} (val := {val}#128) (by decide) '
                     f'(by decide) rfl')
            kind = 'sh'
        elif t.startswith('(mov (reg'):
            m2 = re.match(r'\(mov \(reg ' + REG64 + r'\) \(\(mem \{ base := some \(reg \((\w+)\)\), disp := int64 \(?(-?\d+)\)? \}', t)
            val = int(ev.group(3).split('=')[1])
            nt = none_term(a, cur_layers())
            proof = (f'sgLdSh hparse {HC} {HS} (a := {a}#64) ((eaddr_reg_disp _ _ _ _).trans (by decide)) {nt} '
                     f'(val := {val}#128) (by decide) (by decide) rfl')
            kind = 'sh'
        elif t.startswith('(mov (mem'):
            val = int(ev.group(3).split(':=')[1])
            nt = none_term(a, cur_layers())
            newM = f'M{i}'
            mdefs.append((i, newM, f'({M_name}.append {{ loc := ⟨{a}#64, 8⟩, val := {val}#128, tid := 0 }}).1'))
            proof = (f'sgStSh hparse {HC} {HS} (a := {a}#64) ((eaddr_reg_disp _ _ _ _).trans (by decide)) {nt} '
                     f'(val := {val}#128) (by decide) rfl')
            Mi = M_name
            M_name = newM
            shared_vals[a] = val
            kind = 'sh'
        else:
            old, nv = map(int, ev.group(3).split(' -> '))
            nt = none_term(a, cur_layers())
            newM = f'M{i}'
            mdefs.append((i, newM, f'({M_name}.append {{ loc := ⟨{a}#64, 8⟩, val := {nv}#128, tid := 0 }}).1'))
            if t.startswith('(xadd'):
                proof = (f'sgXaddSh hparse {HC} {HS} (a := {a}#64) ((eaddr_reg_disp _ _ _ _).trans (by decide)) {nt} '
                         f'(old := {old}#128) (nv := {nv}#128) (by decide) (by decide) (by decide) (by decide) rfl')
            else:
                proof = (f'sgXchgSh hparse {HC} {HS} (a := {a}#64) ((eaddr_reg_disp _ _ _ _).trans (by decide)) {nt} '
                         f'(old := {old}#128) (nv := {nv}#128) (by decide) (by decide) (by decide) rfl')
            Mi = M_name
            M_name = newM
            shared_vals[a] = nv
            kind = 'sh'
    else:
        raise Exception(f'unhandled {i}: {t}')
    post = f'(· = mk {R2} {F2} {D_term()} {pc2})'
    if kind == 'sh':
        if Mi == 'M':
            Mi = M_name
            M2 = M_name
        else:
            M2 = M_name
        stmt = f'Sg {pre} {Mi} X {post} {M2} X'
        binders = '{X : Kernel.KState}'
    elif kind == 'take':
        stmt = f'Sg {pre} {M_name} X0 {post} {M_name} X1'
        binders = ''
    else:
        stmt = f'Sg {pre} M X {post} M X'
        binders = '{M : Memory} {X : Kernel.KState}'
    steps[i] = dict(stmt=stmt, proof=proof, binders=binders, kind=kind, M=M_name)

json.dump(dict(last=LAST, steps={str(k): v for k, v in steps.items()}, rdefs=rdefs, fdefs=fdefs, lists=lists, mdefs=mdefs,
               labels=labels), open(GEN_DIR + '/gen.json', 'w'))
print('ok', len(steps), len(rdefs), len(fdefs), len(lists), len(mdefs))
