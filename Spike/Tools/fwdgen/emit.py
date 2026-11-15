#!/usr/bin/env python3
"""Emit chunk module k: steps [lo, hi)."""
import json, os, sys

GEN_DIR = os.environ.get('FWDGEN_DIR', '/tmp/fwdgen')
g = json.load(open(GEN_DIR + '/gen.json'))
steps = {int(k): v for k, v in g['steps'].items()}
LAST = g['last']
CH = [(a, min(a + 36, LAST)) for a in range(0, LAST, 36)]
k = int(sys.argv[1])
lo, hi = CH[k - 1]
prev = 'Spike.Test.HelloRootL0XClosedStep' if k == 1 else f'Spike.Test.HelloRootL0XClosedC{k - 1}'
out = []
W = out.append

W(f'''/-
**`hello.w` on x86-64, the closed run, chunk {k}**: steps {lo} … {hi - 1} of
thread 0 from the load (`HelloRootL0XClosedStep`), one `SegP` segment per
instruction, composed into `c{k}`.

Generated from the reference run of the program (the states before every
step: registers `R…`, flags `F_…` (`cf pf af zf sf of`), private memory the
entry stack after the 8-byte stores `L…` (after the take: the taken copy
`B2` after `N…`), shared memory the write chain `M…`). Every step is proved,
not trusted: the generator only chooses the lemma and the witnesses.
-/
import {prev}

namespace Spike.Test.HelloRootL0XClosed

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Spike.Test.HelloLinkedX64 (Λe)
open Spike.Lib.Fwd

set_option maxRecDepth 100000
''')

if k == 1:
    W('''/-! ## Labels -/
''')
    for name, (kd, a) in g['labels'].items():
        ln = 'lab_' + name.replace('.', '_')
        if kd == 'code':
            W(f'theorem {ln} : (_root_.Executable.labels st0.exe).label "{name}" = Int64.ofNat {a} :=\n'
              f'  Scc.Cert.Rt.X64.label_threadAt_of_codeLabel habove (by decide +kernel)')
        else:
            W(f'theorem {ln} : (_root_.Executable.labels st0.exe).label "{name}" = Int64.ofNat {a} :=\n'
              f'  Scc.Cert.Rt.X64.label_threadAt_of_sym (by decide +kernel) (by decide +kernel) (by decide +kernel)\n'
              f'    (Scc.Cert.Rt.X64.ne_label_of_codeLabel (lo := Λe.code.lo) (by decide +kernel))')
    W('''
/-- A mapped slot, through an equation of loads. -/
theorem ex_eq {m m' : DataMem} {a b : BitVec 64} (h : Mem.loadInt m a 8 = Mem.loadInt m' b 8)
    (hb : ∃ j, Mem.loadInt m' b 8 = some j) : ∃ j, Mem.loadInt m a 8 = some j := by
  rw [h]; exact hb

/-! ## States -/

abbrev Lnil : List (BitVec 64 × BitVec 64) := []
''')
    for n, (i, v) in g['fdefs'].items():
        W(f'abbrev {n} : StatusFlags := {v}')
    W('')

# definitions
for (i, n, v) in g['rdefs']:
    if (k == 1 and i <= hi) or (k > 1 and CH[k - 2][1] < i <= hi):
        W(f'abbrev {n} : Reg64s := {v}')
for (i, n, v) in g['lists']:
    if lo <= i < hi:
        if n == 'Llast':
            W(f'abbrev Llast : List (BitVec 64 × BitVec 64) := {v}')
            W('/-- The private memory after the take. -/\nabbrev B2 : DataMem := Kernel.copyRange ∅ (stores Ent Llast) rTk')
            W('abbrev Nnil : List (BitVec 64 × BitVec 64) := []')
        else:
            W(f'abbrev {n} : List (BitVec 64 × BitVec 64) := {v}')
for (i, n, v) in g['mdefs']:
    if lo <= i < hi:
        W(f'abbrev {n} : Memory := {v}')
W('')
W('/-! ## Steps -/\n')
for i in range(lo, hi):
    s = steps[i]
    b = (' ' + s['binders']) if s['binders'] else ''
    hp = 'hparse' if 'hparse' in s['proof'] else '_hparse'
    W(f'theorem s{i} ({hp} : Parse){b} :\n    {s["stmt"]} :=\n  {s["proof"]}\n')

# chunk theorem
first, last = steps[lo], steps[hi - 1]
pre = first['stmt'].split(' M')[0] if False else None


def close(s, j):
    d = 0
    for x in range(j, len(s)):
        if s[x] == '(':
            d += 1
        elif s[x] == ')':
            d -= 1
            if d == 0:
                return x + 1
    raise Exception(s)


def parts(stmt):
    # Sg PRE Mi Xi POST M2 X2
    body = stmt[3:]
    i1 = close(body, 0)
    p = body[:i1]
    rest = body[i1:].split()
    Mi, Xi = rest[0], rest[1]
    j = body.index('(·', i1)
    j2 = close(body, j)
    q = body[j:j2]
    rest2 = body[j2:].split()
    return p, Mi, Xi, q, rest2[0], rest2[1]


P0, M0_, X0_, _, _, _ = parts(first['stmt'])
_, _, _, Q, M2_, X2_ = parts(last['stmt'])
# memory: first concrete M in chunk
Ms = [parts(steps[i]['stmt']) for i in range(lo, hi)]
concrete = [m for p in Ms for m in (p[1], p[4]) if m != 'M']
Min = next((p[1] for p in Ms if p[1] != 'M'), None)
Mout = next((p[4] for p in reversed(Ms) if p[4] != 'M'), None)
if Min is None:
    Min = Mout = 'M'
Xin = 'X0' if any(p[2] == 'X0' for p in Ms) else 'X'
Xout = 'X1' if any(p[5] == 'X1' for p in Ms) else 'X'
binders = []
if Min == 'M':
    binders.append('{M : Memory}')
if Xin == 'X' or Xout == 'X':
    binders.append('{X : Kernel.KState}')
b = (' ' + ' '.join(binders)) if binders else ''
W(f'/-- **Steps {lo} … {hi - 1}.** -/')
W(f'theorem c{k} (hparse : Parse){b} :\n    Sg {P0} {Min} {Xin} {Q} {Mout} {Xout} :=')
terms = [f'(s{i} hparse)' for i in range(lo, hi)]
expr = terms[-1]
for t in reversed(terms[:-1]):
    expr = f'SegP.trans {t} <|\n  {expr}'
W('  ' + expr)
W('')
W(f"/-- info: 'Spike.Test.HelloRootL0XClosed.c{k}' depends on axioms: [propext, Classical.choice, Quot.sound] -/")
W(f'#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.c{k}')
W('\nend Spike.Test.HelloRootL0XClosed')
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'Test', f'HelloRootL0XClosedC{k}.lean'), 'w').write('\n'.join(out) + '\n')
print('wrote', k, Min, Mout, Xin, Xout)
