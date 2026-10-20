/-
**WeakCore's own MS-queue `deq` lowered to
AArch64.**

WeakCore's `queueLib` (`WeakCore/CoreTerm.lean`, `deqBody`/`enqLoop`) differs
from msqueue2's `deq` (the MS queue pilots `MsqPilot`, `MsqAlloc` and `MsqX`):

- `deq` tries once: on `next = null` it returns `inr ()`; it retries only on
  a failed `head` CAS (`tail "deq" q`);
- no `head = tail` check: `head` may pass `tail`;
- the payload is loaded **after** the successful `head` CAS.

Lowering (`Lower/README.md`, the lowering table): `load false` ↦ `ldr`,
`cas false false` ↦ `mov xC,xE; casal xC,xV,[xA]; cmp xC,xE; b.ne`, `fld i` ↦
`add`, `ifnull` ↦ `cbz`, `tail "deq"` ↦ `b deq`.

- `deq(x0 = q) → (x0, x1)`: the result `sum τ unit` (τ = the payload word) is
  a **wide sum** (`[num j, w]`, tag word first, then the
  arm's payload): `x0 = 0`, `x1 =` the payload for `inl x`; `x0 = 1` for
  `inr ()` (no payload word; `x1` is not written). The data word is
  4 bytes (`ldr w1`), as the existing protocol `form2` fixes (`P.dat =
  ⟨n1, 4⟩`; a WeakCore `Int` would be `ldr x1`).
- `enq(x0 = q, x1 = node)`: `enqLoop`. Its control flow is `MsqPilot`'s
  `enqFrag` exactly (help on a non-null `next` and retry either way; retry on
  a failed link CAS; the swing CAS's result ignored), with `ldr` in place of
  msqueue2's `ldar` for the two loads (`wcEnqFrag`).

Contents: the fragments, the texts of the two shapes (one dequeuer calling
twice; two dequeuers calling once), the runner layouts, the start states and
the explorer runs.
-/
import Kraken.Promising.Lower.MsqPilotProg

namespace Kraken.Promising.Lower.WcMsq

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG
open Kraken.AArch64.Parser

/-- **`deq(x0 = q) → (x0 = tag, x1 = payload)`**: WeakCore's `deqBody`. -/
def wcDeqFrag : Program := parseAArch64("
deq:
    ldr x3, [x0]
    add x8, x3, #8
    ldr x5, [x8]
    cbz x5, deq_empty
    mov x6, x3
    casal x6, x5, [x0]
    cmp x6, x3
    b.ne deq
    ldr w1, [x5]
    mov x0, #0
    ret
deq_empty:
    mov x0, #1
    ret
")

/-- **`enq(x0 = q, x1 = node)`**: WeakCore's `enqLoop` (`MsqPilot`'s `enqFrag`
with `ldr` loads). -/
def wcEnqFrag : Program := parseAArch64("
enq:
    mov x2, x1
    add x1, x0, #8
enq_loop:
    ldr x3, [x1]
    add x8, x3, #8
    ldr x4, [x8]
    cbnz x4, enq_fix
    mov x5, #0
    casal x5, x2, [x8]
    cbnz x5, enq_loop
    mov x5, x3
    casal x5, x2, [x1]
    ret
enq_fix:
    mov x5, x3
    casal x5, x4, [x1]
    b enq_loop
")

/-- The enqueuer's text: `MsqPilot`'s `main_e`, then `wcEnqFrag`. -/
def progE : Program :=
  (Directive.label "main_e" :: MsqPilot.mainEBody) ++ wcEnqFrag ++ [Directive.label "e_end"]

/-- Between the `bl deq`s: the first result `(x0, x1)` to the callee-saved
`x20`/`x23`, the argument `q`. -/
def dMid : Program := parseAArch64("
    mov x20, x0
    mov x23, x1
    mov x0, x21
")

/-- Behind the second `bl deq`: the results to `x10, x11` (first tag,
payload) and `x12, x13` (second), return. -/
def dTail : Program := parseAArch64("
    mov x10, x20
    mov x11, x23
    mov x12, x0
    mov x13, x1
    mov x30, x19
    ret
")

/-- `main_d` (one dequeuer, two calls): `MsqPilot`'s `dPre` (save the link,
argument `q`), `bl deq`, `dMid`, `bl deq`, `dTail`. -/
def mainDBody : Program := MsqPilot.dPre ++ MsqPilot.blTo "deq" :: (dMid ++ MsqPilot.blTo "deq" :: (dTail ++ []))

/-- **Shape A, the dequeuer's text**: `main_d`, then `deq`. -/
def progD : Program := parseAArch64("
main_d:
    mov x19, x30
    mov x0, x21
    bl deq
    mov x20, x0
    mov x23, x1
    mov x0, x21
    bl deq
    mov x10, x20
    mov x11, x23
    mov x12, x0
    mov x13, x1
    mov x30, x19
    ret
deq:
    ldr x3, [x0]
    add x8, x3, #8
    ldr x5, [x8]
    cbz x5, deq_empty
    mov x6, x3
    casal x6, x5, [x0]
    cmp x6, x3
    b.ne deq
    ldr w1, [x5]
    mov x0, #0
    ret
deq_empty:
    mov x0, #1
    ret
d_end:
")

/-- `progD` is its pieces. -/
theorem progD_split : progD = (Directive.label "main_d" :: mainDBody) ++ wcDeqFrag ++ [Directive.label "d_end"] := by
  decide

/-- `main_d1` (a dequeuer calling once): result in `x10, x11`. -/
def mainD1Body : Program := parseAArch64("
    mov x19, x30
    mov x0, x21
    bl deq
    mov x10, x0
    mov x11, x1
    mov x30, x19
    ret
")

/-- **Shape B, a dequeuer's text**: `main_d1`, then `deq`. -/
def progD1 : Program := (Directive.label "main_d1" :: mainD1Body) ++ wcDeqFrag ++ [Directive.label "d1_end"]

/-- info: (33, 30, 24) -/
#guard_msgs in
#eval (progE.length, progD.length, progD1.length)

/-! ## Runner-style layouts and start states -/

@[reducible] def layoutE : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize progE
@[reducible] def layoutD : _root_.Layout := Kraken.Layout.ofSize 0x200000 Directive.fakeSize progD
@[reducible] def layoutD1 : _root_.Layout := Kraken.Layout.ofSize 0x300000 Directive.fakeSize progD1
@[reducible] def layoutD2 : _root_.Layout := Kraken.Layout.ofSize 0x400000 Directive.fakeSize progD1

instance validD : Executable.ValidLayout (layoutD progD) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-- The enqueuer (`MsqPilot`'s `threadE` with this text). -/
def threadE : AArch64.State where
  exe := layoutE progE
  endPc := 0x100000 + 4 * 28
  st := ({ regs := { X21 := 0x1000, X22 := 0x1200, X23 := 0x1300, X30 := 0x100000 + 4 * 28 } }, 0x100000)

/-- Shape A's dequeuer. -/
def threadD : AArch64.State where
  exe := layoutD progD
  endPc := 0x200000 + 4 * 26
  st := ({ regs := { X21 := 0x1000, X30 := 0x200000 + 4 * 26 } }, 0x200000)

/-- Shape B's first dequeuer. -/
def threadD1 : AArch64.State where
  exe := layoutD1 progD1
  endPc := 0x300000 + 4 * 20
  st := ({ regs := { X21 := 0x1000, X30 := 0x300000 + 4 * 20 } }, 0x300000)

/-- Shape B's second dequeuer. -/
def threadD2 : AArch64.State where
  exe := layoutD2 progD1
  endPc := 0x400000 + 4 * 20
  st := ({ regs := { X21 := 0x1000, X30 := 0x400000 + 4 * 20 } }, 0x400000)

/-- A result `(tag, payload)` with the payload read as `0` on `inr`. -/
def res (tag val : BitVec 64) : Nat × Nat :=
  (tag.toNat, if tag = 0 then val.toNat else 0)

/-- **Shape A explorer**: per final configuration, the dequeuer's two results. -/
def exploreA (o : ExploreOpts) : List ((Nat × Nat) × (Nat × Nat)) × Bool × List String :=
  let r := explore Arch.armv8 (Config.init [threadE, threadD] MsqPilot.initMem : Config isa)
    (fun c => match c.threads.toList with
      | [_, d] => let g := d.st.st.1.regs
        (res g.X10.toBitVec g.X11.toBitVec, res g.X12.toBitVec g.X13.toBitVec)
      | _ => ((9, 9), (9, 9))) o
  (r.finals, r.boundHit, r.faults)

/-- **Shape B explorer**: per final configuration, the two dequeuers' results. -/
def exploreB (o : ExploreOpts) : List ((Nat × Nat) × (Nat × Nat)) × Bool × List String :=
  let r := explore Arch.armv8
    (Config.init [threadE, threadD1, threadD2] MsqPilot.initMem : Config isa)
    (fun c => match c.threads.toList with
      | [_, d1, d2] => let g1 := d1.st.st.1.regs; let g2 := d2.st.st.1.regs
        (res g1.X10.toBitVec g1.X11.toBitVec, res g2.X10.toBitVec g2.X11.toBitVec)
      | _ => ((9, 9), (9, 9))) o
  (r.finals, r.boundHit, r.faults)

/-- **Shape A** (`isa`, promise-free, `boundHit = false`: exhausted): the
dequeuer's `(tag, payload)` pairs (payload read as `0` on `inr`). Exactly
the four outcomes of a sequential FIFO with try-once dequeues:
`(v1, E)`, `(E, E)`, `(E, v1)`, `(v1, v2)`. No fault. -/
def wcMsqRunA := exploreA { fuel := 60, maxPromises := some 0 }

/-- info: ([((0, 1), 1, 0), ((1, 0), 1, 0), ((1, 0), 0, 1), ((0, 1), 0, 2)], false, []) -/
#guard_msgs in
#eval wcMsqRunA

/-- **Shape B** (`isa`, promise-free, exhausted): the two dequeuers'
results; as shape A plus `(v2, v1)` (the second dequeuer dequeued first).
About 30 s. -/
def wcMsqRunB := exploreB { fuel := 80, maxPromises := some 0 }

/-- info: ([((0, 1), 1, 0), ((1, 0), 1, 0), ((1, 0), 0, 1), ((0, 1), 0, 2), ((0, 2), 0, 1)], false, []) -/
#guard_msgs in
#eval wcMsqRunB

/-- **Shape A with `MsqPilot`'s enqueuer** (`MsqPilot.progE`, `ldar` loads; the
configuration of `wcMsq_promising`): the same four outcomes. -/
def wcMsqRunA' : List ((Nat × Nat) × (Nat × Nat)) × Bool × List String :=
  let r := explore Arch.armv8 (Config.init [MsqPilot.threadE, threadD] MsqPilot.initMem : Config isa)
    (fun c => match c.threads.toList with
      | [_, d] => let g := d.st.st.1.regs
        (res g.X10.toBitVec g.X11.toBitVec, res g.X12.toBitVec g.X13.toBitVec)
      | _ => ((9, 9), (9, 9))) { fuel := 60, maxPromises := some 0 }
  (r.finals, r.boundHit, r.faults)

/-- info: ([((0, 1), 1, 0), ((1, 0), 1, 0), ((1, 0), 0, 1), ((0, 1), 0, 2)], false, []) -/
#guard_msgs in
#eval wcMsqRunA'

/-! ## The static checks of the EnvG link -/

section Static

variable [layout : _root_.Layout]

theorem progD_rmwLive : (layout progD).rmwLive = true := by rw [Layout.apply_rmwLive]; decide

theorem progD_phase1F [Executable.ValidLayout (layout progD)] : Phase1TreeF (layout progD) :=
  phase1TreeF_of_dirs (by dirs_phase1F progD)

theorem progD_noFault : DirsNoFault (layout progD) := by dirs_no_fault' progD

end Static

end Kraken.Promising.Lower.WcMsq
