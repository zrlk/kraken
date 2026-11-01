/-
**`h2`'s invariant at hello** (`inv2H`, AArch64; layer 1; the hello twin of
`Spike/Lib/A64WakeH1Inv.lean`'s `inv1W`, one level up): the statement of the segment after the box's allocation
(`HelloPreA.H2StmtH`, `HelloO.OPremH.h2`) with its invariant fixed, generic in the level's fragment `W2`, outside
move `K` and memory side `ms2`, so that the machine side (the post-box nodes up to the `clone`) and the clone's
consumers (`HelloHClW.hClH_of`'s `hown2`, `hx1`) agree on one object.

`inv2H … l b n l' b' n'` is the greatest closed invariant (`A64GfpS.GfpS`) inside `W2 … ∧ X2H …` under `K` at
`ms2 …` and the twice extended placement. `X2H` carries the per-state facts `W2` does not: at the clone's pc
`CloneInvH`, `c`'s label of positive size, the child's stack owned, `x1` at its top (`kOf`), main's segment-end
facts (`CloneSegD`) and `x3` the second TCB (`tH`); at the take pc the
site's range the child's stack, main's stack owned, the child's not private (wake's `X1W`, plus `x1`).

- `X2H`, `x2H_off`: the per-state facts; off both pcs they hold outright.
- `inv2H`, `segInvS_inv2H`: the invariant, a segment inside `W2`.
- `x2H_of`, `cloneInv2_of`, `lsize2_of`, `own2_of`, `x1_2_of`, `seg2_of`, `x3_2_of`, `take2_of`: `X2H`'s clauses at
  `inv2H`'s pairs (`H2StmtH`'s clone clause; `hClH_of`'s `hown2`, `hx1`; `HelloSegEnd.hpc_ofR`'s `hseg`).
- `inv2H_of_segWS`: the start of a segment inside `W2 ∧ X2H` with no exit is in `inv2H` (how the landing gets in).
- `h2Stmt_of`: `H2StmtH` at `inv2H`, given the landing `Box` in it.
-/
import Spike.Lib.A64HelloHClW
import Spike.Lib.A64GfpS
import Spike.Lib.A64HelloCloneSegD
import Spike.Lib.A64HelloWcSp3

namespace Spike.Lib.HelloH2Inv

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib (Arena FragS SegWS MemSide)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (SegInvS)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.HelloPreA (clonePcH CloneInvH H2StmtH)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.A64GfpS (GfpS)

/-- **`h2`'s per-state facts**: at the clone's pc, `CloneInvH` at the placement `lbl`, `c`'s label of positive
size under `lsize`, the child's stack owned, `x1` its top (`kOf`), main's segment-end facts
(`HelloCloneSegD.CloneSegD`, row 5j-segEnd-X2) and `x3` the second TCB (`tH`, root-hCP); at the take pc `a`, the
site's range the child's stack, main's stack owned and the child's not private. -/
def X2H (L : RuntimeLayout) (a endPc : Int64) (lbl : Lbl) (lsize : Lsize) : FragS isaLSE2 := fun s c fs =>
  (pcOf s = clonePcH L → CloneInvH L endPc lbl s c fs ∧
    -- `c`'s label has cells: the landing binds `o` to the box with `n' = 1`, `c` is `publish o`
    (∀ l', TermRun.evalAt c.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l', 0⟩ 0)]) →
      0 < lsize l') ∧
    -- the child's stack is owned at the clone (`hClH_of`'s `hown2`): `scc_rt_thread_init` took it
    Spike.Lib.A64Consumer.Owned L.Λ (Spike.Lib.A64.Rt.PreChild.r1Of L.lab) s ∧
    -- `x1` the child's stack top (`hClH_of`'s `hx1`; `ClonePostH` leaves it existential)
    s.st.1.regs.X1.toBitVec = Spike.Lib.A64.Flow.WakeWc.kOf L.lab ∧
    -- main's segment end (`HelloSegEnd.hpc_ofR`'s `hseg`): `At` in the widened region, base, alignment, `ra`, `x13`
    Spike.Lib.HelloCloneSegD.CloneSegD L endPc s c ∧
    -- `x3` the second TCB (`HelloTcbArea.x3_of_cloneMidH`; root-hCP's `hx3`, row B8-hS-Q2's clone side)
    (s.st.1.regs.getXReg .X3).toBitVec = Spike.Lib.A64.Flow.HelloWc.tH L.lab) ∧
    (pcOf s = a.toBitVec.toNat →
      Kernel.siteRange abi s = Spike.Lib.A64.Rt.PreChild.r1Of L.lab ∧
      Spike.Lib.A64Consumer.Owned L.Λ (Spike.Lib.A64.Rt.Ti2.r0Of L.lab) s ∧
      ¬ Spike.Lib.A64.Flow.Ret0.StackM (Spike.Lib.A64.Rt.PreChild.r1Of L.lab) s.st.1)

/-- **`X2H` off the clone's and the take's pcs**: both clauses are guarded by the pc. -/
theorem x2H_off {L : RuntimeLayout} {a endPc : Int64} {lbl : Lbl} {lsize : Lsize} {s : State}
    {c : Spike.Lib.Ctl} {fs : List TermRun.Frame} (hc : pcOf s ≠ clonePcH L) (ha : pcOf s ≠ a.toBitVec.toNat) :
    X2H L a endPc lbl lsize s c fs :=
  ⟨fun h => absurd h hc, fun h => absurd h ha⟩

section Inv

variable (W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2)
  (K : State → State → Prop)
  (ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2)
  (L : RuntimeLayout) (a endPc : Int64) (L0 : Lbl) (ls0 : Lsize)

set_option hygiene false in
/-- The level's placement. -/
local notation "L2" => fun (l : WeakMem.AllocLabel) (b : Nat) (l' : WeakMem.AllocLabel) (b' : Nat) =>
  Spike.Lib.A64ConsumerA.upd (Spike.Lib.A64ConsumerA.upd L0 l b) l' b'

set_option hygiene false in
/-- The level's sizes. -/
local notation "S2" => fun (l : WeakMem.AllocLabel) (n : Nat) (l' : WeakMem.AllocLabel) (n' : Nat) =>
  Spike.Lib.A64ConsumerA.updN (Spike.Lib.A64ConsumerA.updN ls0 l n) l' n'

/-- **`h2`'s invariant**: the greatest closed invariant inside `W2 ∧ X2H` under `K` at `ms2`. -/
def inv2H (l : WeakMem.AllocLabel) (b n : Nat) (l' : WeakMem.AllocLabel) (b' n' : Nat) : FragS isaLSE2 :=
  GfpS (fun s c fs => W2 l b n l' b' n' s c fs ∧ X2H L a endPc ((L2) l b l' b') ((S2) l n l' n') s c fs)
    K helloSrc ((L2) l b l' b') (ms2 l b n l' b' n')

/-- **`inv2H` is a segment inside `W2`.** -/
theorem segInvS_inv2H (l : WeakMem.AllocLabel) (b n : Nat) (l' : WeakMem.AllocLabel) (b' n' : Nat) :
    SegInvS (W2 l b n l' b' n') K helloSrc ((L2) l b l' b') (ms2 l b n l' b' n')
      (inv2H W2 K ms2 L a endPc L0 ls0 l b n l' b' n') :=
  fun s c fs hi => let h' := Spike.Lib.A64GfpS.segInvS_gfpS s c fs hi; ⟨h'.1.1, h'.2⟩

variable {W2 K ms2 L a endPc L0 ls0} {l : WeakMem.AllocLabel} {b n : Nat} {l' : WeakMem.AllocLabel} {b' n' : Nat}
  {s : State} {c : Spike.Lib.Ctl} {fs : List TermRun.Frame}

/-- **`X2H` at `inv2H`'s pairs.** -/
theorem x2H_of (h : inv2H W2 K ms2 L a endPc L0 ls0 l b n l' b' n' s c fs) :
    X2H L a endPc ((L2) l b l' b') ((S2) l n l' n') s c fs :=
  (Spike.Lib.A64GfpS.segInvS_gfpS s c fs h).1.2

/-- **`H2StmtH`'s clone clause** at `inv2H`. -/
theorem cloneInv2_of (h : inv2H W2 K ms2 L a endPc L0 ls0 l b n l' b' n' s c fs) (hpc : pcOf s = clonePcH L) :
    CloneInvH L endPc ((L2) l b l' b') s c fs :=
  ((x2H_of h).1 hpc).1

/-- **`c`'s label has cells** at `inv2H`'s clone states. -/
theorem lsize2_of (h : inv2H W2 K ms2 L a endPc L0 ls0 l b n l' b' n' s c fs) (hpc : pcOf s = clonePcH L)
    (l'' : WeakMem.AllocLabel)
    (hc : TermRun.evalAt c.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l'', 0⟩ 0)])) :
    0 < (S2) l n l' n' l'' :=
  ((x2H_of h).1 hpc).2.1 l'' hc

/-- **The child's stack owned** at `inv2H`'s clone states (`HelloHClW.hClH_of`'s `hown2`). -/
theorem own2_of (h : inv2H W2 K ms2 L a endPc L0 ls0 l b n l' b' n' s c fs) (hpc : pcOf s = clonePcH L) :
    Spike.Lib.A64Consumer.Owned L.Λ (Spike.Lib.A64.Rt.PreChild.r1Of L.lab) s :=
  ((x2H_of h).1 hpc).2.2.1

/-- **`x1` the child's stack top** at `inv2H`'s clone states (`HelloHClW.hClH_of`'s `hx1`). -/
theorem x1_2_of (h : inv2H W2 K ms2 L a endPc L0 ls0 l b n l' b' n' s c fs) (hpc : pcOf s = clonePcH L) :
    s.st.1.regs.X1.toBitVec = Spike.Lib.A64.Flow.WakeWc.kOf L.lab :=
  ((x2H_of h).1 hpc).2.2.2.1

/-- **main's segment-end facts** at `inv2H`'s clone states (`HelloSegEnd.hpc_ofR`'s `hseg`). -/
theorem seg2_of (h : inv2H W2 K ms2 L a endPc L0 ls0 l b n l' b' n' s c fs) (hpc : pcOf s = clonePcH L) :
    Spike.Lib.HelloCloneSegD.CloneSegD L endPc s c :=
  ((x2H_of h).1 hpc).2.2.2.2.1

/-- **`x3` the second TCB** at `inv2H`'s clone states (root-hCP's `hx3`). Not vacuous: the real clone state
(`CloneMidH`, `H2CP.hCP_of`, the only producer of `X2H`'s clone clause) has `x3 = tH` by
`HelloTcbArea.x3_of_cloneMidH`. -/
theorem x3_2_of (h : inv2H W2 K ms2 L a endPc L0 ls0 l b n l' b' n' s c fs) (hpc : pcOf s = clonePcH L) :
    (s.st.1.regs.getXReg .X3).toBitVec = Spike.Lib.A64.Flow.HelloWc.tH L.lab :=
  ((x2H_of h).1 hpc).2.2.2.2.2

/-- **The take's facts** at `inv2H`'s take states: the site's range the child's stack, main's stack owned, the
child's not private. -/
theorem take2_of (h : inv2H W2 K ms2 L a endPc L0 ls0 l b n l' b' n' s c fs) (hpc : pcOf s = a.toBitVec.toNat) :
    Kernel.siteRange abi s = Spike.Lib.A64.Rt.PreChild.r1Of L.lab ∧
      Spike.Lib.A64Consumer.Owned L.Λ (Spike.Lib.A64.Rt.Ti2.r0Of L.lab) s ∧
      ¬ Spike.Lib.A64.Flow.Ret0.StackM (Spike.Lib.A64.Rt.PreChild.r1Of L.lab) s.st.1 :=
  (x2H_of h).2 hpc

/-- **The start of a segment inside `W2 ∧ X2H` with no exit is in `inv2H`** (`gfpS_of_segWS`). -/
theorem inv2H_of_segWS {P : FragS isaLSE2}
    (h : SegWS (fun s c fs => W2 l b n l' b' n' s c fs ∧ X2H L a endPc ((L2) l b l' b') ((S2) l n l' n') s c fs)
      K helloSrc ((L2) l b l' b') (ms2 l b n l' b' n') P (fun _ _ _ => False)) :
    ∀ s c fs, P s c fs → inv2H W2 K ms2 L a endPc L0 ls0 l b n l' b' n' s c fs :=
  Spike.Lib.A64GfpS.gfpS_of_segWS h

variable (W2 K ms2 L a endPc L0 ls0)

/-- **`H2StmtH` at `inv2H`**, given the landing `Box` in it (`hB`). -/
theorem h2Stmt_of (ar : Arena)
    (Box : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → State → Spike.Lib.Ctl → Prop)
    (hB : ∀ l b n l' b' n', L0 l = none → AllocLand ar.heap ar.cells b n →
      Spike.Lib.A64ConsumerA.upd L0 l b l' = none → AllocLand ar.heap ar.cells b' n' →
      ∀ s c, Box l b n l' b' n' s c → inv2H W2 K ms2 L a endPc L0 ls0 l b n l' b' n' s c []) :
    H2StmtH W2 K ar L0 ms2 L endPc Box (inv2H W2 K ms2 L a endPc L0 ls0) :=
  fun l b n l' b' n' hl hb hl' hb' =>
    ⟨segInvS_inv2H W2 K ms2 L a endPc L0 ls0 l b n l' b' n', hB l b n l' b' n' hl hb hl' hb',
      fun _ _ _ h hpc => cloneInv2_of h hpc⟩

end Inv

end Spike.Lib.HelloH2Inv

/-- info: 'Spike.Lib.HelloH2Inv.segInvS_inv2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloH2Inv.segInvS_inv2H

/-- info: 'Spike.Lib.HelloH2Inv.own2_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloH2Inv.own2_of

/-- info: 'Spike.Lib.HelloH2Inv.x1_2_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloH2Inv.x1_2_of

/-- info: 'Spike.Lib.HelloH2Inv.inv2H_of_segWS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloH2Inv.inv2H_of_segWS

/-- info: 'Spike.Lib.HelloH2Inv.h2Stmt_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloH2Inv.h2Stmt_of
