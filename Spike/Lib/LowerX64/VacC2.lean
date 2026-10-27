/-
**Construct premises that never fire** (x86-64; the twin of
`Spike/Lib/LowerA64/VacC2.lean`): `CallC2`, `CallC2H`, `LaneC` and
`NewBufC` (`Spike/Lib/LowerX64/Body2.lean`, `Spike/Lib/LowerX64/HeldC.lean`)
hold outright at a walk predicate `T` that meets no such construct: no
plain call (a `let x = call g …` under `T` with `g` a plain callee,
`Callee`, e.g. only calls of the output extern), no lane store, no buffer
allocation. E.g. at `T := TailAt2 p j` for a compiled block without them
(`hello1`'s setup block `rodata` has no call; its `main` no plain call, lane
store or buffer).

- `callC2_of_noCallee`, `callC2H_of_noCallee`: no plain call under `T`;
- `laneC_of_noXchg`: no lane store under `T`;
- `newBufC_of_noNewBuf`: no buffer allocation under `T`.
-/
import Spike.Lib.LowerX64.HeldC

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.LowerCall (Callee)

section Vac

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {lcx : Scc.Lower.Ctx} {fr : Scc.Emit.X64.Frame} {Cd : Int64 → List (Directive × Nat) → Prop}
  {Bl : Int64 → Nat → Label → Nat → Prop}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {W : FragS isa}
  {K : State → State → Prop} {ms : List TermRun.Frame → MemSide isa} {fp ra : BitVec 64} {tp : UInt64}
  {fs : List TermRun.Frame} {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat} {T : Expr → Prop}
  {Ab : FragS isa} {Lk : Expr × List (String × Scc.Lower.LitV) → Prop}

/-- **`CallC2` with no plain call under `T`.** -/
theorem callC2_of_noCallee (hno : ∀ x g is a ts e, T (.let_ x (.call g is a ts) e) → Callee lcx g → False) :
    CallC2 p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab Lk := by
  intro c0 pc pc' kk kk' env n x g is a ts e t w lits cs bufs _ hT _ _ _ _ _ hC
  exact (hno x g is a ts e hT hC).elim

/-- **`CallC2H` with no plain call under `T`.** -/
theorem callC2H_of_noCallee (hno : ∀ x g is a ts e, T (.let_ x (.call g is a ts) e) → Callee lcx g → False) :
    CallC2H p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab Lk := by
  intro c0 pc pc' kk kk' env n x g is a ts e t w lits cs bufs _ hT _ _ _ _ _ hC
  exact (hno x g is a ts e hT hC).elim

/-- **`LaneC` with no lane store under `T`.** -/
theorem laneC_of_noXchg (hno : ∀ x b j v e, ¬ T (.let_ x (.xchgAt b j v) e)) :
    LaneC p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab := by
  intro c0 pc pc' kk kk' env n x b j v e _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hT
  exact (hno x b j v e hT).elim

/-- **`NewBufC` with no buffer allocation under `T`.** -/
theorem newBufC_of_noNewBuf (hno : ∀ x cn τ e, ¬ T (.let_ x (.newBuf cn τ) e)) :
    NewBufC p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab Lk := by
  intro c0 pc pc' kk kk' env n x cn τ e _ _ _ _ _ _ _ _ _ hT
  exact (hno x cn τ e hT).elim

end Vac

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.callC2_of_noCallee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.callC2_of_noCallee

/-- info: 'Spike.Lib.LowerX64.callC2H_of_noCallee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.callC2H_of_noCallee

/-- info: 'Spike.Lib.LowerX64.laneC_of_noXchg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.laneC_of_noXchg

/-- info: 'Spike.Lib.LowerX64.newBufC_of_noNewBuf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.newBufC_of_noNewBuf
