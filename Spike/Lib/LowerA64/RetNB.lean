/-
**The return's exit with the source facts for the caller** (AArch64):
`retN2` with `RetL` (the returned atom at the callee's return type), the
exit a callee's segment at a plain call of an `Accepted2` body ends in; the
twin of `Spike/Lib/LowerX64/RetNB.lean`.

- `retNB`: `retN2`'s invariant and `RetL ty`;
- `ExitC2B`: `ExitC2` at `retNB`; `ExitC2B.toC2` (forgetting `RetL`),
  `ExitC2B.trans` (the ghost re-anchored by a frame run).
-/
import Spike.Lib.LowerA64.Body2
import Spike.Lib.Src.RetB

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.LowerNode

/-- **The return's exit with `RetL`**: `retN2`'s node, its invariant with
the returned atom's facts at the callee's return type `ty`. -/
def retNB (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (fp ra : BitVec 64) (c0 : Ctl)
    (ty : Ty) : ND :=
  ⟨Int64.ofBitVec ra, ⟨0, []⟩, fun σ c => (RetJ2 lbl fp ra σ c ∧ LocalRun p c0 c) ∧ RetL ty c⟩

section RetNB

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **The body's exits at the frames `fs` with `RetL`**: `ExitC2` at
`retNB`. -/
def ExitC2B (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (fp ra : BitVec 64) (tp : UInt64) (c0 : Ctl) (fs : List TermRun.Frame)
    (ty : Ty) (Ab : FragS isaLSE2) : FragS isaLSE2 :=
  fun s c fs' =>
    (fs' = fs ∧ ∃ c0', FrameRunM p (c0, fs) (c0', fs) ∧
      At exe endPc R F ((retNB p lbl fp ra c0' ty).withTp tp) s c) ∨
      Ab s c fs'

/-- **`ExitC2B` is an `ExitC2`** (`RetL` dropped). -/
theorem ExitC2B.toC2 {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl} {fs : List TermRun.Frame}
    {ty : Ty} {Ab : FragS isaLSE2} {s : State} {c : Ctl}
    {fs' : List TermRun.Frame} (h : ExitC2B p lbl exe endPc R F fp ra tp c0 fs ty Ab s c fs') :
    ExitC2 p lbl exe endPc R F fp ra tp c0 fs Ab s c fs' := by
  rcases h with ⟨e, c0', hr, he, hn, hd, hpc, σ, hA, hFm, ⟨hJ, -⟩, htp⟩ | h
  · exact .inl ⟨e, c0', hr, he, hn, hd, hpc, σ, hA, hFm, hJ, htp⟩
  · exact .inr h

/-- **`ExitC2B` re-anchored by a frame run** of the ghost. -/
theorem ExitC2B.trans {fp ra : BitVec 64} {tp : UInt64} {c0 c0' : Ctl} {fs : List TermRun.Frame}
    {ty : Ty} {Ab : FragS isaLSE2}
    (hr : FrameRunM p (c0, fs) (c0', fs)) :
    ∀ s c fs', ExitC2B p lbl exe endPc R F fp ra tp c0' fs ty Ab s c fs' →
      ExitC2B p lbl exe endPc R F fp ra tp c0 fs ty Ab s c fs' :=
  fun _ _ _ h => h.imp_left fun ⟨e, c1, hr', h⟩ => ⟨e, c1, hr.trans hr', h⟩

end RetNB

end Spike.Lib.LowerA64

/-- info: 'Spike.Lib.LowerA64.ExitC2B.toC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.ExitC2B.toC2
