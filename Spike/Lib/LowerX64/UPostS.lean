/-
**The user function's post at depth** (x86-64, H7a calls): `UPost`
(`Spike/Lib/LowerX64/UserCall.lean`) with a frame run from the start in
place of the local run, so that `main` may call (its source's frames pushed
and popped before its return), and `main`'s exit there (`uPost_exit`'s
twin, `Spike/Lib/LowerX64/StartU.lean`).

- `UPostS`: the source control is the start `c0` (held back), from which a
  frame run at the empty frames reaches the return of `v` (`RetV`).
- `UPost.toS`: a local run is a frame run at `[]`.
- `uPostS_exit`: at a control `UPostS` relates to the number in `%rdi`, a
  frame run reaches a control (`main`'s `ret`) whose exit with that number
  mod 256 is `MainExit` there (`MainExitS`; `uPost_exit` at the reached
  control).

The `LocalRun` forms (`UPost`, `uPost_exit`) are unchanged.
-/
import Spike.Lib.LowerX64.StartU
import Spike.Lib.SegLagS

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Sem (Marks)
open Spike.Lib.X64Consumer (Own Lbl Lsize msOf)

/-- **The user function's post at depth**: the source control is the start
`c0` (held back), from which a frame run at the empty frames reaches the
return of `v` (`RetV`). -/
def UPostS (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (c0 c : Ctl) (v : BitVec 64) : Prop :=
  c = c0 ∧ ∃ c', FrameRun p (c0, []) (c', []) ∧ RetV lbl c' v

/-- The call-free post is the post at depth. -/
theorem UPost.toS {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {c0 c : Ctl} {v : BitVec 64}
    (h : UPost p lbl c0 c v) : UPostS p lbl c0 c v := by
  obtain ⟨rfl, c', hr, hv⟩ := h
  exact ⟨rfl, c', FrameRun.ofLocal hr [], hv⟩

/-- **`main`'s exit at the post `UPostS`**, under the placement's memory
side: a frame run from the control reaches `main`'s `ret` of the number in
`%rdi`, where the return is the exit with the number mod 256. -/
theorem uPostS_exit {p : Prog} {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop}
    {G : Loc → Val → Prop} {own : Own} {lbl : Lbl} {ls0 : Lsize} {ms : MemSide isa}
    (hms : ms = msOf Λ μ rd G own lbl ls0) {c0 : Ctl} {exe : _root_.Executable} {endPc : Int64} {pc : Int64}
    {o : SO} :
    ∀ (R' : Region) (F' : MachineData → Prop) s c (v : BitVec 64), UPostS p lbl c0 c v →
      At exe endPc R' F' ⟨pc, o, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c → ¬ ms.abortAt s →
        MainExitS p ms s c v.toNat := by
  rintro R' F' s c v ⟨rfl, c', hr, hv⟩ ⟨he, hn, hdc, hpc, σ, hA, hD, hx⟩ hab
  exact ⟨c', hr, uPost_exit hms R' F' s c' v ⟨rfl, c', .refl _, hv⟩ ⟨he, hn, hdc, hpc, σ, hA, hD, hx⟩ hab⟩

end Spike.Lib.LowerX64
