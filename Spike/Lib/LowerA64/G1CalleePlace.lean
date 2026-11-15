/-
**A plain callee's states placed at its entry** (AArch64): at the entry of
a callee of an `Accepted2` body, under its frame condition `CalleeF2`
(`Spike/Lib/LowerA64/CallC2.lean`), every state agreeing with the entry's
argument register `x0` places the callee's entry control `q.cE` (its one
argument word in `x0`, `ArgV`) on the call's frame and the caller's frames
(`framesPlaced_calleeF2`), as a callee prologue's placement premise asks
(`proW_w2F`'s `hPl`, `Spike/Lib/LowerA64/G1ProW.lean`).

- `placed_argV`: the entry control placed from `x0`;
- `placedS_calleeEntryG`: the entry control and frames placed, at any
  layout and labels;
- `placedS_calleeEntry`: at the callee's entry invariant `calleeN` of the
  assembled theorem's layout, at every state agreeing on `x0`…`x7`.
-/
import Spike.Lib.LowerA64.G1CallCx

namespace Spike.Lib.LowerA64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.A64Consumer (Lbl Placed)
open Spike.Lib.A64ConsumerS (PlacedS FramesPlacedInI)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Rt (argX)
open Spike.Lib.LowerNode (imms2Me)

section Gen

variable {p : Prog} {Λ : Scc.Sem.Layout} {lbl : Lbl} {lsize : WeakMem.AllocLabel → Nat}

/-- **A callee's entry control placed from `x0`**: its one argument word
(`ArgV`) at the register `x0`, which holds the argument's value `q.v`. -/
theorem placed_argV {q : CallG} (hv : ArgV lbl q) {s : State} (hx : Scc.Sem.A64.regVal s (.x 0) = q.v) :
    Placed Λ lbl s q.cE := by
  obtain ⟨y, t, w, he, hw, -⟩ := hv
  refine ⟨fun x k => if x = y ∧ k = 0 then some (.one (.reg (.x 0))) else none, ?_, ?_, ?_⟩
  · intro x ty ws hl k wd wp hk hp
    dsimp only at hp
    split at hp
    · obtain ⟨rfl, rfl⟩ := ‹x = y ∧ k = 0›
      cases hp
      rw [he] at hl
      simp only [TermRun.lookupE, List.find?_cons, beq_self_eq_true, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at hl
      obtain ⟨-, rfl⟩ := hl
      cases hk
      exact ⟨q.v.toNat, congrArg (fun b : BitVec 64 => some b.toNat) hx, hw⟩
    · cases hp
  · intro x _ ty ws hl k hk
    rw [he] at hl
    by_cases hxy : x = y
    · subst hxy
      simp only [TermRun.lookupE, List.find?_cons, beq_self_eq_true, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at hl
      obtain ⟨-, rfl⟩ := hl
      obtain rfl : k = 0 := by simpa using hk
      exact ⟨.one (.reg (.x 0)), by simp⟩
    · have hne : (y == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm hxy)
      simp [TermRun.lookupE, hne] at hl
  · intro x k m hm
    dsimp only at hm
    split at hm <;> cases hm

/-- **A plain callee's entry placed** (any layout `Λ` and labels `lbl`):
under the callee's frame condition `F'` (`CalleeF2` at the layout's
immediates, the callee's region below the caller's frame), the caller's
frames `fs` placed under the caller's `F` (`hfp`), at every state whose
`x0` holds the argument's value, the entry control `q.cE` (`ArgV`,
`placed_argV`) on the call's frame and `fs` (`framesPlaced_calleeF2`). -/
theorem placedS_calleeEntryG {cx : Scc.Emit.A64.FnCtx} (hfo : Scc.Lower.InvA64.FrameOk cx)
    {R : Region} {F : MachineData → Prop} {D : Int} {fp ra : BitVec 64} {T : Expr → Prop} {q : CallG}
    {frm : TermRun.Frame} {F' : MachineData → Prop}
    (hCF : CalleeF2 p lbl lsize cx R F D fp ra Λ.imms T q frm F')
    (hlo : R.lo ≤ -(cx.frame : Int) - D) (hhi : 0 ≤ R.hi) (hD0 : 0 ≤ D)
    {fs : List TermRun.Frame} (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    (hv : ArgV lbl q) :
    ∀ s : State, F' s.st.1 → Scc.Sem.A64.regVal s (.x 0) = q.v → PlacedS Λ lbl s q.cE (frm :: fs) := by
  intro s hF hx
  obtain ⟨B, hB⟩ := framesPlaced_calleeF2 hfo hCF hlo hhi hD0 hfp s hF
  exact Spike.Lib.A64ConsumerS.PlacedS.ofFrames (placed_argV hv hx) hB.toFramesPlaced

end Gen

section G1Place

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

/-- **A plain callee's entry placed at its entry invariant** (the
assembled theorem's layout, no label placed; `proW_w2F`'s `hPl` at the
entry `calleeN` with `sp` at the region's base): at every control and
registers of the entry, every state under the callee's frame condition
agreeing on `x0`…`x7` places the control on the call's frame and the
caller's frames (`placedS_calleeEntryG`, the control `q.cE` and `x0`
holding `q.v` by `calleeN`). -/
theorem placedS_calleeEntry {cx : Scc.Emit.A64.FnCtx} (hfo : Scc.Lower.InvA64.FrameOk cx)
    {R : Region} {F : MachineData → Prop} {D : Int} {fp ra : BitVec 64} {T : Expr → Prop} {q : CallG}
    {frm : TermRun.Frame} {F' : MachineData → Prop}
    (hCF : CalleeF2 p (fun _ => none) (fun _ => 0) cx R F D fp ra (Ly).Λ.imms T q frm F')
    (hlo : R.lo ≤ -(cx.frame : Int) - D) (hhi : 0 ≤ R.hi) (hD0 : 0 ≤ D)
    {fs : List TermRun.Frame} (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI (Ly).Λ (fun _ => none) s fs B)
    (hv : ArgV (fun _ => none) q) (lab : Label → Int64) (g : String) (tp : UInt64) (R' : Region) :
    ∀ σ c, ((calleeN lab g tp q).J σ c ∧ SORel R' ⟨0, []⟩ σ.regs) → ∀ s : State, F' s.st.1 →
      (∀ i < 8, s.st.1.regs.getXReg (argX i) = σ.regs.getXReg (argX i)) →
      PlacedS (Ly).Λ (fun _ => none) s c (frm :: fs) := by
  rintro σ c ⟨⟨rfl, -, -, hx0, -⟩, -⟩ s hF ha
  refine placedS_calleeEntryG hfo hCF hlo hhi hD0 hfp hv s hF ?_
  show s.st.1.regs.X0.toBitVec = q.v
  rw [show s.st.1.regs.X0 = σ.regs.X0 from ha 0 (by decide)]
  exact hx0

end G1Place

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.placed_argV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.placed_argV
/-- info: 'Spike.Lib.LowerA64.placedS_calleeEntryG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.placedS_calleeEntryG
/-- info: 'Spike.Lib.LowerA64.placedS_calleeEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.placedS_calleeEntry
