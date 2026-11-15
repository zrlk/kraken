/-
**A plain callee's states placed at its entry** (x86-64; the twin of
`Spike/Lib/LowerA64/G1CalleePlace.lean`): at the entry of a callee of an
`Accepted2` body, under its frame condition `CalleeF2`
(`Spike/Lib/LowerX64/CallC2.lean`), every state agreeing with the entry's
argument register `%rdi` places the callee's entry control `q.cE` (its one
argument word in `%rdi`, `ArgV`) on the call's frame and the caller's frames
(`framesPlaced_calleeF2`), as a callee prologue's placement premise asks
(`proW_w2F`'s `hPl`, `Spike/Lib/LowerX64/G1ProW.lean`).

- `placed_argV`: the entry control placed from `%rdi`;
- `placedS_calleeEntryG`: the entry control and frames placed, at any
  layout and labels;
- `placedS_calleeEntry`: at the callee's entry invariant `calleeJSO` of the
  assembled theorem's layout, at every state agreeing on `%rdi`…`%r9`.
-/
import Spike.Lib.LowerX64.G1CallCx
import Spike.Lib.LowerX64.G1CalleeFacts

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region)
open Spike.Lib.X64Consumer (Lbl Placed)
open Spike.Lib.X64ConsumerS (PlacedS FramesPlacedInI)
open Spike.Lib.X64.Flow
open Spike.Lib.X64.Rt (argXs)
open Spike.Lib.LowerNode (imms2Me)

section Gen

variable {p : Prog} {Λ : Scc.Sem.Layout} {lbl : Lbl} {lsize : WeakMem.AllocLabel → Nat}

/-- **A callee's entry control placed from `%rdi`**: its one argument word
(`ArgV`) at the register `%rdi`, which holds the argument's value `q.v`. -/
theorem placed_argV {q : CallG} (hv : ArgV lbl q) {s : State} (hx : Scc.Sem.X64.regVal s (.r .rdi) = q.v) :
    Placed Λ lbl s q.cE := by
  obtain ⟨y, t, w, he, hw, -⟩ := hv
  refine ⟨fun x k => if x = y ∧ k = 0 then some (.one (.reg (.r .rdi))) else none, ?_, ?_, ?_⟩
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
      exact ⟨.one (.reg (.r .rdi)), by simp⟩
    · have hne : (y == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm hxy)
      simp [TermRun.lookupE, hne] at hl
  · intro x k m hm
    dsimp only at hm
    split at hm <;> cases hm

/-- **A plain callee's entry placed** (any layout `Λ` and labels `lbl`):
under the callee's frame condition `F'` (`CalleeF2` at the layout's
immediates, the callee's region below the caller's frame and saved `%rbp`),
the caller's frames `fs` placed under the caller's `F` (`hfp`), at every
state whose `%rdi` holds the argument's value, the entry control `q.cE`
(`ArgV`, `placed_argV`) on the call's frame and `fs`
(`framesPlaced_calleeF2`). -/
theorem placedS_calleeEntryG {fr : Scc.Emit.X64.Frame} (hfo : FrameOk fr)
    {R : Region} {F : MachineData → Prop} {D : Int} {fp ra : BitVec 64} {T : Expr → Prop} {q : CallG}
    {frm : TermRun.Frame} {F' : MachineData → Prop}
    (hCF : CalleeF2 p lbl lsize fr R F D fp ra Λ.imms T q frm F')
    (hlo : R.lo ≤ -(fr.size : Int) - 8 - D) (hhi : 16 ≤ R.hi) (hD0 : 0 ≤ D)
    {fs : List TermRun.Frame} (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    (hv : ArgV lbl q) :
    ∀ s : State, F' s.st.1 → Scc.Sem.X64.regVal s (.r .rdi) = q.v → PlacedS Λ lbl s q.cE (frm :: fs) := by
  intro s hF hx
  obtain ⟨B, hB⟩ := framesPlaced_calleeF2 hfo hCF hlo hhi hD0 hfp s hF
  exact Spike.Lib.X64ConsumerS.PlacedS.ofFrames (placed_argV hv hx) hB.toFramesPlaced

end Gen

section G1Place

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

/-- **A plain callee's entry placed at its entry invariant** (the
assembled theorem's layout, no label placed; `proW_w2F`'s `hPl` at the
entry `calleeJSO`): at every control and registers of the entry, every
state under the callee's frame condition agreeing on `%rdi`…`%r9` places
the control on the call's frame and the caller's frames
(`placedS_calleeEntryG`, the control `q.cE` and `%rdi` holding `q.v` by
`calleeN`). -/
theorem placedS_calleeEntry {fr : Scc.Emit.X64.Frame} (hfo : FrameOk fr)
    {R : Region} {F : MachineData → Prop} {D : Int} {fp ra : BitVec 64} {T : Expr → Prop} {q : CallG}
    {frm : TermRun.Frame} {F' : MachineData → Prop}
    (hCF : CalleeF2 p (fun _ => none) (fun _ => 0) fr R F D fp ra (Ly).Λ.imms T q frm F')
    (hlo : R.lo ≤ -(fr.size : Int) - 8 - D) (hhi : 16 ≤ R.hi) (hD0 : 0 ≤ D)
    {fs : List TermRun.Frame} (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI (Ly).Λ (fun _ => none) s fs B)
    (hv : ArgV (fun _ => none) q) (lab : Label → Int64) (g : String) (tp : UInt64) (R' : Region) :
    ∀ σ c, calleeJSO R' F' lab g tp q σ c → ∀ s : State, F' s.st.1 →
      (∀ i < 6, s.st.1.regs.get64 (argXs.getD i .rdi) = σ.regs.get64 (argXs.getD i .rdi)) →
      PlacedS (Ly).Λ (fun _ => none) s c (frm :: fs) := by
  rintro σ c ⟨⟨rfl, -, -, hx0, -⟩, -⟩ s hF ha
  refine placedS_calleeEntryG hfo hCF hlo hhi hD0 hfp hv s hF ?_
  have h0 : s.st.1.regs.get64 .rdi = σ.regs.get64 .rdi := ha 0 (by decide)
  show s.st.1.regs.get64 .rdi = q.v
  rw [h0]
  exact hx0

end G1Place

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.placed_argV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.placed_argV
/-- info: 'Spike.Lib.LowerX64.placedS_calleeEntryG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.placedS_calleeEntryG
/-- info: 'Spike.Lib.LowerX64.placedS_calleeEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.placedS_calleeEntry
