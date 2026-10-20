/-
**Message passing on `EnvG`, the two rules**: the MP writer
and reader (`SLR/MpTrees.lean`) as `ThreadRuleRX`s from their `vcgen` proofs
on `EnvG` (`EnvG/MpSmokeVCGen.lean`) through `ThreadRuleRX.ofSafelyEnvG`,
with the shared postcondition `MpPost P rd` of the old rules
(`SLR/MpRule.lean`), and their `NoFaultRule`s.

Per thread, the hypotheses of `ofSafelyEnvG` are discharged by:
- `pl.Valid`: `mpPlan_valid` (`EnvG/MpSmoke.lean`);
- `e.rmwLive`: `Layout.apply_rmwLive` and `decide`;
- `Phase1Tree`: `phase1Tree_of_dirs` and the `dirs_phase1` tactic;
- `hpost`, `hstuck`: `postOf_end`, `not_instrStepEnv_of_end_labels`;
- `hB`: with no promise the actual resource is the env's (`EnvRel.res`);
  the writer's `W3` gives the token `W`; the reader's `R4` gives its acquire
  id (`WorldR.mono` along `EnvRel.ghost`) and the seen flag message
  (`SnapLe.read?` along `EnvRel.snap`), and `W4 = 1` under the clean flag
  (`EnvRel.cl`).

No fault (both threads): `noFaultRule_ofSafelyEnvG_struct` from
`DirsNoFault` (`dirs_no_fault`).

Phase-1 limits apply (single-access trees, read-side acquire only, releases
are stores).
-/
import Kraken.Promising.SLR.EnvG.SafelyBridge
import Kraken.Promising.SLR.EnvG.A64Answers
import Kraken.Promising.SLR.EnvG.MpSmokeVCGen
import Kraken.Promising.SLR.MpSpec

namespace Kraken.Promising.SLR.EnvG.MpLink

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Mp Kraken.Promising.SLR.MpTrees
open Kraken.Promising.SLR.EnvG.MpSmoke

variable [layout : _root_.Layout]

/-! ## The writer -/

section Writer

variable [Executable.ValidLayout (layout mpWriter)]

omit [Executable.ValidLayout (layout mpWriter)] in
theorem mpWriter_rmwLive : (layout mpWriter).rmwLive = true := by rw [Layout.apply_rmwLive]; decide

theorem mpWriter_phase1 : Phase1Tree Arch.armv8 (layout mpWriter) := phase1Tree_of_dirs (by dirs_phase1 mpWriter)

omit [Executable.ValidLayout (layout mpWriter)] in
theorem mpWriter_noFault : DirsNoFault (layout mpWriter) := by dirs_no_fault' mpWriter

/-- The writer's postcondition: the end of its text and `W3`. -/
abbrev postW (P : Params) : MachineState × EStateA → Prop := postOf mpWriter fun _ σ => W3 P σ

omit [Executable.ValidLayout (layout mpWriter)] in
/-- **`hB` for the writer**: it keeps the token `W`. -/
theorem hB_W (P : Params) (tid rd : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postW P (t.st.st, σ) → t.prom = [] → EnvRel tid (mpPlan P) σ c t r g cl → cl → MpPost P rd c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, hW⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inl hW.2
  · rw [hp] at hts; cases hts

/-- **The writer's rule on `EnvG`.** -/
def mpRuleW_envG (P : Params) (hL : MpLocs P) (tid rd : Nat) : ThreadRuleRX (I := isa) Arch.armv8 (MpPost P rd) tid :=
  ThreadRuleRX.ofSafelyEnvG (post := postW P) (mpPlan_valid hL) mpWriter_rmwLive mpWriter_phase1 postOf_end
    (not_instrStepEnv_of_end_labels _ 1) (hB_W P tid rd)

/-- **The writer's rule excludes faults.** -/
theorem mpRuleW_envG_noFault (P : Params) (hL : MpLocs P) (tid rd : Nat) : NoFaultRule (mpRuleW_envG P hL tid rd) :=
  noFaultRule_ofSafelyEnvG_struct _ _ _ _ _ _ mpWriter_noFault

end Writer

/-! ## The reader -/

section Reader

variable [Executable.ValidLayout (layout mpReader)]

omit [Executable.ValidLayout (layout mpReader)] in
theorem mpReader_rmwLive : (layout mpReader).rmwLive = true := by rw [Layout.apply_rmwLive]; decide

theorem mpReader_phase1 : Phase1Tree Arch.armv8 (layout mpReader) := phase1Tree_of_dirs (by dirs_phase1 mpReader)

omit [Executable.ValidLayout (layout mpReader)] in
theorem mpReader_noFault : DirsNoFault (layout mpReader) := by dirs_no_fault' mpReader

/-- The reader's postcondition: the end of its text, `R4`, and `W4 = 1`
under the clean flag (the counter of `mpReader_envGP` projected away). -/
abbrev postR (P : Params) : MachineState × EStateA → Prop :=
  postOf mpReader fun s σ => ∃ _ : Nat, R4 P σ ∧ (σ.cl → s.regs.X4.toBitVec.setWidth 32 = 1)

omit [Executable.ValidLayout (layout mpReader)] in
/-- **`hB` for the reader**: its result, the seen flag message, and its
acquire id. -/
theorem hB_R (P : Params) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postR P (t.st.st, σ) → t.prom = [] → EnvRel tid (mpPlan P) σ c t r g cl → cl → MpPost P tid c r g := by
  rintro c t r g cl σ hpost hp hrel hcl
  obtain ⟨-, -, ⟨hw, tsF, vF, hrd, hv⟩, hx4⟩ := hpost.resolve_right id
  obtain rfl : r = σ.r := by
    rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
    · rfl
    · rw [hp] at hts; cases hts
  exact .inr ⟨⟨⟨t, hrel.ht, hx4 (hrel.cl hcl)⟩, tsF, vF, hrel.snap.read? hrd, hv⟩, (hw.mono hrel.ghost).2⟩

/-- **The reader's rule on `EnvG`.** -/
def mpRuleR_envG (P : Params) (hL : MpLocs P) (tid : Nat) : ThreadRuleRX (I := isa) Arch.armv8 (MpPost P tid) tid :=
  ThreadRuleRX.ofSafelyEnvG (post := postR P) (mpPlan_valid hL) mpReader_rmwLive mpReader_phase1 postOf_end
    (not_instrStepEnv_of_end_labels _ 1) (hB_R P tid)

/-- **The reader's rule excludes faults.** -/
theorem mpRuleR_envG_noFault (P : Params) (hL : MpLocs P) (tid : Nat) : NoFaultRule (mpRuleR_envG P hL tid) :=
  noFaultRule_ofSafelyEnvG_struct _ _ _ _ _ _ mpReader_noFault

end Reader

end Kraken.Promising.SLR.EnvG.MpLink
