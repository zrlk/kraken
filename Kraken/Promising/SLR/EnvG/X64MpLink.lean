/-
**x64 message passing on `EnvG`, the two rules**: the x64 MP writer and reader
(`EnvG/X64MpVCGen.lean`) as `ThreadRuleRX`s through
`ThreadRuleRX.ofSafelyEnvGX` (`EnvG/X64Link.lean`), with the shared
postcondition `MpPost P rd` (`EnvG/X64MpSpec.lean`), and their
`NoFaultRule`s.

Per thread, the hypotheses of `ofSafelyEnvGX` are discharged by:
- `pl.Valid`: `mpPlan_valid`; `Le16 S`: `mpS_le16`;
- `Phase1TreeX`: `phase1TreeX_of_dirs` and the `dirs_phase1X` tactic (no RMW:
  under `Arch.tso` the plain `mov` store is a release store, admitted);
- `hpost`, `hstuck`: `postOfX_end`, `not_instrStepEnv_of_end_labels`;
- `hB`: as on AArch64 (`EnvRel.res`, `WorldR.mono`, `SnapLe.read?`, `EnvRel.cl`).

No fault: `noFaultRule_ofSafelyEnvGX_struct` from `DirsNoFault`
(`dirs_no_fault`).
-/
import Kraken.Promising.SLR.EnvG.X64MpVCGen
import Kraken.Promising.EnvLinkTermX64

namespace Kraken.Promising.X64.EnvG.MpLink

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Mp Kraken.Promising.X64.EnvG.MpSmoke

variable [layout : _root_.Layout]

/-! ## The writer -/

section Writer

variable [Executable.ValidLayout (layout mpWriterX)]

theorem mpWriterX_phase1 : Phase1TreeX Arch.tso (layout mpWriterX) :=
  phase1TreeX_of_dirs (by dirs_phase1X mpWriterX)

omit [Executable.ValidLayout (layout mpWriterX)] in
theorem mpWriterX_noFault : DirsNoFault (layout mpWriterX) := by dirs_no_fault mpWriterX

/-- The writer's postcondition: the end of its text and `W3`. -/
abbrev postW (P : Params) : MachineState × EStateX → Prop := postOfX mpWriterX fun _ σ => W3 P σ

omit [Executable.ValidLayout (layout mpWriterX)] in
/-- **`hB` for the writer**: it keeps the token `W`. -/
theorem hB_W (P : Params) (tid rd : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postW P (t.st.st, σ) → t.prom = [] → EnvRel tid (mpPlan P) σ c t r g cl → cl → MpPost P rd c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, hW⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inl hW.2
  · rw [hp] at hts; cases hts

/-- **The x64 writer's rule on `EnvG`** (`Arch.tso`). -/
def mpRuleW_envGX (P : Params) (hL : MpLocs P) (tid rd : Nat) :
    ThreadRuleRX (I := isa) Arch.tso (MpPost P rd) tid :=
  ThreadRuleRX.ofSafelyEnvGX (S := mpS P) (post := postW P) (mpPlan_valid hL) (mpS_le16 P) mpWriterX_phase1
    postOfX_end (not_instrStepEnv_of_end_labels _ 0) (hB_W P tid rd)

/-- **The x64 writer's rule excludes faults.** -/
theorem mpRuleW_envGX_noFault (P : Params) (hL : MpLocs P) (tid rd : Nat) :
    NoFaultRule (mpRuleW_envGX P hL tid rd) :=
  noFaultRule_ofSafelyEnvGX_struct _ _ _ _ _ _ mpWriterX_noFault

end Writer

/-! ## The reader -/

section Reader

variable [Executable.ValidLayout (layout mpReaderX)]

theorem mpReaderX_phase1 : Phase1TreeX Arch.tso (layout mpReaderX) := by
  refine phase1TreeX_of_dirs ?_
  dirs_phase1X mpReaderX
  -- `je spin`: the branch is inside `toEv`, which the tactic's `split` misses
  all_goals by_cases h : s.status.zf = true <;>
    simp [h, Kraken.Promising.X64.toEv, DetAccess, SingleAccessS]

omit [Executable.ValidLayout (layout mpReaderX)] in
theorem mpReaderX_noFault : DirsNoFault (layout mpReaderX) := by
  dirs_no_fault mpReaderX
  -- `je spin`, as in `mpReaderX_phase1`
  all_goals by_cases h : s.status.zf = true <;> simp [h, Kraken.Promising.X64.toEv, EvTree.NoFault]

/-- The reader's postcondition for the flag predicate `φ`: the end
of its text, `R4G`, and `ebx = 42` under the clean flag. -/
abbrev postRG (P : Params) (φ : Pred) : MachineState × EStateX → Prop :=
  postOfX mpReaderX fun s σ => ∃ _ : Nat, R4G P φ σ ∧ (σ.cl → (s.regs.get64 .rbx).setWidth 32 = 42)

omit [Executable.ValidLayout (layout mpReaderX)] in
/-- **`hB` for the reader**, for the flag predicate `φ`: its result, the
seen flag message, and its acquire id. -/
theorem hB_RG (P : Params) (φ : Pred) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postRG P φ (t.st.st, σ) → t.prom = [] → EnvRel tid (mpPlan P) σ c t r g cl → cl → MpPostG P φ tid c r g := by
  rintro c t r g cl σ hpost hp hrel hcl
  obtain ⟨-, -, ⟨hw, tsF, vF, hrd, hv⟩, hx⟩ := hpost.resolve_right id
  obtain rfl : r = σ.r := by
    rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
    · rfl
    · rw [hp] at hts; cases hts
  exact .inr ⟨⟨⟨t, hrel.ht, hx (hrel.cl hcl)⟩, tsF, vF, hrel.snap.read? hrd, hv⟩, (hw.mono hrel.ghost).2⟩

/-- The reader's postcondition: the end of its text, `R4`, and `ebx = 42`
under the clean flag (the counter of `mpReaderX_envGP` projected away). -/
abbrev postR (P : Params) : MachineState × EStateX → Prop :=
  postOfX mpReaderX fun s σ => ∃ _ : Nat, R4 P σ ∧ (σ.cl → (s.regs.get64 .rbx).setWidth 32 = 42)

omit [Executable.ValidLayout (layout mpReaderX)] in
/-- **`hB` for the reader**: its result, the seen flag message, and its
acquire id. -/
theorem hB_R (P : Params) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postR P (t.st.st, σ) → t.prom = [] → EnvRel tid (mpPlan P) σ c t r g cl → cl → MpPost P tid c r g :=
  hB_RG P P.φ tid

/-- **The x64 reader's rule on `EnvG`** (`Arch.tso`). -/
def mpRuleR_envGX (P : Params) (hL : MpLocs P) (tid : Nat) :
    ThreadRuleRX (I := isa) Arch.tso (MpPost P tid) tid :=
  ThreadRuleRX.ofSafelyEnvGX (S := mpS P) (post := postR P) (mpPlan_valid hL) (mpS_le16 P) mpReaderX_phase1
    postOfX_end (not_instrStepEnv_of_end_labels _ 1) (hB_R P tid)

/-- **The x64 reader's rule excludes faults.** -/
theorem mpRuleR_envGX_noFault (P : Params) (hL : MpLocs P) (tid : Nat) : NoFaultRule (mpRuleR_envGX P hL tid) :=
  noFaultRule_ofSafelyEnvGX_struct _ _ _ _ _ _ mpReaderX_noFault

end Reader

end Kraken.Promising.X64.EnvG.MpLink
