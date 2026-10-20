/-
**x64 MP with an unlocked `incl` release, the two rules**.

- **The writer** through `ThreadRuleRX.ofSafelyEnvGLRX` (`LRX64.lean`, the
  load-then-release link): `incl (%rdi)` is a load-then-store tree
  (`dirs_lrX`), `movl $42, (%rsi)` a phase-1 one. Plan `mpIncPlan`
  (`mpIncPlan_valid`), layout `mpS` (`mpS_le16`). No fault:
  `noFaultRule_ofSafelyEnvGLRX_struct` from `DirsNoFault` (`dirs_no_fault`).
- **The reader** (`mpReaderX`, unchanged) through `ofSafelyEnvGX` as in
  `X64MpLink`, with the postcondition `MpPostI` (flag predicate `φI`);
  its shape and no-fault facts are `X64MpLink`'s (`mpReaderX_phase1`,
  `mpReaderX_noFault`).
-/
import Kraken.Promising.SLR.EnvG.X64MpIncVCGen
import Kraken.Promising.SLR.EnvG.X64MpLink

namespace Kraken.Promising.X64.EnvG.MpInc

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Mp Kraken.Promising.X64.EnvG.MpSmoke
open Kraken.Promising.X64.EnvG.MpLink

variable [layout : _root_.Layout]

/-! ## The writer -/

section Writer

variable [Executable.ValidLayout (layout mpIncWriterX)]

/-- **The writer is load-then-release** (`incl` is not phase-1 or phase-2
under `Arch.tso`). -/
theorem mpIncWriterX_lr : LRTreeX Arch.tso (layout mpIncWriterX) :=
  lrTreeX_of_dirs (by dirs_lrX mpIncWriterX)

omit [Executable.ValidLayout (layout mpIncWriterX)] in
theorem mpIncWriterX_noFault : DirsNoFault (layout mpIncWriterX) := by dirs_no_fault mpIncWriterX

/-- The writer's postcondition: the end of its text and `W3I`. -/
abbrev postWI (P : Params) : MachineState × EStateX → Prop := postOfX mpIncWriterX fun _ σ => W3I P σ

omit [Executable.ValidLayout (layout mpIncWriterX)] in
/-- **`hB` for the writer**: it keeps the token `W`. -/
theorem hB_WI (P : Params) (tid rd : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postWI P (t.st.st, σ) → t.prom = [] → EnvRel tid (mpIncPlan P) σ c t r g cl → cl → MpPostI P rd c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, hW⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inl hW.2
  · rw [hp] at hts; cases hts

/-- **The x64 `incl` writer's rule on `EnvGLR`** (`Arch.tso`). -/
def mpIncRuleW (P : Params) (hL : MpLocs P) (tid rd : Nat) :
    ThreadRuleRX (I := isa) Arch.tso (MpPostI P rd) tid :=
  ThreadRuleRX.ofSafelyEnvGLRX (S := mpS P) (post := postWI P) (mpIncPlan_valid hL) (mpS_le16 P) mpIncWriterX_lr
    postOfX_end (not_instrStepEnv_of_end_labels _ 0) (hB_WI P tid rd)

/-- **The x64 `incl` writer's rule excludes faults.** -/
theorem mpIncRuleW_noFault (P : Params) (hL : MpLocs P) (tid rd : Nat) :
    NoFaultRule (mpIncRuleW P hL tid rd) :=
  noFaultRule_ofSafelyEnvGLRX_struct _ _ _ _ _ _ mpIncWriterX_noFault

end Writer

/-! ## The reader -/

section Reader

variable [Executable.ValidLayout (layout mpReaderX)]

/-- The reader's postcondition: the end of its text, `R4I`, and `ebx = 42`
under the clean flag. -/
abbrev postRI (P : Params) : MachineState × EStateX → Prop :=
  postOfX mpReaderX fun s σ => ∃ _ : Nat, R4I P σ ∧ (σ.cl → (s.regs.get64 .rbx).setWidth 32 = 42)

omit [Executable.ValidLayout (layout mpReaderX)] in
/-- **`hB` for the reader**: its result, the seen flag message, and its
acquire id. -/
theorem hB_RI (P : Params) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postRI P (t.st.st, σ) → t.prom = [] → EnvRel tid (mpPlan P) σ c t r g cl → cl → MpPostI P tid c r g :=
  hB_RG P (φI P) tid

/-- **The x64 reader's rule on `EnvG`** with the `φI` postcondition. -/
def mpIncRuleR (P : Params) (hL : MpLocs P) (tid : Nat) :
    ThreadRuleRX (I := isa) Arch.tso (MpPostI P tid) tid :=
  ThreadRuleRX.ofSafelyEnvGX (S := mpS P) (post := postRI P) (mpPlan_valid hL) (mpS_le16 P) mpReaderX_phase1
    postOfX_end (not_instrStepEnv_of_end_labels _ 1) (hB_RI P tid)

/-- **The reader's rule excludes faults.** -/
theorem mpIncRuleR_noFault (P : Params) (hL : MpLocs P) (tid : Nat) : NoFaultRule (mpIncRuleR P hL tid) :=
  noFaultRule_ofSafelyEnvGX_struct _ _ _ _ _ _ mpReaderX_noFault

end Reader

end Kraken.Promising.X64.EnvG.MpInc
