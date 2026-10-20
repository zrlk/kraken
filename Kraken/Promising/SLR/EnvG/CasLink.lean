/-
**The CAS spinlock on `EnvG`, the worker's rule**: the
worker `casTtasWorker` (`EnvG/CasSmoke.lean`) as a `ThreadRuleRX` from its
`vcgen` proof on `EnvG` (`casWorker_envG`, `EnvG/CasVCGen.lean`) through
`ThreadRuleRX.ofSafelyEnvG`, with the spinlock's postcondition `Post`
(`SLR/Adequacy.lean`, the one `counter_init`/`adequacy` consume), and its
`NoFaultRule`.

The hypotheses of `ofSafelyEnvG` are discharged by:
- `pl.Valid`: `lockPlan_valid` (`EnvG/CasRelease.lean`);
- `e.rmwLive`, `Phase1Tree`: `casTtasWorker_rmwLive`, `casTtasWorker_phase1`;
- `hpost`, `hstuck`: `postOf_end`, `not_instrStepEnv_of_end_labels`;
- `hB` (`hB_cas`): with no promise the actual resource is the env's
  (`EnvRel.res`), and `QEnd` gives `Post` under the clean flag (`EnvRel.cl`).

No fault: `noFaultRule_ofSafelyEnvG_struct` from `DirsNoFault`
(`casTtasWorker_noFault`).

Phase-1 limits apply (single-access trees, read-side acquire only, releases
are stores).
-/
import Kraken.Promising.SLR.EnvG.CasVCGen

namespace Kraken.Promising.SLR.EnvG.CasSmoke

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon

variable [layout : _root_.Layout] [Executable.ValidLayout (layout casTtasWorker)]

/-- The worker's postcondition: the end of its text and `QEnd` (the counter
of `casWorker_envG` projected away). -/
abbrev postCas (P : Sys) : MachineState × EStateA → Prop := postOf casTtasWorker fun _ σ => ∃ _ : Nat, QEnd P σ

omit [Executable.ValidLayout (layout casTtasWorker)] in
/-- **`hB` for the worker**: `Post` from `QEnd` under the clean flag. -/
theorem hB_cas (P : Sys) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postCas P (t.st.st, σ) → t.prom = [] → EnvRel tid (casPlan P tid) σ c t r g cl → cl →
      Post P.N P.Lk P.K r := by
  rintro c t r g cl σ hpost hp hrel hcl
  obtain ⟨-, -, -, hQ⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact hQ (hrel.cl hcl)
  · rw [hp] at hts; cases hts

/-- **The CAS worker's rule on `EnvG`.** -/
noncomputable def casRule_envG (P : Sys) (tid : Nat) :
    ThreadRuleRX (I := isa) Arch.armv8 (fun _ r _ => Post P.N P.Lk P.K r) tid :=
  ThreadRuleRX.ofSafelyEnvG (post := postCas P) (lockPlan_valid P tid) casTtasWorker_rmwLive casTtasWorker_phase1
    postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_cas P tid)

/-- **The CAS worker's rule excludes faults.** -/
theorem casRule_envG_noFault (P : Sys) (tid : Nat) : NoFaultRule (casRule_envG P tid) :=
  noFaultRule_ofSafelyEnvG_struct _ _ _ _ _ _ casTtasWorker_noFault

end Kraken.Promising.SLR.EnvG.CasSmoke
