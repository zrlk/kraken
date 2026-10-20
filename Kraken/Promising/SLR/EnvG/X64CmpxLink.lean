/-
**The x64 `lock cmpxchg` spinlock on `EnvG`, the worker's rule**
(`EnvG/X64SpinLink.lean` with the `F` link): the worker
`cmpxWorkerG` (`EnvG/X64CmpxVCGen.lean`) as a `ThreadRuleRXF` through
`ThreadRuleRXF.ofSafelyEnvGFX` (`EnvG/X64RmwFail.lean`; under `Arch.tso` the
`lock cmpxchgl` is a release-kind RMW that may fail, so the `R` link
`ofSafelyEnvGRX` does not apply), with the spinlock's postcondition `Post`
(`SLR/Adequacy.lean`), and its `NoFaultRuleF`.

The hypotheses of `ofSafelyEnvGFX` are discharged as in `X64SpinLink`:
- `pl.Valid`: `xlockPlan_valid`; `Le16 S`: `spinS_le16`;
- `Phase1TreeFX`: `phase1TreeFX_of_dirs` and `dirs_phase1FX` (the
  `lock cmpxchgl` may fail; `Phase1ShapeF` has no totality condition);
- `RelRmwGiveOk`: `xlockPlan` gives nothing (`xlockPlan_gives`): the
  `lock cmpxchgl` writes `1`, never a planned release;
- `hpost`, `hstuck`: `postOfX_end`, `not_instrStepEnv_of_end_labels`;
- `hB` (`hB_cmpx`): as `X64SpinLink.hB_spin`.

The rule gives `NPSafeF` (`NPSafeF.of_ruleRXF`); Theorem 1′ for it is the
open `Theorem1FChain` (`EnvG/RmwFailRule.lean`).
-/
import Kraken.Promising.SLR.EnvG.X64CmpxVCGen
import Kraken.Promising.SLR.EnvG.X64RmwFail
import Kraken.Promising.SLR.EnvG.X64SpinLink

namespace Kraken.Promising.X64.EnvG.CmpxLink

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Spin Kraken.Promising.X64.EnvG.Cmpx
open Kraken.Promising.X64.EnvG.SpinLink
open Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon Kraken.Promising.SLR.EnvG.X64Spin

variable [layout : _root_.Layout] [Executable.ValidLayout (layout cmpxWorkerG)]

theorem cmpxWorkerG_phase1 : Phase1TreeFX (layout cmpxWorkerG) := by
  refine phase1TreeFX_of_dirs ?_
  dirs_phase1FX cmpxWorkerG
  -- `jmp done`: `RelRegOrMem.interp` is not a `kstep` definition
  all_goals simp [_root_.RelRegOrMem.interp, Kraken.Promising.X64.toEv, DetAccess, SingleAccessS2]

omit [Executable.ValidLayout (layout cmpxWorkerG)] in
theorem cmpxWorkerG_noFault : DirsNoFault (layout cmpxWorkerG) := by
  dirs_no_fault cmpxWorkerG
  -- `jmp done`, as in `cmpxWorkerG_phase1`
  all_goals simp [_root_.RelRegOrMem.interp, Kraken.Promising.X64.toEv, EvTree.NoFault]

/-- The worker's postcondition: the end of its text and `QEnd` (the counter
of `cmpxWorkerG_envG` projected away). -/
abbrev postCmpx (P : Sys) : MachineState × EStateX → Prop :=
  postOfX cmpxWorkerG fun _ σ => ∃ _ : Nat, QEnd P σ

omit [Executable.ValidLayout (layout cmpxWorkerG)] in
/-- **`hB` for the worker**: `Post` from `QEnd` under the clean flag. -/
theorem hB_cmpx (P : Sys) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postCmpx P (t.st.st, σ) → t.prom = [] → EnvRel tid (xlockPlan P tid) σ c t r g cl → cl →
      Post P.N P.Lk P.K r := by
  rintro c t r g cl σ hpost hp hrel hcl
  obtain ⟨-, -, -, hQ⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact hQ (hrel.cl hcl)
  · rw [hp] at hts; cases hts

/-- **The x64 `lock cmpxchg` spinlock worker's rule on `EnvG`**
(`Arch.tso`, failing release RMWs), at the release predicates `rel₀`. -/
noncomputable def cmpxRule_envGF (P : Sys) (tid : Nat) (l c : BitVec 64) (rel₀ : Loc → Pred) :
    ThreadRuleRXF (I := isa) Arch.tso (fun _ r _ => Post P.N P.Lk P.K r) tid :=
  ThreadRuleRXF.ofSafelyEnvGFX (S := spinS l c) (post := postCmpx P) (rel₀ := rel₀) (xlockPlan_valid P tid)
    (spinS_le16 l c) cmpxWorkerG_phase1 (RelRmwGiveOk.of_gives_nil (xlockPlan_gives P tid))
    postOfX_end (not_instrStepEnv_of_end_labels _ 1) (hB_cmpx P tid)

/-- **The x64 `lock cmpxchg` spinlock worker's rule excludes faults.** -/
theorem cmpxRule_envGF_noFault (P : Sys) (tid : Nat) (l c : BitVec 64) (rel₀ : Loc → Pred) :
    NoFaultRuleF (cmpxRule_envGF P tid l c rel₀) :=
  noFaultRuleF_ofSafelyEnvGFX_struct _ _ _ _ _ _ _ cmpxWorkerG_noFault

end Kraken.Promising.X64.EnvG.CmpxLink
