/-
**The x64 xchg spinlock on `EnvG`, the worker's rule**: the worker
`spinWorkerG` (`EnvG/X64SpinVCGen.lean`) as a `ThreadRuleRX` through
`ThreadRuleRX.ofSafelyEnvGRX` (`EnvG/X64Link.lean`; under `Arch.tso` the
`xchgl` is a release-kind RMW), with the spinlock's postcondition `Post`
(`SLR/Adequacy.lean`), and its `NoFaultRule`.

The hypotheses of `ofSafelyEnvGRX` are discharged by:
- `pl.Valid`: `xlockPlan_valid` (`EnvG/X64SpinRelease.lean`); `Le16 S`:
  `spinS_le16`;
- `Phase1TreeRX`: `phase1TreeRX_of_dirs` and `dirs_phase1RX` (the `xchgl`'s
  operation is total), with a `zf` case split for the two `jne worker`;
- `RelRmwGiveOk`: `xlockPlan` gives nothing (`xlockPlan_gives`): the `xchgl`
  writes `1`, never a planned release;
- `hpost`, `hstuck`: `postOfX_end`, `not_instrStepEnv_of_end_labels`;
- `hB` (`hB_spin`): as `CasLink.hB_cas`.

The rule is stated at any release predicates `rel₀` (`invGRX_init` fixes
them to the initial ghost's).
-/
import Kraken.Promising.SLR.EnvG.X64SpinVCGen
import Kraken.Promising.EnvLinkTermX64

namespace Kraken.Promising.X64.EnvG.SpinLink

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Spin
open Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon Kraken.Promising.SLR.EnvG.X64Spin

/-- The shared layout: the lock and the counter word. -/
abbrev spinS (l c : BitVec 64) : SharedEnv.Layout := [(l, 4), (c, 4)]

theorem spinS_le16 (l c : BitVec 64) : Le16 (spinS l c) := fun x hx => by
  simp only [spinS, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> exact (by decide : 4 ≤ 16)

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spinWorkerG)]

theorem spinWorkerG_phase1 : Phase1TreeRX Arch.tso (layout spinWorkerG) := by
  refine phase1TreeRX_of_dirs ?_
  dirs_phase1RX spinWorkerG

omit [Executable.ValidLayout (layout spinWorkerG)] in
theorem spinWorkerG_noFault : DirsNoFault (layout spinWorkerG) := by
  dirs_no_fault spinWorkerG
  -- `jmp done`: `RelRegOrMem.interp` is not a `kstep` definition (and
  -- `dirs_no_fault`, `Promising/EnvLinkTermX64.lean`, does not unfold it)
  all_goals simp [_root_.RelRegOrMem.interp, Kraken.Promising.X64.toEv, EvTree.NoFault]

/-- The worker's postcondition: the end of its text and `QEnd` (the counter
of `spinWorkerG_envG` projected away). -/
abbrev postSpin (P : Sys) : MachineState × EStateX → Prop :=
  postOfX spinWorkerG fun _ σ => ∃ _ : Nat, QEnd P σ

omit [Executable.ValidLayout (layout spinWorkerG)] in
/-- **`hB` for the worker**: `Post` from `QEnd` under the clean flag. -/
theorem hB_spin (P : Sys) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postSpin P (t.st.st, σ) → t.prom = [] → EnvRel tid (xlockPlan P tid) σ c t r g cl → cl →
      Post P.N P.Lk P.K r := by
  rintro c t r g cl σ hpost hp hrel hcl
  obtain ⟨-, -, -, hQ⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact hQ (hrel.cl hcl)
  · rw [hp] at hts; cases hts

/-- **The x64 spinlock worker's rule on `EnvG`** (`Arch.tso`), at the
release predicates `rel₀`. -/
noncomputable def spinRule_envG (P : Sys) (tid : Nat) (l c : BitVec 64) (rel₀ : Loc → Pred) :
    ThreadRuleRX (I := isa) Arch.tso (fun _ r _ => Post P.N P.Lk P.K r) tid :=
  ThreadRuleRX.ofSafelyEnvGRX (S := spinS l c) (post := postSpin P) (rel₀ := rel₀) (xlockPlan_valid P tid)
    (spinS_le16 l c) spinWorkerG_phase1 (RelRmwGiveOk.of_gives_nil (xlockPlan_gives P tid))
    postOfX_end (not_instrStepEnv_of_end_labels _ 1) (hB_spin P tid)

/-- **The x64 spinlock worker's rule excludes faults.** -/
theorem spinRule_envG_noFault (P : Sys) (tid : Nat) (l c : BitVec 64) (rel₀ : Loc → Pred) :
    NoFaultRule (spinRule_envG P tid l c rel₀) :=
  noFaultRule_ofSafelyEnvGRX_struct _ _ _ _ _ _ _ spinWorkerG_noFault

end Kraken.Promising.X64.EnvG.SpinLink
