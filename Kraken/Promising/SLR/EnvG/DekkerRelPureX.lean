/-
**Dekker's worker makes only release
writes** (`EnvG/X64MpRelPure.lean` for
Dekker's worker). The worker in
`(relPureQ Arch.tso (fun _ _ => False)).within (dkS f o c)` (every write a
release: every `mov` store under `Arch.tso`), counted, partial; through
`final_of_relPureSafelyQX_tso` this gives the scope `NTFree Arch.tso` and the
purity hypotheses of `final_of_relWrites`.
-/
import Kraken.Promising.SLR.EnvG.RelPureEnvX64
import Kraken.Promising.SLR.EnvG.DekkerVCGenX

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvSpike Kraken.Promising.X64.EnvG

namespace Kraken.Promising.X64.EnvG.Dekker

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- The all-release environment on Dekker's layout. -/
abbrev EnvR (f o c : BitVec 64) : SharedEnv :=
  (SharedEnv.relPureQ Arch.tso fun _ _ => False).within (dkS f o c)

variable [layout : _root_.Layout] [Executable.ValidLayout (layout worker)]

local instance worker.envR : CodeEnv := ⟨layout worker⟩

/-- The worker's all-release table: the frame at `worker`. -/
abbrev relTable (f o c : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (EnvR f o c)).State → Prop :=
  fun lb s _ => lb = "worker" → Frame f o c s

/-- **Dekker's worker writes only by releases** (counted, partial). -/
theorem worker_noNT (f o c : BitVec 64) :
    PartialTripleEnv (SharedEnv.counted (EnvR f o c)) (fun s _ => Frame f o c s) worker (fun _ _ => True)
      (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (relTable f o c) (hP := by funext s g; simp [relTable])
  cfg_cases_env [worker]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨hT, rfl, rfl⟩ := ‹(_ → _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [forall_const] at hT
  all_goals obtain ⟨hx0, hx1, hx2, hdf, hdo, hdc⟩ := hT
  all_goals simp only [Reg64s.get64] at hx0 hx1 hx2
  case vc4 | vc9 => exact Table.ofLabelsEnv_at ⟨by decide, fun h => absurd h (by decide), .inl (by decide)⟩
  all_goals simp_all
  all_goals first
    | trivial
    | exact fun h => h rfl

end Kraken.Promising.X64.EnvG.Dekker
