/-
**The x64 spinlock worker makes only release writes**: `spinWorkerG` in
`(relPureQ Arch.tso (fun _ _ => False)).within [(l, 4), (c, 4)]`, by one
`cfgEnv_partial` table and `vcgen`. Under `Arch.tso` the `xchgl` (an
`.acqRel` RMW) and both plain `movl` stores are releases, so the purity
obligation is vacuous; the table only carries the frame (the accesses are in
the layout). Through `final_of_relPureSafelyQX_tso` this gives both
`NTFree Arch.tso` and the purity hypotheses of `final_of_relWrites`.
-/
import Kraken.Promising.SLR.EnvG.RelPureEnvX64
import Kraken.Promising.SLR.EnvG.X64SpinVCGen

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvSpike Kraken.Promising.X64.EnvG

namespace Kraken.Promising.X64.EnvG.SpinRelPure

open Kraken.Promising.X64.EnvG.Spin

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- The all-release environment on the spinlock layout. -/
abbrev EnvR (l c : BitVec 64) : SharedEnv :=
  (SharedEnv.relPureQ Arch.tso fun _ _ => False).within [(l, 4), (c, 4)]

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spinWorkerG)]

local instance spinWorkerG.env : CodeEnv := ⟨layout spinWorkerG⟩

/-- The purity table: the frame at `worker` (the accesses are in the
layout). -/
abbrev spinPureTable (l c : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (EnvR l c)).State → Prop :=
  fun lb s _ => lb = "worker" → FrameX l c s

/-- **The x64 spinlock worker makes only release writes** (counted,
partial). -/
theorem spinWorkerG_noNT (l c : BitVec 64) :
    PartialTripleEnv (SharedEnv.counted (EnvR l c)) (fun s _ => FrameX l c s) spinWorkerG
      (fun _ _ => True) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (spinPureTable l c) (hP := by funext s g; simp [spinPureTable])
  cfg_cases_env [spinWorkerG]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨hT, rfl, rfl⟩ := ‹(_ → _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [forall_const] at hT
  all_goals obtain ⟨hx0, hx1, hdl, hdc⟩ := hT
  all_goals simp only [Reg64s.get64, SharedEnv.counted_step, SharedEnv.counted_ok, SharedEnv.tick_load,
    SharedEnv.tick_rmw, SharedEnv.tick_store] at *
  case vc1 => simp [hx0]; trivial
  case vc2 =>
    rename_i x σ1 af hz hld _
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hx0, hdl] at hm
    · refine Table.ofLabelsEnv_at ⟨by decide, fun _ => ⟨by simp [hx0], by simp [hx1], by simpa using hdl,
        by simpa using hdc⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      have hn := hst.2
      subst hg
      omega
  case vc3 => simp [hx0, hdl]
  case vc4 => simp [hx0]; exact fun h => absurd rfl h
  case vc5 =>
    rename_i x σ1 af hz1 old σ5 af2 hz2 hld hx _
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hx0, hdl] at hm
    · refine Table.ofLabelsEnv_at ⟨by decide, fun _ => ⟨by simp [hx0], by simp [hx1], by simpa using hdl,
        by simpa using hdc⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      have hn := hst.2
      have hn' := hx.2
      subst hg
      omega
  case vc6 => simp [hx1]; trivial
  case vc7 => simp [hx1]; exact fun h => h rfl
  case vc8 =>
    rename_i x σ1 af hz1 old σ5 af2 hz2 y σ8 dm σ10 hld hx hld2 hst3 _
    rcases hst3 with ⟨hm, -, -⟩ | ⟨-, rfl, -⟩
    · simp [hx1, hdc] at hm
    · simp [hx0, hdl]
  case vc9 => simp [hx0]; exact fun h => h rfl
  case vc10 =>
    exact Table.ofLabelsEnv_at ⟨by decide, fun h => absurd h (by decide), .inl (by decide)⟩
  all_goals trivial

end Kraken.Promising.X64.EnvG.SpinRelPure
