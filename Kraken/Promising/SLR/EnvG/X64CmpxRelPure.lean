/-
**The x64 `lock cmpxchg` spinlock worker makes only release writes**
`cmpxWorkerG` in `(relPureQ Arch.tso (fun _ _ => False)).within [(l, 4), (c, 4)]`,
by one `cfgEnv_partial` table and `vcgen`. Under `Arch.tso` the
`lock cmpxchgl` (an `.acqRel` RMW) and both plain `movl` stores are releases,
so the purity obligation is vacuous; the table only carries the frame.
-/
import Kraken.Promising.SLR.EnvG.X64SpinRelPure
import Kraken.Promising.SLR.EnvG.X64CmpxVCGen

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvSpike Kraken.Promising.X64.EnvG

namespace Kraken.Promising.X64.EnvG.CmpxRelPure

open Kraken.Promising.X64.EnvG.Spin Kraken.Promising.X64.EnvG.Cmpx Kraken.Promising.X64.EnvG.SpinRelPure

set_option mvcgen.warning false
set_option experimental.vcgen true

variable [layout : _root_.Layout] [Executable.ValidLayout (layout cmpxWorkerG)]

local instance cmpxWorkerG.env : CodeEnv := ⟨layout cmpxWorkerG⟩

/-- **The x64 `lock cmpxchg` spinlock worker makes only release writes**
(counted, partial). -/
theorem cmpxWorkerG_noNT (l c : BitVec 64) :
    PartialTripleEnv (SharedEnv.counted (EnvR l c)) (fun s _ => FrameX l c s) cmpxWorkerG
      (fun _ _ => True) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (spinPureTable l c) (hP := by funext s g; simp [spinPureTable])
  cfg_cases_env [cmpxWorkerG]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨hT, rfl, rfl⟩ := ‹(_ → _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [forall_const] at hT
  all_goals obtain ⟨hx0, hx1, hdl, hdc⟩ := hT
  all_goals simp only [Reg64s.get64, SharedEnv.counted_step, SharedEnv.counted_ok, SharedEnv.tick_load,
    SharedEnv.tick_rmw, SharedEnv.tick_store] at *
  all_goals first
    | (simp [hx0, hdl]; done)
    | (simp [hx1]; done)
    | (simp [hx0]; trivial)
    | (simp [hx1]; trivial)
    | (simp [hx0]; exact fun h => absurd rfl h)
    | (simp [hx1]; exact fun h => h rfl)
    | (exact Table.ofLabelsEnv_at ⟨by decide, fun h => absurd h (by decide), .inl (by decide)⟩)
    | skip
  case vc3 | vc9 =>
    rename_i hx _
    refine Table.ofLabelsEnv_at ⟨by decide, fun _ => ⟨by simp [hx0], by simp [hx1], by simpa using hdl,
      by simpa using hdc⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    have hn := hx.2
    subst hg
    omega
  case vc6 | vc12 =>
    rename_i hst3 _
    rcases hst3 with ⟨hm, -, -⟩ | ⟨-, rfl, -⟩
    · simp [hx1, hdc] at hm
    · simp [hx0, hdl]

end Kraken.Promising.X64.EnvG.CmpxRelPure
