/-
**The x64 `lock cmpxchg` spinlock worker on `EnvG` by `vcgen`**: the worker of
`Kraken/Examples/LockFree/X64/spinlock_cmpxchg2.kl`,
with the lock and the counter addressed through `%rdi`/`%rsi` (as
`X64SpinVCGen.spinWorkerG`), as a `PartialTripleEnv` in the counted `EnvGX`
(`EnvG` restricted to `[(l, 4), (c, 4)]`, `Arch.tso`), by `cfgEnv_partial`
with the two-label table of `X64SpinVCGen` (`worker`: `Fr`; `done`: `QEnd`)
and the VCs of `EnvG/X64CmpxVC.lean` (acquire) and `EnvG/X64SpinVC.lean`
(counter and release).

The `lock cmpxchgl` cell uses `CmpxSpecs.lock_cmpxchg32_shared_spec`
(`EnvG/X64CmpxSpecs.lean`), `addl $1` and `movl $0, (%rdi)` the rules of
`EnvG/X64SpinSpecs.lean`; the silent cells `envMonoX_lift_spec`.
-/
import Kraken.Promising.SLR.EnvG.X64CmpxVC
import Kraken.Promising.SLR.EnvG.X64CmpxSpecs
import Kraken.Promising.SLR.EnvG.X64SpinVCGen

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon Kraken.Promising.SLR.EnvG.X64Spin
open Kraken.X64.Parser Kraken.Promising.X64.EnvG.Spin

namespace Kraken.Promising.X64.EnvG.Cmpx

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The program -/

/-- **The x64 `lock cmpxchg` spinlock worker** of `spinlock_cmpxchg2.kl`
(`code` block verbatim, with `(lock)`/`(counter)` as `(%rdi)`/`(%rsi)`): a
bare `lock cmpxchgl` acquire loop (expected `0`, new `1`; a failed attempt
writes nothing), plain increment of the counter, plain-store release
`movl $0`. -/
def cmpxWorkerG : Program := parse("
worker:
  xorl %eax,%eax
  movl $1,%ecx
  lock cmpxchgl %ecx,(%rdi)
  jne worker
  movl (%rsi),%edx
  addl $1,%edx
  movl %edx,(%rsi)
  movl $0,(%rdi)
  jmp done
done:
")

/-- info: 11 -/
#guard_msgs in
#eval cmpxWorkerG.length

/-! ## The worker -/

variable [layout : _root_.Layout] [Executable.ValidLayout (layout cmpxWorkerG)]

local instance cmpxWorkerG.env : CodeEnv := ⟨layout cmpxWorkerG⟩

/-- **The x64 `lock cmpxchg` spinlock worker on `EnvG`** (counted, partial):
from `Fr`, every run that reaches the end is in `QEnd`. -/
theorem cmpxWorkerG_envG (P : Sys) (tid : Nat) (l c : BitVec 64) (hLk : P.Lk = ⟨l, 4⟩) (hC : P.C = ⟨c, 4⟩)
    (hL : SpinLocs P.N P.Lk P.C P.K P.F) (hN0 : 0 < P.N) (htid : tid < P.N) (hN32 : P.N < 2 ^ 32) :
    PartialTripleEnv (SharedEnv.counted (E P tid l c))
      (fun s σ => FrameX l c s ∧ Fr P tid σ.1) cmpxWorkerG (fun _ σ => QEnd P σ.1) (fun _ _ _ => False) := by
  obtain ⟨N, Lk, C, K, F⟩ := P
  simp only at hLk hC
  subst hLk hC
  have hLC : Sys.Lk ⟨N, ⟨l, 4⟩, ⟨c, 4⟩, K, F⟩ ≠ Sys.C ⟨N, ⟨l, 4⟩, ⟨c, 4⟩, K, F⟩ := hL.lk_c
  apply MachineWP.cfgEnv_partial (spinTable ⟨N, ⟨l, 4⟩, ⟨c, 4⟩, K, F⟩ tid l c)
    (hP := by funext s g; simp [spinTable])
  cfg_cases_env [cmpxWorkerG]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hx0, hx1, hdl, hdc⟩, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envG, Reg64s.get64] at *
  case vc1 => simp [hx0, hdl]
  case vc2 =>
    rename_i af σ1 σ2 hf1 hf2 _
    simp only [SharedEnv.counted_ok, SharedEnv.within_ok_rmw]
    refine ⟨vc_cmpx_ok_at hN0 _ (Fr.fence (Fr.fence hT hf1.1) hf2.1) (by simp [hx0]) rfl (by simp [cmpxOp]),
      by simp [hx0]⟩
  case vc3 =>
    rename_i af σ1 σ2 old σ3 hx heq hz σ4 hf1 hf2 hf3 _
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact absurd heq hz
  case vc4 => simp [hx1] <;> trivial
  case vc5 =>
    rename_i af σ1 σ2 old σ3 hx heq hz σ4 y σ5 hld σ6 hm hf1 hf2 hf3 hf4 _
    simp at heq
    rcases vc_cmpx_at hN0 _ (Fr.fence (Fr.fence hT hf1.1) hf2.1) (by simp [hx0]) rfl (by simp [cmpxOp]) old _
      hx.1 with ⟨h0, -⟩ | ⟨-, hH1⟩
    · exact absurd heq h0
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst2, rfl⟩
    · simp [hx1, hdc] at hm
    have hH2 := vc_ld_c_at hLC _ (H1.fence hH1 hf3.1) (by simp [hx1]) rfl w _ hst2.1
    simp only [SharedEnv.counted_ok, SharedEnv.within_ok_store]
    exact ⟨vc_st_c_ok_at hLC _ _ (H2.fence hH2 hf4.1) (by simp [hx1]) rfl (by simp [BitVec.add_comm]),
      by simp [hx1]⟩
  case vc6 =>
    rename_i af σ1 σ2 old σ3 hx heq hz σ4 y σ5 hld σ6 dm σ7 hst3 hf1 hf2 hf3 hf4 _
    rcases hst3 with ⟨hm, -, -⟩ | ⟨-, rfl, -, -⟩
    · simp [hx1, hdc] at hm
    · simp [hx0, hdl]
  case vc7 =>
    rename_i af σ1 σ2 old σ3 hx heq hz σ4 y σ5 hld σ6 dm σ7 hst3 hf1 hf2 hf3 hf4 _
    simp at heq
    rcases vc_cmpx_at hN0 _ (Fr.fence (Fr.fence hT hf1.1) hf2.1) (by simp [hx0]) rfl (by simp [cmpxOp]) old _
      hx.1 with ⟨h0, -⟩ | ⟨-, hH1⟩
    · exact absurd heq h0
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst2, rfl⟩
    · simp [hx1, hdc] at hm
    have hH2 := vc_ld_c_at hLC _ (H1.fence hH1 hf3.1) (by simp [hx1]) rfl w _ hst2.1
    rcases hst3 with ⟨hm, -, -⟩ | ⟨-, rfl, b, hst3⟩
    · simp [hx1, hdc] at hm
    have hH3 := vc_st_c_at hLC _ _ (H2.fence hH2 hf4.1) (by simp [hx1]) rfl (by simp [BitVec.add_comm]) b _
      hst3.1
    simp only [SharedEnv.counted_ok, SharedEnv.within_ok_store]
    exact ⟨vc_rel_ok_at hL hN0 htid hN32 _ _ hH3 (by simp [hx0]) rfl (by simp), by simp [hx0]⟩
  case vc8 =>
    rename_i af σ1 σ2 old σ3 hx heq hz σ4 y σ5 hld σ6 dm σ7 hst3 b' σ8 hrel σ9 hf1 hf2 hf3 hf4 hf5 _
    simp at heq
    rcases vc_cmpx_at hN0 _ (Fr.fence (Fr.fence hT hf1.1) hf2.1) (by simp [hx0]) rfl (by simp [cmpxOp]) old _
      hx.1 with ⟨h0, -⟩ | ⟨-, hH1⟩
    · exact absurd heq h0
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst2, rfl⟩
    · simp [hx1, hdc] at hm
    have hH2 := vc_ld_c_at hLC _ (H1.fence hH1 hf3.1) (by simp [hx1]) rfl w _ hst2.1
    rcases hst3 with ⟨hm, -, -⟩ | ⟨-, rfl, b, hst3⟩
    · simp [hx1, hdc] at hm
    have hH3 := vc_st_c_at hLC _ _ (H2.fence hH2 hf4.1) (by simp [hx1]) rfl (by simp [BitVec.add_comm]) b _
      hst3.1
    have hQ := vc_rel_at hL hN0 htid hN32 _ _ hH3 (by simp [hx0]) rfl (by simp) b' _ hrel.1
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simpa using hdl,
      by simpa using hdc⟩, .inr ⟨rfl, QEnd.fence hQ hf5.1⟩⟩, .inl (by decide)⟩
  case vc9 =>
    rename_i af σ1 σ2 old σ3 hx hne hz σ4 hf1 hf2 hf3 _
    simp at hne
    rcases vc_cmpx_at hN0 _ (Fr.fence (Fr.fence hT hf1.1) hf2.1) (by simp [hx0]) rfl (by simp [cmpxOp]) old _
      hx.1 with ⟨-, hF⟩ | ⟨h0, -⟩
    · have hn := hx.2
      refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simpa using hdl,
        by simpa using hdc⟩, .inl ⟨rfl, Fr.fence hF hf3.1⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg
      simp [SharedAccess.tick] at hn
      omega
    · exact absurd h0 hne
  case vc10 =>
    rename_i af σ1 σ2 old σ3 hx hne hz σ4 hm hf1 hf2 hf3 _
    simp at hne
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact absurd hz hne
  case vc11 =>
    rename_i af σ1 σ2 old σ3 hx hne hz σ4 y σ5 hld σ6 hm hf1 hf2 hf3 hf4 _
    simp at hne
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact absurd hz hne
  case vc12 =>
    rename_i af σ1 σ2 old σ3 hx hne hz σ4 y σ5 hld σ6 dm σ7 hst3 hf1 hf2 hf3 hf4 _
    simp at hne
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact absurd hz hne
  case vc13 =>
    rename_i af σ1 σ2 old σ3 hx hne hz σ4 y σ5 hld σ6 dm σ7 hst3 hf1 hf2 hf3 hf4 _
    simp at hne
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact absurd hz hne
  case vc14 =>
    rename_i af σ1 σ2 old σ3 hx hne hz σ4 y σ5 hld σ6 dm σ7 hst3 b' σ8 hrel σ9 hf1 hf2 hf3 hf4 hf5 _
    simp at hne
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact absurd hz hne
  case vc1 => exact hT

end Kraken.Promising.X64.EnvG.Cmpx
