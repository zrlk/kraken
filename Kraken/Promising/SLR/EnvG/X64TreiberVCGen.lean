/-
**Part 5: the two threads of the x64
`treiber_pp.kl` on `EnvGCX` by `vcgen`**: `pusherX_envGC` and
`popperX_envGC`, `PartialTripleEnv`s in the counted `EnvGCX` by
`cfgEnv_partial` with the VCs of `EnvG/TreiberVCCommon.lean` at the x64
instance (`EnvG/X64TreiberVC.lean`). The x64 counterpart of the Treiber proof's
`EnvG/TreiberVCGen.lean`.

The `lock cmpxchgq` cells use `MachineWP.lock_cmpxchg_shared_spec` (both
outcomes are VCs; on a mismatch the old value lands in `rax`), the loads and
stores the generic `mov*_env_spec`s, `movl $1` the shared
`mov32_store_imm_shared_spec`; the silent cells `envMonoX_lift_spec`.
-/
import Kraken.Promising.SLR.EnvG.X64TreiberVC
import Kraken.EnvCfg

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.EnvG.Treiber Kraken.Promising.SLR.EnvG.TreiberCommon

namespace Kraken.Promising.X64.EnvG.TreiberX

set_option mvcgen.warning false
set_option experimental.vcgen true

variable [layout : _root_.Layout]

section Pusher

variable [Executable.ValidLayout (layout treiberPusherX)]

local instance treiberPusherX.env : CodeEnv := ⟨layout treiberPusherX⟩

/-- The pusher's frame: `rdi = t`, `rbx = n`, none of `top`, `n1d`, `n1n` in
`dmem`. -/
abbrev PFrameX (t n : BitVec 64) (s : MachineData) : Prop :=
  s.regs.get64 .rdi = t ∧ s.regs.get64 .rbx = n ∧ Mem.loadInt s.dmem t 8 = none ∧
    Mem.loadInt s.dmem n 4 = none ∧ Mem.loadInt s.dmem (n + 8) 8 = none

/-- The pusher's table. -/
abbrev pushTableX (t n : BitVec 64) (tok : Loc) :
    Label → MachineData → (SharedEnv.counted (EPX t n tok)).State → Prop :=
  fun lb s σ => PFrameX t n s ∧
    ((lb = "pusher" ∧ Pu0 (tParamsX t n tok) σ.1) ∨ (lb = "push" ∧ Pu (tParamsX t n tok) σ.1) ∨
      (lb = "pdone" ∧ Pd (tParamsX t n tok) σ.1))

theorem pusherX_envGC (t n : BitVec 64) (tok : Loc) (hL : TLocs (tParamsX t n tok)) :
    PartialTripleEnv (SharedEnv.counted (EPX t n tok))
      (fun s σ => PFrameX t n s ∧ Pu0 (tParamsX t n tok) σ.1)
      treiberPusherX (fun _ σ => Pd (tParamsX t n tok) σ.1) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (pushTableX t n tok) (hP := by funext s g; simp [pushTableX])
  cfg_cases_env [treiberPusherX]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hx0, hx1, hdt, hdd, hdn⟩, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [Reg64s.get64] at hx0 hx1
  all_goals have hdn' : Mem.loadInt _ (n + 8#64) 8 = none := hdn
  -- cut `pusher`: `movl $1, (%rbx)`
  case vc1 => simp [hx1, hdd]
  case vc2 =>
    simp only [SharedEnv.counted_ok]
    exact vc_push_str_d_ok_at hL _ hT (by simp [hx1]) (by decide)
  case vc3 =>
    rename_i b σ1 hst _
    exact ⟨⟨by simp [hx0], by simp [hx1], hdt, hdd, hdn⟩,
      .inr (.inl ⟨rfl, vc_push_str_d_at hL _ hT (by simp [hx1]) (by decide) b σ1.1 hst.1⟩)⟩
  -- cut `push`
  case vc1 =>
    simp only [SharedEnv.counted_ok]
    simp [hx0]
    exact trivial
  case vc2 =>
    rename_i v σ1 hld hnone _
    have hP : Pu (tParamsX t n tok) σ1.1 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hx0, hdt] at hm
      · exact vc_push_load_at _ hT w σ1.1 hst.1
    simp only [SharedEnv.counted_ok]
    exact vc_push_str_n_ok_at hL _ hP _ (by simp [hx1])
  case vc3 =>
    rename_i v σ1 hld dm σ2 hst _
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, -⟩ := hst
    subst hdm
    simp [hx0, hdt]
  case vc4 =>
    rename_i v σ1 hld dm σ2 hst _
    have hP : Pu (tParamsX t n tok) σ1.1 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hx0, hdt] at hm
      · exact vc_push_load_at _ hT w σ1.1 hst.1
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, hso, -⟩ := hst
    subst hdm
    have hP2 : Pu (tParamsX t n tok) σ2.1 := by
      rcases hso with h | h <;> exact vc_push_str_n_at hL _ hP _ (by simp [hx1]) _ σ2.1 h
    simp only [SharedEnv.counted_ok]
    exact vc_push_cas_ok_at hL _ hP2 v (by simp [hx0]) (by simp [hx1, cmpxOp64])
  case vc5 =>
    rename_i σ v σ1 hld dm σ2 hst old σ3 hcas heq hz σ4 hf _
    have hP : Pu (tParamsX t n tok) σ1.1 ∧ σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hx0, hdt] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_push_load_at _ hT w σ1.1 hst.1, by omega⟩
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, hso, hst2⟩ := hst
    subst hdm
    have hP2 : Pu (tParamsX t n tok) σ2.1 := by
      rcases hso with h | h <;> exact vc_push_str_n_at hL _ hP.1 _ (by simp [hx1]) _ σ2.1 h
    have hc := vc_push_cas_at hL _ hP2 v (by simp [hx0]) (by simp [hx1, cmpxOp64]) old σ3.1 hcas.1
    have h3 := hcas.2
    simp only [SharedAccess.tick] at h3
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact absurd (by rw [heq]; exact BitVec.sub_self _) hz
  case vc6 =>
    rename_i σ v σ1 hld dm σ2 hst old σ3 hcas heq hz σ4 hf1 σ5 hf2 _
    have hP : Pu (tParamsX t n tok) σ1.1 ∧ σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hx0, hdt] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_push_load_at _ hT w σ1.1 hst.1, by omega⟩
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, hso, hst2⟩ := hst
    subst hdm
    have hP2 : Pu (tParamsX t n tok) σ2.1 := by
      rcases hso with h | h <;> exact vc_push_str_n_at hL _ hP.1 _ (by simp [hx1]) _ σ2.1 h
    have hc := vc_push_cas_at hL _ hP2 v (by simp [hx0]) (by simp [hx1, cmpxOp64]) old σ3.1 hcas.1
    have h3 := hcas.2
    simp only [SharedAccess.tick] at h3
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCX] at hf1 hf2
    rcases hc with ⟨hne, -⟩ | ⟨-, hPd⟩
    · exact absurd heq hne
    · exact Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simpa using hdt,
        by simpa using hdd, by simpa using hdn⟩, .inr (.inr ⟨rfl, Pd.fence (Pd.fence hPd hf1.1) hf2.1⟩)⟩,
        .inl (by decide)⟩
  case vc7 =>
    rename_i σ v σ1 hld dm σ2 hst old σ3 hcas heq hz σ4 hf _
    have hP : Pu (tParamsX t n tok) σ1.1 ∧ σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hx0, hdt] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_push_load_at _ hT w σ1.1 hst.1, by omega⟩
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, hso, hst2⟩ := hst
    subst hdm
    have hP2 : Pu (tParamsX t n tok) σ2.1 := by
      rcases hso with h | h <;> exact vc_push_str_n_at hL _ hP.1 _ (by simp [hx1]) _ σ2.1 h
    have hc := vc_push_cas_at hL _ hP2 v (by simp [hx0]) (by simp [hx1, cmpxOp64]) old σ3.1 hcas.1
    have h3 := hcas.2
    simp only [SharedAccess.tick] at h3
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCX] at hf
    rcases hc with ⟨-, hPu⟩ | ⟨heq', -⟩
    · refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simpa using hdt,
        by simpa using hdd, by simpa using hdn⟩, .inr (.inl ⟨rfl, Pu.fence hPu hf.1⟩)⟩,
        .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg
      have h4 := hf.2
      omega
    · exact absurd heq' heq
  case vc8 =>
    rename_i σ v σ1 hld dm σ2 hst old σ3 hcas heq hz σ4 hf1 σ5 hf2 _
    have hP : Pu (tParamsX t n tok) σ1.1 ∧ σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hx0, hdt] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_push_load_at _ hT w σ1.1 hst.1, by omega⟩
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, hso, hst2⟩ := hst
    subst hdm
    have hP2 : Pu (tParamsX t n tok) σ2.1 := by
      rcases hso with h | h <;> exact vc_push_str_n_at hL _ hP.1 _ (by simp [hx1]) _ σ2.1 h
    have hc := vc_push_cas_at hL _ hP2 v (by simp [hx0]) (by simp [hx1, cmpxOp64]) old σ3.1 hcas.1
    have h3 := hcas.2
    simp only [SharedAccess.tick] at h3
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact absurd (by bv_omega) heq
  -- cut `pdone`
  case vc1 => exact hT

end Pusher

section Popper

variable [Executable.ValidLayout (layout treiberPopperX)]

local instance treiberPopperX.env : CodeEnv := ⟨layout treiberPopperX⟩

/-- The popper's frame: `rdi = t`, and `dmem` maps no 4- or 8-byte word (the
popper's layout is `sAll`; its loads at `rax` are at a loaded address). -/
abbrev QFrameX (t : BitVec 64) (s : MachineData) : Prop :=
  s.regs.get64 .rdi = t ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ (∀ a, Mem.loadInt s.dmem a 4 = none)

/-- The popper's postcondition: on a clean run it popped `n1` and read its
data word `1`. -/
abbrev PopPostX (n : BitVec 64) (s : MachineData) (cl : Prop) : Prop :=
  cl → s.regs.get64 .r10 = n ∧ BitVec.setWidth 32 (s.regs.get64 .r11) = 1

/-- The popper's table. -/
abbrev popTableX (t n : BitVec 64) (tok : Loc) :
    Label → MachineData → (SharedEnv.counted (EQX t n tok)).State → Prop :=
  fun lb s σ => QFrameX t s ∧
    ((lb = "popper" ∧ Pp (tParamsX t n tok) σ.1) ∨ (lb = "qdone" ∧ PopPostX n s σ.1.cl))

theorem popperX_envGC (t n : BitVec 64) (tok : Loc) (hL : TLocs (tParamsX t n tok)) :
    PartialTripleEnv (SharedEnv.counted (EQX t n tok))
      (fun s σ => QFrameX t s ∧ Pp (tParamsX t n tok) σ.1)
      treiberPopperX (fun s σ => PopPostX n s σ.1.cl) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (popTableX t n tok) (hP := by funext s g; simp [popTableX])
  cfg_cases_env [treiberPopperX]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hx0, hd8, hd4⟩, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [Reg64s.get64] at hx0
  -- cut `popper`
  case vc1 =>
    simp only [SharedEnv.counted_ok]
    exact ⟨trivial, mem_sAll8 _⟩
  case vc2 =>
    -- `je popper` taken
    rename_i σ v σ1 hld af σ2 hf1 hz σ3 hf2 _
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCX] at hf1 hf2
    have hP1 : Pp (tParamsX t n tok) σ1.1 ∧ σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_pop_load_at _ hT w σ1.1 hst.1, by omega⟩
    have hP3 : Pp (tParamsX t n tok) σ3.1 := (hP1.1.fence hf1.1).fence hf2.1
    simp [CondCode.interp, StatusFlags.from_result] at hz
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simpa using hd8, by simpa using hd4⟩, .inl ⟨rfl, hP3⟩⟩,
      .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    have := hf1.2
    have := hf2.2
    omega
  case vc3 =>
    simp only [SharedEnv.counted_ok]
    exact ⟨trivial, mem_sAll8 _⟩
  case vc4 => simp [hd8]
  case vc5 =>
    rename_i σ v σ1 hld af σ2 hf1 hz σ3 hf2 v4 σ4 hld2 _
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCX] at hf1 hf2
    have hP1 : Pp (tParamsX t n tok) σ1.1 ∧ σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_pop_load_at _ hT w σ1.1 hst.1, by omega⟩
    have hP3 : Pp (tParamsX t n tok) σ3.1 := (hP1.1.fence hf1.1).fence hf2.1
    simp [CondCode.interp, StatusFlags.from_result] at hz
    have hP4 : Pp (tParamsX t n tok) σ4.1 ∧ σ3.2 ≤ σ4.2 := by
      rcases hld2 with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_pop_load_at _ hP3 w σ4.1 hst.1, by omega⟩
    simp only [SharedEnv.counted_ok]
    exact vc_pop_cas_ok_at hL _ hP4.1 v v4 hz (by simp [hx0]) (by simp [cmpxOp64])
  case vc6 =>
    rename_i σ v σ1 hld af σ2 hf1 hz σ3 hf2 v4 σ4 hld2 old σ5 hcas heq hz2 σ6 hf3 _
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCX] at hf1 hf2
    have hP1 : Pp (tParamsX t n tok) σ1.1 ∧ σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_pop_load_at _ hT w σ1.1 hst.1, by omega⟩
    have hP3 : Pp (tParamsX t n tok) σ3.1 := (hP1.1.fence hf1.1).fence hf2.1
    simp [CondCode.interp, StatusFlags.from_result] at hz
    have hP4 : Pp (tParamsX t n tok) σ4.1 ∧ σ3.2 ≤ σ4.2 := by
      rcases hld2 with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_pop_load_at _ hP3 w σ4.1 hst.1, by omega⟩
    have hc := vc_pop_cas_at hL _ hP4.1 v v4 hz (by simp [hx0]) (by simp [cmpxOp64]) old σ5.1 hcas.1
    have h5 := hcas.2
    simp only [SharedAccess.tick] at h5
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz2
    exact absurd (by rw [heq]; exact BitVec.sub_self _) hz2
  case vc7 =>
    simp only [SharedEnv.counted_ok]
    exact ⟨trivial, mem_sAll4 _⟩
  case vc8 =>
    rename_i σ v σ1 hld af σ2 hf1 hz σ3 hf2 v4 σ4 hld2 old σ5 hcas heq hz2 σ6 hf3 σ7 hf4 w σ8 hld3 σ9 hf5 _
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCX] at hf1 hf2
    have hP1 : Pp (tParamsX t n tok) σ1.1 ∧ σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_pop_load_at _ hT w σ1.1 hst.1, by omega⟩
    have hP3 : Pp (tParamsX t n tok) σ3.1 := (hP1.1.fence hf1.1).fence hf2.1
    simp [CondCode.interp, StatusFlags.from_result] at hz
    have hP4 : Pp (tParamsX t n tok) σ4.1 ∧ σ3.2 ≤ σ4.2 := by
      rcases hld2 with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_pop_load_at _ hP3 w σ4.1 hst.1, by omega⟩
    have hc := vc_pop_cas_at hL _ hP4.1 v v4 hz (by simp [hx0]) (by simp [cmpxOp64]) old σ5.1 hcas.1
    have h5 := hcas.2
    simp only [SharedAccess.tick] at h5
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz2
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCX] at hf3 hf4 hf5
    rcases hc with ⟨hne, -⟩ | ⟨-, hPc⟩
    · exact absurd heq hne
    have hPc7 := (hPc.fence hf3.1).fence hf4.1
    rcases hld3 with ⟨w', hw, -, -⟩ | ⟨-, w', hlo, hv⟩
    · simp [hd4] at hw
    have hfin := vc_pop_ldr_at _ v hPc7 (by simp) w' σ8.1 hlo.1
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simpa using hd8, by simpa using hd4⟩, .inr ⟨rfl, fun hcl => ?_⟩⟩, .inl (by decide)⟩
    obtain ⟨h1, h2⟩ := hfin (hf5.1.cl ▸ hcl)
    subst hv
    simp
    exact ⟨h1.symm, h2⟩
  case vc9 =>
    rename_i σ v σ1 hld af σ2 hf1 hz σ3 hf2 v4 σ4 hld2 old σ5 hcas heq hz2 σ6 hf3 _
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCX] at hf1 hf2
    have hP1 : Pp (tParamsX t n tok) σ1.1 ∧ σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_pop_load_at _ hT w σ1.1 hst.1, by omega⟩
    have hP3 : Pp (tParamsX t n tok) σ3.1 := (hP1.1.fence hf1.1).fence hf2.1
    simp [CondCode.interp, StatusFlags.from_result] at hz
    have hP4 : Pp (tParamsX t n tok) σ4.1 ∧ σ3.2 ≤ σ4.2 := by
      rcases hld2 with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_pop_load_at _ hP3 w σ4.1 hst.1, by omega⟩
    have hc := vc_pop_cas_at hL _ hP4.1 v v4 hz (by simp [hx0]) (by simp [cmpxOp64]) old σ5.1 hcas.1
    have h5 := hcas.2
    simp only [SharedAccess.tick] at h5
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz2
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCX] at hf3
    rcases hc with ⟨-, hPp⟩ | ⟨heq', -⟩
    · refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simpa using hd8, by simpa using hd4⟩, .inl ⟨rfl, hPp.fence hf3.1⟩⟩,
        .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg
      have := hf1.2
      have := hf2.2
      have := hf3.2
      omega
    · exact absurd heq' heq
  case vc10 =>
    simp only [SharedEnv.counted_ok]
    exact ⟨trivial, mem_sAll4 _⟩
  case vc11 =>
    rename_i σ v σ1 hld af σ2 hf1 hz σ3 hf2 v4 σ4 hld2 old σ5 hcas heq hz2 σ6 hf3 σ7 hf4 w σ8 hld3 σ9 hf5 _
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCX] at hf1 hf2
    have hP1 : Pp (tParamsX t n tok) σ1.1 ∧ σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_pop_load_at _ hT w σ1.1 hst.1, by omega⟩
    have hP3 : Pp (tParamsX t n tok) σ3.1 := (hP1.1.fence hf1.1).fence hf2.1
    simp [CondCode.interp, StatusFlags.from_result] at hz
    have hP4 : Pp (tParamsX t n tok) σ4.1 ∧ σ3.2 ≤ σ4.2 := by
      rcases hld2 with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_pop_load_at _ hP3 w σ4.1 hst.1, by omega⟩
    have hc := vc_pop_cas_at hL _ hP4.1 v v4 hz (by simp [hx0]) (by simp [cmpxOp64]) old σ5.1 hcas.1
    have h5 := hcas.2
    simp only [SharedAccess.tick] at h5
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz2
    exact absurd (by bv_omega) heq
  -- cut `qdone`
  case vc1 => exact hT ‹_›

end Popper

end Kraken.Promising.X64.EnvG.TreiberX
