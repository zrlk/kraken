/-
**Part 2: the relay and the reader by `vcgen`
on `EnvGT`** (the `TakeMpVCGen.takeReader_envGT` pattern).

- `relay_envGT`: the relay (`spin: ldar; cbz; mov; str; mov; stlr`), a
  `PartialTripleEnv` in the counted `EnvGT` with plan `mpPlan rp.Q`, by
  `cfgEnv_partial` with a two-label table: `RK1` at `spin`, `RK4` (the token
  `W2`) at `done_y`.
- `reader_envGT`: MP's reader text (`spin: ldar; cbz; ldr`) on `f2`, in the
  counted `EnvGT` with the empty plan: `DK1` at `spin`; at `done_r`, `Own43`
  and, under the clean flag, `W4 = 43`.

One `vcgen` call per cut; the goals are discharged by the isolated VCs of
`EnvG/RelaySpec.lean`.
-/
import Kraken.Promising.SLR.EnvG.RelaySpec
import Kraken.AArch64.EnvCfg

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Mp Kraken.Promising.SLR.MpTrees
open Kraken.Promising.SLR.EnvG.TakeSmoke Kraken.Promising.SLR.EnvG.TakeMp Kraken.Promising.SLR.EnvG.MpSmoke

namespace Kraken.Promising.SLR.EnvG.Relay

set_option mvcgen.warning false
set_option experimental.vcgen true

variable [layout : _root_.Layout]

/-! ## The reader -/

section Reader

variable [Executable.ValidLayout (layout mpReader)]

local instance mpReader.envT : CodeEnv := ⟨layout mpReader⟩

/-- The reader's table: `DK1` at `spin`; at `done_r`, `Own43` and, under the
clean flag, `W4 = 43`. -/
abbrev readerTableD (Q : Params) (tid : Nat) :
    Label → MachineData → (SharedEnv.counted (ET tid)).State → Prop :=
  fun lb s σ => s.regs.X0.toBitVec = Q.f ∧ s.regs.X1.toBitVec = Q.d ∧ Mem.loadInt s.dmem Q.f 4 = none ∧
    Mem.loadInt s.dmem Q.d 4 = none ∧
    ((lb = "spin" ∧ DK1 Q σ.1) ∨ (lb = "done_r" ∧ Own43 Q σ.1.r ∧ (σ.1.cl → s.regs.X4.toBitVec.setWidth 32 = 43)))

/-- **The reader on `EnvGT`** (counted, partial): every run that reaches the
end holds all of `Dt` with maximal write `(43, tw)`, and under the clean flag
has `W4 = 43`. -/
theorem reader_envGT (Q : Params) (tid : Nat) :
    PartialTripleEnv (SharedEnv.counted (ET tid))
      (fun s σ => s.regs.X0.toBitVec = Q.f ∧ s.regs.X1.toBitVec = Q.d ∧ Mem.loadInt s.dmem Q.f 4 = none ∧
        Mem.loadInt s.dmem Q.d 4 = none ∧ DK1 Q σ.1)
      mpReader (fun s σ => Own43 Q σ.1.r ∧ (σ.1.cl → s.regs.X4.toBitVec.setWidth 32 = 43))
      (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (readerTableD Q tid) (hP := by funext s g; simp [readerTableD])
  cfg_cases_env [mpReader]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hdf, hdd, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  case vc1 => simp
  case vc2 => simp [hx0, hdf]
  case vc3 => simp
  case vc5 => simp
  case vc6 => simp
  case vc4 =>
    -- the back edge (`cbz` taken): `DK1` again; the counter moved
    rename_i s σ0 b σ1 hst1 hcbz σ2 hf _
    simp only [fenceMono_le_counted, fenceMono_le_envGT, SharedEnv.counted_step, envGT_step_load] at hst1 hf
    simp [hx0] at hst1
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hdf], by simp [hdd],
      .inl ⟨rfl, DK1.fence (((vc_d1 tid σ0.1 hT) _ σ1.1 hst1.1).1 (by simpa using hcbz)) hf.1⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg; omega
  case vc7 =>
    -- `cbz` not taken, then the data load
    rename_i v σ1 hst1 hcbz σ2 hf1 rng w σ3 hld _
    simp only [fenceMono_le_counted, fenceMono_le_envGT, SharedEnv.counted_step, envGT_step_load] at hst1 hf1
    simp [hx0] at hst1
    have hK2 : DK2 Q σ2.1 := DK2.fence (((vc_d1 tid _ hT) _ σ1.1 hst1.1).2 (by simpa using hcbz)) hf1.1
    simp [hx1, hdd] at hld
    obtain ⟨v, ⟨hst3, -⟩, rfl⟩ := hld
    have h3 := vc_d2 tid σ2.1 hK2 v σ3.1 (by simpa using hst3)
    refine ⟨by simp [hx0], by simp [hx1], by simp [hdf], by simp [hdd], .inr ⟨rfl, h3.1, fun hcl => ?_⟩⟩
    rw [h3.2 hcl]
    simp
  case vc1 => exact hT

end Reader

/-! ## The relay -/

section Relay

variable [Executable.ValidLayout (layout relay)]

local instance relay.env : CodeEnv := ⟨layout relay⟩

/-- The relay's frame: the three addresses in `X0`/`X1`/`X2`, none in
`dmem`. -/
abbrev RFrame (rp : RP) (s : MachineData) : Prop :=
  s.regs.X0.toBitVec = rp.f1 ∧ s.regs.X1.toBitVec = rp.d ∧ s.regs.X2.toBitVec = rp.f2 ∧
    Mem.loadInt s.dmem rp.f1 4 = none ∧ Mem.loadInt s.dmem rp.d 4 = none ∧ Mem.loadInt s.dmem rp.f2 4 = none

/-- The relay's table: `RK1` at `spin`, `RK4` at `done_y`. -/
abbrev relayTable (rp : RP) (tid : Nat) :
    Label → MachineData → (SharedEnv.counted (ER rp tid)).State → Prop :=
  fun lb s σ => RFrame rp s ∧ ((lb = "spin" ∧ RK1 rp σ.1) ∨ (lb = "done_y" ∧ RK4 rp σ.1))

/-- **The relay on `EnvGT`** (counted, partial): from `RK1` every run that
reaches the end keeps the token `W2`, having taken `Dt`, written `43` and
released `Dt` to `f2`. -/
theorem relay_envGT (rp : RP) (hL : MpLocs rp.Q) (tid : Nat) :
    PartialTripleEnv (SharedEnv.counted (ER rp tid))
      (fun s σ => RFrame rp s ∧ RK1 rp σ.1) relay (fun _ σ => RK4 rp σ.1) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (relayTable rp tid) (hP := by funext s g; simp [relayTable])
  cfg_cases_env [relay]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hx0, hx1, hx2, hdf, hdd, hdg⟩, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  case vc1 => simp
  case vc2 => simp [hx0, hdf]
  case vc3 => simp
  case vc5 => simp
  case vc7 => simp
  case vc4 =>
    -- the back edge (`cbz` taken): `RK1` again; the counter moved
    rename_i s σ0 b σ1 hst1 hcbz σ2 hf _
    simp only [fenceMono_le_counted, fenceMono_le_envGT, SharedEnv.counted_step, envGT_step_load] at hst1 hf
    simp [hx0] at hst1
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simp [hx2], by simp [hdf],
      by simp [hdd], by simp [hdg]⟩, .inl ⟨rfl, RK1.fence (((vc_r1 tid σ0.1 hT) _ σ1.1 hst1.1).1
        (by simpa using hcbz)) hf.1⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg; omega
  case vc6 =>
    rename_i v σ1 hst1 hcbz σ2 hf1 σ3 hf2 rng hdm _
    simp only [fenceMono_le_counted, fenceMono_le_envGT, SharedEnv.counted_step, envGT_step_load] at hst1 hf1 hf2
    simp [hx0] at hst1
    have hK2 : RK2 rp σ3.1 :=
      RK2.fence (RK2.fence (((vc_r1 tid _ hT) _ σ1.1 hst1.1).2 (by simpa using hcbz)) hf1.1) hf2.1
    simpa [hx1] using (vc_r2 hL tid σ3.1 hK2).1
  case vc8 =>
    rename_i v σ1 hst1 hcbz σ2 hf1 σ3 hf2 rng dm σ4 hd σ5 hf3 _
    simp [hx1, hdd] at hd
    simp [hd.1, hx2, hdg]
  case vc9 =>
    rename_i v σ1 hst1 hcbz σ2 hf1 σ3 hf2 rng dm σ4 hd σ5 hf3 _
    simp only [fenceMono_le_counted, fenceMono_le_envGT, SharedEnv.counted_step, envGT_step_load] at hst1 hf1 hf2 hf3
    simp [hx0] at hst1
    have hK2 : RK2 rp σ3.1 :=
      RK2.fence (RK2.fence (((vc_r1 tid _ hT) _ σ1.1 hst1.1).2 (by simpa using hcbz)) hf1.1) hf2.1
    simp [hx1, hdd] at hd
    have hK3 : RK3 rp σ4.1 := by
      rcases hd.2 with hst | hst <;> exact (vc_r2 hL tid σ3.1 hK2).2 _ σ4.1 (by simpa using hst)
    simpa [hx2, hd.1, hdg] using (vc_r3 hL tid σ5.1 (RK3.fence hK3 hf3.1)).1
  case vc10 =>
    rename_i v σ1 hst1 hcbz σ2 hf1 σ3 hf2 rng dm σ4 hd σ5 hf3 b σ6 hst6 _
    simp only [fenceMono_le_counted, fenceMono_le_envGT, SharedEnv.counted_step, envGT_step_load] at hst1 hf1 hf2 hf3
    simp [hx0] at hst1
    have hK2 : RK2 rp σ3.1 :=
      RK2.fence (RK2.fence (((vc_r1 tid _ hT) _ σ1.1 hst1.1).2 (by simpa using hcbz)) hf1.1) hf2.1
    simp [hx1, hdd] at hd
    have hK3 : RK3 rp σ4.1 := by
      rcases hd.2 with hst | hst <;> exact (vc_r2 hL tid σ3.1 hK2).2 _ σ4.1 (by simpa using hst)
    simp [hx2] at hst6
    have h4 : RK4 rp σ6.1 := (vc_r3 hL tid σ5.1 (RK3.fence hK3 hf3.1)).2 _ σ6.1 (by simpa using hst6.1)
    exact ⟨⟨by simp [hx0], by simp [hx1], by simp [hx2], by simp [hd.1, hdf], by simp [hd.1, hdd],
      by simp [hd.1, hdg]⟩, .inr ⟨rfl, h4⟩⟩
  case vc1 => exact hT

end Relay

end Kraken.Promising.SLR.EnvG.Relay
