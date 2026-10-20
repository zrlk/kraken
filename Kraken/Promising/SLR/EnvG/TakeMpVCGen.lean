/-
**Part 6: the writing reader by `vcgen` on
`EnvGT`** (the `MpSmokeVCGen.mpReader_envGP` pattern).

- `takeReader_envGT`: the reader (`spin: ldar; cbz; mov; str; ldr`), a
  `PartialTripleEnv` in the counted `EnvGT` by `cfgEnv_partial` with a
  two-label table: `K1` at `spin`; at `done_t`, `Own43` (all of `Dt`, maximal
  write `(43, tw)`) and, under the clean flag, `W4 = 43`. One `vcgen` call
  per cut; the goals are discharged by the isolated VCs of `EnvG/TakeMp.lean`.
-/
import Kraken.Promising.SLR.EnvG.TakeMp
import Kraken.AArch64.EnvCfg

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Mp Kraken.Promising.SLR.EnvG.TakeSmoke

namespace Kraken.Promising.SLR.EnvG.TakeMp

set_option mvcgen.warning false
set_option experimental.vcgen true

variable [layout : _root_.Layout] [Executable.ValidLayout (layout takeReader)]

local instance takeReader.env : CodeEnv := ⟨layout takeReader⟩

/-- The reader's table: `K1` at `spin`; at `done_t`, `Own43` and, under the
clean flag, `W4 = 43`. -/
abbrev readerTableK (P : Params) (tid : Nat) :
    Label → MachineData → (SharedEnv.counted (ET tid)).State → Prop :=
  fun lb s σ => s.regs.X0.toBitVec = P.f ∧ s.regs.X1.toBitVec = P.d ∧ Mem.loadInt s.dmem P.f 4 = none ∧
    Mem.loadInt s.dmem P.d 4 = none ∧
    ((lb = "spin" ∧ K1 P σ.1) ∨ (lb = "done_t" ∧ Own43 P σ.1.r ∧ (σ.1.cl → s.regs.X4.toBitVec.setWidth 32 = 43)))

/-- **The writing reader on `EnvGT`** (counted, partial): every run that
reaches the end holds all of `Dt` with maximal write `(43, tw)`, and under
the clean flag has `W4 = 43`. -/
theorem takeReader_envGT (P : Params) (tid : Nat) :
    PartialTripleEnv (SharedEnv.counted (ET tid))
      (fun s σ => s.regs.X0.toBitVec = P.f ∧ s.regs.X1.toBitVec = P.d ∧ Mem.loadInt s.dmem P.f 4 = none ∧
        Mem.loadInt s.dmem P.d 4 = none ∧ K1 P σ.1)
      takeReader (fun s σ => Own43 P σ.1.r ∧ (σ.1.cl → s.regs.X4.toBitVec.setWidth 32 = 43))
      (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (readerTableK P tid) (hP := by funext s g; simp [readerTableK])
  cfg_cases_env [takeReader]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hdf, hdd, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  case vc1 => simp
  case vc2 => simp [hx0, hdf]
  case vc3 => simp
  case vc5 => simp
  case vc8 => simp
  case vc4 =>
    -- the back edge (`cbz` taken): `K1` again; the counter moved
    rename_i s σ0 b σ1 hst1 hcbz σ2 hf _
    simp only [fenceMono_le_counted, fenceMono_le_envGT, SharedEnv.counted_step, envGT_step_load] at hst1 hf
    simp [hx0] at hst1
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hdf], by simp [hdd],
      .inl ⟨rfl, K1.fence (((vc_k1 tid σ0.1 hT) _ σ1.1 hst1.1).1 (by simpa using hcbz)) hf.1⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg; omega
  case vc6 =>
    rename_i v σ1 hst1 hcbz σ2 hf1 σ3 hf2 rng hdm _
    simp only [fenceMono_le_counted, fenceMono_le_envGT, SharedEnv.counted_step, envGT_step_load] at hst1 hf1 hf2
    simp [hx0] at hst1
    have hK2 : K2 P σ3.1 :=
      K2.fence (K2.fence (((vc_k1 tid _ hT) _ σ1.1 hst1.1).2 (by simpa using hcbz)) hf1.1) hf2.1
    simpa [hx1] using (vc_k2 tid σ3.1 hK2).1
  case vc7 =>
    rename_i v σ1 hst1 hcbz σ2 hf1 σ3 hf2 rng dm σ4 hd _
    simp [hx1, hdd] at hd
    simp [hd.1]
  case vc9 =>
    -- `cbz` not taken, the store, then the load back
    rename_i v σ1 hst1 hcbz σ2 hf1 σ3 hf2 rng dm σ4 hd rng2 w σ5 hld _
    simp only [fenceMono_le_counted, fenceMono_le_envGT, SharedEnv.counted_step, envGT_step_load] at hst1 hf1 hf2
    simp [hx0] at hst1
    have hK2 : K2 P σ3.1 :=
      K2.fence (K2.fence (((vc_k1 tid _ hT) _ σ1.1 hst1.1).2 (by simpa using hcbz)) hf1.1) hf2.1
    simp [hx1, hdd] at hd
    have hK3 : K3 P σ4.1 := by
      rcases hd.2 with hst | hst <;> exact (vc_k2 tid σ3.1 hK2).2 _ σ4.1 (by simpa using hst)
    simp [hx1, hd.1, hdd] at hld
    obtain ⟨v, ⟨hst5, -⟩, rfl⟩ := hld
    have h5 := vc_k3 tid σ4.1 hK3 v σ5.1 (by simpa using hst5)
    refine ⟨by simp [hx0], by simp [hx1], by simp [hd.1, hdf], by simp [hd.1, hdd], .inr ⟨rfl, h5.1, fun hcl => ?_⟩⟩
    rw [h5.2 hcl]
    simp
  case vc1 => exact hT

end Kraken.Promising.SLR.EnvG.TakeMp
