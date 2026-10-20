/-
**Part 8: the skipping reader by `vcgen` on
`EnvGTU`** (the `TakeMpVCGen.takeReader_envGT` pattern).

- `skipReader_envGTU`: the reader (`start: ldar; sub; cbnz; mov; str; ldr`),
  a `PartialTripleEnv` in the counted `EnvGTU` by `cfgEnv_partial` with a
  two-label table: `K1` at `start`; at `done_s`, if `W3 = 2` then `Own43`
  and, under the clean flag, `W4 = 43`. One `vcgen` call per cut; the goals
  are discharged by the isolated VCs of `EnvG/TakeUSkip.lean`.
-/
import Kraken.Promising.SLR.EnvG.TakeUSkip
import Kraken.AArch64.EnvCfg

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Mp Kraken.Promising.SLR.EnvG.TakeSmoke
open Kraken.Promising.SLR.EnvG.TakeMp

namespace Kraken.Promising.SLR.EnvG.TakeUSkip

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- The `sub`/`cbnz` test: a zero difference means the low word is `2`. -/
theorem two_of_sub {x : BitVec 32} (h : x - 2#32 = 0#32) : x = 2 := by bv_omega

variable [layout : _root_.Layout] [Executable.ValidLayout (layout skipReader)]

local instance skipReader.env : CodeEnv := ⟨layout skipReader⟩

/-- What the reader ends with: if it read `2`, `Own43` and (clean) `W4 = 43`. -/
def SkipDone (P : Params) (x3 x4 : BitVec 32) (cl : Prop) (r : Res) : Prop :=
  x3 = 2 → Own43 P r ∧ (cl → x4 = 43)

/-- The reader's table: `K1` at `start`; `SkipDone` at `done_s`. -/
abbrev skipTable (P : Params) (tid : Nat) :
    Label → MachineData → (SharedEnv.counted (EU tid)).State → Prop :=
  fun lb s σ => s.regs.X0.toBitVec = P.f ∧ s.regs.X1.toBitVec = P.d ∧ Mem.loadInt s.dmem P.f 4 = none ∧
    Mem.loadInt s.dmem P.d 4 = none ∧
    ((lb = "start" ∧ K1 P σ.1) ∨
      (lb = "done_s" ∧ SkipDone P (s.regs.X3.toBitVec.setWidth 32) (s.regs.X4.toBitVec.setWidth 32) σ.1.cl σ.1.r))

/-- **The skipping reader on `EnvGTU`** (counted, partial): every run that
reaches the end and read `2` holds all of `Dt` with maximal write
`(43, tw)`, and under the clean flag has `W4 = 43`. -/
theorem skipReader_envGTU (P : Params) (tid : Nat) :
    PartialTripleEnv (SharedEnv.counted (EU tid))
      (fun s σ => s.regs.X0.toBitVec = P.f ∧ s.regs.X1.toBitVec = P.d ∧ Mem.loadInt s.dmem P.f 4 = none ∧
        Mem.loadInt s.dmem P.d 4 = none ∧ K1 P σ.1)
      skipReader
      (fun s σ => SkipDone P (s.regs.X3.toBitVec.setWidth 32) (s.regs.X4.toBitVec.setWidth 32) σ.1.cl σ.1.r)
      (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (skipTable P tid) (hP := by funext s g; simp [skipTable])
  cfg_cases_env [skipReader]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hdf, hdd, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  case vc1 => simp
  case vc2 => simp [hx0, hdf]
  case vc3 => simp
  case vc5 => simp
  case vc4 =>
    rename_i v σ1 hst1 rng σ2 hf1 hcbz σ3 hf2 _
    simp at hcbz
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hdf], by simp [hdd],
      .inr ⟨rfl, fun h3 => ?_⟩⟩, .inl (by decide)⟩
    simp at h3
    exact absurd (by rw [h3]; rfl) hcbz
  case vc6 =>
    rename_i v σ1 hst1 rng σ2 hf1 hcbz σ3 hf2 σ4 hf3 rng2 _ _
    simp only [fenceMono_le_counted, fenceMono_le_envGTU, SharedEnv.counted_step, envGTU_step_load] at hst1 hf1 hf2 hf3
    simp [hx0] at hst1
    simp at hcbz
    have hK2 : K2 P σ4.1 :=
      K2.fence (K2.fence (K2.fence (vc_s1 tid _ hT _ σ1.1 hst1.1 (two_of_sub hcbz)) hf1.1) hf2.1) hf3.1
    simpa [hx1] using (vc_s2 tid σ4.1 hK2).1
  case vc7 =>
    rename_i v σ1 hst1 rng σ2 hf1 hcbz σ3 hf2 σ4 hf3 rng2 dm σ5 hd _
    simp [hx1, hdd] at hd
    simp [hd.1]
  case vc8 => simp
  case vc9 =>
    rename_i v σ1 hst1 rng σ2 hf1 hcbz σ3 hf2 σ4 hf3 rng2 dm σ5 hd rng3 w σ6 hld _
    simp only [fenceMono_le_counted, fenceMono_le_envGTU, SharedEnv.counted_step, envGTU_step_load] at hst1 hf1 hf2 hf3
    simp [hx0] at hst1
    simp at hcbz
    have hK2 : K2 P σ4.1 :=
      K2.fence (K2.fence (K2.fence (vc_s1 tid _ hT _ σ1.1 hst1.1 (two_of_sub hcbz)) hf1.1) hf2.1) hf3.1
    simp [hx1, hdd] at hd
    have hK3 : K3 P σ5.1 := by
      rcases hd.2 with hst | hst <;> exact (vc_s2 tid σ4.1 hK2).2 _ σ5.1 (by simpa using hst)
    simp [hx1, hd.1, hdd] at hld
    obtain ⟨v', ⟨hst6, -⟩, rfl⟩ := hld
    have h6 := vc_s3 tid σ5.1 hK3 v' σ6.1 (by simpa using hst6)
    refine ⟨by simp [hx0], by simp [hx1], by simp [hd.1, hdf], by simp [hd.1, hdd], .inr ⟨rfl, fun _ => ⟨h6.1, fun hcl => ?_⟩⟩⟩
    rw [h6.2 hcl]
    simp
  case vc1 => exact hT

end Kraken.Promising.SLR.EnvG.TakeUSkip
