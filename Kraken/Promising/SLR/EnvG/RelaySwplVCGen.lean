/-
**Part 3: the `swpl` relay by `vcgen` on
`EnvGTC`** (the relay proof's `relay_envGT` pattern, `EnvG/RelayVCGen.lean`, with the
`EnvGC`/`EnvGTC` glue of `EnvG/RmwGhostVCGen.lean`).

- `relaySwpl_envGTC`: the relay (`spin: ldar; cbz; mov; str; mov; swpl`), a
  `PartialTripleEnv` in the counted `EnvGTC` with plan `mpPlan rp.Q`, by
  `cfgEnv_partial` with the relay proof's two-label table shape: `RK1` at `spin`, `RK4`
  (the token `W2`) at `done_y`.

One `vcgen` call per cut; the goals are discharged by the VCs of
`EnvG/RelaySwplSpec.lean`. The swap goes through the generic
`swp_shared_spec`; its operation `rmwOpBits 32 (fun _ => some 1)` writes `1`.
The writer and the reader are the relay proof's (`mpWriter_envG`, `reader_envGT`).
-/
import Kraken.Promising.SLR.EnvG.RelaySwplSpec
import Kraken.Promising.SLR.EnvG.RelayVCGen
import Kraken.AArch64.EnvCfg

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Mp Kraken.Promising.SLR.MpTrees
open Kraken.Promising.SLR.EnvG.TakeSmoke Kraken.Promising.SLR.EnvG.TakeMp Kraken.Promising.SLR.EnvG.MpSmoke

namespace Kraken.Promising.SLR.EnvG.Relay

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- The swap's operation writes `1`. -/
theorem rmwOpBits_one (x y : Val) (h : rmwOpBits 32 (fun _ => some (1#32)) x = some y) : y = 1#128 := by
  simp [rmwOpBits] at h; exact h.symm

variable [layout : _root_.Layout]

section RelaySwpl

variable [Executable.ValidLayout (layout relaySwpl)]

local instance relaySwpl.env : CodeEnv := ⟨layout relaySwpl⟩

/-- The `swpl` relay's table: `RK1` at `spin`, `RK4` at `done_y`. -/
abbrev relaySwplTable (rp : RP) (tid : Nat) :
    Label → MachineData → (SharedEnv.counted (ERC rp tid)).State → Prop :=
  fun lb s σ => RFrame rp s ∧ ((lb = "spin" ∧ RK1 rp σ.1) ∨ (lb = "done_y" ∧ RK4 rp σ.1))

/-- **The `swpl` relay on `EnvGTC`** (counted, partial): from `RK1` every run
that reaches the end keeps the token `W2`, having taken `Dt`, written `43`
and released `Dt` to `f2` by a release-only swap. -/
theorem relaySwpl_envGTC (rp : RP) (hL : MpLocs rp.Q) (tid : Nat) :
    PartialTripleEnv (SharedEnv.counted (ERC rp tid))
      (fun s σ => RFrame rp s ∧ RK1 rp σ.1) relaySwpl (fun _ σ => RK4 rp σ.1) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (relaySwplTable rp tid) (hP := by funext s g; simp [relaySwplTable])
  cfg_cases_env [relaySwpl]
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
    simp only [fenceMono_le_counted, fenceMono_le_envGTC, SharedEnv.counted_step, envGTC_step_load] at hst1 hf
    simp [hx0] at hst1
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simp [hx2], by simp [hdf],
      by simp [hdd], by simp [hdg]⟩, .inl ⟨rfl, RK1.fence (((vc_r1c tid σ0.1 hT) _ σ1.1 hst1.1).1
        (by simpa using hcbz)) hf.1⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg; omega
  case vc6 =>
    rename_i v σ1 hst1 hcbz σ2 hf1 σ3 hf2 rng hdm _
    simp only [fenceMono_le_counted, fenceMono_le_envGTC, SharedEnv.counted_step, envGTC_step_load] at hst1 hf1 hf2
    simp [hx0] at hst1
    have hK2 : RK2 rp σ3.1 :=
      RK2.fence (RK2.fence (((vc_r1c tid _ hT) _ σ1.1 hst1.1).2 (by simpa using hcbz)) hf1.1) hf2.1
    simpa [hx1] using (vc_r2c hL tid σ3.1 hK2).1
  case vc8 =>
    rename_i v σ1 hst1 hcbz σ2 hf1 σ3 hf2 rng dm σ4 hd σ5 hf3 _
    simp [hx1, hdd] at hd
    simp [hd.1, hx2, hdg]
  case vc9 =>
    rename_i v σ1 hst1 hcbz σ2 hf1 σ3 hf2 rng dm σ4 hd σ5 hf3 _
    simp only [fenceMono_le_counted, fenceMono_le_envGTC, SharedEnv.counted_step, envGTC_step_load] at hst1 hf1 hf2 hf3
    simp [hx0] at hst1
    have hK2 : RK2 rp σ3.1 :=
      RK2.fence (RK2.fence (((vc_r1c tid _ hT) _ σ1.1 hst1.1).2 (by simpa using hcbz)) hf1.1) hf2.1
    simp [hx1, hdd] at hd
    have hK3 : RK3 rp σ4.1 := by
      rcases hd.2 with hst | hst <;> exact (vc_r2c hL tid σ3.1 hK2).2 _ σ4.1 (by simpa using hst)
    simpa [hx2, hd.1, hdg] using (vc_r3c hL tid σ5.1 (RK3.fence hK3 hf3.1) _ rmwOpBits_one).1
  case vc10 =>
    rename_i v σ1 hst1 hcbz σ2 hf1 σ3 hf2 rng dm σ4 hd σ5 hf3 b σ6 hst6 _
    simp only [fenceMono_le_counted, fenceMono_le_envGTC, SharedEnv.counted_step, envGTC_step_load] at hst1 hf1 hf2 hf3
    simp [hx0] at hst1
    have hK2 : RK2 rp σ3.1 :=
      RK2.fence (RK2.fence (((vc_r1c tid _ hT) _ σ1.1 hst1.1).2 (by simpa using hcbz)) hf1.1) hf2.1
    simp [hx1, hdd] at hd
    have hK3 : RK3 rp σ4.1 := by
      rcases hd.2 with hst | hst <;> exact (vc_r2c hL tid σ3.1 hK2).2 _ σ4.1 (by simpa using hst)
    simp [hx2] at hst6
    have h4 : RK4 rp σ6.1 := (vc_r3c hL tid σ5.1 (RK3.fence hK3 hf3.1) _ rmwOpBits_one).2 _ σ6.1 hst6.1
    exact ⟨⟨by simp [hx0], by simp [hx1], by simp [hx2], by simp [hd.1, hdf], by simp [hd.1, hdd],
      by simp [hd.1, hdg]⟩, .inr ⟨rfl, h4⟩⟩
  case vc1 => exact hT

end RelaySwpl

#print axioms relaySwpl_envGTC

end Kraken.Promising.SLR.EnvG.Relay
