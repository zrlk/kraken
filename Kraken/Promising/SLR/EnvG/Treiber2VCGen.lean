/-
Part 6: **the worker of `treiber2_nodes.kl` on
`EnvGCAdj` by `vcgen`**: `worker_envGCAdj`, a `PartialTripleEnv` in the
counted `EW P w` by `cfgEnv_partial` with the VCs of `EnvG/Treiber2VC.lean`.
-/
import Kraken.Promising.SLR.EnvG.Treiber2VC
import Kraken.Promising.SLR.EnvG.Treiber2Smoke
import Kraken.Promising.SLR.EnvG.A64VCGen
import Kraken.AArch64.EnvCfg

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR.EnvG

namespace Kraken.Promising.SLR.EnvG.Treiber2

open Kraken.Promising.SLR.EnvG.Treiber (casOp64)

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- Back at `push` after a failed `casal`: the link's maximal write is at
or below `coh`. -/
theorem Pu2.pu {P : Params} {w : Nat} {y : Val} {σ : State isa} (h : Pu2 P w y σ) : Pu P w σ := by
  obtain ⟨h1, h2, h3, ⟨t, -, hm, -, hc⟩, h5, h6⟩ := h
  exact ⟨h1, h2, h3, fun p hp => Nat.le_trans (hm p hp) hc, h5, h6⟩

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiber2Worker)]

local instance treiber2Worker.envG : CodeEnv := ⟨layout treiber2Worker⟩

/-- The worker's table: `x0 = top`, `x1` the node, `dmem` maps no 8-byte
word (the link load's address is a loaded value). -/
abbrev workTable (P : Params) (w : Nat) :
    Label → MachineData → (SharedEnv.counted (EW P w)).State → Prop :=
  fun lb s σ => s.regs.X0.toBitVec = P.t ∧ s.regs.X1.toBitVec = P.n w ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
    ((lb = "push" ∧ Pu P w σ.1) ∨ (lb = "pop" ∧ Po P w σ.1) ∨
      (lb = "done" ∧ Dn P w s.regs.X10.toBitVec σ.1))

theorem worker_envGCAdj (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) :
    PartialTripleEnv (SharedEnv.counted (EW P w))
      (fun s σ => s.regs.X0.toBitVec = P.t ∧ s.regs.X1.toBitVec = P.n w ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
        Pu P w σ.1)
      treiber2Worker (fun s σ => Dn P w s.regs.X10.toBitVec σ.1) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (workTable P w) (hP := by funext s g; simp [workTable])
  cfg_cases_env [treiber2Worker]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hd8, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj, SharedEnv.counted_step,
    SharedEnv.counted_ok] at *
  all_goals try (simp [hx0, hx1, hd8]; done)
  case vc5 =>
    rename_i s σ0 v σ1 rng hnone hld _
    have hP := vc_push_load _ hT v σ1.1 hld.1
    simp [hx1]
    exact (vc_push_str hL hw _ hP _).1
  case vc7 =>
    rename_i s σ0 v σ1 rng dm σ2 σ3 hld hst hf _
    simp [hx1, hd8] at hst
    obtain ⟨hdm, -, -⟩ := hst
    subst hdm
    simp [hx0, hd8]
  case vc8 =>
    rename_i s σ0 v σ1 rng dm σ2 σ3 hld hst hf _
    have hP := vc_push_load _ hT v σ1.1 hld.1
    simp [hx1, hd8] at hst
    obtain ⟨hdm, hso, -⟩ := hst
    subst hdm
    have hP2 : Pu2 P w (BitVec.setWidth 128 (BitVec.setWidth 64 v)) σ2.1 := by
      rcases hso with h | h <;> exact (vc_push_str hL hw _ hP _).2 _ σ2.1 (by simpa [Params.nd] using h)
    have h := (vc_push_cas hL hw _ (hP2.fence hf.1) (BitVec.setWidth 64 v) (by simp)).1
    simp [hx0, hx1]
    simpa [casOp64, Params.top] using h
  case vc9 =>
    rename_i s σ0 v σ1 rng dm σ2 σ3 old σ4 σ5 hbr σ6 hld hst hf1 hcas hf2 hf3 _
    have hP := vc_push_load _ hT v σ1.1 hld.1
    simp [hx1, hd8] at hst
    obtain ⟨hdm, hso, htk⟩ := hst
    subst hdm
    have hP2 : Pu2 P w (BitVec.setWidth 128 (BitVec.setWidth 64 v)) σ2.1 := by
      rcases hso with h | h <;> exact (vc_push_str hL hw _ hP _).2 _ σ2.1 (by simpa [Params.nd] using h)
    have hc := (vc_push_cas hL hw _ (hP2.fence hf1.1) (BitVec.setWidth 64 v) (by simp)).2 old σ4.1
      (by simpa [hx0, hx1, casOp64, Params.top] using hcas.1)
    simp at hbr
    have hs2 : σ1.2 ≤ σ2.2 := by omega
    rcases hc with ⟨-, hPu⟩ | ⟨heq, -⟩
    · refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8],
        .inl ⟨rfl, Pu.fence (Pu.fence hPu.pu hf2.1) hf3.1⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg
      have h1 := hld.2; have h2 := hcas.2; have h3 := hf1.2; have h4 := hf2.2; have h5 := hf3.2
      simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
      omega
    · exact absurd (by rw [heq]; exact BitVec.sub_self _) hbr
  case vc10 =>
    rename_i s σ0 v σ1 rng dm σ2 σ3 old σ4 σ5 hbr σ6 hld hst hf1 hcas hf2 hf3 _
    have hP := vc_push_load _ hT v σ1.1 hld.1
    simp [hx1, hd8] at hst
    obtain ⟨hdm, hso, -⟩ := hst
    subst hdm
    have hP2 : Pu2 P w (BitVec.setWidth 128 (BitVec.setWidth 64 v)) σ2.1 := by
      rcases hso with h | h <;> exact (vc_push_str hL hw _ hP _).2 _ σ2.1 (by simpa [Params.nd] using h)
    have hc := (vc_push_cas hL hw _ (hP2.fence hf1.1) (BitVec.setWidth 64 v) (by simp)).2 old σ4.1
      (by simpa [hx0, hx1, casOp64, Params.top] using hcas.1)
    simp at hbr
    rcases hc with ⟨hne, -⟩ | ⟨-, hPo⟩
    · exact absurd (TreiberCommon.bv64_eq_of_sub_eq_zero hbr) hne
    · simp [hx0, hx1, hd8]
      exact Po.fence (Po.fence hPo hf2.1) hf3.1
  case vc4 =>
    rename_i s σ0 v σ1 hz σ2 hld hf _
    simp at hz
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8],
      .inr (.inr ⟨rfl, Dn.fence (vc_pop_cbz _ (vc_pop_ldar (xcl := false) _ hT v σ1.1 (by simpa [hx0, Params.top] using hld.1)) hz _) hf.1⟩)⟩, .inl (by decide)⟩
  case vc9 =>
    rename_i s σ0 v σ1 hnz σ2 rng v4 σ3 σ4 hld hf1 hld2 hf2 _
    simp [hd8] at hnz hld2
    have hP1 : Pl P w v σ2.1 := (vc_pop_ldar (xcl := false) _ hT v σ1.1 (by simpa [hx0, Params.top] using hld.1)).fence hf1.1
    obtain ⟨u, h, rfl⟩ := hld2
    have hP3 := vc_pop_ldr _ hP1 u σ3.1 h.1
    have h := (vc_pop_cas hw _ (hP3.fence hf2.1) hnz).1
    simp [hx0]
    simpa [casOp64, Params.top] using h
  case vc10 =>
    rename_i s σ0 v σ1 hnz σ2 rng v4 σ3 σ4 old σ5 σ6 hbr σ7 hld hf1 hld2 hf2 hcas hf3 hf4 _
    simp [hd8] at hnz hld2
    have hP1 : Pl P w v σ2.1 := (vc_pop_ldar (xcl := false) _ hT v σ1.1 (by simpa [hx0, Params.top] using hld.1)).fence hf1.1
    obtain ⟨u, h, rfl⟩ := hld2
    have hP3 := vc_pop_ldr _ hP1 u σ3.1 h.1
    have hc := (vc_pop_cas hw _ (hP3.fence hf2.1) hnz).2 old σ5.1 (by simpa [hx0, casOp64, Params.top] using hcas.1)
    simp at hbr
    rcases hc with ⟨-, hPo⟩ | ⟨heq, -⟩
    · refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8],
        .inr (.inl ⟨rfl, Po.fence (Po.fence hPo hf3.1) hf4.1⟩)⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg
      have h1 := hld.2; have h2 := hcas.2; have h3 := hf1.2; have h4 := hf2.2; have h5 := hf3.2
      have h6 := hf4.2
      simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
      omega
    · exact absurd (by rw [heq]; exact BitVec.sub_self _) hbr
  case vc11 =>
    rename_i s σ0 v σ1 hnz σ2 rng v4 σ3 σ4 old σ5 σ6 hbr σ7 σ8 σ9 hld hf1 hld2 hf2 hcas hf3 hf4 hf5 hf6 _
    simp [hd8] at hnz hld2
    have hP1 : Pl P w v σ2.1 := (vc_pop_ldar (xcl := false) _ hT v σ1.1 (by simpa [hx0, Params.top] using hld.1)).fence hf1.1
    obtain ⟨u, h, rfl⟩ := hld2
    have hP3 := vc_pop_ldr _ hP1 u σ3.1 h.1
    have hc := (vc_pop_cas hw _ (hP3.fence hf2.1) hnz).2 old σ5.1 (by simpa [hx0, casOp64, Params.top] using hcas.1)
    simp at hbr
    rcases hc with ⟨hne, -⟩ | ⟨-, hDn⟩
    · exact absurd (TreiberCommon.bv64_eq_of_sub_eq_zero hbr) hne
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8],
      .inr (.inr ⟨rfl, ?_⟩)⟩, .inl (by decide)⟩
    simp
    exact ((((hDn.fence hf3.1).fence hf4.1).fence hf5.1).fence hf6.1).dn
  case vc1 => exact hT
  all_goals done

end Kraken.Promising.SLR.EnvG.Treiber2
