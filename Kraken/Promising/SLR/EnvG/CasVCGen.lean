/-
**The CAS spinlock worker on `EnvG` by `vcgen`**:
the whole worker `casTtasWorker` as a `PartialTripleEnv` in the counted
`EnvG`, by `cfgEnv_partial` with a five-label table and the VCs of
`EnvG/CasVC.lean`. No open hypotheses: the unclaimed read of the
`casa` is `stepRmwU` (`EnvG/CasStepRmwU.lean`, the claim fix), and the release
`stlr wzr, [x0]` is `vc_stlr` (F1's `Plan.Split`, `EnvG/CasRelease.lean`).
-/
import Kraken.Promising.SLR.EnvG.CasStepRmwU
import Kraken.Promising.SLR.EnvG.A64VCGen
import Kraken.AArch64.EnvCfg

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon

namespace Kraken.Promising.SLR.EnvG.CasSmoke

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The table predicates are monotone under fences -/

theorem Fr.fence {P : Sys} {tid : Nat} {σ σ' : State isa} (h : Fr P tid σ) (hf : FenceLe σ σ') : Fr P tid σ' := by
  unfold Fr; rw [hf.g, hf.r, hf.getFwd]; exact h

theorem H1.fence {P : Sys} {tid : Nat} {σ σ' : State isa} (h : H1 P tid σ) (hf : FenceLe σ σ') : H1 P tid σ' := by
  obtain ⟨hW, S, k, R, hA⟩ := h
  exact ⟨by rw [hf.g]; exact hW, S, k, R, by rw [hf.r]; exact hA.mono hf.vrNew hf.vwNew (Nat.le_of_eq (hf.getCoh _).symm)⟩

theorem H2.fence {P : Sys} {tid : Nat} {x5 : BitVec 32} {σ σ' : State isa} (h : H2 P tid x5 σ)
    (hf : FenceLe σ σ') : H2 P tid x5 σ' := by
  obtain ⟨hW, S, k, R, hA, hc⟩ := h
  exact ⟨by rw [hf.g]; exact hW, S, k, R, by rw [hf.r]; exact hA.mono hf.vrNew hf.vwNew (Nat.le_of_eq (hf.getCoh _).symm),
    by rw [hf.cl, hf.r]; exact hc⟩

theorem H3.fence {P : Sys} {tid : Nat} {x5 : BitVec 32} {σ σ' : State isa} (h : H3 P tid x5 σ)
    (hf : FenceLe σ σ') : H3 P tid x5 σ' := by
  obtain ⟨hW, S, k, R, rr, tw, hA, hr, hvw, hb, hc⟩ := h
  exact ⟨by rw [hf.g]; exact hW, S, k, R, rr, tw, hA.mono hf.vrNew hf.vwNew (Nat.le_of_eq (hf.getCoh _).symm),
    by rw [hf.r]; exact hr, by rw [hf.vwOld]; exact hvw, hb, by rw [hf.cl]; exact hc⟩

theorem QEnd.fence {P : Sys} {σ σ' : State isa} (h : QEnd P σ) (hf : FenceLe σ σ') : QEnd P σ' := by
  unfold QEnd; rw [hf.g, hf.r, hf.cl]; exact h

variable [layout : _root_.Layout] [Executable.ValidLayout (layout casTtasWorker)]

local instance casTtasWorker.envG : CodeEnv := ⟨layout casTtasWorker⟩

/-- The worker's table. -/
abbrev casTable (P : Sys) (tid : Nat) (l c : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (E P tid)).State → Prop :=
  fun lb s σ => s.regs.X0.toBitVec = l ∧ s.regs.X1.toBitVec = c ∧ Mem.loadInt s.dmem l 4 = none ∧
    Mem.loadInt s.dmem c 4 = none ∧
    ((lb = "worker" ∧ Fr P tid σ.1) ∨ ((lb = "try" ∨ lb = "spin") ∧ s.regs.X3.toBitVec.setWidth 32 = 1 ∧ Fr P tid σ.1) ∨
      (lb = "cs" ∧ H1 P tid σ.1) ∨ (lb = "done" ∧ QEnd P σ.1))

/-- **The CAS worker on `EnvG`** (counted, partial): from `Fr`, every run
that reaches the end is in `QEnd`. -/
theorem casWorker_envG (P : Sys) (tid : Nat) (l c : BitVec 64) (hLk : P.Lk = ⟨l, 4⟩) (hC : P.C = ⟨c, 4⟩)
    (hL : SpinLocs P.N P.Lk P.C P.K P.F) (hN0 : 0 < P.N) (htid : tid < P.N) (hN32 : P.N < 2 ^ 32) :
    PartialTripleEnv (SharedEnv.counted (E P tid))
      (fun s σ => s.regs.X0.toBitVec = l ∧ s.regs.X1.toBitVec = c ∧ Mem.loadInt s.dmem l 4 = none ∧
        Mem.loadInt s.dmem c 4 = none ∧ Fr P tid σ.1)
      casTtasWorker (fun _ σ => QEnd P σ.1) (fun _ _ _ => False) := by
  -- make `P.Lk`, `P.C` definitionally the concrete locations (the access
  -- values' types depend on the addresses, so `rw [hLk]` is not available)
  obtain ⟨N, Lk, C, K, F⟩ := P
  simp only at hLk hC
  subst hLk hC
  have hLC : Sys.Lk ⟨N, ⟨l, 4⟩, ⟨c, 4⟩, K, F⟩ ≠ Sys.C ⟨N, ⟨l, 4⟩, ⟨c, 4⟩, K, F⟩ := hL.lk_c
  have hU := stepRmwU Arch.armv8 tid (casPlan ⟨N, ⟨l, 4⟩, ⟨c, 4⟩, K, F⟩ tid)
  apply MachineWP.cfgEnv_partial (casTable ⟨N, ⟨l, 4⟩, ⟨c, 4⟩, K, F⟩ tid l c)
    (hP := by funext s g; simp [casTable])
  cfg_cases_env [casTtasWorker]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hdl, hdc, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envG, SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp [hx0, hx1, hdl, hdc]; done)
  · -- `mov w3, #1`, then `try`
    rename_i hf _
    simp [hx0, hx1, hdl, hdc]
    exact Fr.fence hT hf.1
  · -- the `casa` is permitted
    rename_i hf _
    have hc := (vc_casa hU hN0 _ (Fr.fence hT.2 hf.1)).1
    simpa [hx0, hT.1] using hc
  · -- the `casa` succeeded: `cs`
    rename_i s σ0 σ1 old σ2 hz σ3 hf1 hst hf2 _
    have hc := (vc_casa hU hN0 _ (Fr.fence hT.2 hf1.1)).2 old σ2.1
    simp [hx0, hT.1] at old hz hst
    rcases hc (by simpa using hst.1) with ⟨h0, -⟩ | ⟨-, hH⟩
    · exact absurd hz h0
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hdl], by simp [hdc],
      .inr (.inr (.inl ⟨rfl, H1.fence hH hf2.1⟩))⟩, .inl (by decide)⟩
  · -- the `casa` failed: `spin`
    rename_i s σ0 σ1 old σ2 hz σ3 hf1 hst hf2 _
    have hc := (vc_casa hU hN0 _ (Fr.fence hT.2 hf1.1)).2 old σ2.1
    simp [hx0, hT.1] at old hz hst
    rcases hc (by simpa using hst.1) with ⟨-, hF⟩ | ⟨h0, -⟩
    · simp [hx0, hx1, hdl, hdc, hT.1]
      exact Fr.fence hF hf2.1
    · exact absurd h0 hz
  · -- `ldr w2, [x0]`, `cbnz` taken: `spin` again; the counter moved
    rename_i s σ0 rng val σ1 hnz σ2 hld hf _
    simp [hx0, hdl] at hld
    obtain ⟨v, hst, rfl⟩ := hld
    have hF := vc_ldr_spin σ0.1 hT.2 v σ1.1 (by simpa using hst.1)
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hdl], by simp [hdc],
      .inr (.inl ⟨.inr rfl, by simpa using hT.1, Fr.fence hF hf.1⟩)⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg; omega
  · -- `ldr w2, [x0]`, `cbnz` not taken, `b try`; the counter moved
    rename_i s σ0 rng val σ1 hnz σ2 σ3 hld hf1 hf2 _
    simp [hx0, hdl] at hld
    obtain ⟨v, hst, rfl⟩ := hld
    have hF := vc_ldr_spin σ0.1 hT.2 v σ1.1 (by simpa using hst.1)
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hdl], by simp [hdc],
      .inr (.inl ⟨.inl rfl, by simpa using hT.1, Fr.fence (Fr.fence hF hf1.1) hf2.1⟩)⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg; omega
  · -- `ldr w5, [x1]`, `add`, `str w5, [x1]` is permitted
    rename_i s σ0 r1 val σ1 r2 σ2 r3 _ hld hf _
    simp [hx1, hdc] at hld
    obtain ⟨v, hst, rfl⟩ := hld
    have hH2 := vc_ldr_c hLC σ0.1 hT v σ1.1 (by simpa using hst.1)
    have hs := (vc_str_c hLC _ σ2.1 (H2.fence hH2 hf.1)).1
    simpa [hx1] using hs
  · -- the private memory is untouched by the shared store
    rename_i s σ0 r1 val σ1 r2 σ2 r3 dm σ3 hld hf hst _
    simp [hx1, hdc] at hld
    obtain ⟨v, -, rfl⟩ := hld
    simp [hx1, hdc] at hst
    simp [hst.1, hx0, hdl]
  · -- `stlr wzr, [x0]` is permitted
    rename_i s σ0 r1 val σ1 r2 σ2 r3 dm σ3 hld hf hst _
    simp [hx1, hdc] at hld
    obtain ⟨v, hl, rfl⟩ := hld
    have hH2 := vc_ldr_c hLC σ0.1 hT v σ1.1 (by simpa using hl.1)
    have hs := (vc_str_c hLC _ σ2.1 (H2.fence hH2 hf.1)).2
    simp [hx1, hdc] at hst
    have hH3 : H3 ⟨N, ⟨l, 4⟩, ⟨c, 4⟩, K, F⟩ tid (BitVec.setWidth 32 v + 1) σ3.1 := by
      rcases hst.2.1 with h | h <;> exact hs _ _ (by simpa using h)
    have hr := (vc_stlr hL hN0 htid hN32 _ σ3.1 hH3).1
    simpa [hx0, hst.1, hdl] using hr
  · -- after the release: `done`
    rename_i s σ0 r1 val σ1 r2 σ2 r3 dm σ3 b σ4 σ5 hld hf1 hst hst' hf _
    simp [hx1, hdc] at hld
    obtain ⟨v, hl, rfl⟩ := hld
    have hH2 := vc_ldr_c hLC σ0.1 hT v σ1.1 (by simpa using hl.1)
    have hs := (vc_str_c hLC _ σ2.1 (H2.fence hH2 hf1.1)).2
    simp [hx1, hdc] at hst
    have hH3 : H3 ⟨N, ⟨l, 4⟩, ⟨c, 4⟩, K, F⟩ tid (BitVec.setWidth 32 v + 1) σ3.1 := by
      rcases hst.2.1 with h | h <;> exact hs _ _ (by simpa using h)
    have hr := (vc_stlr hL hN0 htid hN32 _ σ3.1 hH3).2 b σ4.1
    have hQ := QEnd.fence (hr (by simpa [hx0, hst.1, hdl] using hst'.1)) hf.1
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hst.1, hdl], by simp [hst.1, hdc],
      .inr (.inr (.inr ⟨rfl, hQ⟩))⟩, .inl (by decide)⟩
  · exact hT

end Kraken.Promising.SLR.EnvG.CasSmoke
