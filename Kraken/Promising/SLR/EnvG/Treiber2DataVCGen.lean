/-
Part 11: **the worker of `treiber2.kl`** (with the
data word): the program and its static checks, `workerD_envGCAdj` by
`vcgen` (VCs of `EnvG/Treiber2VC.lean` and `EnvG/Treiber2DataVC.lean`).
Its purity is in `EnvG/Treiber2DataRelPure.lean`.
-/
import Kraken.Promising.SLR.EnvG.Treiber2DataVC
import Kraken.Promising.SLR.EnvG.Treiber2VCGen
import Kraken.Promising.SLR.EnvG.Treiber2RelPure

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.SLR.EnvG.Treiber2

open Kraken.Promising.SLR.EnvG.Treiber (casOp64)

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- **The worker** of `treiber2.kl` (`x0 = top`, `x1` the node, `w9` its
data): write the data word, then `treiber2Worker`'s push and pop, the popped
node's data word in `w11`. -/
def treiber2DWorker : Program := parseAArch64("
worker:
    str w9, [x1]
push:
    ldar x2, [x0]
    str x2, [x1, #8]
    mov x3, x2
    casal x3, x1, [x0]
    cmp x3, x2
    b.ne push
pop:
    ldar x2, [x0]
    cbz x2, done
    ldr x4, [x2, #8]
    mov x3, x2
    casal x3, x4, [x0]
    cmp x3, x2
    b.ne pop
    mov x10, x2
    ldr w11, [x2]
    b done
done:
")

/-- info: 21 -/
#guard_msgs in
#eval treiber2DWorker.length

section Static

variable [layout : _root_.Layout]

theorem treiber2DWorker_rmwLive : (layout treiber2DWorker).rmwLive = true := by
  rw [Layout.apply_rmwLive]; decide

theorem treiber2DWorker_phase1F [Executable.ValidLayout (layout treiber2DWorker)] :
    Phase1TreeF (layout treiber2DWorker) :=
  phase1TreeF_of_dirs (by dirs_phase1F treiber2DWorker)

theorem treiber2DWorker_noFault : DirsNoFault (layout treiber2DWorker) := by dirs_no_fault' treiber2DWorker

end Static

section Worker

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiber2DWorker)]

local instance treiber2DWorker.envG : CodeEnv := ⟨layout treiber2DWorker⟩

/-- The worker's table: `x0 = top`, `x1` the node, `w9` its data (at
`worker`), `dmem` maps no 8- or 4-byte word. -/
abbrev workDTable (P : Params) (w : Nat) (d9 : BitVec 32) :
    Label → MachineData → (SharedEnv.counted (EW P w)).State → Prop :=
  fun lb s σ => s.regs.X0.toBitVec = P.t ∧ s.regs.X1.toBitVec = P.n w ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
    (∀ a, Mem.loadInt s.dmem a 4 = none) ∧
    ((lb = "worker" ∧ s.regs.X9.toBitVec.setWidth 32 = d9 ∧ Pu0 P w σ.1) ∨ (lb = "push" ∧ Pu P w σ.1) ∨
      (lb = "pop" ∧ Po P w σ.1) ∨
      (lb = "done" ∧ DnD P w s.regs.X10.toBitVec s.regs.X11.toBitVec σ.1))

theorem workerD_envGCAdj (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (d9 : BitVec 32)
    (hD : ∀ d : Val, BitVec.setWidth 32 d = d9 → P.D w d) :
    PartialTripleEnv (SharedEnv.counted (EW P w))
      (fun s σ => s.regs.X0.toBitVec = P.t ∧ s.regs.X1.toBitVec = P.n w ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
        (∀ a, Mem.loadInt s.dmem a 4 = none) ∧ s.regs.X9.toBitVec.setWidth 32 = d9 ∧ Pu0 P w σ.1)
      treiber2DWorker (fun s σ => DnD P w s.regs.X10.toBitVec s.regs.X11.toBitVec σ.1) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (workDTable P w d9) (hP := by funext s g; simp [workDTable])
  cfg_cases_env [treiber2DWorker]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hd8, hd4, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj, SharedEnv.counted_step,
    SharedEnv.counted_ok] at *
  all_goals try (simp [hx0, hx1, hd8, hd4]; done)
  case vc2 =>
    have h := (vc_data_str _ hT.2 (BitVec.setWidth 128 d9) (hD _ (by simp))).1
    simp [hx1, hT.1]
    simpa [Params.dd] using h
  case vc3 =>
    rename_i s σ0 rng dm σ1 hst _
    simp [hx1, hd4] at hst
    obtain ⟨hdm, hso, -⟩ := hst
    subst hdm
    have hP : Pu P w σ1.1 := by
      rcases hso with h | h <;>
        exact (vc_data_str _ hT.2 (BitVec.setWidth 128 d9) (hD _ (by simp))).2 _ σ1.1
          (by simpa [Params.dd, hT.1] using h)
    simp (config := { decide := true }) [hx0, hx1, hd8, hd4]
    exact hP
  case vc5 =>
    rename_i s σ0 v σ1 rng hnone hld _
    have hP := vc_push_load _ hT v σ1.1 hld.1
    simp [hx1]
    exact (vc_push_str hL hw _ hP _).1
  case vc7 =>
    rename_i s σ0 v σ1 rng dm σ2 σ3 hld hst hf _
    simp [hx1, hd8, hd4] at hst
    obtain ⟨hdm, -, -⟩ := hst
    subst hdm
    simp [hx0, hd8, hd4]
  case vc8 =>
    rename_i s σ0 v σ1 rng dm σ2 σ3 hld hst hf _
    have hP := vc_push_load _ hT v σ1.1 hld.1
    simp [hx1, hd8, hd4] at hst
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
    simp [hx1, hd8, hd4] at hst
    obtain ⟨hdm, hso, htk⟩ := hst
    subst hdm
    have hP2 : Pu2 P w (BitVec.setWidth 128 (BitVec.setWidth 64 v)) σ2.1 := by
      rcases hso with h | h <;> exact (vc_push_str hL hw _ hP _).2 _ σ2.1 (by simpa [Params.nd] using h)
    have hc := (vc_push_cas hL hw _ (hP2.fence hf1.1) (BitVec.setWidth 64 v) (by simp)).2 old σ4.1
      (by simpa [hx0, hx1, casOp64, Params.top] using hcas.1)
    simp at hbr
    have hs2 : σ1.2 ≤ σ2.2 := by omega
    rcases hc with ⟨-, hPu⟩ | ⟨heq, -⟩
    · refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], by simp [hd4],
        .inr (.inl ⟨rfl, Pu.fence (Pu.fence hPu.pu hf2.1) hf3.1⟩)⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg
      have h1 := hld.2; have h2 := hcas.2; have h3 := hf1.2; have h4 := hf2.2; have h5 := hf3.2
      simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
      omega
    · exact absurd (by rw [heq]; exact BitVec.sub_self _) hbr
  case vc10 =>
    rename_i s σ0 v σ1 rng dm σ2 σ3 old σ4 σ5 hbr σ6 hld hst hf1 hcas hf2 hf3 _
    have hP := vc_push_load _ hT v σ1.1 hld.1
    simp [hx1, hd8, hd4] at hst
    obtain ⟨hdm, hso, -⟩ := hst
    subst hdm
    have hP2 : Pu2 P w (BitVec.setWidth 128 (BitVec.setWidth 64 v)) σ2.1 := by
      rcases hso with h | h <;> exact (vc_push_str hL hw _ hP _).2 _ σ2.1 (by simpa [Params.nd] using h)
    have hc := (vc_push_cas hL hw _ (hP2.fence hf1.1) (BitVec.setWidth 64 v) (by simp)).2 old σ4.1
      (by simpa [hx0, hx1, casOp64, Params.top] using hcas.1)
    simp at hbr
    rcases hc with ⟨hne, -⟩ | ⟨-, hPo⟩
    · exact absurd (TreiberCommon.bv64_eq_of_sub_eq_zero hbr) hne
    · simp [hx0, hx1, hd8, hd4]
      exact Po.fence (Po.fence hPo hf2.1) hf3.1
  case vc4 =>
    rename_i s σ0 v σ1 hz σ2 hld hf _
    simp at hz
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], by simp [hd4],
      .inr (.inr (.inr ⟨rfl, DnD.fence (vc_pop_cbz_d _ (vc_pop_ldar (xcl := false) _ hT v σ1.1 (by simpa [hx0, Params.top] using hld.1)) hz _ _) hf.1⟩))⟩, .inl (by decide)⟩
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
    · refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], by simp [hd4],
        .inr (.inr (.inl ⟨rfl, Po.fence (Po.fence hPo hf3.1) hf4.1⟩))⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg
      have h1 := hld.2; have h2 := hcas.2; have h3 := hf1.2; have h4 := hf2.2; have h5 := hf3.2
      have h6 := hf4.2
      simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
      omega
    · exact absurd (by rw [heq]; exact BitVec.sub_self _) hbr
  case vc13 =>
    rename_i s σ0 v σ1 hnz σ2 rng v4 σ3 σ4 old σ5 σ6 hbr σ7 σ8 rng2 v11 σ9 σ10 hld hf1 hld2 hf2 hcas hf3 hf4 hf5
      hld3 hf6 _
    simp [hd8] at hnz hld2
    simp [hd4] at hld3
    have hP1 : Pl P w v σ2.1 := (vc_pop_ldar (xcl := false) _ hT v σ1.1 (by simpa [hx0, Params.top] using hld.1)).fence hf1.1
    obtain ⟨u, h, rfl⟩ := hld2
    have hP3 := vc_pop_ldr _ hP1 u σ3.1 h.1
    have hc := (vc_pop_cas hw _ (hP3.fence hf2.1) hnz).2 old σ5.1 (by simpa [hx0, casOp64, Params.top] using hcas.1)
    simp at hbr
    rcases hc with ⟨hne, -⟩ | ⟨-, hDn⟩
    · exact absurd (TreiberCommon.bv64_eq_of_sub_eq_zero hbr) hne
    have hD8 := ((hDn.fence hf3.1).fence hf4.1).fence hf5.1
    obtain ⟨u', h3, rfl⟩ := hld3
    have hfin := (vc_ldr_data _ hD8 u' σ9.1 h3.1).fence hf6.1
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], by simp [hd4],
      .inr (.inr (.inr ⟨rfl, ?_⟩))⟩, .inl (by decide)⟩
    simp
    exact hfin
  case vc1 => exact hT
  all_goals done

end Worker

end Kraken.Promising.SLR.EnvG.Treiber2
