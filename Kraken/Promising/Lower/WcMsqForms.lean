/-
**The WeakCore MS queue (shape A) on the
semantic machines** (`isaLSE2`, `Arch.armv8`).
`wcMsq(F)_promising_lse2_sem` (`ReachableSem`) and `_semInf`
(`Live.Inf.ReachableSemInf`, the form the lowering consumes) are
`wcMsq(F)_promising_lse2`'s hypotheses and conclusion verbatim, with only the
machine changed, by `Kit.lower_promising_lse2_sem`/`_semInf` with the
`_lse2` proofs' threads, start, `hfree` and final step (factored: `wcTs`, `wcTsF`).
-/
import Kraken.Promising.Lower.WcEnqWhole

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG
open Kraken.Promising.Live.Bridge

namespace Kraken.Promising.Lower.WcMsq

open Kraken.Promising.SLR.EnvG.MsQueue Kraken.Promising.Lower.Kit
open Kraken.Promising.Lower.MsqPilot (StartE)

theorem g2pure {P : Params2} {l : Loc} (hl : ¬ P.IsW l) (v : Val) : Pred.Pure ((ghost2 P).rel l) v := by
  rw [ghost2_rel_ne hl]; exact Pred.emp_pure v

/-- The threads of `wcMsq_promising_lse2` (`P` with `hL`, `ht`). -/
noncomputable def wcTs (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 MsqPilot.progE)]
    [Executable.ValidLayout (l1 progD)] (P : Params2) (hL : QLocs2 P) (ht : P.t = P.h + 8) :
    ∀ tid, tid < 2 → LowerThread Arch.armv8 tid (ghost2 P).rel (WB P)
  | 0, _ => enqT l0 P hL ht (g2pure (not_isW_dat _)) (g2pure (not_isW_dat2 _))
  | 1, _ => deqT l1 P hL
  | _ + 2, hh => absurd hh (by omega)

/-- The threads of `wcMsqF_promising_lse2`. -/
noncomputable def wcTsF (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 progE)]
    [Executable.ValidLayout (l1 progD)] (P : Params2) (hL : QLocs2 P) (ht : P.t = P.h + 8) :
    ∀ tid, tid < 2 → LowerThread Arch.armv8 tid (ghost2 P).rel (WB P)
  | 0, _ => enqTF l0 P hL ht  (g2pure (not_isW_dat _)) (g2pure (not_isW_dat2 _))
  | 1, _ => deqT l1 P hL
  | _ + 2, hh => absurd hh (by omega)

section Start

variable {h t d n1 n2 : BitVec 64} {s0 s1 : isa.State} {initMem : List (Loc × Val)}
  (hi : InitV2 (Config.init [s0, s1] initMem : Config isa).mem ⟨⟨h, t, d, n1⟩, n2⟩)
include hi

theorem wcTs_start (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 MsqPilot.progE)]
    [Executable.ValidLayout (l1 progD)] (hL : QLocs2 ⟨⟨h, t, d, n1⟩, n2⟩) (ht : t = h + 8)
    (h0 : StartE (layout := l0) h n1 n2 s0) (h1 : StartD (layout := l1) h s1) :
    ∀ tid (hh : tid < [s0, s1].length), (wcTs l0 l1 _ hL ht tid hh).Start
      (σInit (Config.init [s0, s1] initMem) (tRes2 (Config.init [s0, s1] initMem : Config isa).mem
        ⟨⟨h, t, d, n1⟩, n2⟩ tid) (ghost2 ⟨⟨h, t, d, n1⟩, n2⟩)) [s0, s1][tid] := by
  intro tid hh
  rcases tid with _ | _ | _
  · obtain ⟨he, hds, hend, hpc, h30, h21, h22, h23, hd8, hd4⟩ := h0
    exact ⟨⟨he, hds, hend, hpc, 0, h30, h22, h23, hd8, hd4⟩, 0, h30, h21, h22, h23, ⟨hd8, hd4⟩, start1_init _ _⟩
  · obtain ⟨he, hds, hend, hpc, h30, h21, hd8, hd4⟩ := h1
    exact ⟨⟨he, hds, hend, hpc, 0, h30, hd8, hd4⟩, 0, h30, h21, ⟨hd8, hd4⟩, comD2_init _ _ hi⟩
  · simp at hh; omega

theorem wcTsF_start (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 progE)]
    [Executable.ValidLayout (l1 progD)] (hL : QLocs2 ⟨⟨h, t, d, n1⟩, n2⟩) (ht : t = h + 8)
    (h0 : StartEF (layout := l0) h n1 n2 s0) (h1 : StartD (layout := l1) h s1) :
    ∀ tid (hh : tid < [s0, s1].length), (wcTsF l0 l1 _ hL ht tid hh).Start
      (σInit (Config.init [s0, s1] initMem) (tRes2 (Config.init [s0, s1] initMem : Config isa).mem
        ⟨⟨h, t, d, n1⟩, n2⟩ tid) (ghost2 ⟨⟨h, t, d, n1⟩, n2⟩)) [s0, s1][tid] := by
  intro tid hh
  rcases tid with _ | _ | _
  · obtain ⟨he, hds, hend, hpc, h30, h21, h22, h23, hd8, hd4⟩ := h0
    exact ⟨⟨he, hds, hend, hpc, 0, h30, h22, h23, hd8, hd4⟩, 0, h30, h21, h22, h23, ⟨hd8, hd4⟩, start1_init _ _⟩
  · obtain ⟨he, hds, hend, hpc, h30, h21, hd8, hd4⟩ := h1
    exact ⟨⟨he, hds, hend, hpc, 0, h30, hd8, hd4⟩, 0, h30, h21, ⟨hd8, hd4⟩, comD2_init _ _ hi⟩
  · simp at hh; omega

end Start

theorem wcTs_free (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 MsqPilot.progE)]
    [Executable.ValidLayout (l1 progD)] (P : Params2) (hL : QLocs2 P) (ht : P.t = P.h + 8) {s0 s1 : isa.State} :
    ∀ tid (hh : tid < [s0, s1].length), ∀ x ∈ (wcTs l0 l1 P hL ht tid hh).p, x.LSE2Free
  | 0, _ => MsqPilot.progE_lse2Free | 1, _ => progD_wcLowerable.lse2Free | _ + 2, hh => absurd hh (by simp)

theorem wcTsF_free (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 progE)]
    [Executable.ValidLayout (l1 progD)] (P : Params2) (hL : QLocs2 P) (ht : P.t = P.h + 8) {s0 s1 : isa.State} :
    ∀ tid (hh : tid < [s0, s1].length), ∀ x ∈ (wcTsF l0 l1 P hL ht tid hh).p, x.LSE2Free
  | 0, _ => progE_wcLowerable.lse2Free | 1, _ => progD_wcLowerable.lse2Free | _ + 2, hh => absurd hh (by simp)

/-- **`wcMsq_promising_lse2`, semantic machine** (`ReachableSem`). -/
theorem wcMsq_promising_lse2_sem {fuel : Nat} (l0 l1 : _root_.Layout)
    [Executable.ValidLayout (l0 MsqPilot.progE)] [Executable.ValidLayout (l1 progD)] (h t d n1 n2 : BitVec 64)
    (ht : t = h + 8) (hht : h ≠ t) (hhd : h ≠ d + 8) (hhn : h ≠ n1 + 8) (hhn2 : h ≠ n2 + 8)
    (htd : t ≠ d + 8) (htn : t ≠ n1 + 8) (htn2 : t ≠ n2 + 8) (hdn : d ≠ n1) (hdn2 : d ≠ n2) (hn12 : n1 ≠ n2)
    (hn1 : n1 ≠ 0) (hn2 : n2 ≠ 0) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartE (layout := l0) h n1 n2 s0) (h1 : StartD (layout := l1) h s1)
    (hi : InitV2 (Config.init [s0, s1] initMem : Config isa).mem ⟨⟨h, t, d, n1⟩, n2⟩)
    {cfg : Config isaLSE2} (hc : ReachableSem Arch.armv8 fuel (Config.init [s0, s1] initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : WcMsqFinal (ofL cfg) :=
  have hL : QLocs2 ⟨⟨h, t, d, n1⟩, n2⟩ := ⟨⟨hht, hhd, hhn, htd, htn, hdn⟩, hhn2, htn2, hdn2, hn12, hn1, hn2⟩
  lower_promising_lse2_sem Arch.armv8 (fun _ hc' => Config.ntFree_armv8K hc') (erase_init2 hL _) rfl
    (wcTs l0 l1 _ hL ht) (wcTs_start hi l0 l1 hL ht h0 h1) (wcTs_free l0 l1 _ hL ht)
    (fun _ hf' _ _ E' hle hsize hB => wcMsq_final_of_hB hL hf' E' hle hsize hB) hc hf

/-- **`wcMsq_promising_lse2`, fuel-free semantic machine** (`ReachableSemInf`). -/
theorem wcMsq_promising_lse2_semInf (l0 l1 : _root_.Layout)
    [Executable.ValidLayout (l0 MsqPilot.progE)] [Executable.ValidLayout (l1 progD)] (h t d n1 n2 : BitVec 64)
    (ht : t = h + 8) (hht : h ≠ t) (hhd : h ≠ d + 8) (hhn : h ≠ n1 + 8) (hhn2 : h ≠ n2 + 8)
    (htd : t ≠ d + 8) (htn : t ≠ n1 + 8) (htn2 : t ≠ n2 + 8) (hdn : d ≠ n1) (hdn2 : d ≠ n2) (hn12 : n1 ≠ n2)
    (hn1 : n1 ≠ 0) (hn2 : n2 ≠ 0) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartE (layout := l0) h n1 n2 s0) (h1 : StartD (layout := l1) h s1)
    (hi : InitV2 (Config.init [s0, s1] initMem : Config isa).mem ⟨⟨h, t, d, n1⟩, n2⟩)
    {cfg : Config isaLSE2}
    (hc : Live.Inf.ReachableSemInf Arch.armv8 (Config.init [s0, s1] initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : WcMsqFinal (ofL cfg) :=
  have hL : QLocs2 ⟨⟨h, t, d, n1⟩, n2⟩ := ⟨⟨hht, hhd, hhn, htd, htn, hdn⟩, hhn2, htn2, hdn2, hn12, hn1, hn2⟩
  lower_promising_lse2_semInf Arch.armv8 (fun _ hc' => Config.ntFree_armv8K hc') (erase_init2 hL _) rfl
    (wcTs l0 l1 _ hL ht) (wcTs_start hi l0 l1 hL ht h0 h1) (wcTs_free l0 l1 _ hL ht)
    (fun _ hf' _ _ E' hle hsize hB => wcMsq_final_of_hB hL hf' E' hle hsize hB) hc hf

/-- **`wcMsqF_promising_lse2`, semantic machine** (`ReachableSem`). -/
theorem wcMsqF_promising_lse2_sem {fuel : Nat} (l0 l1 : _root_.Layout)
    [Executable.ValidLayout (l0 progE)] [Executable.ValidLayout (l1 progD)] (h t d n1 n2 : BitVec 64)
    (ht : t = h + 8) (hht : h ≠ t) (hhd : h ≠ d + 8) (hhn : h ≠ n1 + 8) (hhn2 : h ≠ n2 + 8)
    (htd : t ≠ d + 8) (htn : t ≠ n1 + 8) (htn2 : t ≠ n2 + 8) (hdn : d ≠ n1) (hdn2 : d ≠ n2) (hn12 : n1 ≠ n2)
    (hn1 : n1 ≠ 0) (hn2 : n2 ≠ 0) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartEF (layout := l0) h n1 n2 s0) (h1 : StartD (layout := l1) h s1)
    (hi : InitV2 (Config.init [s0, s1] initMem : Config isa).mem ⟨⟨h, t, d, n1⟩, n2⟩)
    {cfg : Config isaLSE2} (hc : ReachableSem Arch.armv8 fuel (Config.init [s0, s1] initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : WcMsqFinal (ofL cfg) :=
  have hL : QLocs2 ⟨⟨h, t, d, n1⟩, n2⟩ := ⟨⟨hht, hhd, hhn, htd, htn, hdn⟩, hhn2, htn2, hdn2, hn12, hn1, hn2⟩
  lower_promising_lse2_sem Arch.armv8 (fun _ hc' => Config.ntFree_armv8K hc') (erase_init2 hL _) rfl
    (wcTsF l0 l1 _ hL ht) (wcTsF_start hi l0 l1 hL ht h0 h1) (wcTsF_free l0 l1 _ hL ht)
    (fun _ hf' _ _ E' hle hsize hB => wcMsq_final_of_hB hL hf' E' hle hsize hB) hc hf

/-- **`wcMsqF_promising_lse2`, fuel-free semantic machine** (`ReachableSemInf`). -/
theorem wcMsqF_promising_lse2_semInf (l0 l1 : _root_.Layout)
    [Executable.ValidLayout (l0 progE)] [Executable.ValidLayout (l1 progD)] (h t d n1 n2 : BitVec 64)
    (ht : t = h + 8) (hht : h ≠ t) (hhd : h ≠ d + 8) (hhn : h ≠ n1 + 8) (hhn2 : h ≠ n2 + 8)
    (htd : t ≠ d + 8) (htn : t ≠ n1 + 8) (htn2 : t ≠ n2 + 8) (hdn : d ≠ n1) (hdn2 : d ≠ n2) (hn12 : n1 ≠ n2)
    (hn1 : n1 ≠ 0) (hn2 : n2 ≠ 0) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartEF (layout := l0) h n1 n2 s0) (h1 : StartD (layout := l1) h s1)
    (hi : InitV2 (Config.init [s0, s1] initMem : Config isa).mem ⟨⟨h, t, d, n1⟩, n2⟩)
    {cfg : Config isaLSE2}
    (hc : Live.Inf.ReachableSemInf Arch.armv8 (Config.init [s0, s1] initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : WcMsqFinal (ofL cfg) :=
  have hL : QLocs2 ⟨⟨h, t, d, n1⟩, n2⟩ := ⟨⟨hht, hhd, hhn, htd, htn, hdn⟩, hhn2, htn2, hdn2, hn12, hn1, hn2⟩
  lower_promising_lse2_semInf Arch.armv8 (fun _ hc' => Config.ntFree_armv8K hc') (erase_init2 hL _) rfl
    (wcTsF l0 l1 _ hL ht) (wcTsF_start hi l0 l1 hL ht h0 h1) (wcTsF_free l0 l1 _ hL ht)
    (fun _ hf' _ _ E' hle hsize hB => wcMsq_final_of_hB hL hf' E' hle hsize hB) hc hf

end Kraken.Promising.Lower.WcMsq

#print axioms Kraken.Promising.Lower.WcMsq.wcMsq_promising_lse2_sem
#print axioms Kraken.Promising.Lower.WcMsq.wcMsq_promising_lse2_semInf
#print axioms Kraken.Promising.Lower.WcMsq.wcMsqF_promising_lse2_sem
#print axioms Kraken.Promising.Lower.WcMsq.wcMsqF_promising_lse2_semInf
