/-
**A kit instance on `isaLSE2` with no clone.**

`msqPilot_promising_lse2_viaKit` is the lowering kit's `msqPilot_promising_viaKit`
(`Lower/KitMsq.lean`) with `lower_promising` replaced by
`lower_promising_lse2` (`Lower/KitLSE2.lean`): the same threads `enqT`/
`deqT` and start discharge, `hH` along `ReachableK` (`ntFree_armv8K`),
`hfree` from `progE_lse2Free`/`progD_lse2Free`, and the final reading for
every final configuration. No `#chaink_clone'`: this is the per-program cost
of the `isaLSE2` headline for a kit instance. The statement is
`msqPilot_promising_lse2`'s (`Lower/MsqPilotLSE2.lean`, by the clone route),
verbatim (checked below by `rfl`).
-/
import Kraken.Promising.Lower.KitMsq
import Kraken.Promising.Lower.KitLSE2
import Kraken.Promising.Lower.MsqPilotLSE2

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG
open Kraken.Promising.Lower.Kit Kraken.Promising.Lower.MsqPilot

namespace Kraken.Promising.Lower.KitMsq

open Kraken.Promising.SLR.EnvG.MsQueue

/-- **`msqPilot_promising` on `isaLSE2` through the kit** (executable
machine; same statement as `msqPilot_promising_lse2`). -/
theorem msqPilot_promising_lse2_viaKit {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 progE)]
    [Executable.ValidLayout (l1 progD)] (h t d n1 n2 : BitVec 64) (ht : t = h + 8) (hht : h ≠ t)
    (hhd : h ≠ d + 8) (hhn : h ≠ n1 + 8) (hhn2 : h ≠ n2 + 8) (htd : t ≠ d + 8) (htn : t ≠ n1 + 8)
    (htn2 : t ≠ n2 + 8) (hdn : d ≠ n1) (hdn2 : d ≠ n2) (hn12 : n1 ≠ n2) (hn1 : n1 ≠ 0) (hn2 : n2 ≠ 0)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : StartE (layout := l0) h n1 n2 s0)
    (h1 : StartD (layout := l1) h s1)
    (hi : InitV2 (Config.init [s0, s1] initMem : Config isa).mem ⟨⟨h, t, d, n1⟩, n2⟩)
    {cfg : Config isaLSE2} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : MsQueue2Final (ofL cfg) := by
  have hL : QLocs2 ⟨⟨h, t, d, n1⟩, n2⟩ := ⟨⟨hht, hhd, hhn, htd, htn, hdn⟩, hhn2, htn2, hdn2, hn12, hn1, hn2⟩
  have hr : ∀ l, ¬ Params2.IsW ⟨⟨h, t, d, n1⟩, n2⟩ l → ∀ v, Pred.Pure ((ghost2 ⟨⟨h, t, d, n1⟩, n2⟩).rel l) v :=
    fun l hl v => by rw [ghost2_rel_ne hl]; exact Pred.emp_pure v
  refine lower_promising_lse2 Arch.armv8 (fun _ hc' => Config.ntFree_armv8K hc') (erase_init2 hL _) rfl
    (fun tid hh => match tid, hh with
      | 0, _ => enqT l0 _ hL ht (hr _ (not_isW_dat _)) (hr _ (not_isW_dat2 _))
      | 1, _ => deqT l1 _ hL ht
      | _ + 2, hh => absurd hh (by simp))
    (fun tid hh => ?_) (fun tid hh => ?_)
    (fun _ hf' rF' g' E' hle hsize hB => msqueue2_final_of_hB hL hf' E' hle hsize hB) hc hf
  · rcases tid with _ | _ | _
    · obtain ⟨he, hds, hend, hpc, h30, h21, h22, h23, hd8, hd4⟩ := h0
      exact ⟨⟨he, hds, hend, hpc, 0, h30, h22, h23, hd8, hd4⟩, 0, h30, h21, h22, h23, ⟨hd8, hd4⟩, start1_init _ _⟩
    · obtain ⟨he, hds, hend, hpc, h30, h21, hd8, hd4⟩ := h1
      exact ⟨⟨he, hds, hend, hpc, 0, h30, hd8, hd4⟩, 0, h30, h21, ⟨hd8, hd4⟩, comD2_init _ _ hi⟩
    · simp at hh; omega
  · rcases tid with _ | _ | _
    · exact progE_lse2Free
    · exact progD_lse2Free
    · simp at hh; omega

/-- The statement is `msqPilot_promising_lse2`'s, verbatim. -/
example : @msqPilot_promising_lse2_viaKit = @MsqPilot.msqPilot_promising_lse2 := rfl

end Kraken.Promising.Lower.KitMsq

#print axioms Kraken.Promising.Lower.KitMsq.msqPilot_promising_lse2_viaKit
