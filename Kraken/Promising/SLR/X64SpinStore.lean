/-
The counter cells of the x64 spinlock worker for `ThreadRuleR.wp`
(`CellWP`, `SLR/X64SpinRule.lean`): the x64 twins of `wp_ldr_c` and
`wp_str_c` (`SLR/SwpStore.lean`), with the ISA-neutral helpers of
`SLR/StoreHelpers.lean`.

- `wp_load_counter` (`movl (%rsi),%ecx`, position 8 → 9): under the clean
  flag the thread holds all of `C` with its maximal write below the read
  bound, so it reads that write (`read_max`): `%ecx = k`, and the write is
  below the new `coh C`.
-/
import Kraken.Promising.SLR.X64SpinRule
import Kraken.Promising.SLR.StoreHelpers

namespace Kraken.Promising.SLR.X64SpinInv

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SpinCommon
open Kraken.Promising.SLR.X64SpinTrees

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout spinWorker)]

/-- **The counter load** (`movl (%rsi),%ecx`, position 8 → 9). -/
theorem wp_load_counter {P : Params} {A : Arch} {tid : Nat} : CellWP P A tid 8 := by
  intro cl c r g g₀ rF t tree hW ht hF hL hp hph hg₀ hex E hM hWf hpd
  rw [exec_load_counter t.st (hF.at hp (by decide)) hF.rsi hF.dc] at hex
  cases hex
  simp only [Phase, Held] at hph
  obtain ⟨S, k, hh, hm⟩ := hph
  refine EvTree.eraseWPR_load fun x hx => ?_
  obtain ⟨hmem, hpr⟩ := readSuccs_memProm A _ hx
  obtain ⟨tr, val, rfl, -, hrd, hwi, hnp⟩ := (mem_readSuccs A).mp hx
  refine WpPostR.noWrite hmem hpr fun t' hst _ hv => ?_
  refine inv_withThread (hW := hW) (i := 9) ht hst (hF.goto (by simp) (by simp) rfl) hL rfl ?_
  simp only [Phase]
  refine ⟨S, k, hh, fun ⟨hcl, E'⟩ => ?_⟩
  obtain ⟨hlk, hgood | hsur⟩ := hm hcl
  · obtain ⟨ts, ⟨⟨hX, hmax⟩, hkS⟩, hts⟩ := hgood
    have hvr : t.views.vrNew ≤ readPre A (instrViews t (isa.deps t.st)) (ctx₀ t tid c.mem) .plain :=
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    obtain ⟨rfl, rfl⟩ := read_max E' ht hh.1 hX hmax hrd hnp hwi
      (Nat.le_trans hts (Nat.le_trans hvr (Nat.le_max_left _ _)))
    refine ⟨hlk, .inl ⟨tr, ⟨⟨hX, hmax⟩, hkS⟩, ?_, ?_⟩⟩
    · have hc : t'.views.coh = (readNext A (instrViews t (isa.deps t.st)) (ctx₀ t tid c.mem) .plain false P.C
          false tr (BitVec.ofNat 128 k)).views.coh := by simpa using congrArg Views.coh hv
      have : t'.views.getCoh P.C = Views.getCoh (readNext A (instrViews t (isa.deps t.st)) (ctx₀ t tid c.mem)
          .plain false P.C false tr (BitVec.ofNat 128 k)).views P.C := by unfold Views.getCoh; rw [hc]
      rw [this]
      simp only [readNext]
      refine Nat.le_trans ?_ (Nat.le_of_eq (Views.getCoh_setCoh t.views P.C P.C _).symm)
      simp only [↓reduceIte]
      exact Nat.le_trans hts (Nat.le_trans hvr (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)))
    · simp only [ecxOf, get_set_low_rcx]
      apply BitVec.eq_of_toNat_eq
      simp
  · exact ⟨hlk, .inr hsur⟩

end Kraken.Promising.SLR.X64SpinInv
