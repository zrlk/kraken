/-
The counter store cell of the SWP spinlock worker (`str w5, [x1]`, position
12 → 13) for `ThreadRuleR.wp` (`CellWP P A tid 12`, `SLR/SwpRule.lean`).

The store is plain and the counter's release predicate is pure
(`World`), so the shape is `EvTree.eraseWPR_store_pure`:

- the fresh/unpended write `tw` enters the write set of `C`; `WriteOk` puts
  it above `coh C`, hence above the counter's maximal write, so `(k + 1, tw)`
  becomes the maximal write, and below the new `vwOld` (a non-NT store);
- a pending promise fulfilled at `C` contradicts the clean flag: the
  pre-state's erasure at `T = ⊥` counts it as a settled message of `C`, so it
  is in the (unique, `q = 1`) holder's write set, below `coh C`.
-/
import Kraken.Promising.SLR.SwpRule
import Kraken.Promising.SLR.StoreHelpers

namespace Kraken.Promising.SLR.SwpInv

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.AArch64.Examples.InvEnv
open Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SwpTrees

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout swpWorker)]

/-! ## The counter store -/

omit hv in
/-- **`Inv` after a step of thread `tid`** with new memory `m`. -/
theorem inv_withThread_mem {P : Params} {tid : Nat} {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    {t t' : Thread isa} {m : Memory} (hW : World P g) (ht : c.threads[tid]? = some t) {s : State}
    (hst : t'.st = s) (hF : Frame P s) (hL : LockWritesIn P r m) {i : Nat} (hp : AtPos s i)
    (hph : Phase P tid cl i (BitVec.setWidth 32 s.st.1.regs.X2.toBitVec)
      (BitVec.setWidth 32 s.st.1.regs.X5.toBitVec) t'.views r)
    (hpp : PrepaidProm P tid i t' m r := by intro h; exact absurd h (by decide))
    (hla : LkMem P i (BitVec.setWidth 32 s.st.1.regs.X2.toBitVec) t'.views m := by
      exact fun _ _ => ⟨fun h => absurd h (by decide), fun h => by simp at h⟩) :
    Inv P tid cl (c.withThread tid t' m) r g := by
  have hn := lt_size_of_get? ht
  exact ⟨hW, t', by rw [Config.withThread_get? c t' m hn, ite_eq_left rfl], hst ▸ hF, hL, i, hst ▸ hp,
    hst ▸ hph, hpp, by simpa [Config.withThread, hst] using hla⟩

omit layout hv in
/-- The holder's count is below `N`: it is not in its own set. -/
theorem count_lt {P : Params} {tid : Nat} {S : Nat → Bool} {r : Res} (hh : Holding P tid S r) :
    ((List.range P.N).filter S).length < P.N := by
  have := (List.length_filter_lt_length_iff_exists (p := S) (l := List.range P.N)).mpr
    ⟨tid, List.mem_range.mpr hh.2.2.1, by simp [hh.2.1]⟩
  simpa using this

/-- **The counter store** (`str w5, [x1]`, position 12 → 13). -/
theorem wp_str_c {P : Params} {A : Arch} {tid : Nat} (hne : P.c ≠ P.l) (hN32 : P.N < 2 ^ 32)
    (hA : A.storeKind .plain ≠ .nt) : CellWP P A tid 12 := by
  intro cl c r g g₀ rF t tree hW ht hF hL hp hph hg₀ hex E hM hWf hpd
  have hn := lt_size_of_get? ht
  have hnd : t.prom.Nodup := hM.promNodup tid t ht
  have hCL : P.Lk ≠ P.C := fun h => hne (by simp [Params.Lk, Params.C] at h; exact h.symm)
  have hx3 := hF.x3_at hp (by decide)
  rw [exec_str_c t.st (hF.at hp (by decide)) hF.x1 hF.dc] at hex
  cases hex
  simp only [Phase] at hph
  obtain ⟨S, k, hh, hm⟩ := hph
  have hq : (r.wr P.C).q = 1 := hh.1
  have hk : k = ((List.range P.N).filter S).length → k + 1 < 2 ^ 32 := fun hk =>
    Nat.lt_of_le_of_lt (hk ▸ count_lt hh) hN32
  refine EvTree.eraseWPR_store_pure hn (by show 0 < (r.wr P.C).q; rw [hq]; decide) (hW.2.1 _) ?_ ?_
  · -- a pending promise of `C` is fulfilled: impossible under the clean flag
    intro cx' tw hc hev hpd'
    have hget : c.mem.get? tw = some ⟨P.C, BitVec.setWidth 128 (BitVec.setWidth 32 t.st.st.1.regs.X5.toBitVec), tid⟩ ∧ tw ∈ t.prom ∧ cx'.mem = c.mem := by
      rcases hev.cases with ⟨hm', htw, hg⟩ | ⟨-, rfl⟩
      · exact ⟨hg, htw, hm'⟩
      · obtain ⟨⟨w, hw⟩, -⟩ := E.pend _ hpd'
        exact absurd (Memory.last_le_of_get?_eq_some _ hw) (Nat.not_succ_le_self _)
    obtain ⟨hget, htw, hmem⟩ := hget
    have hcoh : t.views.getCoh P.C < tw :=
      Nat.lt_of_le_of_lt (Nat.le_max_right _ _) (writeSuccs_tw hnd hc hev).1.1
    simp only [EvTree.EraseWPR]
    refine ⟨⟨rfl, List.prefix_refl _, fun _ => List.prefix_refl _⟩, fun ts hts hor => ?_,
      fun ts h => (mem_unpend_pend.mp h).1, fun _ h => h, fun w hw => ?_, fun t' ht' _ => ?_⟩
    · refine mem_unpend_pend.mpr ⟨hts, fun he => ?_⟩
      subst he
      rcases hor with h | ⟨i, t'', hi, hti, hpr⟩
      · rw [hev.prom] at h
        exact ((List.Nodup.mem_erase_iff hnd).mp h).1 rfl
      · obtain ⟨w, hw, hwt⟩ := hM.promWf i t'' hti _ hpr
        rw [hget] at hw
        cases hw
        exact hi hwt.symm
    · rw [writtenCx_writeEv hev hw]; show 0 < (r.wr P.C).q; rw [hq]; decide
    · obtain ⟨hpr, hvs⟩ := finishInstr_relKey ht'
      refine inv_withThread_mem (i := 13) hW ht (finishInstr_st ht') (hF.goto rfl rfl rfl)
        (by rw [hmem]; exact hL) rfl ?_ (fun _ h => absurd (hq.symm.trans h) (by decide))
      simp only [Phase]
      refine .inl ⟨S, k, hh, fun ⟨hcl, E'⟩ => ?_⟩
      obtain ⟨hlk, hgood | hsur⟩ := hm hcl
      · exfalso
        obtain ⟨ts, ⟨⟨-, hmax⟩, -⟩, hts, -⟩ := hgood
        have hX : ((total (setRes rF tid r) g c).wr P.C).X (_, tw) :=
          (E'.writes P.C (.inr ⟨tw, _, hget, rfl, .inr hpd'⟩) _).mpr (.inr ⟨_, hget, rfl, rfl, .inr hpd'⟩)
        have hq' : ((setRes rF tid r tid).wr P.C).q = 1 := by rw [setRes_self]; exact hq
        obtain ⟨hth, hsl⟩ := E'.unique_holder hn hq'
        rcases X_total_cases hX with ⟨j, hj, hXj⟩ | ⟨s, hs, hXs⟩
        · by_cases hjt : j = tid
          · subst hjt
            rw [setRes_self] at hXj
            exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_trans (hmax _ hXj) hts) hcoh)
          · exact ((setRes rF tid r j).wr P.C).zero (hth j hj hjt) _ hXj
        · exact (s.res.wr P.C).zero (hsl s hs) _ hXs
      · exact ⟨hlk, .inr hsur⟩
  · -- the write enters `C`'s write set
    intro cx' tw hc hev _
    obtain ⟨hok, hvw⟩ := writeSuccs_tw hnd hc hev
    have hcoh : t.views.getCoh P.C < tw := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hok.1
    rw [storeGhost_plain]
    simp only [EvTree.EraseWPR]
    refine ⟨Ghost.Le.refl g, fun ts h _ => h, fun ts h => h, fun x h => ?_, fun w hw => ?_, fun t' ht' _ => ?_⟩
    · simpa only [mayWrite, Res.addW_q, Res.addW_acq] using h
    · rw [writtenCx_writeEv hev hw]; show 0 < (r.wr P.C).q; rw [hq]; decide
    · obtain ⟨hpr, hvs⟩ := finishInstr_relKey ht'
      have hvw' : t'.views.vwOld = cx'.views.vwOld := by simpa using congrArg Views.vwOld hvs
      refine inv_withThread_mem (i := 13) hW ht (finishInstr_st ht') (hF.goto rfl rfl rfl) ?_ rfl ?_
        (fun _ h => absurd ((Res.addW_q _ _ _ _).symm.trans h) (by rw [hq]; decide))
      · intro p hp'
        rw [Res.addW_wr_ne _ _ hCL] at hp'
        exact Nat.le_trans (hL p hp') hev.last_le
      simp only [Phase]
      refine .inl ⟨S, k, ?_, fun ⟨hcl, _⟩ => ?_⟩
      · simpa only [Holding, Res.addW_q] using hh
      obtain ⟨hlk, hgood | hsur⟩ := hm hcl
      · obtain ⟨ts, ⟨⟨-, hmax⟩, hkS⟩, hts, hx5⟩ := hgood
        refine ⟨by simpa only [Res.addW_q] using hlk, .inl ⟨tw, ⟨?_, fun p hp' => ?_⟩, hkS, ?_⟩⟩
        · refine (Res.addW_X_self _ _ _ _).mpr (.inr ⟨by rw [hq]; decide, ?_⟩)
          rw [hx5, setWidth_ofNat_32 (hk hkS)]
        · rcases (Res.addW_X_self _ _ _ _).mp hp' with hp' | ⟨-, rfl⟩
          · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_trans (hmax _ hp') hts) hcoh)
          · exact Nat.le_refl _
        · rw [hvw', hvw]
          have hnt : (A.storeKind StoreKind.plain == StoreKind.nt) = false := by
            revert hA; cases A.storeKind StoreKind.plain <;> decide
          simp only [hnt, Bool.false_eq_true, ↓reduceIte]
          exact Nat.le_max_right _ _
      · exact ⟨by simpa only [Res.addW_q] using hlk, .inr (by simpa only [Res.addW_q] using hsur)⟩

/-! ## The counter load -/

/-- **The counter load** (`ldr w5, [x1]`, position 10 → 11). -/
theorem wp_ldr_c {P : Params} {A : Arch} {tid : Nat} : CellWP P A tid 10 := by
  intro cl c r g g₀ rF t tree hW ht hF hL hp hph hg₀ hex E hM hWf hpd
  have hx3 := hF.x3_at hp (by decide)
  rw [exec_ldr_c t.st (hF.at hp (by decide)) hF.x1 hF.dc] at hex
  cases hex
  simp only [Phase] at hph
  obtain ⟨S, k, hh, hm⟩ := hph
  refine EvTree.eraseWPR_load fun x hx => ?_
  obtain ⟨hmem, hpr⟩ := readSuccs_memProm A _ hx
  obtain ⟨tr, val, rfl, -, hrd, hwi, hnp⟩ := (mem_readSuccs A).mp hx
  refine WpPostR.noWrite hmem hpr fun t' hst _ hv => ?_
  refine inv_withThread (i := 11) hW ht hst (hF.goto (by simp [Reg64s.setXReg]) (by simp [Reg64s.setXReg]) rfl)
    hL rfl ?_
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
    · simp only [Reg64s.setXReg]
      apply BitVec.eq_of_toNat_eq
      simp
  · exact ⟨hlk, .inr hsur⟩

end Kraken.Promising.SLR.SwpInv
