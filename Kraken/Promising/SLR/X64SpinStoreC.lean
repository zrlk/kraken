/-
The counter store cell of the x64 spinlock worker (`movl %ecx,(%rsi)`,
position 10 → 11), `HardCellsX.strC : CellWPX P A tid 10`
(`SLR/X64SpinRule.lean`): the x64 twin of `wp_str_c`
(`SLR/SwpStore.lean`) in `ThreadRuleRX` form.

Under TSO the store is a release, so it may have been promised and prepaid
(`Phase 10`'s third clean alternative: the counter's maximal write is the
promised `(k + 1, ts)` above `coh C`, an own message by `PrepaidProm`). The
counter's release predicate is pure (`World`), so the write attaches no
slots either way.

- **No own pending promise** (`wp_store_counter_np`, lifted by `x64_lift`):
  `EvTree.eraseWPR_store_pure`. A pending write is impossible; the
  non-pending write enters `C`'s write set above `coh C`, as in `wp_str_c`.
  The prepaid alternative cannot hold: its write would be an outstanding own
  message (`alt3_own`: erasure, `PrepaidProm`, `ownCoh`), counted as settled
  only if pending.
- **An own pending promise `ts₀`** (`OwnPend`: the message `⟨C, ecx, tid⟩`,
  the only pending one, every other own promise of `C` above it):
  `EvTree.eraseWPRD_store_pendOrDead`. Fulfilling `ts₀` reaches `Phase 11`:
  the first clean alternative contradicts the pending write's place in the
  holder's write set (below `coh C`), the prepaid one has its write at `ts₀`
  (uniqueness), below the new `vwOld`. Every other write is fresh or fulfils
  a promise above `ts₀`, raising `coh C` over the outstanding `ts₀`
  (`Ctx.Overtaken`).

The lift is `X64SpinInv.x64_lift` (`SLR/X64SpinLift.lean`) and the
`Inv` re-packing `inv_withThread_mem` comes from `SLR/X64SpinUnlock.lean`.
-/
import Kraken.Promising.SLR.X64SpinUnlock
import Kraken.Promising.SLR.StoreHelpers
import Kraken.Promising.SLR.ReleaseStore

namespace Kraken.Promising.SLR.X64SpinInv

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SpinCommon
open Kraken.Promising.SLR.X64SpinTrees

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout spinWorker)]

/-! ## Helpers -/

omit layout hv in
/-- `PrepaidProm` at position 11 while holding all of `C`. -/
theorem prepaidProm_11 {P : Params} {tid : Nat} {cl : Prop} {t : Thread isa} {m : Memory} {r : Res}
    (hq : (r.wr P.C).q = 1) : PrepaidProm P tid cl 11 t m r :=
  ⟨fun h => absurd h (by decide), fun _ h => absurd (hq.symm.trans h) (by decide)⟩

omit layout hv in
/-- The holder's count is below `N`: it is not in its own set. -/
theorem count_lt {P : Sys} {tid : Nat} {S : Nat → Bool} {r : Res} (hh : Holding P tid S r) :
    ((List.range P.N).filter S).length < P.N := by
  have := (List.length_filter_lt_length_iff_exists (p := S) (l := List.range P.N)).mpr
    ⟨tid, List.mem_range.mpr hh.2.2.1, by simp [hh.2.1]⟩
  simpa using this

omit layout hv in
/-- **The prepaid counter write is an own pending promise**: a write of `C`
in the (sole) holder's write set above its `coh C` that is a message of the
thread (`PrepaidProm`) is an outstanding own promise (`ownCoh`), settled in
the clean erasure, hence pending. -/
theorem alt3_own {P : Params} {tid : Nat} {rF : Nat → Res} {g : Ghost} {c : Config isa} {t : Thread isa}
    {r : Res} {v : Val} {ts : Time}
    (E : Erase (setRes rF tid r) g (fun _ => False) c) (hM : c.MachInv) (ht : c.threads[tid]? = some t)
    (hq : (r.wr P.C).q = 1) (hX : (r.wr P.C).X (v, ts)) (hcoh : t.views.getCoh P.C < ts)
    (hown : ∃ w, c.mem.get? ts = some w ∧ w.tid = tid) : ts ∈ t.prom ∧ ts ∈ g.pend := by
  have hn := lt_size_of_get? ht
  have hq' : ((setRes rF tid r tid).wr P.C).q = 1 := by rw [setRes_self]; exact hq
  obtain ⟨d, hd⟩ := sub_total_thread (rF := setRes rF tid r) (g := g) hn
  have hXt : ((total (setRes rF tid r) g c).wr P.C).X (v, ts) := by
    rw [hd]; exact Or.inl (by rw [setRes_self]; exact hX)
  have htr : Tracked c g (total (setRes rF tid r) g c) P.C := .inl (by
    rw [hd]; show 0 < ((setRes rF tid r tid).wr P.C).q + (d.wr P.C).q
    rw [hq']; have := (d.wr P.C).nonneg; grind)
  rcases (E.writes P.C htr _).mp hXt with ⟨h0, -⟩ | ⟨w, hw, hl, -, hs⟩
  · simp only at h0; rw [h0] at hcoh; exact absurd hcoh (Nat.not_lt_zero _)
  · have hw : c.mem.get? ts = some w := hw
    obtain ⟨w', hw', hwt⟩ := hown
    rw [hw] at hw'; cases hw'
    have hin : ts ∈ t.prom := by
      refine Classical.byContradiction fun hnin => ?_
      have := hM.ownCoh tid t ht ts w hw hwt hnin
      rw [hl] at this
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hcoh this)
    exact ⟨hin, hs.resolve_left fun h => h ⟨tid, t, ht, hin⟩⟩

omit layout hv in
/-- **A pending write of `C` is in the holder's write set** (clean erasure):
so it is at or below the counter's maximal write. -/
theorem pend_le_max {P : Params} {tid : Nat} {rF : Nat → Res} {g : Ghost} {c : Config isa} {t : Thread isa}
    {r : Res} {v : Val} {ts tw : Time}
    (E : Erase (setRes rF tid r) g (fun _ => False) c) (ht : c.threads[tid]? = some t)
    (hq : (r.wr P.C).q = 1) (hmax : ∀ p, (r.wr P.C).X p → p.2 ≤ ts)
    (hget : c.mem.get? tw = some ⟨P.C, v, tid⟩) (hpd : tw ∈ g.pend) : tw ≤ ts := by
  have hn := lt_size_of_get? ht
  have hX : ((total (setRes rF tid r) g c).wr P.C).X (v, tw) :=
    (E.writes P.C (.inr ⟨tw, _, hget, rfl, .inr hpd⟩) _).mpr (.inr ⟨_, hget, rfl, rfl, .inr hpd⟩)
  have hq' : ((setRes rF tid r tid).wr P.C).q = 1 := by rw [setRes_self]; exact hq
  obtain ⟨hth, hsl⟩ := E.unique_holder hn hq'
  rcases X_total_cases hX with ⟨j, hj, hXj⟩ | ⟨s, hs, hXs⟩
  · by_cases hjt : j = tid
    · subst hjt
      rw [setRes_self] at hXj
      exact hmax _ hXj
    · exact absurd hXj (((setRes rF tid r j).wr P.C).zero (hth j hj hjt) _)
  · exact absurd hXs ((s.res.wr P.C).zero (hsl s hs) _)

/-! ## The counter store -/

omit hv in
/-- **The counter store without an own pending promise**, as an `EraseWPR`
proof into `WpPostR Inv` (lifted by `x64_lift`). -/
theorem wp_store_counter_np {P : Params} {A : Arch} {tid : Nat} (hne : P.c ≠ P.l) (hN32 : P.N < 2 ^ 32)
    (hA : A.storeKind .plain ≠ .nt) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost} (rF : Nat → Res)
    (t : Thread isa) (hW : World P.sys g) (ht : c.threads[tid]? = some t) (hF : Frame P t.st)
    (hL : LockWritesIn P.sys r c.mem)
    (hph : Phase P tid cl 10 (eaxOf t.st) (ecxOf t.st) t.st.st.1.status.zf t.views r)
    (hpp : PrepaidProm P tid cl 10 t c.mem r)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hM : c.MachInv) (hnp : ∀ ts ∈ t.prom, ts ∉ g.pend) :
    (EvTree.store .plain false P.C (BitVec.setWidth 128 (ecxOf t.st))
      fun _ => .done (goto t.st t.st.st.1 ((layout spinWorker).addrOf 11))).EraseWPR
      A tid (instrViews t (isa.deps t.st)) rF (fun _ => True) c t
      (WpPostR (Inv P tid) (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g
      (ctx₀ t tid c.mem) := by
  have hn := lt_size_of_get? ht
  have hnd : t.prom.Nodup := hM.promNodup tid t ht
  have hCL : P.Lk ≠ P.C := fun h => hne (by simp [Params.Lk, Params.C] at h; exact h.symm)
  simp only [Phase] at hph
  obtain ⟨S, k, hh, hm⟩ := hph
  have hq : (r.wr P.C).q = 1 := hh.1
  have hk : k = ((List.range P.N).filter S).length → k + 1 < 2 ^ 32 := fun hk =>
    Nat.lt_of_le_of_lt (hk ▸ count_lt hh) hN32
  refine EvTree.eraseWPR_store_pure hn (by show 0 < (r.wr P.C).q; rw [hq]; decide) (hW.2.1 _) ?_ ?_
  · -- a pending write: neither an own (unpended) promise nor fresh
    intro cx' tw _ hev hpd
    exfalso
    rcases hev.cases with ⟨-, htw, -⟩ | ⟨-, rfl⟩
    · exact hnp tw htw hpd
    · exact Nat.not_succ_le_self _ (E.pend_le hpd)
  · intro cx' tw hc hev _
    obtain ⟨hok, hvw⟩ := writeSuccs_tw hnd hc hev
    have hcoh : t.views.getCoh P.C < tw := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hok.1
    rw [storeGhost_plain]
    simp only [EvTree.EraseWPR]
    refine ⟨Ghost.Le.refl g, fun ts h _ => h, fun ts h => h, fun x h => ?_, fun w hw => ?_, fun t' ht' _ => ?_⟩
    · simpa only [mayWrite, Res.addW_q, Res.addW_acq] using h
    · rw [writtenCx_writeEv hev hw]; show 0 < (r.wr P.C).q; rw [hq]; decide
    · obtain ⟨hpr, hvs⟩ := finishInstr_relKey ht'
      have hvw' : t'.views.vwOld = cx'.views.vwOld := by simpa using congrArg Views.vwOld hvs
      refine inv_withThread_mem (i := 11) hW ht (finishInstr_st ht') (hF.goto rfl rfl rfl) ?_ rfl ?_
        (prepaidProm_11 (by rw [Res.addW_q]; exact hq))
      · intro p hp'
        rw [Res.addW_wr_ne _ _ hCL] at hp'
        exact Nat.le_trans (hL p hp') hev.last_le
      simp only [Phase]
      refine .inl ⟨S, k, ?_, fun ⟨hcl, E'⟩ => ?_⟩
      · simpa only [Holding, Res.addW_q] using hh
      obtain ⟨hlk, halt⟩ := hm hcl
      have hlk' : 1 / (P.N : Rat) ≤ ((r.addW P.C (BitVec.setWidth 128 (ecxOf t.st), tw)).wr P.Lk).q := by
        rw [Res.addW_q]; exact hlk
      by_cases hsur : 1 / (P.N : Rat) < (r.wr P.Lk).q
      · exact ⟨hlk', .inr (by rw [Res.addW_q]; exact hsur)⟩
      rcases halt with hgood | hsur' | ⟨ts, ⟨hX, -⟩, -, hcts, -⟩
      · obtain ⟨ts, ⟨⟨-, hmax⟩, hkS⟩, hts, hx5⟩ := hgood
        refine ⟨hlk', .inl ⟨tw, ⟨?_, fun p hp' => ?_⟩, hkS, ?_⟩⟩
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
      · exact absurd hsur' hsur
      · exfalso
        have hle : (r.wr P.Lk).q ≤ 1 / (P.N : Rat) := Rat.not_lt.mp hsur
        obtain ⟨hin, hpd'⟩ := alt3_own E' hM ht hq hX hcts (hpp.1 rfl hcl hle _ hX hcts)
        exact hnp _ hin hpd'

/-- **The counter store** (`movl %ecx,(%rsi)`, position 10 → 11,
`HardCellsX.strC`). -/
theorem wp_store_counter {P : Params} {A : Arch} {tid : Nat} (hne : P.c ≠ P.l) (hN32 : P.N < 2 ^ 32)
    (hA : A.storeKind .plain ≠ .nt) : CellWPX P A tid 10 := by
  intro cl c r g g₀ rF t tree hW ht hF hL hp hph hpp hg₀ hex E hM hWf hpd hOP
  have hn := lt_size_of_get? ht
  have hnd : t.prom.Nodup := hM.promNodup tid t ht
  rw [exec_store_counter t.st (hF.at hp (by decide)) hF.rsi hF.dc] at hex
  cases hex
  by_cases hnp : ∀ ts ∈ t.prom, ts ∉ g.pend
  · exact x64_lift P A tid rF t _ ht E hM hnp
      (wp_store_counter_np hne hN32 hA rF t hW ht hF hL hph hpp E hM hnp)
  obtain ⟨ts₀, hts₀, hpd₀⟩ : ∃ ts ∈ t.prom, ts ∈ g.pend :=
    Classical.byContradiction fun h => hnp fun ts h1 h2 => h ⟨ts, h1, h2⟩
  obtain ⟨hshape, huniq, habove⟩ := hOP t ht ts₀ hts₀ hpd₀
  have hget₀ : c.mem.get? ts₀ = some ⟨P.C, BitVec.setWidth 128 (ecxOf t.st), tid⟩ := by
    rcases hshape with ⟨h5, -⟩ | ⟨-, hw⟩ | ⟨h11, -⟩
    · exact absurd (atPos_eq_rel (by decide) (.inl rfl) hp h5) (by decide)
    · exact hw
    · exact absurd (atPos_eq_rel (by decide) (.inr (.inr rfl)) hp h11) (by decide)
  simp only [Phase] at hph
  obtain ⟨S, k, hh, hm⟩ := hph
  have hq : (r.wr P.C).q = 1 := hh.1
  refine EvTree.eraseWPRD_store_pendOrDead hn ?_ ?_
  · -- the pending fulfilment: of `ts₀`
    intro cx' tw hc hev hpd'
    have hget : c.mem.get? tw = some ⟨P.C, BitVec.setWidth 128 (ecxOf t.st), tid⟩ ∧ tw ∈ t.prom ∧
        cx'.mem = c.mem := by
      rcases hev.cases with ⟨hm', htw, hg⟩ | ⟨-, rfl⟩
      · exact ⟨hg, htw, hm'⟩
      · exact absurd (E.pend_le hpd') (Nat.not_succ_le_self _)
    obtain ⟨hget, htw, hmem⟩ := hget
    have htw₀ : tw = ts₀ := huniq tw htw hpd'
    obtain ⟨hok, hvw⟩ := writeSuccs_tw hnd hc hev
    have hcoh : t.views.getCoh P.C < tw := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hok.1
    have hgle : g.Le (unpend g tw) := ⟨rfl, List.prefix_refl _, fun _ => List.prefix_refl _⟩
    simp only [EvTree.EraseWPRD]
    refine ⟨hgle, fun ts hts hor => ?_, fun ts h => (mem_unpend_pend.mp h).1, fun _ h => h, fun w hw => ?_,
      fun t' ht' _ => ⟨?_, ?_, ?_⟩⟩
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
      have hvw' : t'.views.vwOld = cx'.views.vwOld := by simpa using congrArg Views.vwOld hvs
      refine inv_withThread_mem (i := 11) hW ht (finishInstr_st ht') (hF.goto rfl rfl rfl)
        (by rw [hmem]; exact hL) rfl ?_ (prepaidProm_11 hq)
      simp only [Phase]
      refine .inl ⟨S, k, hh, fun ⟨hcl, E'⟩ => ?_⟩
      obtain ⟨hlk, halt⟩ := hm hcl
      by_cases hsur : 1 / (P.N : Rat) < (r.wr P.Lk).q
      · exact ⟨hlk, .inr hsur⟩
      rcases halt with hgood | hsur' | ⟨ts, ⟨hX, hmax⟩, hkS, hcts, -⟩
      · exfalso
        obtain ⟨ts, ⟨⟨-, hmax⟩, -⟩, hts, -⟩ := hgood
        exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt
          (Nat.le_trans (pend_le_max E' ht hq hmax hget hpd') hts) hcoh)
      · exact absurd hsur' hsur
      · have hle : (r.wr P.Lk).q ≤ 1 / (P.N : Rat) := Rat.not_lt.mp hsur
        obtain ⟨hin, hpdts⟩ := alt3_own E' hM ht hq hX hcts (hpp.1 rfl hcl hle _ hX hcts)
        have hts : ts = tw := (huniq ts hin hpdts).trans htw₀.symm
        refine ⟨hlk, .inl ⟨ts, ⟨hX, hmax⟩, hkS, ?_⟩⟩
        rw [hvw', hvw, hts]
        have hnt : (A.storeKind StoreKind.plain == StoreKind.nt) = false := by
          revert hA; cases A.storeKind StoreKind.plain <;> decide
        simp only [hnt, Bool.false_eq_true, ↓reduceIte]
        exact Nat.le_max_right _ _
    · intro ts h
      show ts ≤ cx'.mem.last
      rw [hmem]; exact E.pend_le (mem_unpend_pend.mp h).1
    · intro t'' ht'' ts h1 h2
      exfalso
      rw [Config.withThread_get? _ _ _ hn] at ht''
      simp only [ite_true, Option.some.injEq] at ht''
      subst ht''
      rw [(finishInstr_relKey ht').1, hev.prom] at h1
      obtain ⟨hne', h1⟩ := (List.Nodup.mem_erase_iff hnd).mp h1
      exact hne' (huniq ts h1 (mem_unpend_pend.mp h2).1 |>.trans (huniq tw htw hpd').symm)
  · -- every other write overtakes `ts₀`
    intro cx' tw hc hev hpd' _ _
    have hne₀ : tw ≠ ts₀ := fun h => hpd' (h ▸ hpd₀)
    have hle₀ : ts₀ ≤ c.mem.last := c.mem.last_le_of_get?_eq_some hget₀
    refine ⟨ts₀, ?_, _, writeSuccs_get? hc hget₀, ?_⟩
    · rw [hev.prom]
      exact (List.mem_erase_of_ne (Ne.symm hne₀)).mpr hts₀
    · rcases (mem_writeSuccs A tid).mp hc with ⟨p, hp', w, hw, hl, -, -, -, heq⟩ | ⟨-, heq⟩
      · have hpt : p = tw := by
          have h1 := hev.prom
          rw [heq] at h1
          exact erase_inj hnd hp' h1.symm |>.symm
        subst hpt
        have hlt := habove p hp' hne₀ w _ hw hget₀ hl
        rw [heq, afterWrite_getCoh]
        simp only [↓reduceIte]
        exact Nat.le_trans (Nat.le_of_lt hlt) (Nat.le_max_right _ _)
      · rw [heq, afterWrite_getCoh]
        simp only [↓reduceIte]
        exact Nat.le_trans (Nat.le_succ_of_le hle₀) (Nat.le_max_right _ _)

end Kraken.Promising.SLR.X64SpinInv
