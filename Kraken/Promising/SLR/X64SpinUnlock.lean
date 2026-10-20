/-
The unlock cell of the x64 spinlock worker (`movl $0,(%rdi)`, position
11 → 12), `HardCellsX.unlock : CellWPX P A tid 11` (`SLR/X64SpinRule.lean`).
The x64 twin of `SLR/SwpStlr.lean`.

The unlock is a plain store; it is a release when the architecture makes
plain stores releases (`hA : A.storeKind .plain = .rel`, true of `Arch.tso`),
which the `Good` split needs (the counter's maximal write is below `vwOld`,
below the fresh unlock message).

Position 11's `Phase` has two disjuncts.

- **Holding** (`wp_unlock_holding`): `C` is held whole, so `OwnPend` says no
  own promise is pending (an own pending promise is the swap's at 5, the
  counter store's at 10, or the unlock's at 11 with no counter permission;
  `atPos_eq_rel`); the cell is an `EraseWPR` proof
  (`EvTree.eraseWPR_store_rel`) lifted by `x64_lift`. The pending branch is
  vacuous (a fulfilled promise is not pending, a fresh timestamp is above
  every pending mark). In the non-pending branch the write is fresh
  (`Erase.fresh_of_impure`: the lock's release predicate is impure at `0`),
  `tw = |M| + 1`, not claimed (`not_claimed_new`), and the thread splits
  `r ⊎ {(0, tw)}` (`SpinCommon.release_split`, `SLR/SpinRelease.lean`); the
  slots carry `R` (`Erase.slotsFor`), `mayWrite` is kept (`mayWrite_release`).
- **Prepaid**: the thread has already handed the release over at its
  promise `ts` (`PrepaidProm`). Fulfilling a pending promise leaves `r` as
  is and reaches `Phase 12` from `Prepaid`; a non-pending fulfilment is
  impossible (as above) and a fresh write at `|M| + 1 > ts` raises
  `coh Lk` over the outstanding `ts`: `Ctx.Overtaken`, a dead branch.

The lock-word promise and the counter promises are told apart by
`OwnPend`'s position: at position 11 only the unlock's `(Lk, 0)` promise can
be pending (and only with no counter permission), so a prepaid counter store
(position 10) has been fulfilled before the unlock runs.
-/
import Kraken.Promising.SLR.X64SpinLift
import Kraken.Promising.SLR.SpinRelease
import Kraken.Promising.SLR.StoreHelpers

namespace Kraken.Promising.SLR.X64SpinInv

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SpinCommon
open Kraken.Promising.SLR.X64SpinTrees

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout spinWorker)]

omit hv in
/-- **`Inv` after a step of thread `tid`** with new memory `m`. -/
theorem inv_withThread_mem {P : Params} {tid : Nat} {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    {t t' : Thread isa} {m : Memory} (hW : World P.sys g) (ht : c.threads[tid]? = some t) {s : State}
    (hst : t'.st = s) (hF : Frame P s) (hL : LockWritesIn P.sys r m) {i : Nat} (hp : AtPos s i)
    (hph : Phase P tid cl i (eaxOf s) (ecxOf s) s.st.1.status.zf t'.views r)
    (hpp : PrepaidProm P tid cl i t' m r := by
      exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩) :
    Inv P tid cl (c.withThread tid t' m) r g := by
  have hn := lt_size_of_get? ht
  exact ⟨hW, t', by rw [Config.withThread_get? c t' m hn, ite_eq_left rfl], hst ▸ hF, hL, i, hst ▸ hp,
    hst ▸ hph, hpp⟩

omit hv in
/-- **The unlock from `Holding`**, as a `CellWPN`-style erasure WP. -/
theorem wp_unlock_holding {P : Params} {A : Arch} {tid : Nat} (hA : A.storeKind .plain = .rel)
    (hL : SpinLocs P.N P.Lk P.C P.K P.F)
    {cl : Prop} {c : Config isa} {r : Res} {g : Ghost} (rF : Nat → Res) (t : Thread isa)
    (hW : World P.sys g) (ht : c.threads[tid]? = some t) (hF : Frame P t.st) (hLW : LockWritesIn P.sys r c.mem)
    {S : Nat → Bool} {k : Nat} (hh : Holding P.sys tid S r)
    (hm : cl → 1 / P.N ≤ (r.wr P.Lk).q ∧
      ((∃ ts, CounterMax P.sys (BitVec.ofNat 128 (k + 1)) ts r ∧ k = ((List.range P.N).filter S).length ∧
        ts ≤ t.views.vwOld) ∨ 1 / P.N < (r.wr P.Lk).q))
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hM : c.MachInv) (hnp : ∀ ts ∈ t.prom, ts ∉ g.pend) :
    (EvTree.store .plain false P.Lk 0#128 fun _ => .done (goto t.st t.st.st.1 ((layout spinWorker).addrOf 12))).EraseWPR
      A tid (instrViews t (isa.deps t.st)) rF (fun _ => True) c t
      (WpPostR (Inv P tid) (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g
      (ctx₀ t tid c.mem) := by
  have hn := lt_size_of_get? ht
  have hpos : 0 < (r.wr P.Lk).q := hh.2.2.2.2.2.1
  refine EvTree.eraseWPR_store_rel hn hpos ?_ ?_
  · -- a pending write: neither an own (unpended) promise nor fresh
    intro cx' tw _ hev hpd
    exfalso
    rcases hev.cases with ⟨-, htw, -⟩ | ⟨-, rfl⟩
    · exact hnp tw htw hpd
    · exact Nat.not_succ_le_self _ (E.pend_le hpd)
  · intro cx' tw hc hev hpd _
    obtain ⟨hm', htw⟩ := E.fresh_of_impure ht rfl rfl hev hpd (lock_impure hW)
    have hvw : t.views.vwOld < tw := htw ▸ writeSuccs_fresh_vwOld hc hA hm'
    have hlt : ∀ p, (r.wr P.Lk).X p → p.2 < tw := fun p hx =>
      htw ▸ Nat.lt_succ_of_le (hLW p hx)
    obtain ⟨R, r', hres, hR0, hGB, hK, hX, hpost, -, -⟩ := release_split (P := P.sys) hL hh hm hlt hvw
    refine ⟨fun hin => ?_, htw ▸ not_claimed_new E _, R, r', ?_, hres, fun ss hss hprod => ?_⟩
    · obtain ⟨w, hw, -⟩ := hM.promWf tid t ht tw hin
      exact Nat.not_succ_le_self _ (htw ▸ c.mem.last_le_of_get?_eq_some hw)
    · rw [hW.1]; exact fun _ => hGB
    have hdisj : ∀ s ∈ g.u, ∀ s' ∈ ss, s.key ≠ s'.key := fun s hs s' hs' he => by
      have h1 := E.slot_key_le hs
      rw [he, hss.key s' hs', htw] at h1
      exact Nat.not_succ_le_self _ h1
    have hlast : cx'.mem.last = tw := by rw [hm', Memory.last_append, htw]
    have hgle : g.Le (storeGhost g P.Lk tw true ss) := ⟨rfl, List.prefix_refl _, fun _ => List.prefix_refl _⟩
    simp only [EvTree.EraseWPR]
    refine ⟨hgle, fun ts h _ => h, fun ts h => h, fun y h => mayWrite_release hres hprod hR0 hdisj h,
      fun w hw => ?_, fun t' ht' _ => ?_⟩
    · rw [writtenCx_fresh rfl hev hm' htw hw]; exact hpos
    · refine inv_withThread_mem (i := 12) (hW.mono hgle) ht (finishInstr_st ht') (hF.goto rfl rfl rfl) ?_ rfl
        ⟨hK, fun h => hpost h.1⟩
      intro p hx
      rw [hlast]
      rcases hX p hx with h | rfl
      · exact Nat.le_of_lt (hlt p h)
      · exact Nat.le_refl _

omit hv in
/-- **The unlock from `Prepaid`**, directly in the dead-branch form: the
pending fulfilment of the prepaid promise reaches `Phase 12`; every other
write is a fresh one overtaking the outstanding prepaid promise. `hts` and
`huniq` are the `PrepaidProm` and `OwnPend` facts this branch uses (the
unlock promise is outstanding, the own pending promise is unique). -/
theorem wp_unlock_prepaid {P : Params} {A : Arch} {tid : Nat} {cl : Prop} {c : Config isa} {r : Res}
    {g : Ghost} (rF : Nat → Res) (t : Thread isa)
    (hW : World P.sys g) (ht : c.threads[tid]? = some t) (hF : Frame P t.st) (hLW : LockWritesIn P.sys r c.mem)
    (hpre : Prepaid P tid cl r)
    (hts : ∃ ts ∈ t.prom, c.mem.get? ts = some ⟨P.Lk, 0, tid⟩)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hM : c.MachInv)
    (huniq : ∀ ts ∈ t.prom, ts ∈ g.pend → ∀ ts' ∈ t.prom, ts' ∈ g.pend → ts' = ts) :
    (EvTree.store .plain false P.Lk 0#128 fun _ => .done (goto t.st t.st.st.1 ((layout spinWorker).addrOf 12))).EraseWPRD
      A tid (instrViews t (isa.deps t.st)) rF (fun _ => True) c t
      (WpPostR (InvX P tid) (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g
      (ctx₀ t tid c.mem) := by
  have hn := lt_size_of_get? ht
  have hnd : t.prom.Nodup := hM.promNodup tid t ht
  refine EvTree.eraseWPRD_store_pendOrDead hn ?_ ?_
  · -- the pending fulfilment
    intro cx' tw _ hev hpd
    have hget : c.mem.get? tw = some ⟨P.Lk, 0#128, tid⟩ ∧ tw ∈ t.prom ∧ cx'.mem = c.mem := by
      rcases hev.cases with ⟨hm', htw, hg⟩ | ⟨-, rfl⟩
      · exact ⟨hg, htw, hm'⟩
      · exact absurd (E.pend_le hpd) (Nat.not_succ_le_self _)
    obtain ⟨hget, htw, hmem⟩ := hget
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
    · rw [writtenCx_writeEv hev hw]; exact hpre.2.2.1
    · exact inv_withThread_mem (i := 12) (hW.mono hgle) ht (finishInstr_st ht') (hF.goto rfl rfl rfl)
        (by rw [hmem]; exact hLW) rfl ⟨hpre.2.1, fun h => hpre.2.2.2 h.1⟩
    · intro ts h
      show ts ≤ cx'.mem.last
      rw [hmem]; exact E.pend_le (mem_unpend_pend.mp h).1
    · intro t'' ht'' ts h1 h2
      exfalso
      rw [Config.withThread_get? _ _ _ hn] at ht''
      simp only [ite_true, Option.some.injEq] at ht''
      subst ht''
      rw [(finishInstr_relKey ht').1, hev.prom] at h1
      obtain ⟨hne, h1⟩ := (List.Nodup.mem_erase_iff hnd).mp h1
      exact hne (huniq tw htw hpd ts h1 (mem_unpend_pend.mp h2).1)
  · -- every other write is fresh and overtakes the prepaid promise
    intro cx' tw hc hev hpd _ _
    obtain ⟨hm', htw⟩ := E.fresh_of_impure ht rfl rfl hev hpd (lock_impure hW)
    obtain ⟨ts, hts, hget⟩ := hts
    have hle : ts ≤ c.mem.last := c.mem.last_le_of_get?_eq_some hget
    refine ⟨ts, ?_, _, writeSuccs_get? hc hget, ?_⟩
    · rw [hev.prom]
      exact (List.mem_erase_of_ne fun he => Nat.not_succ_le_self _ (htw ▸ he ▸ hle)).mpr hts
    · rcases (mem_writeSuccs A tid).mp hc with ⟨_, _, _, _, _, _, _, _, heq⟩ | ⟨_, heq⟩
      · exfalso
        rw [heq] at hm'
        have := congrArg Memory.last hm'
        simp only [afterWrite, Memory.last_append] at this
        exact Nat.succ_ne_self _ this.symm
      · rw [heq, afterWrite_getCoh]
        simp only [↓reduceIte]
        exact Nat.le_trans (Nat.le_succ_of_le hle) (Nat.le_max_right _ _)

/-- **The unlock cell** (`HardCellsX.unlock`). `hA`: plain stores are
releases (`Arch.tso`). -/
theorem x64_unlock {P : Params} {A : Arch} {tid : Nat} (hA : A.storeKind .plain = .rel)
    (hL : SpinLocs P.N P.Lk P.C P.K P.F) : CellWPX P A tid 11 := by
  intro cl c r g g₀ rF t tree hW ht hF hLW hp hph hpp hg₀ hex E hM hWf hpd hOP
  rw [exec_unlock t.st (hF.at hp (by decide)) hF.rdi hF.dl] at hex
  cases hex
  simp only [Phase] at hph
  rcases hph with ⟨S, k, hh, hm⟩ | hpre
  · have hnp : ∀ ts ∈ t.prom, ts ∉ g.pend := fun ts hts hpd' => by
      rcases (hOP t ht ts hts hpd').1 with ⟨h5, -⟩ | ⟨h10, -⟩ | ⟨-, h0, -⟩
      · exact absurd (atPos_eq_rel (i := 11) (by decide) (.inl rfl) hp h5) (by decide)
      · exact absurd (atPos_eq_rel (i := 11) (by decide) (.inr (.inl rfl)) hp h10) (by decide)
      · rw [hh.1] at h0
        exact absurd h0 (by decide)
    exact x64_lift P A tid rF t _ ht E hM hnp (wp_unlock_holding hA hL rF t hW ht hF hLW hh hm E hM hnp)
  · exact wp_unlock_prepaid rF t hW ht hF hLW hpre (hpp.2 rfl hpre.1) E hM
      fun ts hts hpd' ts' hts' hpd'' => (hOP t ht ts hts hpd').2.1 ts' hts' hpd''

end Kraken.Promising.SLR.X64SpinInv
