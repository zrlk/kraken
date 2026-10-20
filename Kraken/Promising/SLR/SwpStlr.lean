/-
The unlock cell of the SWP spinlock worker (`stlr wzr, [x0]`, position
13 → 14), `HardCellsX.stlr : CellWPX P A tid 13` (`SLR/SwpRuleX.lean`).

Position 13's `Phase` has two disjuncts.

- **Holding** (`wp_stlr_holding`): `C` is held whole, so `OwnPend` says no
  own promise is pending; the cell is an `EraseWPR` proof
  (`EvTree.eraseWPR_store_rel`) lifted by `swp_lift`. The pending branch is
  vacuous (a fulfilled promise is not pending, a fresh timestamp is above
  every pending mark). In the non-pending branch the write is fresh
  (`Erase.fresh_of_impure`: the lock's release predicate is impure at `0`),
  `tw = |M| + 1`, not claimed (`not_claimed_new`), and the thread splits
  `r ⊎ {(0, tw)}` (`release_split`, `SLR/SwpRelease.lean`); the slots carry
  `R` (`Erase.slotsFor`), `mayWrite` is kept (`mayWrite_release`: `R` has no
  acquire ids, the slots' keys are fresh).
- **Prepaid**: the thread has already handed the release over at its
  promise `ts` (`PrepaidProm`). Fulfilling a pending promise leaves `r` as
  is and reaches `Phase 14` from `Prepaid`; a non-pending fulfilment is
  impossible (as above) and a fresh write at `|M| + 1 > ts` raises
  `coh Lk` over the outstanding `ts`: `Ctx.Overtaken`, a dead branch.
-/
import Kraken.Promising.SLR.SwpRelease
import Kraken.Promising.SLR.SwpLift
import Kraken.Promising.SLR.SwpStore

namespace Kraken.Promising.SLR.SwpInv

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.AArch64.Examples.InvEnv
open Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SwpTrees

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout swpWorker)]

omit layout hv in
/-- The lock's release predicate is impure at `0`. -/
theorem lock_impure {P : Params} {g : Ghost} (hW : World P g) : ¬ Pred.Pure (g.rel P.Lk) 0#128 := fun h => by
  rw [hW.1] at h
  rcases h default 0 (by first | rfl | decide) with ⟨_, _, _, ⟨hq, _⟩, _⟩ | ⟨hq, _⟩
  · simp [Res.unit, Perm.unit] at hq
  · simp [Res.unit, Perm.unit] at hq

/-- **The unlock from `Holding`**, as a `CellWPN`-style erasure WP. -/
theorem wp_stlr_holding {P : Params} {A : Arch} {tid : Nat} (hL : SpinLocs P.N P.Lk P.C P.K P.F)
    {cl : Prop} {c : Config isa} {r : Res} {g : Ghost} (rF : Nat → Res) (t : Thread isa)
    (hW : World P g) (ht : c.threads[tid]? = some t) (hF : Frame P t.st) (hLW : LockWritesIn P r c.mem)
    (hp : AtPos t.st 13) {S : Nat → Bool} {k : Nat} (hh : Holding P tid S r)
    (hm : cl → 1 / P.N ≤ (r.wr P.Lk).q ∧
      ((∃ ts, CounterMax P (BitVec.ofNat 128 (k + 1)) ts r ∧ k = ((List.range P.N).filter S).length ∧
        ts ≤ t.views.vwOld) ∨ 1 / P.N < (r.wr P.Lk).q))
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hM : c.MachInv) (hnp : ∀ ts ∈ t.prom, ts ∉ g.pend) :
    (EvTree.store .rel false P.Lk 0#128 fun _ => .done (goto t.st t.st.st.1 ((layout swpWorker).addrOf 14))).EraseWPR
      A tid (instrViews t (isa.deps t.st)) rF (fun _ => True) c t
      (WpPostR (Inv P tid) (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g
      (ctx₀ t tid c.mem) := by
  have hx3 := hF.x3_at hp (by decide)
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
    have hvw : t.views.vwOld < tw := htw ▸ writeSuccs_fresh_vwOld hc rfl hm'
    have hlt : ∀ p, (r.wr P.Lk).X p → p.2 < tw := fun p hx =>
      htw ▸ Nat.lt_succ_of_le (hLW p hx)
    obtain ⟨R, r', hres, hR0, hGB, hK, hX, hpost, -, -⟩ := release_split hL hh hm hlt hvw
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
    · refine inv_withThread_mem (i := 14) (hW.mono hgle) ht (finishInstr_st ht') (hF.goto rfl rfl rfl) ?_ rfl
        ⟨hK, fun h => hpost h.1⟩
      intro p hx
      rw [hlast]
      rcases hX p hx with h | rfl
      · exact Nat.le_of_lt (hlt p h)
      · exact Nat.le_refl _

/-- **The unlock from `Prepaid`**, directly in the dead-branch form: the
pending fulfilment of the prepaid promise reaches `Phase 14`; every other
write is a fresh one overtaking the outstanding prepaid promise. `hLk` and
`huniq` are the `Prepaid` and `OwnPend` facts this branch uses (the lock is
held, the own pending promise is unique). -/
theorem wp_stlr_prepaid {P : Params} {A : Arch} {tid : Nat} {cl : Prop} {c : Config isa} {r : Res}
    {g : Ghost} (rF : Nat → Res) (t : Thread isa)
    (hW : World P g) (ht : c.threads[tid]? = some t) (hF : Frame P t.st) (hLW : LockWritesIn P r c.mem)
    (hp : AtPos t.st 13) (hpre : Prepaid P tid cl r) (hLk : 0 < (r.wr P.Lk).q)
    (hts : ∃ ts ∈ t.prom, c.mem.get? ts = some ⟨P.Lk, 0, tid⟩)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hM : c.MachInv)
    (huniq : ∀ ts ∈ t.prom, ts ∈ g.pend → ∀ ts' ∈ t.prom, ts' ∈ g.pend → ts' = ts) :
    (EvTree.store .rel false P.Lk 0#128 fun _ => .done (goto t.st t.st.st.1 ((layout swpWorker).addrOf 14))).EraseWPRD
      A tid (instrViews t (isa.deps t.st)) rF (fun _ => True) c t
      (WpPostR (InvX P tid) (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g
      (ctx₀ t tid c.mem) := by
  have hx3 := hF.x3_at hp (by decide)
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
    · rw [writtenCx_writeEv hev hw]; exact hLk
    · exact inv_withThread_mem (i := 14) (hW.mono hgle) ht (finishInstr_st ht') (hF.goto rfl rfl rfl)
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

/-- **The unlock cell** (`HardCellsX.stlr`). -/
theorem swp_stlr {P : Params} {A : Arch} {tid : Nat} (hL : SpinLocs P.N P.Lk P.C P.K P.F)
 :
    CellWPX P A tid 13 := by
  intro cl c r g g₀ rF t tree hW ht hF hLW hp hph hpp hg₀ hex E hM hWf hpd hOP
  have hx3 := hF.x3_at hp (by decide)
  rw [exec_stlr t.st (hF.at hp (by decide)) hF.x0 hF.dl] at hex
  cases hex
  simp only [Phase] at hph
  rcases hph with ⟨S, k, hh, hm⟩ | hpre
  · have hnp : ∀ ts ∈ t.prom, ts ∉ g.pend := fun ts hts hpd' => by
      have h0 := (hOP t ht ts hts hpd').2.1
      rw [hh.1] at h0
      exact absurd h0 (by decide)
    exact swp_lift P A tid rF t _ ht E hM hnp (wp_stlr_holding hL rF t hW ht hF hLW hp hh hm E hM hnp)
  · exact wp_stlr_prepaid rF t hW ht hF hLW hp hpre hpre.2.2.1 (hpp rfl hpre.1) E hM
      fun ts hts hpd' ts' hts' hpd'' => (hOP t ht ts hts hpd').2.2 ts' hts' hpd''

end Kraken.Promising.SLR.SwpInv
