/-
The prepay obligation of the SWP spinlock worker (`HardCellsX.prepay`,
`PrepayObX`, `SLR/SwpRuleX.lean`): thread `tid` promises `w` at
`ts = |M| + 1`, and its next instruction can fulfil `ts` with a release store
(`Thread.RelFulfils`).

- **Which instruction**: only the unlock `stlr wzr, [x0]` (position 13).
  The other cells are silent, loads, the counter's plain store
  (`A.plainStore ≠ .rel`) or the acquire swap (`hA3`: its write is not a
  release). The fulfilled message is `(Lk, 0)` (`writeSuccs_unpromise`), so
  `w = ⟨Lk, 0, _⟩`, and the write is allowed at `ts`, which is above `vwOld`
  (`writeOk_rel_vwOld`).
- **From `Holding`**: `release_split` at `ts`, the slots of `R`
  (`Erase.slotsFor`), `Erase.prepay_exempt`, and K1/K2 (`prepay_K1`,
  `prepay_K2`). After the promise the thread is `Prepaid` with `ts` as its
  only own pending promise (`OwnPend`, from `Holding`'s whole `C`: no earlier
  promise was pending).
- **From `Prepaid`** (a second prepayment) is excluded by `hfresh`: the
  thread has no outstanding `(Lk, 0)` promise. This is `PrepayObXN`;
  `NPSafe`'s prepay conjunct asks only about runs with a well-formed outcome,
  where the fresh release write at `ts` would have overtaken the earlier
  prepaid promise.
-/
import Kraken.Promising.SLR.SwpStlr

namespace Kraken.Promising.SLR.SwpInv

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.AArch64.Examples.InvEnv
open Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SwpTrees

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout swpWorker)]

/-! ## Machine facts -/

section Machine

variable {A : Arch} {tid : Nat} {iv : InstrViews}

omit layout hv in
/-- A write that removes the outstanding promise `ts` is allowed at `ts`. -/
theorem writeSuccs_fulfil_writeOk {cx cx' : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr : Option Time} {extra : View} (h : cx' ∈ writeSuccs A tid iv cx k xcl l v tr extra)
    (hb : ∀ p ∈ cx.prom, p ≤ cx.mem.last) {ts : Time} (hin : ts ∈ cx.prom) (hout : ts ∉ cx'.prom) :
    WriteOk A tid iv cx k l tr extra ts := by
  rcases (mem_writeSuccs A tid).mp h with ⟨t, -, -, -, -, -, -, hok, rfl⟩ | ⟨-, rfl⟩
  · by_cases hne : ts = t
    · subst hne; exact hok
    · exact absurd ((List.mem_erase_of_ne hne).mpr hin) hout
  · exfalso
    apply hout
    simp only [afterWrite]
    have hne : ts ≠ cx.mem.last + 1 := fun he => Nat.not_succ_le_self _ (he ▸ hb ts hin)
    exact (List.mem_erase_of_ne hne).mpr (List.mem_append_left _ hin)

omit layout hv in
/-- A release write lies above `vwOld`. -/
theorem writeOk_rel_vwOld {cx : Ctx} {k : StoreKind} {l : Loc} {tr : Option Time} {extra : View} {ts : Time}
    (hk : A.storeKind k = .rel) (h : WriteOk A tid iv cx k l tr extra ts) : cx.views.vwOld < ts := by
  have h1 := h.1
  simp only [writePre, hk, show (StoreKind.rel == StoreKind.rel) = true from rfl, ↓reduceIte] at h1
  simp only [View] at *
  omega

omit layout hv in
/-- A write that removes the outstanding promise `ts` writes at `ts`: it
erases `ts` from the promises, keeps the memory and raises `coh l` to `ts`. -/
theorem writeSuccs_fulfil_coh {cx cx' : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr : Option Time} {extra : View} (h : cx' ∈ writeSuccs A tid iv cx k xcl l v tr extra)
    (hb : ∀ p ∈ cx.prom, p ≤ cx.mem.last) {ts : Time} (hin : ts ∈ cx.prom) (hout : ts ∉ cx'.prom) :
    cx'.prom = cx.prom.erase ts ∧ cx'.mem = cx.mem ∧ ts ≤ cx'.views.getCoh l := by
  rcases (mem_writeSuccs A tid).mp h with ⟨t, -, -, -, -, -, -, -, rfl⟩ | ⟨-, rfl⟩
  · by_cases hne : ts = t
    · subst hne
      refine ⟨rfl, rfl, ?_⟩
      rw [afterWrite_getCoh]
      simp only [↓reduceIte]
      exact Nat.le_max_right _ _
    · exact absurd ((List.mem_erase_of_ne hne).mpr hin) hout
  · exfalso
    apply hout
    simp only [afterWrite]
    have hne : ts ≠ cx.mem.last + 1 := fun he => Nat.not_succ_le_self _ (he ▸ hb ts hin)
    exact (List.mem_erase_of_ne hne).mpr (List.mem_append_left _ hin)

end Machine

/-! ## The fulfilling instruction -/

/-- **Only the unlock fulfils a promise with a release store**, and it
fulfils a `(Lk, 0)` message above `vwOld`; a live run (`RelFulfilsLive`)
leaves every other outstanding `Lk` promise above `ts`. -/
theorem relFulfils_pos {P : Params} {A : Arch} {tid : Nat} (hA : A.plainStore ≠ .rel)
    (hA3 : A.storeKind (A.rmwKind .acq).storeKind ≠ .rel) {t : Thread isa} {mem : Memory} {ts : Time} {i : Nat}
    (hF : Frame P t.st) (hp : AtPos t.st i)
    (hi : i = 1 ∨ i = 3 ∨ i = 4 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 16)
    (hb : ∀ p ∈ t.prom, p ≤ mem.last) (h : t.RelFulfilsLive A tid ts mem) :
    i = 13 ∧ (∃ w, mem.get? ts = some w ∧ w.loc = P.Lk ∧ w.val = 0#128) ∧ t.views.vwOld < ts ∧
      ∀ p ∈ t.prom, p ≠ ts → ∀ w, mem.get? p = some w → w.loc = P.Lk → ts < p := by
  obtain ⟨tree, hex, hrf⟩ := h
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [exec_mov t.st (hF.at hp (by decide))] at hex; cases hex; simp [EvTree.RelFulfilsLive] at hrf
  · rw [exec_swpa t.st (hF.at hp (by decide)) hF.x0 hF.dl] at hex; cases hex
    simp [EvTree.RelFulfilsLive, hA3] at hrf
  · rw [exec_cbz t.st (hF.at hp (by decide))] at hex; cases hex; simp [EvTree.RelFulfilsLive] at hrf
  · rw [exec_ldr_spin t.st (hF.at hp (by decide)) hF.x0 hF.dl] at hex; cases hex
    simp [EvTree.RelFulfilsLive] at hrf
  · rw [exec_cbnz t.st (hF.at hp (by decide))] at hex; cases hex; simp [EvTree.RelFulfilsLive] at hrf
  · rw [exec_b_try t.st (hF.at hp (by decide))] at hex; cases hex; simp [EvTree.RelFulfilsLive] at hrf
  · rw [exec_ldr_c t.st (hF.at hp (by decide)) hF.x1 hF.dc] at hex; cases hex
    simp [EvTree.RelFulfilsLive] at hrf
  · rw [exec_add t.st (hF.at hp (by decide))] at hex; cases hex; simp [EvTree.RelFulfilsLive] at hrf
  · rw [exec_str_c t.st (hF.at hp (by decide)) hF.x1 hF.dc] at hex; cases hex
    simp [EvTree.RelFulfilsLive, Arch.storeKind, hA] at hrf
  · rw [exec_stlr t.st (hF.at hp (by decide)) hF.x0 hF.dl] at hex; cases hex
    simp only [EvTree.RelFulfilsLive, or_false] at hrf
    obtain ⟨cx', hc, ⟨hk, hin, hout⟩, hnd⟩ := hrf
    refine ⟨rfl, writeSuccs_unpromise hc hin hout, writeOk_rel_vwOld hk (writeSuccs_fulfil_writeOk hc hb hin hout),
      fun p hpt hne w hw hwl => ?_⟩
    obtain ⟨hpr, hmem, hcoh⟩ := writeSuccs_fulfil_coh hc hb hin hout
    have h1 := hnd p (by rw [hpr]; exact (List.mem_erase_of_ne hne).mpr hpt) w (by rw [hmem]; exact hw)
    rw [hwl] at h1
    exact Nat.lt_of_le_of_lt hcoh (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) h1)
  · rw [exec_b_done t.st (hF.at hp (by decide))] at hex; cases hex; simp [EvTree.RelFulfilsLive] at hrf
  · rw [exec_end hF hp] at hex; cases hex

/-! ## The prepayment -/

/-- **The prepay obligation** (`HardCellsX.prepay`). -/
theorem swp_prepay {P : Params} {A : Arch} {tid : Nat} (hL : SpinLocs P.N P.Lk P.C P.K P.F)
    (hA : A.plainStore ≠ .rel) (hA3 : A.storeKind (A.rmwKind .acq).storeKind ≠ .rel) : PrepayObX P A tid := by
  intro cl c₀ c r g₀ g rF t₁ w h he hle ht E hM hnp hrel
  have htw : (c.mem.append { w with tid }).2 = c.mem.last + 1 := rfl
  rw [htw] at hrel ⊢
  have hOP := ownPend_transport h he ht hnp
  obtain ⟨hW, t, ht', hF, hLW, i, hp, hph, hpp, -⟩ := inv_env h.1 he hle
  rw [ht] at ht'
  obtain rfl : t₁ = t := Option.some.inj ht'
  have hn := lt_size_of_get? ht
  have hb : ∀ p ∈ t₁.prom ++ [c.mem.last + 1], p ≤ (c.mem.append { w with tid }).1.last := fun p hp' => by
    rw [Memory.last_append]
    rcases List.mem_append.mp hp' with h1 | h1
    · obtain ⟨w', hw', -⟩ := hM.promWf tid t₁ ht p h1
      exact Nat.le_succ_of_le (c.mem.last_le_of_get?_eq_some hw')
    · rw [List.mem_singleton.mp h1]; exact Nat.le_refl _
  obtain ⟨rfl, ⟨w', hw', hwl, hwv⟩, hvw, hlive⟩ := relFulfils_pos (P := P) (t := { t₁ with prom := t₁.prom ++ [c.mem.last + 1] }) hA hA3 hF hp
    (Phase.pos hph) hb hrel
  rw [Memory.get?_append_last] at hw'
  obtain rfl := Option.some.inj hw'
  obtain ⟨wl, wv, wt⟩ := w
  simp only at hwl hwv
  subst hwl hwv
  simp only [Phase] at hph
  rcases hph with ⟨S, k, hh, hm⟩ | hpre
  case inr =>
    -- a second prepayment: the fresh release at `|M| + 1` would leave the
    -- prepaid promise `ts ≤ |M|` dead
    obtain ⟨ts, hts, hget⟩ := hpp rfl hpre.1
    have hle : ts ≤ c.mem.last := c.mem.last_le_of_get?_eq_some hget
    have h1 := hlive ts (List.mem_append_left _ hts) (fun he => Nat.not_succ_le_self _ (he ▸ hle)) _
      (by rw [Memory.get?_append_of_le _ _ _ hle]; exact hget) rfl
    exact absurd h1 (Nat.not_lt.mpr (Nat.le_succ_of_le hle))
  -- from `Holding`: no own promise is pending
  have hnp0 : ∀ ts ∈ t₁.prom, ts ∉ g.pend := fun ts hts hpd => by
    have h0 := (hOP t₁ ht ts hts hpd).2.1
    rw [hh.1] at h0
    exact absurd h0 (by decide)
  have hpos : 0 < (r.wr P.Lk).q := hh.2.2.2.2.2.1
  have hlt : ∀ p, (r.wr P.Lk).X p → p.2 < c.mem.last + 1 := fun p hx => Nat.lt_succ_of_le (hLW p hx)
  obtain ⟨R, r', hres, hR0, hGB, hK, hX, hpost, hC', hLk'⟩ := release_split hL hh hm hlt hvw
  have hR : (g.rel P.Lk).P 0#128 (c.mem.append ⟨P.Lk, 0#128, tid⟩).1 (c.mem.last + 1) R := by
    rw [hW.1]; exact fun _ => hGB
  obtain ⟨ss, hss, hprod⟩ := Erase.slotsFor E hR
  have hres' : r'.op (Res.prod (ss.map (·.res))) = r.addW P.Lk (0#128, c.mem.last + 1) := by
    rw [hprod]; exact hres
  have E' := Erase.prepay_exempt (w := ⟨P.Lk, 0#128, wt⟩) E ht trivial (ss := ss) (r' := r')
    (by rw [setRes_self]; exact hpos) hss (by rw [setRes_self]; exact hres')
  rw [setRes_setRes] at E'
  have hgle : g.Le (prepayGhost g P.Lk (c.mem.last + 1) ss) :=
    ⟨rfl, List.prefix_refl _, fun _ => List.prefix_refl _⟩
  have hdisj : ∀ s ∈ g.u, ∀ s' ∈ ss, s.key ≠ s'.key := fun s hs s' hs' he' => by
    have h1 := E.slot_key_le hs
    rw [he', hss.key s' hs'] at h1
    exact Nat.not_succ_le_self _ h1
  refine ⟨r', _, E', hgle, List.mem_cons_self .., fun ts h => List.mem_cons_of_mem _ h,
    fun ts h => (List.mem_cons.mp h).elim .inr .inl, ⟨?_, ?_, ?_⟩,
    fun y h => mayWrite_release (x := P.Lk) (tw := c.mem.last + 1) hres hprod hR0 hdisj h,
    prepay_K2 hss, prepay_K1 hss hres'⟩
  · -- `Inv`: `Prepaid` at position 13
    refine inv_withThread_mem (i := 13) (t' := { t₁ with prom := t₁.prom ++ [c.mem.last + 1] }) (hW.mono hgle)
      ht rfl hF ?_ hp ?_ fun _ _ => ⟨c.mem.last + 1, List.mem_append_right _ (List.mem_singleton_self _),
        Memory.get?_append_last _ _⟩
    · intro p hx
      rw [Memory.last_append]
      rcases hX p hx with h1 | rfl
      · exact Nat.le_of_lt (hlt p h1)
      · exact Nat.le_refl _
    · simp only [Phase]
      exact .inr ⟨hC', hK, hLk', fun h => hpost h.1⟩
  · -- `PendIn`
    intro ts h
    show ts ≤ (c.mem.append _).1.last
    rw [Memory.last_append]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_refl _
    · exact Nat.le_succ_of_le (E.pend_le h)
  · -- `OwnPend`: the promise is the only own pending one
    intro t'' ht'' ts h1 h2
    rw [Config.withThread_get? _ _ _ hn] at ht''
    simp only [ite_true, Option.some.injEq] at ht''
    subst ht''
    have key : ∀ x ∈ t₁.prom ++ [c.mem.last + 1], x ∈ (prepayGhost g P.Lk (c.mem.last + 1) ss).pend →
        x = c.mem.last + 1 := fun x hx hxp => by
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_cons.mp hxp with h | h
        · exact h
        · exact absurd h (hnp0 x hx)
      · exact List.mem_singleton.mp hx
    exact ⟨hp, hC', fun ts' h1' h2' => (key ts' h1' h2').trans (key ts h1 h2).symm⟩

end Kraken.Promising.SLR.SwpInv
