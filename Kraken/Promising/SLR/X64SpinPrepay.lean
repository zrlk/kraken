/-
The prepay obligation of the x64 spinlock worker (`HardCellsX.prepay`,
`PrepayObX`, `SLR/X64SpinRule.lean`): thread `tid` promises `w` at
`ts = |M| + 1`, and its next instruction can fulfil `ts` with a release store
leaving no promise dead (`Thread.RelFulfilsLive`). The x64 twin of
`SLR/SwpPrepay.lean`.

- **Which instruction** (`relFulfils_pos`, `SLR/X64SpinFulfil.lean`): under
  TSO three cells qualify, the swap (5), the counter store (10) and the
  unlock (11). The live run gives the fulfilled message and puts every other
  own promise at its location above `ts`.
- **No earlier own pending promise** (`hnp0`): by `OwnPend` it would be the
  same cell's prepaid write, at the same location and below `|M| < ts`; the
  live run would have left it dead. This also excludes a second prepayment
  of the unlock (`Prepaid` at 11 has its `(Lk, 0)` promise outstanding,
  `PrepaidProm`), with no extra hypothesis.
- **Swap (5)**, message `(Lk, 1)` (`Phase 5`: `%eax = 1`): `lockPred` is pure
  at a non-zero low word, so the message carries nothing (`R = unit`); the
  thread's write set of `Lk` gains `(1, ts)` and `Phase 5` is unchanged.
- **Counter store (10)**, message `(C, %ecx)`: the counter's predicate is
  pure (`World`); the write set of `C` gains `(k + 1, ts)`, which becomes the
  counter's maximal write above `coh C` (the third clean alternative of
  `Phase 10`: from the first, whose maximal write is below `coh C`, and from
  the third, whose earlier prepaid write is a message, `PrepaidProm`). The
  value is `ofNat 128 (k + 1)` because `k + 1 ≤ N < 2³²` (`hN32`, as in the
  AArch64 `wp_str_c`). `PrepaidProm`'s clause at 10 gains the new own message.
- **Unlock (11)**, from `Holding` (the argument of `SLR/SwpPrepay.lean`): `release_split` at `ts`
  (above `vwOld`), the slots of `R` (`Erase.slotsFor`),
  `Erase.prepay_exempt`, K1/K2 (`prepay_K1`, `prepay_K2`); after the promise
  the thread is `Prepaid`.

In every case `OwnPend` after the promise says: `ts` is the only own pending
promise, it carries the cell's message, and every other own promise at its
location is above it (the live run).
-/
import Kraken.Promising.SLR.X64SpinUnlock
import Kraken.Promising.SLR.X64SpinFulfil

namespace Kraken.Promising.SLR.X64SpinInv

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SpinCommon
open Kraken.Promising.SLR.X64SpinTrees

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout spinWorker)]

/-! ## The ghost side of a prepayment -/

omit layout hv in
/-- **A prepaid release store of `(x, v)` at `|M| + 1`** whose message
carries `R` (no acquire ids; the thread keeps `r'`, `r' ⋅ R = r ⊎ {(v, ts)}`):
erasure after the promise (`Erase.prepay_exempt`) in the ghost `prepayGhost`
for the slots of `R`, and the `acqLe`/K2/K1 conjuncts of `PrepayObX`. -/
theorem prepay_core {c : Config isa} {tid : Nat} {r r' R : Res} {g : Ghost} {rF : Nat → Res} {t₁ : Thread isa}
    (ht : c.threads[tid]? = some t₁) (E : Erase (setRes rF tid r) g (fun _ => True) c) {x : Loc} {v : Val}
    {wt : Nat} (hpos : 0 < (r.wr x).q) (hR : (g.rel x).P v (c.mem.append ⟨x, v, tid⟩).1 (c.mem.last + 1) R)
    (hR0 : ∀ y ι, R.acq y ι = 0) (hres : r'.op R = r.addW x (v, c.mem.last + 1)) :
    ∃ ss, Erase (setRes rF tid r') (prepayGhost g x (c.mem.last + 1) ss) (fun _ => True)
        (PromisedBy c tid t₁ ⟨x, v, wt⟩) ∧ g.Le (prepayGhost g x (c.mem.last + 1) ss) ∧
      (∀ y, mayWrite r' (prepayGhost g x (c.mem.last + 1) ss) y → mayWrite r g y) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ y, reachB ρ (prepayGhost g x (c.mem.last + 1) ss) y b → reachB ρ g y b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ y, reachB r' (prepayGhost g x (c.mem.last + 1) ss) y b → reachB r g y b) := by
  obtain ⟨ss, hss, hprod⟩ := Erase.slotsFor E hR
  have hres' : r'.op (Res.prod (ss.map (·.res))) = r.addW x (v, c.mem.last + 1) := by
    rw [hprod]; exact hres
  have E' := Erase.prepay_exempt (w := ⟨x, v, wt⟩) E ht trivial (ss := ss) (r' := r')
    (by rw [setRes_self]; exact hpos) hss (by rw [setRes_self]; exact hres')
  rw [setRes_setRes] at E'
  have hgle : g.Le (prepayGhost g x (c.mem.last + 1) ss) :=
    ⟨rfl, List.prefix_refl _, fun _ => List.prefix_refl _⟩
  have hdisj : ∀ s ∈ g.u, ∀ s' ∈ ss, s.key ≠ s'.key := fun s hs s' hs' he' => by
    have h1 := E.slot_key_le hs
    rw [he', hss.key s' hs'] at h1
    exact Nat.not_succ_le_self _ h1
  exact ⟨ss, E', hgle, fun y h => mayWrite_release (x := x) (tw := c.mem.last + 1) hres hprod hR0 hdisj h,
    prepay_K2 hss, prepay_K1 hss hres'⟩

/-! ## The prepayment -/

omit layout hv in
/-- The write set after adding `(v, ts)`: the old writes and the new one. -/
theorem addW_X_cases {r : Res} {x : Loc} {p p' : Val × Time} (h : ((r.addW x p).wr x).X p') :
    (r.wr x).X p' ∨ p' = p := by
  rcases (Res.addW_X_self r x p p').mp h with h | ⟨-, h⟩
  · exact .inl h
  · exact .inr h

/-- **The prepay obligation** (`HardCellsX.prepay`). `hN32`: the counter's
values fit the 32-bit register (as in the counter store). -/
theorem x64_prepay {P : Params} {A : Arch} {tid : Nat} (hL : SpinLocs P.N P.Lk P.C P.K P.F)
    (hN32 : P.N < 2 ^ 32) : PrepayObX P A tid := by
  intro cl c₀ c r g₀ g rF t₁ w h he hle ht E hM hnp hrel
  have htw : (c.mem.append { w with tid }).2 = c.mem.last + 1 := rfl
  rw [htw] at hrel ⊢
  have hOP := ownPend_transport h he ht hnp
  obtain ⟨hW, t, ht', hF, hLW, i, hp, hph, hpp⟩ := inv_env h.1 he hle
  rw [ht] at ht'
  obtain rfl : t₁ = t := Option.some.inj ht'
  have hn := lt_size_of_get? ht
  have hb : ∀ p ∈ t₁.prom ++ [c.mem.last + 1], p ≤ (c.mem.append { w with tid }).1.last := fun p hp' => by
    rw [Memory.last_append]
    rcases List.mem_append.mp hp' with h1 | h1
    · obtain ⟨w', hw', -⟩ := hM.promWf tid t₁ ht p h1
      exact Nat.le_succ_of_le (c.mem.last_le_of_get?_eq_some hw')
    · rw [List.mem_singleton.mp h1]; exact Nat.le_refl _
  have hpos := Phase.pos hph
  -- an old own promise at the fulfilled location would be left dead
  have kill : ∀ {x : Loc}, (∀ p ∈ t₁.prom ++ [c.mem.last + 1], p ≠ c.mem.last + 1 → ∀ w',
      (c.mem.append { w with tid }).1.get? p = some w' → w'.loc = x → c.mem.last + 1 < p) →
      ∀ ts0 ∈ t₁.prom, ∀ m0, c.mem.get? ts0 = some m0 → m0.loc = x → False := by
    intro x hlive ts0 h0 m0 hm0 hl
    have hle := c.mem.last_le_of_get?_eq_some hm0
    have h1 := hlive ts0 (List.mem_append_left _ h0) (fun he => Nat.not_succ_le_self _ (he ▸ hle)) m0
      (by rw [Memory.get?_append_of_le _ _ _ hle]; exact hm0) hl
    exact absurd h1 (Nat.not_lt.mpr (Nat.le_succ_of_le hle))
  -- `OwnPend` after the promise from: no old own pending promise, the
  -- position/message clause, and the live run
  have ownPend_new : ∀ {r' : Res} {ss : List Slot} {x : Loc}, (∀ ts0 ∈ t₁.prom, ts0 ∉ g.pend) →
      (∀ p ∈ t₁.prom ++ [c.mem.last + 1], p ≠ c.mem.last + 1 → ∀ w',
        (c.mem.append { w with tid }).1.get? p = some w' → w'.loc = x → c.mem.last + 1 < p) →
      w.loc = x →
      ((AtPos t₁.st 5 ∧ (c.mem.append { w with tid }).1.get? (c.mem.last + 1) =
          some ⟨P.Lk, BitVec.setWidth 128 (eaxOf t₁.st), tid⟩) ∨
        (AtPos t₁.st 10 ∧ (c.mem.append { w with tid }).1.get? (c.mem.last + 1) =
          some ⟨P.C, BitVec.setWidth 128 (ecxOf t₁.st), tid⟩) ∨
        (AtPos t₁.st 11 ∧ (r'.wr P.C).q = 0 ∧ (c.mem.append { w with tid }).1.get? (c.mem.last + 1) =
          some ⟨P.Lk, 0, tid⟩)) →
      OwnPend P tid (PromisedBy c tid t₁ w) r' (prepayGhost g x (c.mem.last + 1) ss) := by
    intro r' ss x hnp0 hlive hwl hcl t'' ht'' ts h1 h2
    rw [show PromisedBy c tid t₁ w = c.withThread tid { t₁ with prom := t₁.prom ++ [c.mem.last + 1] }
      (c.mem.append { w with tid }).1 from rfl, Config.withThread_get? _ _ _ hn] at ht''
    simp only [ite_true, Option.some.injEq] at ht''
    subst ht''
    have key : ∀ y ∈ t₁.prom ++ [c.mem.last + 1], y ∈ (prepayGhost g x (c.mem.last + 1) ss).pend →
        y = c.mem.last + 1 := fun y hy hyp => by
      rcases List.mem_append.mp hy with hy | hy
      · rcases List.mem_cons.mp hyp with h | h
        · exact h
        · exact absurd h (hnp0 y hy)
      · exact List.mem_singleton.mp hy
    obtain rfl := key ts h1 h2
    refine ⟨hcl, fun ts' h1' h2' => key ts' h1' h2', fun p hp' hne w₁ w₂ hw₁ hw₂ hl => ?_⟩
    have hw₂' : (c.mem.append { w with tid }).1.get? (c.mem.last + 1) = some w₂ := hw₂
    rw [Memory.get?_append_last] at hw₂'
    obtain rfl := Option.some.inj hw₂'
    exact hlive p hp' hne w₁ hw₁ (hl.trans hwl)
  have pendIn_new : ∀ {x : Loc} {ss : List Slot},
      PendIn (prepayGhost g x (c.mem.last + 1) ss) (c.mem.append { w with tid }).1 := by
    intro x ss ts h
    show ts ≤ (c.mem.append _).1.last
    rw [Memory.last_append]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_refl _
    · exact Nat.le_succ_of_le (E.pend_le h)
  -- an old own pending promise is the same cell's prepaid write
  have hnp0 : ∀ {x : Loc}, (∀ ts0 ∈ t₁.prom, ∀ m0, c.mem.get? ts0 = some m0 → m0.loc = x → False) →
      (i = 5 → x = P.Lk) → (i = 10 → x = P.C) → (i = 11 → x = P.Lk) → ∀ ts0 ∈ t₁.prom, ts0 ∉ g.pend := by
    intro x hk h5' h10' h11' ts0 h0 hpd
    rcases (hOP t₁ ht ts0 h0 hpd).1 with ⟨h5, hm⟩ | ⟨h10, hm⟩ | ⟨h11, -, hm⟩
    · obtain rfl := atPos_eq_rel hpos (.inl rfl) hp h5
      exact hk ts0 h0 _ hm (h5' rfl).symm
    · obtain rfl := atPos_eq_rel hpos (.inr (.inl rfl)) hp h10
      exact hk ts0 h0 _ hm (h10' rfl).symm
    · obtain rfl := atPos_eq_rel hpos (.inr (.inr rfl)) hp h11
      exact hk ts0 h0 _ hm (h11' rfl).symm
  rcases relFulfils_pos (P := P) (t := { t₁ with prom := t₁.prom ++ [c.mem.last + 1] }) hF hp hpos hb hrel with
    ⟨rfl, -, ⟨w', hw', hwl, hwv⟩, hlive⟩ | ⟨rfl, -, ⟨⟨w', hw', hwl, hwv⟩, hlive⟩, hcoh, -⟩ |
      ⟨rfl, -, ⟨⟨w', hw', hwl, hwv⟩, hlive⟩, -, hvw⟩
  · ---------------- the swap (5): `(Lk, 1)`, pure
    rw [Memory.get?_append_last] at hw'
    obtain rfl := Option.some.inj hw'
    have hk := kill hlive
    have hnp0' := hnp0 hk (fun _ => rfl) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    obtain ⟨wl, wv, wt⟩ := w
    simp only at hwl hwv
    subst hwl hwv
    simp only [Phase] at hph
    obtain ⟨⟨hfr, htid⟩, hfwd, heax⟩ := hph
    have hR : (g.rel P.Lk).P (BitVec.setWidth 128 (eaxOf t₁.st)) (c.mem.append ⟨P.Lk, BitVec.setWidth 128 (eaxOf t₁.st), tid⟩).1
        (c.mem.last + 1) Res.unit := by
      rw [hW.1]
      exact lockPred_pure (by rw [setWidth_32_128, heax]; decide) _ _
    obtain ⟨ss, E', hgle, hmw, hK2, hK1⟩ := prepay_core (wt := wt) ht E
      (by have := one_div_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) htid); have := hfr.2.2; grind) hR (fun _ _ => rfl)
      (Res.op_unit _)
    refine ⟨_, _, E', hgle, List.mem_cons_self .., fun ts h => List.mem_cons_of_mem _ h,
      fun ts h => (List.mem_cons.mp h).elim .inr .inl, ⟨?_, pendIn_new, ownPend_new hnp0' hlive rfl
        (.inl ⟨hp, Memory.get?_append_last _ _⟩)⟩, hmw, hK2, hK1⟩
    refine inv_withThread_mem (i := 5) (t' := { t₁ with prom := t₁.prom ++ [c.mem.last + 1] }) (hW.mono hgle)
      ht rfl hF ?_ hp ?_
    · intro p hx
      rw [Memory.last_append]
      rcases addW_X_cases hx with h1 | rfl
      · exact Nat.le_succ_of_le (hLW p h1)
      · exact Nat.le_refl _
    · simp only [Phase, FreshN, Fresh, Res.addW_q]
      exact ⟨⟨hfr, htid⟩, hfwd, heax⟩
  · ---------------- the counter store (10): `(C, %ecx)`, pure
    rw [Memory.get?_append_last] at hw'
    obtain rfl := Option.some.inj hw'
    have hk := kill hlive
    have hnp0' := hnp0 hk (fun h => absurd h (by decide)) (fun _ => rfl) (fun h => absurd h (by decide))
    obtain ⟨wl, wv, wt⟩ := w
    simp only at hwl hwv
    subst hwl hwv
    simp only [Phase] at hph
    obtain ⟨S, k, hh, hm⟩ := hph
    have hlc : P.Lk ≠ P.C := hL.lk_c
    have hR : (g.rel P.C).P (BitVec.setWidth 128 (ecxOf t₁.st)) (c.mem.append ⟨P.C, BitVec.setWidth 128 (ecxOf t₁.st), tid⟩).1
        (c.mem.last + 1) Res.unit := hW.2.1 _ _ _
    have hC1 : (0 : Rat) < (r.wr P.C).q := by rw [hh.1]; decide
    obtain ⟨ss, E', hgle, hmw, hK2, hK1⟩ := prepay_core (wt := wt) ht E hC1 hR (fun _ _ => rfl) (Res.op_unit _)
    refine ⟨_, _, E', hgle, List.mem_cons_self .., fun ts h => List.mem_cons_of_mem _ h,
      fun ts h => (List.mem_cons.mp h).elim .inr .inl, ⟨?_, pendIn_new, ownPend_new hnp0' hlive rfl
        (.inr (.inl ⟨hp, Memory.get?_append_last _ _⟩))⟩, hmw, hK2, hK1⟩
    -- the count fits the register
    have hk1 : ∀ {k' : Nat}, k' = ((List.range P.N).filter S).length → k' + 1 < 2 ^ 32 := by
      intro k' hk'
      have h1 := filter_setTrue_length hh.2.1 P.N hh.2.2.1
      have h2 := List.length_filter_le (setTrue S tid) (List.range P.N)
      rw [List.length_range] at h2
      omega
    -- the new counter write is the maximal one
    have hnewX : ∀ {k' : Nat}, k' = ((List.range P.N).filter S).length →
        BitVec.setWidth 32 (ecxOf t₁.st) = BitVec.ofNat 32 (k' + 1) ∨ ecxOf t₁.st = BitVec.ofNat 32 (k' + 1) →
        ((r.addW P.C (BitVec.setWidth 128 (ecxOf t₁.st), c.mem.last + 1)).wr P.C).X
          (BitVec.ofNat 128 (k' + 1), c.mem.last + 1) := by
      intro k' hk' hx
      have hx' : ecxOf t₁.st = BitVec.ofNat 32 (k' + 1) := by
        rcases hx with hx | hx
        · simpa using hx
        · exact hx
      rw [hx', setWidth_ofNat_32 (hk1 hk')]
      exact (Res.addW_X_self _ _ _ _).mpr (.inr ⟨hC1, rfl⟩)
    refine inv_withThread_mem (i := 10) (t' := { t₁ with prom := t₁.prom ++ [c.mem.last + 1] }) (hW.mono hgle)
      ht rfl hF ?_ hp ?_ ⟨fun _ hcl hq p hp' hlt => ?_, fun h => absurd h (by decide)⟩
    · intro p hx
      rw [Res.addW_wr_ne _ _ hlc] at hx
      rw [Memory.last_append]
      exact Nat.le_succ_of_le (hLW p hx)
    · simp only [Phase]
      have hh' : Holding P.sys tid S (r.addW P.C (BitVec.setWidth 128 (ecxOf t₁.st), c.mem.last + 1)) := by
        simp only [Holding, Res.addW_q]; exact hh
      refine ⟨S, k, hh', fun hcl => ?_⟩
      simp only [Res.addW_q]
      obtain ⟨hq, ⟨ts0, ⟨⟨hX, hmax⟩, hkS⟩, hc, hx⟩ | hsur | ⟨ts0, ⟨hX, hmax⟩, hkS, hc, hx⟩⟩ := hm hcl.1
      · -- the first alternative: the old writes are below `coh C`
        refine ⟨hq, .inr (.inr ⟨c.mem.last + 1, ⟨hnewX hkS (.inr hx), fun p hp' => ?_⟩, hkS, hcoh, hx⟩)⟩
        rcases addW_X_cases hp' with h1 | rfl
        · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_trans (hmax p h1) hc) hcoh)
        · exact Nat.le_refl _
      · exact ⟨hq, .inr (.inl hsur)⟩
      · -- the third alternative: the earlier prepaid write is a message
        by_cases hsur : 1 / P.N < (r.wr P.Lk).q
        · exact ⟨hq, .inr (.inl hsur)⟩
        obtain ⟨w0, hw0, -⟩ := hpp.1 rfl hcl.1 (Rat.not_lt.mp hsur) _ hX hc
        have hle0 : ts0 ≤ c.mem.last := c.mem.last_le_of_get?_eq_some hw0
        refine ⟨hq, .inr (.inr ⟨c.mem.last + 1, ⟨hnewX hkS (.inr hx), fun p hp' => ?_⟩, hkS, hcoh, hx⟩)⟩
        rcases addW_X_cases hp' with h1 | rfl
        · exact Nat.le_succ_of_le (Nat.le_trans (hmax p h1) hle0)
        · exact Nat.le_refl _
    · -- `PrepaidProm` at 10: the old own messages, and the new one
      rw [Res.addW_q] at hq
      rcases addW_X_cases hp' with h1 | rfl
      · obtain ⟨w0, hw0, hwt⟩ := hpp.1 rfl hcl.1 hq p h1 hlt
        exact ⟨w0, by rw [Memory.get?_append_of_le _ _ _ (c.mem.last_le_of_get?_eq_some hw0)]; exact hw0, hwt⟩
      · exact ⟨_, Memory.get?_append_last _ _, rfl⟩
  · ---------------- the unlock (11): `(Lk, 0)`, from `Holding`
    rw [Memory.get?_append_last] at hw'
    obtain rfl := Option.some.inj hw'
    have hk := kill hlive
    have hnp0' := hnp0 hk (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun _ => rfl)
    obtain ⟨wl, wv, wt⟩ := w
    simp only at hwl hwv
    subst hwl hwv
    simp only [Phase] at hph
    rcases hph with ⟨S, k, hh, hm⟩ | hpre
    case inr =>
      -- a second prepayment: the earlier unlock promise would be left dead
      obtain ⟨ts0, h0, hm0⟩ := hpp.2 rfl hpre.1
      exact (hk ts0 h0 _ hm0 rfl).elim
    have hpos' : 0 < (r.wr P.Lk).q := hh.2.2.2.2.2.1
    have hlt : ∀ p, (r.wr P.Lk).X p → p.2 < c.mem.last + 1 := fun p hx => Nat.lt_succ_of_le (hLW p hx)
    obtain ⟨R, r', hres, hR0, hGB, hK, hX, hpost, hC', hLk'⟩ := release_split (P := P.sys) hL hh hm hlt hvw
    have hR : (g.rel P.Lk).P 0#128 (c.mem.append ⟨P.Lk, 0#128, tid⟩).1 (c.mem.last + 1) R := by
      rw [hW.1]; exact fun _ => hGB
    obtain ⟨ss, E', hgle, hmw, hK2, hK1⟩ := prepay_core (wt := wt) ht E hpos' hR hR0 hres
    refine ⟨r', _, E', hgle, List.mem_cons_self .., fun ts h => List.mem_cons_of_mem _ h,
      fun ts h => (List.mem_cons.mp h).elim .inr .inl, ⟨?_, pendIn_new, ownPend_new hnp0' hlive rfl
        (.inr (.inr ⟨hp, hC', Memory.get?_append_last _ _⟩))⟩, hmw, hK2, hK1⟩
    refine inv_withThread_mem (i := 11) (t' := { t₁ with prom := t₁.prom ++ [c.mem.last + 1] }) (hW.mono hgle)
      ht rfl hF ?_ hp (.inr ⟨hC', hK, hLk', fun h => hpost h.1⟩)
      ⟨fun h => absurd h (by decide), fun _ _ => ⟨c.mem.last + 1,
        List.mem_append_right _ (List.mem_singleton_self _), Memory.get?_append_last _ _⟩⟩
    intro p hx
    rw [Memory.last_append]
    rcases hX p hx with h1 | rfl
    · exact Nat.le_of_lt (hlt p h1)
    · exact Nat.le_refl _

end Kraken.Promising.SLR.X64SpinInv
