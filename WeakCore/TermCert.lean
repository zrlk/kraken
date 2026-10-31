/-
T3c-7 L1 + fact (f): dead promises.

A promise `t` of a thread whose coherence view at the promise's address has
already reached `t` can never be fulfilled: every fulfil needs `ob < t`, and
`ob ≥ coh a`.  Coherence views never come back down past a dead promise, and
memory only grows, so a dead promise stays dead.  A certificate must fulfil
every promise; so in a certified configuration every outstanding promise is
strictly above the thread's `coh` at its address.
-/
import WeakCore.TermMem

namespace TermCert
open CoreLang CoreTerm TermRun
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-! ## §1 Dead promises -/

/-- `t` is an outstanding promise whose coherence view has already reached it. -/
def DeadM (mem : Memory) (vs : VState) (P : List Ts) (t : Ts) : Prop :=
  t ∈ P ∧ ∃ m, mem[t]? = some m ∧ t ≤ vs.coh m.loc

def DeadP (s : St) (t : Ts) : Prop := DeadM s.mem s.vs s.promises t

/-- Memory `M'` keeps every message of `M` where it was. -/
def MemExt (M M' : Memory) : Prop := ∀ (t : Nat) (m : Msg), M[t]? = some m → M'[t]? = some m

theorem MemExt.rfl' (M : Memory) : MemExt M M := fun _ _ h => h

theorem MemExt.trans {M1 M2 M3 : Memory} (h1 : MemExt M1 M2) (h2 : MemExt M2 M3) : MemExt M1 M3 :=
  fun t m h => h2 t m (h1 t m h)

theorem MemExt.push (M : Memory) (m : Msg) : MemExt M (M.push m) := by
  intro t m' h
  rw [Array.getElem?_push]
  have : t < M.size := TermMem.lt_of_get h
  simp [Nat.ne_of_lt this, h]

theorem DeadM.lt {mem : Memory} {vs : VState} {P : List Ts} {t : Ts} (h : DeadM mem vs P t) :
    t < mem.size := by
  obtain ⟨_, m, hm, _⟩ := h
  exact TermMem.lt_of_get hm

/-- The general shape of preservation. -/
theorem DeadM.mono {mem mem' : Memory} {vs vs' : VState} {P P' : List Ts} {t : Ts}
    (h : DeadM mem vs P t) (hm : MemExt mem mem') (hp : t ∈ P')
    (hc : ∀ m, mem[t]? = some m → t ≤ vs.coh m.loc → t ≤ vs'.coh m.loc) : DeadM mem' vs' P' t := by
  obtain ⟨_, m, hm1, hm2⟩ := h
  exact ⟨hp, m, hm t m hm1, hc m hm1 hm2⟩

/-- A readable message at `a` is the last one at `a` up to the bound. -/
theorem readable_last {mem : Memory} {a : Address} {t1 bound t : Ts} {m : Msg}
    (hr : WeakMem.readable mem a t1 bound = true) (hm : mem[t]? = some m) (hl : m.loc = a)
    (hb : t ≤ bound) : t ≤ t1 := by
  apply Nat.le_of_not_lt
  intro hlt
  have hh : WeakMem.hiddenFrom mem a t1 bound = true := by
    unfold WeakMem.hiddenFrom
    rw [List.any_eq_true]
    exact ⟨t, List.mem_range.2 (Nat.lt_succ_of_le hb), by simp [hlt, hm, hl]⟩
  simp [WeakMem.readable, hh] at hr

theorem stepFence_coh (th : Promises.Thread) (f : WeakMem.Fence) :
    (Promises.stepFence th f).vs.coh = th.vs.coh := by
  cases f <;> rfl

theorem stepFence_prom (th : Promises.Thread) (f : WeakMem.Fence) :
    (Promises.stepFence th f).promises = th.promises := by
  cases f <;> rfl

/-! ## §2 The machine's rules -/

theorem stepLoad_dead {arch : Arch} {mem : Memory} {pairs : List Ts} {th th' : Promises.Thread}
    {dst : WeakMem.Reg} {a : Address} {deps : List WeakMem.Reg} {acq : Bool} {t : Ts}
    (h : th' ∈ Promises.stepLoad arch mem pairs th dst a deps acq)
    (hd : DeadM mem th.vs th.promises t) : DeadM mem th'.vs th'.promises t := by
  simp only [Promises.stepLoad, List.mem_map, List.mem_filter, List.mem_range] at h
  obtain ⟨tr, _, rfl⟩ := h
  refine hd.mono (MemExt.rfl' _) hd.1 fun m _ hle => ?_
  show t ≤ (if m.loc = a then _ else _)
  split
  · rename_i he; subst he; exact Nat.le_trans hle (Nat.le_max_left _ _)
  · exact hle

theorem stepLoadPair_dead {arch : Arch} {mem : Memory} {pairs : List Ts} {th th' : Promises.Thread}
    {dst0 dst1 : WeakMem.Reg} {a : Address} {deps : List WeakMem.Reg} {acq : Bool} {t : Ts}
    (h : th' ∈ Promises.stepLoadPair arch mem pairs th dst0 dst1 a deps acq)
    (hd : DeadM mem th.vs th.promises t) : DeadM mem th'.vs th'.promises t := by
  simp only [Promises.stepLoadPair, List.mem_flatMap, List.mem_filterMap, List.mem_filter,
    List.mem_range] at h
  obtain ⟨t0, _, t1, _, hs⟩ := h
  split at hs
  · cases hs
  · simp only [Option.some.injEq] at hs
    subst hs
    refine hd.mono (MemExt.rfl' _) hd.1 fun m _ hle => ?_
    show t ≤ (if m.loc = a then _ else if m.loc = a.next then _ else _)
    split
    · rename_i he; subst he; exact Nat.le_trans hle (Nat.le_max_left _ _)
    · split
      · rename_i _ he; rw [he] at hle; exact Nat.le_trans hle (Nat.le_max_left _ _)
      · exact hle

theorem le_maxL {x y z : Nat} (h : x ≤ y) : x ≤ max y z := Nat.le_trans h (Nat.le_max_left _ _)
theorem le_maxR {x y z : Nat} (h : x ≤ z) : x ≤ max y z := Nat.le_trans h (Nat.le_max_right _ _)

/-- Close `x ≤ e` where `x` occurs in the `max`/`if` tree `e`. -/
syntax "maxle" : tactic
macro_rules
  | `(tactic| maxle) => `(tactic| first
      | exact Nat.le_refl _
      | (apply le_maxR; maxle)
      | (apply le_maxL; maxle)
      | (split <;> maxle))

theorem deadM_lock {arch : Arch} {mem : Memory} {x : Promises.Thread} {t : Ts}
    (h : DeadM mem x.vs x.promises t) :
    DeadM mem (if arch = .tso then Promises.stepFence x .sy else x).vs
      (if arch = .tso then Promises.stepFence x .sy else x).promises t := by
  split
  · unfold DeadM at *; rw [stepFence_coh, stepFence_prom]; exact h
  · exact h

theorem storeOb_coh (k : Promises.Knobs) (arch : Arch) (th : Promises.Thread) (a : Address)
    (e : WeakMem.Expr) (deps : List WeakMem.Reg) :
    th.vs.coh a ≤ Promises.storeOb k arch th a e deps := by
  simp only [Promises.storeOb]
  split
  · apply le_maxL; apply le_maxR; apply le_maxR; exact Nat.le_refl _
  · apply le_maxR; apply le_maxR; exact Nat.le_refl _

theorem stepStore_dead {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {th th' : Promises.Thread}
    {a : Address} {e : WeakMem.Expr} {deps : List WeakMem.Reg} {rel : Bool} {t : Ts}
    (h : (mem', th') ∈ Promises.stepStore k arch mem th a e deps rel)
    (hd : DeadM mem th.vs th.promises t) : DeadM mem' th'.vs th'.promises t := by
  have hob := storeOb_coh k arch th a e deps
  cases e <;>
  · simp only [Promises.stepStore, List.mem_append, List.mem_singleton, List.mem_filterMap] at h
    rcases h with h | ⟨tw, _, hf⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine hd.mono (MemExt.push _ _) hd.1 fun m _ hle => ?_
      show t ≤ (if m.loc = a then _ else _)
      split
      · exact Nat.le_of_lt hd.lt
      · exact hle
    · cases hm : mem[tw]? with
      | none => simp [hm] at hf
      | some pm =>
          simp only [hm] at hf
          split at hf
          · rename_i hcond
            simp only [Option.some.injEq, Prod.mk.injEq] at hf
            obtain ⟨rfl, rfl⟩ := hf
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
            obtain ⟨⟨⟨hl, -⟩, -⟩, hlt⟩ := hcond
            obtain ⟨htP, m0, hm0, hle0⟩ := hd
            have hne : t ≠ tw := by
              rintro rfl
              have e0 := Option.some.inj (hm.symm.trans hm0)
              subst e0
              rw [hl] at hle0
              exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_trans hle0 hob) hlt)
            refine ⟨(List.mem_erase_of_ne hne).2 htP, m0, hm0, ?_⟩
            show t ≤ (if m0.loc = a then tw else th.vs.coh m0.loc)
            split
            · rename_i he; rw [he] at hle0
              exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_trans hle0 hob) hlt)
            · exact hle0
          · simp at hf

theorem stepRmw_dead_at {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool} {t : Ts}
    (h : (mem', th') ∈ Promises.stepRmwAt k arch mem pairs th dst a kind newv deps acq rel)
    (hd : DeadM mem th.vs th.promises t) : DeadM mem' th'.vs th'.promises t := by
  simp only [Promises.stepRmwAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨tr, _, h⟩ := h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    apply deadM_lock
    refine hd.mono (MemExt.rfl' _) hd.1 fun m _ hle => ?_
    show t ≤ (if m.loc = a then _ else _)
    split
    · rename_i he; rw [he] at hle; exact le_maxL hle
    · exact hle
  · simp only [List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        apply deadM_lock
        refine hd.mono (MemExt.push _ _) hd.1 fun m _ hle => ?_
        show t ≤ (if m.loc = a then _ else if m.loc = a then _ else _)
        split
        · exact Nat.le_of_lt hd.lt
        · exact hle
      · cases h
    · simp only [List.mem_filterMap] at h
      obtain ⟨tw, _, hf⟩ := h
      cases hm : mem[tw]? with
      | none => simp [hm] at hf
      | some pm =>
          simp only [hm, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
          obtain ⟨hcond, rfl, rfl⟩ := hf
          · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
            obtain ⟨⟨⟨⟨hl, -⟩, -⟩, hlt⟩, -⟩ := hcond
            have key : th.vs.coh a < tw := Nat.lt_of_le_of_lt (by maxle) hlt
            obtain ⟨htP, m0, hm0, hle0⟩ := hd
            have hne : t ≠ tw := by
              rintro rfl
              have e0 := Option.some.inj (hm.symm.trans hm0)
              subst e0
              rw [hl] at hle0
              exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hle0 key)
            apply deadM_lock
            refine ⟨(List.mem_erase_of_ne hne).2 htP, m0, hm0, ?_⟩
            show t ≤ (if m0.loc = a then tw else if m0.loc = a then _ else _)
            split
            · rename_i he; rw [he] at hle0
              exact Nat.le_of_lt (Nat.lt_of_le_of_lt hle0 key)
            · exact hle0

theorem stepRmw_dead {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool} {t : Ts}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs th dst a kind newv deps acq rel)
    (hd : DeadM mem th.vs th.promises t) : DeadM mem' th'.vs th'.promises t :=
  stepRmw_dead_at (th := if arch = .tso then Promises.stepFence th .sy else th) h (deadM_lock hd)

theorem stepStorePair_dead {mem : Memory} {pairs : List Ts} {th : Promises.Thread} {a : Address}
    {e0 e1 : WeakMem.Expr} {deps : List WeakMem.Reg} {rel : Bool} {t : Ts}
    (hd : DeadM mem th.vs th.promises t) :
    DeadM (Promises.stepStorePair mem pairs th a e0 e1 deps rel).1
      (Promises.stepStorePair mem pairs th a e0 e1 deps rel).2.2.vs
      (Promises.stepStorePair mem pairs th a e0 e1 deps rel).2.2.promises t := by
  obtain ⟨q1, -, q3, q4, -⟩ := TermMem.stepStorePair_eq mem pairs th a e0 e1 deps rel
  have hlt := hd.lt
  refine hd.mono (by rw [q1]; exact (MemExt.push _ _).trans (MemExt.push _ _)) (by rw [q4]; exact hd.1)
    fun m _ hle => ?_
  rw [q3]
  show t ≤ (if m.loc = a then _ else if m.loc = a.next then _ else _)
  split
  · exact Nat.le_of_lt hlt
  · split
    · exact Nat.le_succ_of_le (Nat.le_of_lt hlt)
    · exact hle

theorem rmwAdjacent_lt {mem : Memory} {a : Address} {tr tw : Ts}
    (h : WeakMem.rmwAdjacent mem a tr tw = true) : tr < tw := by
  simp only [WeakMem.rmwAdjacent, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- The pair RMW.  Its fulfil branch discharges `tw` and `tw + 1` but checks
`ob < tw` only against the first word's coherence; the second word's promise
cannot be dead all the same, because the second read `t1` is readable (so no
message at `a.next` lies in `(t1, coh a.next]`) and adjacent to `tw + 1`
(`t1 < tw + 1`). -/
theorem stepRmwPair_dead_at {arch : Arch} {mem mem' : Memory} {pairs pairs' : List Ts}
    {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address} {cmp0 cmp1 : Val}
    {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool} {t : Ts}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPairAt arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel)
    (hd : DeadM mem th.vs th.promises t) : DeadM mem' th'.vs th'.promises t := by
  simp only [Promises.stepRmwPairAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨t0, ⟨_, hr0⟩, t1, ⟨_, hr1⟩, h⟩ := h
  split at h
  · simp at h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    apply deadM_lock
    refine hd.mono (MemExt.rfl' _) hd.1 fun m _ hle => ?_
    show t ≤ (if m.loc = a then _ else if m.loc = a.next then _ else _)
    repeat' split
    all_goals first | exact hle | (rename_i he; rw [he] at hle; exact le_maxL hle)
  simp only [List.mem_append] at h
  rcases h with h | h
  · split at h
    · simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hlt := hd.lt
      apply deadM_lock
      refine hd.mono ((MemExt.push _ _).trans (MemExt.push _ _)) hd.1 fun m _ hle => ?_
      show t ≤ (if m.loc = a then _ else if m.loc = a.next then _ else _)
      split
      · exact Nat.le_of_lt hlt
      · split
        · exact Nat.le_succ_of_le (Nat.le_of_lt hlt)
        · exact hle
    · cases h
  · simp only [List.mem_filterMap] at h
    obtain ⟨tw, _, hf⟩ := h
    cases hm : mem[tw]? with
    | none => simp [hm] at hf
    | some pm0 =>
    cases hm1 : mem[tw + 1]? with
    | none => simp [hm, hm1] at hf
    | some pm1 =>
    simp only [hm, hm1, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨hcond, rfl, rfl, rfl⟩ := hf
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, hl0⟩, -⟩, -⟩, hl1⟩, -⟩, -⟩, hlt⟩, -⟩, hadj1⟩ := hcond
    have key : th.vs.coh a < tw := Nat.lt_of_le_of_lt (by maxle) hlt
    have k1 := rmwAdjacent_lt hadj1
    have hb1 := TermMem.coh_le_readBound arch th.vs (Promises.depBound th.regs deps) a.next
    obtain ⟨htP, m0, hm0, hle0⟩ := hd
    have hne0 : t ≠ tw := by
      rintro rfl
      have e0 := Option.some.inj (hm.symm.trans hm0)
      subst e0
      rw [hl0] at hle0
      exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hle0 key)
    have hne1 : t ≠ tw + 1 := by
      rintro rfl
      have e0 := Option.some.inj (hm1.symm.trans hm0)
      subst e0
      rw [hl1] at hle0
      have := readable_last hr1 hm1 hl1 (Nat.le_trans hle0 hb1)
      exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt this k1)
    apply deadM_lock
    refine ⟨(List.mem_erase_of_ne hne1).2 ((List.mem_erase_of_ne hne0).2 htP), m0, hm0, ?_⟩
    show t ≤ (if m0.loc = a then tw else if m0.loc = a.next then tw + 1 else _)
    split
    · rename_i he; rw [he] at hle0
      exact Nat.le_of_lt (Nat.lt_of_le_of_lt hle0 key)
    · split
      · rename_i he; rw [he] at hle0
        have := readable_last hr1 hm0 he (Nat.le_trans hle0 hb1)
        exact Nat.le_of_lt (Nat.lt_of_le_of_lt this k1)
      · repeat' split
        all_goals first | exact hle0 | (rename_i he; rw [he] at hle0; exact le_maxL hle0)

theorem stepRmwPair_dead {arch : Arch} {mem mem' : Memory} {pairs pairs' : List Ts}
    {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address} {cmp0 cmp1 : Val}
    {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool} {t : Ts}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel)
    (hd : DeadM mem th.vs th.promises t) : DeadM mem' th'.vs th'.promises t :=
  stepRmwPair_dead_at (th := if arch = .tso then Promises.stepFence th .sy else th) h (deadM_lock hd)

/-! ## §3 The state-level primitives -/

theorem DeadP.lt {s : St} {t : Ts} (h : DeadP s t) : t < s.mem.size := DeadM.lt h

theorem loadUnits_dead {arch : Arch} {pw : Word} {a : Address} {acq : Bool} {t : Ts} :
    ∀ (us : List Acc) (k : Nat) (s : St) (r : St × List Word), r ∈ loadUnits arch pw a acq us k s →
      DeadP s t → DeadP r.1 t
  | [], _, s, r, hr, hd => by
      simp only [loadUnits, List.mem_singleton] at hr; subst hr; exact hd
  | .one :: us, k, s, r, hr, hd => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, hth, ⟨s', ws⟩, hmem, rfl⟩ := hr
      exact loadUnits_dead us (k + 1) _ (s', ws) hmem
        ⟨hd.1, (stepLoad_dead (th := mth s pw pw pw) hth hd).2⟩
  | .two :: us, k, s, r, hr, hd => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, hth, ⟨s', ws⟩, hmem, rfl⟩ := hr
      exact loadUnits_dead us (k + 2) _ (s', ws) hmem
        ⟨hd.1, (stepLoadPair_dead (th := mth s pw pw pw) hth hd).2⟩

theorem storeUnits_dead {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool}
    {t : Ts} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s' ∈ storeUnits k arch pw a rel us ws i s →
      DeadP s t → DeadP s' t
  | [], _, _, s, s', hs, hd => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs; exact hd
  | .one :: us, w :: ws, i, s, s', hs, hd => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      exact storeUnits_dead us ws (i + 1) _ s' hs (stepStore_dead (th := mth s pw w w) hst hd)
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs, hd => by
      simp only [storeUnits] at hs
      have h2 := stepStorePair_dead (pairs := s.pairs) (th := mth s pw w0 w1) (a := offs a i)
        (e0 := dataE 1 w0) (e1 := dataE 2 w1) (deps := [0]) (rel := rel) hd
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
        (dataE 2 w1) [0] rel = R at h2 hs
      obtain ⟨mem', pairs', th⟩ := R
      exact storeUnits_dead us ws (i + 2) _ s' hs h2
  | .one :: _, [], _, _, s', hs, _ => by simp [storeUnits] at hs
  | .two :: _, [], _, _, s', hs, _ => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, s', hs, _ => by simp [storeUnits] at hs

theorem fenceS_dead {s : St} {f : WeakMem.Fence} {t : Ts} (hd : DeadP s t) : DeadP (fenceS s f) t := by
  show DeadM s.mem (Promises.stepFence (mth s _ _ _) f).vs s.promises t
  unfold DeadM; rw [stepFence_coh]; exact hd

/-- The cells `new` lays down: memory grows, and coherence at the new cells is
raised to them, above every existing message. -/
theorem allocPre_dead {s : St} {lbl : AllocLabel} {n : Nat} {f : Nat → Msg} {t : Ts}
    (hd : DeadP s t ∨ (t ∈ s.promises ∧ ∃ m o, s.mem[t]? = some m ∧ m.loc = ⟨lbl, o⟩ ∧ o < n)) :
    DeadP { s with mem := (List.range n).foldl (fun m j => m.push (f j)) s.mem,
                   vs := { s.vs with coh := fun b =>
                     if b.label = lbl ∧ b.offset < n then s.mem.size + b.offset else s.vs.coh b },
                   nalloc := s.nalloc + 1 } t := by
  have hext : MemExt s.mem ((List.range n).foldl (fun m j => m.push (f j)) s.mem) := by
    intro t' m' h'
    rw [TermMem.fold_get]
    simp only [TermMem.lt_of_get h', ↓reduceIte]
    exact h'
  rcases hd with hd | ⟨htP, m, o, hm, hl, ho⟩
  · have hlt := hd.lt
    refine hd.mono hext hd.1 fun m _ hle => ?_
    show t ≤ (if m.loc.label = lbl ∧ m.loc.offset < n then s.mem.size + m.loc.offset else s.vs.coh m.loc)
    split
    · exact Nat.le_trans (Nat.le_of_lt hlt) (Nat.le_add_right _ _)
    · exact hle
  · refine ⟨htP, m, hext t m hm, ?_⟩
    have hlt := TermMem.lt_of_get hm
    show t ≤ (if m.loc.label = lbl ∧ m.loc.offset < n then s.mem.size + m.loc.offset else s.vs.coh m.loc)
    split
    · exact Nat.le_trans (Nat.le_of_lt hlt) (Nat.le_add_right _ _)
    · rename_i hn; exact absurd (by rw [hl]; exact ⟨rfl, ho⟩) hn

theorem alloc_pres {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc}
    {ws : List Word} {s : St} {t : Ts} {r : St × Word} (hr : r ∈ alloc k arch lbl us ws s)
    (hd : DeadP s t) : DeadP r.1 t := by
  simp only [alloc, List.mem_map] at hr
  obtain ⟨s', hs, rfl⟩ := hr
  exact storeUnits_dead us ws 0 _ s' hs (allocPre_dead (Or.inl hd))

/-- **Fact (f).**  A promise made before an allocation, at the allocated
label, is dead afterwards: `new` raises coherence at its cells to the fresh
undef messages, above every existing message. -/
theorem alloc_dead {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc}
    {ws : List Word} {s : St} {t : Ts} {m : Msg} {o : Nat} {r : St × Word}
    (hr : r ∈ alloc k arch lbl us ws s) (ht : t ∈ s.promises) (hm : s.mem[t]? = some m)
    (hl : m.loc = ⟨lbl, o⟩) (ho : o < nWords us) : DeadP r.1 t := by
  simp only [alloc, List.mem_map] at hr
  obtain ⟨s', hs, rfl⟩ := hr
  exact storeUnits_dead us ws 0 _ s' hs (allocPre_dead (Or.inr ⟨ht, m, o, hm, hl, ho⟩))

theorem allocBuf_pres {lbl : AllocLabel} {n : Nat} {zero : Option (List Val)} {s : St} {t : Ts}
    (hd : DeadP s t) : DeadP (allocBuf lbl n zero s).1 t :=
  allocPre_dead (Or.inl hd)

/-- Fact (f) for buffers. -/
theorem allocBuf_dead {lbl : AllocLabel} {n : Nat} {zero : Option (List Val)} {s : St} {t : Ts}
    {m : Msg} {o : Nat} (ht : t ∈ s.promises) (hm : s.mem[t]? = some m)
    (hl : m.loc = ⟨lbl, o⟩) (ho : o < n) : DeadP (allocBuf lbl n zero s).1 t :=
  allocPre_dead (Or.inr ⟨ht, m, o, hm, hl, ho⟩)

theorem injM_dead {g : G} {s : St} {ty : Ty} {j : Nat} {p : List Word} {t : Ts}
    {r : St × List Word} (h : r ∈ injM g s ty j p) (hd : DeadP s t) : DeadP r.1 t := by
  unfold injM at h
  split at h
  · split at h
    · simp only [List.mem_map] at h
      obtain ⟨⟨s', pw⟩, hs, rfl⟩ := h
      have := alloc_pres hs hd
      dsimp only
      split
      · exact fenceS_dead this
      · exact this
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact hd

theorem projM_dead {g : G} {s : St} {ty : Ty} {ws : List Word} {t : Ts}
    {r : St × Nat × List Word} (h : r ∈ projM g s ty ws) (hd : DeadP s t) : DeadP r.1 t := by
  unfold projM at h
  split at h
  · split at h
    · split at h
      · simp only [List.mem_flatMap] at h
        obtain ⟨⟨s1, tw⟩, h1, h⟩ := h
        have d1 := loadUnits_dead _ _ _ _ h1 hd
        repeat' split at h
        all_goals first
          | (simp at h; done)
          | (simp only [List.mem_map] at h
             obtain ⟨⟨s2, p⟩, h2, rfl⟩ := h
             exact loadUnits_dead _ _ _ _ h2 d1)
      · cases h
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact hd

theorem evalOp_dead {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op} {t : Ts}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s op) (hd : DeadP s t) : DeadP r.1 t := by
  cases op <;> simp only [evalOp] at h
  all_goals (try simp only [ol, bind, Option.bind, pure, Option.map] at h)
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h
       first | exact hd | exact fenceS_dead hd | exact allocBuf_pres hd)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact loadUnits_dead _ _ _ _ hx hd
         | exact storeUnits_dead _ _ _ _ _ hx hd
         | exact alloc_pres hx hd
         | exact stepRmw_dead (th := mth s _ _ _) hx hd)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       first
         | exact injM_dead hy (projM_dead hx hd)
         | exact storeUnits_dead _ _ _ _ _ hy (loadUnits_dead _ _ _ _ hx hd))
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       have d1 := loadUnits_dead _ _ _ _ hx hd
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         exact storeUnits_dead _ _ _ _ _ hy d1
       · simp at h)
    | (simp only [List.mem_filterMap] at h
       obtain ⟨x, hx, h⟩ := h
       have d1 := loadUnits_dead _ _ _ _ hx hd
       cases hn : numOf x.2 <;> simp [hn] at h
       subst h; exact d1)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h; dsimp only; exact allocBuf_pres hd)

/-! ## §4 A thread step -/

theorem enter_eq {g : G} {th th' : TTh} {f : String} {ts : List Ty} {a : At}
    (h : enter g th f ts a = some th') : th'.vs = th.vs ∧ th'.promises = th.promises := by
  unfold enter at h
  simp only [bind, Option.bind] at h
  repeat' (first | (split at h) | (dsimp only at h; split at h))
  all_goals first
    | (simp at h; done)
    | (simp only [pure, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩)
    | (simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩)

/-- **A thread step keeps a dead promise dead.** -/
theorem tstep_dead {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {t : Ts}
    {r : Memory × List Ts × TTh} (h : r ∈ tstep g mem pairs th)
    (hd : DeadP (stOf mem pairs th) t) : DeadP (stOf r.1 r.2.1 r.2.2) t := by
  simp only [tstep] at h
  split at h
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_singleton] at h; subst h; exact hd)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
       obtain ⟨th', ⟨fr, -, he⟩, rfl⟩ := h
       obtain ⟨h1, h2⟩ := enter_eq he
       show DeadM mem th'.vs th'.promises t
       rw [h1, h2]; exact hd)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
       obtain ⟨th', he, rfl⟩ := h
       obtain ⟨h1, h2⟩ := enter_eq he
       show DeadM mem th'.vs th'.promises t
       rw [h1, h2]; exact hd)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact evalOp_dead hx hd
         | (split <;> exact evalOp_dead hx hd)
         | exact stepRmw_dead (th := mth _ _ _ _) hx hd
         | exact stepRmwPair_dead (th := mth _ _ _ _) hx hd)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       exact injM_dead hy (projM_dead hx hd))
    | fail "T"

/-! ## §5 The machine -/

/-- Thread `i` of `c` has the dead promise `t`. -/
def DeadAt (c : Cfg) (i : Nat) (t : Ts) : Prop :=
  ∃ th, c.ths[i]? = some th ∧ DeadP (stOf c.mem c.pairs th) t

theorem arr_lt {α : Type} {xs : Array α} {i : Nat} {x : α} (h : xs[i]? = some x) : i < xs.size := by
  apply Nat.lt_of_not_le
  intro hn
  rw [Array.getElem?_eq_none hn] at h
  cases h

theorem arr_set {α : Type} {xs : Array α} {i : Nat} {x y : α} (h : xs[i]? = some x) :
    (xs.set! i y)[i]? = some y := by
  have hi := arr_lt h
  simp [hi]

theorem threadSteps_dead {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat} {t : Ts}
    (h : c' ∈ threadSteps p k arch c i) (hd : DeadAt c i t) : DeadAt c' i t := by
  obtain ⟨th, hth, hd⟩ := hd
  simp only [threadSteps, hth, List.mem_map] at h
  obtain ⟨⟨mem, pairs, th'⟩, hr, rfl⟩ := h
  exact ⟨th', arr_set hth, tstep_dead hr hd⟩

theorem promise_dead {c : Cfg} {i : Nat} {a : Address} {v : Val} {w : Ts} {t : Ts}
    (hd : DeadAt c i t) : DeadAt (promise c i a v w) i t := by
  obtain ⟨th, hth, hd⟩ := hd
  refine ⟨{ th with promises := th.promises ++ [c.mem.size] }, ?_, ?_⟩
  · simp only [promise, hth]; exact arr_set hth
  · simp only [promise, hth]
    exact hd.mono (MemExt.push _ _) (List.mem_append_left _ hd.1) fun _ _ h => h

/-- **Solo runs keep a dead promise dead.** -/
theorem solo_dead {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c c' : Cfg} {t : Ts}
    (h : Solo p k arch i c c') (hd : DeadAt c i t) : DeadAt c' i t := by
  induction h with
  | refl => exact hd
  | thread hs _ ih => exact ih (threadSteps_dead hs hd)
  | prom _ _ _ _ _ ih => exact ih (promise_dead hd)
  | ext hs _ ih =>
      obtain ⟨th, hth, hd⟩ := hd
      obtain ⟨th0, th', h0, h1, hst, hv⟩ := extSteps_vle hs
      rw [hth] at h0; cases h0
      exact ih ⟨th', h1, by rw [hst]; exact DeadM.mono hd (MemExt.rfl' _) hd.1 fun _ _ hle => Nat.le_trans hle (hv.coh _)⟩

/-- **A certified thread has no dead promise.** -/
theorem certified_noDead {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {t : Ts}
    (hc : Certified p k arch c i) : ¬ DeadAt c i t := by
  intro hd
  obtain ⟨c', hs, hn⟩ := hc
  obtain ⟨th, hth, hd'⟩ := solo_dead hs hd
  simp only [noPromises, hth, Option.map_some, Option.getD_some, List.isEmpty_iff] at hn
  have h1 : t ∈ th.promises := hd'.1
  rw [hn] at h1
  cases h1

/-- **L1 (coherence part).**  In a certified configuration every outstanding
promise of thread `i` is strictly above `i`'s coherence view at its address. -/
theorem certified_promAbove {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat}
    {th : TTh} {t : Ts} {m : Msg} (hc : Certified p k arch c i) (hth : c.ths[i]? = some th)
    (ht : t ∈ th.promises) (hm : c.mem[t]? = some m) : th.vs.coh m.loc < t :=
  Nat.lt_of_not_le fun hle => certified_noDead hc ⟨th, hth, ht, m, hm, hle⟩

/-- **Fact (f), machine form.**  If thread `i`'s state in a certified
configuration is the result of an allocation of `lbl`, no promise of `i` made
before the allocation is at `lbl` (within the allocated words). -/
theorem certified_alloc_noProm {p : Prog} {k k' : Promises.Knobs} {arch arch' : Arch} {c : Cfg}
    {i : Nat} {th : TTh} {lbl : AllocLabel} {us : List Acc} {ws : List Word} {s : St}
    {r : St × Word} {t : Ts} {m : Msg} {o : Nat}
    (hc : Certified p k arch c i) (hth : c.ths[i]? = some th)
    (hr : r ∈ alloc k' arch' lbl us ws s) (hst : stOf c.mem c.pairs th = r.1)
    (ht : t ∈ s.promises) (hm : s.mem[t]? = some m) (hl : m.loc = ⟨lbl, o⟩) (ho : o < nWords us) :
    False :=
  certified_noDead hc ⟨th, hth, hst ▸ alloc_dead hr ht hm hl ho⟩

#print axioms stepStore_dead
#print axioms stepRmw_dead
#print axioms stepRmwPair_dead
#print axioms alloc_dead
#print axioms allocBuf_dead
#print axioms evalOp_dead
#print axioms tstep_dead
#print axioms solo_dead
#print axioms certified_noDead
#print axioms certified_promAbove
#print axioms certified_alloc_noProm

/-! ## §6 L1, the rest: the monotone part of `storeOb`

`storeOb`'s base is `max (max vPreBase dTs) (max vCtrl (coh a))`, plus
`max vRd vWr` on TSO with `tsoStoreOrder`.  `dTs` is per-store; the rest is
the thread's own view and never decreases through a step (`VLe`): `vPreBase`
only grows (acquire loads, fences), `vCtrl` is never written by `TermRun`, and
`vRd`/`vWr` only grow.  So a promise at or below `obLow` can never be
fulfilled, by any store or RMW, at any address.  (`vRd`/`vWr` are *not* below
an ARM promise: ARM's `storeOb` omits them.) -/

/-- The part of every write's `ob` that depends only on the thread's views. -/
def obLow (k : Promises.Knobs) (arch : Arch) (vs : VState) : Ts :=
  if (arch = .tso && k.tsoStoreOrder) = true then max (max vs.vPreBase vs.vCtrl) (max vs.vRd vs.vWr)
  else max vs.vPreBase vs.vCtrl

/-- The monotone views. -/
def VLe (v w : VState) : Prop :=
  v.vPreBase ≤ w.vPreBase ∧ v.vCtrl ≤ w.vCtrl ∧ v.vRd ≤ w.vRd ∧ v.vWr ≤ w.vWr

theorem VLe.rfl' (v : VState) : VLe v v :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem VLe.trans {u v w : VState} (h1 : VLe u v) (h2 : VLe v w) : VLe u w :=
  ⟨Nat.le_trans h1.1 h2.1, Nat.le_trans h1.2.1 h2.2.1, Nat.le_trans h1.2.2.1 h2.2.2.1,
    Nat.le_trans h1.2.2.2 h2.2.2.2⟩

theorem max_le_max' {a b c d : Nat} (h1 : a ≤ c) (h2 : b ≤ d) : max a b ≤ max c d :=
  Nat.max_le.2 ⟨le_maxL h1, le_maxR h2⟩

theorem obLow_mono {k : Promises.Knobs} {arch : Arch} {v w : VState} (h : VLe v w) :
    obLow k arch v ≤ obLow k arch w := by
  unfold obLow
  split
  · exact max_le_max' (max_le_max' h.1 h.2.1) (max_le_max' h.2.2.1 h.2.2.2)
  · exact max_le_max' h.1 h.2.1

/-- Close `max … ≤ e` by splitting the left `max`es and finding each part in `e`. -/
syntax "maxle2" : tactic
macro_rules
  | `(tactic| maxle2) => `(tactic| first
      | maxle
      | (apply Nat.max_le.2; constructor <;> maxle2))

/-- Close `VLe v w` for a rule's update of `v`. -/
syntax "vle" : tactic
macro_rules
  | `(tactic| vle) => `(tactic| (refine ⟨?_, ?_, ?_, ?_⟩ <;> (try dsimp only) <;> maxle))

/-- Close `obLow k arch vs ≤ ob` for a rule's `ob`. -/
syntax "oble" : tactic
macro_rules
  | `(tactic| oble) => `(tactic| (unfold obLow; split <;> (try split) <;>
      first | maxle2 | (exfalso; simp_all)))

/-- `t` is an outstanding promise at or below the monotone part of `ob`. -/
def DeadOM (k : Promises.Knobs) (arch : Arch) (mem : Memory) (vs : VState) (P : List Ts) (t : Ts) :
    Prop :=
  t ∈ P ∧ ∃ m, mem[t]? = some m ∧ t ≤ obLow k arch vs

def DeadO (k : Promises.Knobs) (arch : Arch) (s : St) (t : Ts) : Prop :=
  DeadOM k arch s.mem s.vs s.promises t

theorem DeadOM.mono {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {vs vs' : VState}
    {P P' : List Ts} {t : Ts} (h : DeadOM k arch mem vs P t) (hm : MemExt mem mem') (hp : t ∈ P')
    (hv : VLe vs vs') : DeadOM k arch mem' vs' P' t := by
  obtain ⟨_, m, hm1, hm2⟩ := h
  exact ⟨hp, m, hm t m hm1, Nat.le_trans hm2 (obLow_mono hv)⟩

theorem stepFence_vle (th : Promises.Thread) (f : WeakMem.Fence) :
    VLe th.vs (Promises.stepFence th f).vs := by
  cases f <;> vle

theorem deadOM_lock {k : Promises.Knobs} {arch arch' : Arch} {mem : Memory} {x : Promises.Thread}
    {t : Ts} (h : DeadOM k arch mem x.vs x.promises t) :
    DeadOM k arch mem (if arch' = .tso then Promises.stepFence x .sy else x).vs
      (if arch' = .tso then Promises.stepFence x .sy else x).promises t := by
  split
  · exact h.mono (MemExt.rfl' _) (by rw [stepFence_prom]; exact h.1) (stepFence_vle x .sy)
  · exact h

theorem obLow_le {k : Promises.Knobs} {arch : Arch} {vs : VState} {x : Nat}
    (h1 : vs.vPreBase ≤ x) (h2 : vs.vCtrl ≤ x)
    (h3 : arch = .tso → k.tsoStoreOrder = true → vs.vRd ≤ x ∧ vs.vWr ≤ x) : obLow k arch vs ≤ x := by
  unfold obLow
  split
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨h4, h5⟩ := h3 hc.1 hc.2
    exact Nat.max_le.2 ⟨Nat.max_le.2 ⟨h1, h2⟩, Nat.max_le.2 ⟨h4, h5⟩⟩
  · exact Nat.max_le.2 ⟨h1, h2⟩

theorem obLow_le_storeOb (k : Promises.Knobs) (arch : Arch) (th : Promises.Thread) (a : Address)
    (e : WeakMem.Expr) (deps : List WeakMem.Reg) :
    obLow k arch th.vs ≤ Promises.storeOb k arch th a e deps := by
  simp only [Promises.storeOb]
  oble

theorem stepLoad_deadO {k : Promises.Knobs} {arch arch' : Arch} {mem : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {deps : List WeakMem.Reg}
    {acq : Bool} {t : Ts}
    (h : th' ∈ Promises.stepLoad arch' mem pairs th dst a deps acq)
    (hd : DeadOM k arch mem th.vs th.promises t) : DeadOM k arch mem th'.vs th'.promises t := by
  simp only [Promises.stepLoad, List.mem_map, List.mem_filter, List.mem_range] at h
  obtain ⟨tr, _, rfl⟩ := h
  exact hd.mono (MemExt.rfl' _) hd.1 (by vle)

theorem stepLoadPair_deadO {k : Promises.Knobs} {arch arch' : Arch} {mem : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address} {deps : List WeakMem.Reg}
    {acq : Bool} {t : Ts}
    (h : th' ∈ Promises.stepLoadPair arch' mem pairs th dst0 dst1 a deps acq)
    (hd : DeadOM k arch mem th.vs th.promises t) : DeadOM k arch mem th'.vs th'.promises t := by
  simp only [Promises.stepLoadPair, List.mem_flatMap, List.mem_filterMap, List.mem_filter,
    List.mem_range] at h
  obtain ⟨t0, _, t1, _, hs⟩ := h
  split at hs
  · cases hs
  · simp only [Option.some.injEq] at hs
    subst hs
    exact hd.mono (MemExt.rfl' _) hd.1 (by vle)

theorem stepStore_deadO {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory}
    {th th' : Promises.Thread} {a : Address} {e : WeakMem.Expr} {deps : List WeakMem.Reg}
    {rel : Bool} {t : Ts}
    (h : (mem', th') ∈ Promises.stepStore k arch mem th a e deps rel)
    (hd : DeadOM k arch mem th.vs th.promises t) : DeadOM k arch mem' th'.vs th'.promises t := by
  have hob := obLow_le_storeOb k arch th a e deps
  cases e <;>
  · simp only [Promises.stepStore, List.mem_append, List.mem_singleton, List.mem_filterMap] at h
    rcases h with h | ⟨tw, _, hf⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hd.mono (MemExt.push _ _) hd.1 (by vle)
    · cases hm : mem[tw]? with
      | none => simp [hm] at hf
      | some pm =>
          simp only [hm] at hf
          split at hf
          · rename_i hcond
            simp only [Option.some.injEq, Prod.mk.injEq] at hf
            obtain ⟨rfl, rfl⟩ := hf
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
            obtain ⟨-, hlt⟩ := hcond
            have hne : t ≠ tw := by
              rintro rfl
              obtain ⟨_, _, _, hle⟩ := hd
              exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_trans hle hob) hlt)
            exact hd.mono (MemExt.rfl' _) ((List.mem_erase_of_ne hne).2 hd.1) (by vle)
          · simp at hf

theorem stepStorePair_deadO {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts}
    {th : Promises.Thread} {a : Address} {e0 e1 : WeakMem.Expr} {deps : List WeakMem.Reg}
    {rel : Bool} {t : Ts} (hd : DeadOM k arch mem th.vs th.promises t) :
    DeadOM k arch (Promises.stepStorePair mem pairs th a e0 e1 deps rel).1
      (Promises.stepStorePair mem pairs th a e0 e1 deps rel).2.2.vs
      (Promises.stepStorePair mem pairs th a e0 e1 deps rel).2.2.promises t := by
  simp only [Promises.stepStorePair]
  exact hd.mono ((MemExt.push _ _).trans (MemExt.push _ _)) hd.1 (by vle)

theorem stepRmw_deadO_at {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool} {t : Ts}
    (h : (mem', th') ∈ Promises.stepRmwAt k arch mem pairs th dst a kind newv deps acq rel)
    (hd : DeadOM k arch mem th.vs th.promises t) : DeadOM k arch mem' th'.vs th'.promises t := by
  simp only [Promises.stepRmwAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨tr, _, h⟩ := h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    apply deadOM_lock
    exact hd.mono (MemExt.rfl' _) hd.1 (by vle)
  · simp only [List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        apply deadOM_lock
        exact hd.mono (MemExt.push _ _) hd.1 (by vle)
      · cases h
    · simp only [List.mem_filterMap] at h
      obtain ⟨tw, _, hf⟩ := h
      cases hm : mem[tw]? with
      | none => simp [hm] at hf
      | some pm =>
          simp only [hm, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
          obtain ⟨hcond, rfl, rfl⟩ := hf
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
          obtain ⟨⟨-, hlt⟩, -⟩ := hcond
          have key : obLow k arch th.vs < tw := Nat.lt_of_le_of_lt (by oble) hlt
          have hne : t ≠ tw := by
            rintro rfl
            obtain ⟨_, _, _, hle⟩ := hd
            exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hle key)
          apply deadOM_lock
          exact hd.mono (MemExt.rfl' _) ((List.mem_erase_of_ne hne).2 hd.1) (by vle)

theorem stepRmw_deadO {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool} {t : Ts}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs th dst a kind newv deps acq rel)
    (hd : DeadOM k arch mem th.vs th.promises t) : DeadOM k arch mem' th'.vs th'.promises t :=
  stepRmw_deadO_at (th := if arch = .tso then Promises.stepFence th .sy else th) h (deadOM_lock hd)

theorem stepRmwPair_deadO_at {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory}
    {pairs pairs' : List Ts} {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address}
    {cmp0 cmp1 : Val} {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool} {t : Ts}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPairAt arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel)
    (hd : DeadOM k arch mem th.vs th.promises t) : DeadOM k arch mem' th'.vs th'.promises t := by
  simp only [Promises.stepRmwPairAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨t0, _, t1, _, h⟩ := h
  split at h
  · simp at h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    apply deadOM_lock
    exact hd.mono (MemExt.rfl' _) hd.1 (by vle)
  simp only [List.mem_append] at h
  rcases h with h | h
  · split at h
    · simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      apply deadOM_lock
      exact hd.mono ((MemExt.push _ _).trans (MemExt.push _ _)) hd.1 (by vle)
    · cases h
  · simp only [List.mem_filterMap] at h
    obtain ⟨tw, _, hf⟩ := h
    cases hm : mem[tw]? with
    | none => simp [hm] at hf
    | some pm0 =>
    cases hm1 : mem[tw + 1]? with
    | none => simp [hm, hm1] at hf
    | some pm1 =>
    simp only [hm, hm1, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨hcond, rfl, rfl, rfl⟩ := hf
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
    obtain ⟨⟨⟨-, hlt⟩, -⟩, -⟩ := hcond
    have key : obLow k arch th.vs < tw := Nat.lt_of_le_of_lt
      (obLow_le (by maxle) (by maxle) (fun ha _ => by subst ha; simp only [↓reduceIte]; exact ⟨by maxle, by maxle⟩))
      hlt
    have hne0 : t ≠ tw := by
      rintro rfl
      obtain ⟨_, _, _, hle⟩ := hd
      exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hle key)
    have hne1 : t ≠ tw + 1 := by
      rintro rfl
      obtain ⟨_, _, _, hle⟩ := hd
      exact Nat.lt_irrefl _ (Nat.lt_trans (Nat.lt_of_le_of_lt hle key) (Nat.lt_succ_self _))
    apply deadOM_lock
    exact hd.mono (MemExt.rfl' _)
      ((List.mem_erase_of_ne hne1).2 ((List.mem_erase_of_ne hne0).2 hd.1)) (by vle)

theorem stepRmwPair_deadO {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory}
    {pairs pairs' : List Ts} {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address}
    {cmp0 cmp1 : Val} {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool} {t : Ts}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel)
    (hd : DeadOM k arch mem th.vs th.promises t) : DeadOM k arch mem' th'.vs th'.promises t :=
  stepRmwPair_deadO_at (th := if arch = .tso then Promises.stepFence th .sy else th) h (deadOM_lock hd)

/-! ### The state-level primitives, for `DeadO` -/

theorem loadUnits_deadO {k : Promises.Knobs} {arch arch' : Arch} {pw : Word} {a : Address}
    {acq : Bool} {t : Ts} :
    ∀ (us : List Acc) (n : Nat) (s : St) (r : St × List Word), r ∈ loadUnits arch' pw a acq us n s →
      DeadO k arch s t → DeadO k arch r.1 t
  | [], _, s, r, hr, hd => by
      simp only [loadUnits, List.mem_singleton] at hr; subst hr; exact hd
  | .one :: us, n, s, r, hr, hd => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, hth, ⟨s', ws⟩, hmem, rfl⟩ := hr
      exact loadUnits_deadO us (n + 1) _ (s', ws) hmem
        ⟨hd.1, (stepLoad_deadO (th := mth s pw pw pw) hth hd).2⟩
  | .two :: us, n, s, r, hr, hd => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, hth, ⟨s', ws⟩, hmem, rfl⟩ := hr
      exact loadUnits_deadO us (n + 2) _ (s', ws) hmem
        ⟨hd.1, (stepLoadPair_deadO (th := mth s pw pw pw) hth hd).2⟩

theorem storeUnits_deadO {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool}
    {t : Ts} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s' ∈ storeUnits k arch pw a rel us ws i s →
      DeadO k arch s t → DeadO k arch s' t
  | [], _, _, s, s', hs, hd => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs; exact hd
  | .one :: us, w :: ws, i, s, s', hs, hd => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      exact storeUnits_deadO us ws (i + 1) _ s' hs (stepStore_deadO (th := mth s pw w w) hst hd)
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs, hd => by
      simp only [storeUnits] at hs
      have h2 := stepStorePair_deadO (pairs := s.pairs) (th := mth s pw w0 w1) (a := offs a i)
        (e0 := dataE 1 w0) (e1 := dataE 2 w1) (deps := [0]) (rel := rel) hd
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
        (dataE 2 w1) [0] rel = R at h2 hs
      obtain ⟨mem', pairs', th⟩ := R
      exact storeUnits_deadO us ws (i + 2) _ s' hs h2
  | .one :: _, [], _, _, s', hs, _ => by simp [storeUnits] at hs
  | .two :: _, [], _, _, s', hs, _ => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, s', hs, _ => by simp [storeUnits] at hs

theorem fenceS_deadO {k : Promises.Knobs} {arch : Arch} {s : St} {f : WeakMem.Fence} {t : Ts}
    (hd : DeadO k arch s t) : DeadO k arch (fenceS s f) t :=
  DeadOM.mono hd (MemExt.rfl' _) hd.1 (stepFence_vle (mth s _ _ _) f)

theorem fold_ext (f : Nat → Msg) (n : Nat) (M : Memory) :
    MemExt M ((List.range n).foldl (fun m j => m.push (f j)) M) := by
  intro t' m' h'
  rw [TermMem.fold_get]
  simp only [TermMem.lt_of_get h', ↓reduceIte]
  exact h'

theorem alloc_presO {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc}
    {ws : List Word} {s : St} {t : Ts} {r : St × Word} (hr : r ∈ alloc k arch lbl us ws s)
    (hd : DeadO k arch s t) : DeadO k arch r.1 t := by
  simp only [alloc, List.mem_map] at hr
  obtain ⟨s', hs, rfl⟩ := hr
  -- `new` raises `vWr` to the last message in memory (runtime obligation R11)
  exact storeUnits_deadO us ws 0 _ s' hs (DeadOM.mono hd (fold_ext _ _ _) hd.1
    ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
      show s.vs.vWr ≤ max s.vs.vWr (s.mem.size + nWords us - 1) from Nat.le_max_left _ _⟩)

theorem allocBuf_presO {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {n : Nat}
    {zero : Option (List Val)} {s : St} {t : Ts}
    (hd : DeadO k arch s t) : DeadO k arch (allocBuf lbl n zero s).1 t :=
  DeadOM.mono hd (fold_ext _ _ _) hd.1 ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, by
    -- `newBuf` raises `vWr` to the last message in memory (runtime obligation R11)
    show s.vs.vWr ≤ max s.vs.vWr (s.mem.size + n - 1)
    exact Nat.le_max_left _ _⟩

theorem injM_deadO {g : G} {s : St} {ty : Ty} {j : Nat} {p : List Word} {t : Ts}
    {r : St × List Word} (h : r ∈ injM g s ty j p) (hd : DeadO g.k g.arch s t) :
    DeadO g.k g.arch r.1 t := by
  unfold injM at h
  split at h
  · split at h
    · simp only [List.mem_map] at h
      obtain ⟨⟨s', pw⟩, hs, rfl⟩ := h
      have := alloc_presO hs hd
      dsimp only
      split
      · exact fenceS_deadO this
      · exact this
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact hd

theorem projM_deadO {k : Promises.Knobs} {arch : Arch} {g : G} {s : St} {ty : Ty} {ws : List Word}
    {t : Ts} {r : St × Nat × List Word} (h : r ∈ projM g s ty ws) (hd : DeadO k arch s t) :
    DeadO k arch r.1 t := by
  unfold projM at h
  split at h
  · split at h
    · split at h
      · simp only [List.mem_flatMap] at h
        obtain ⟨⟨s1, tw⟩, h1, h⟩ := h
        have d1 := loadUnits_deadO _ _ _ _ h1 hd
        repeat' split at h
        all_goals first
          | (simp at h; done)
          | (simp only [List.mem_map] at h
             obtain ⟨⟨s2, p⟩, h2, rfl⟩ := h
             exact loadUnits_deadO _ _ _ _ h2 d1)
      · cases h
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact hd

theorem evalOp_deadO {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op} {t : Ts}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s op) (hd : DeadO g.k g.arch s t) :
    DeadO g.k g.arch r.1 t := by
  cases op <;> simp only [evalOp] at h
  all_goals (try simp only [ol, bind, Option.bind, pure, Option.map] at h)
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h
       first | exact hd | exact fenceS_deadO hd | exact allocBuf_presO hd)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact loadUnits_deadO _ _ _ _ hx hd
         | exact storeUnits_deadO _ _ _ _ _ hx hd
         | exact alloc_presO hx hd
         | exact stepRmw_deadO (th := mth s _ _ _) hx hd)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       first
         | exact injM_deadO hy (projM_deadO hx hd)
         | exact storeUnits_deadO _ _ _ _ _ hy (loadUnits_deadO _ _ _ _ hx hd))
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       have d1 := loadUnits_deadO _ _ _ _ hx hd
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         exact storeUnits_deadO _ _ _ _ _ hy d1
       · simp at h)
    | (simp only [List.mem_filterMap] at h
       obtain ⟨x, hx, h⟩ := h
       have d1 := loadUnits_deadO _ _ _ _ hx hd
       cases hn : numOf x.2 <;> simp [hn] at h
       subst h; exact d1)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h; dsimp only; exact allocBuf_presO hd)

theorem tstep_deadO {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {t : Ts}
    {r : Memory × List Ts × TTh} (h : r ∈ tstep g mem pairs th)
    (hd : DeadO g.k g.arch (stOf mem pairs th) t) : DeadO g.k g.arch (stOf r.1 r.2.1 r.2.2) t := by
  simp only [tstep] at h
  split at h
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_singleton] at h; subst h; exact hd)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
       obtain ⟨th', ⟨fr, -, he⟩, rfl⟩ := h
       obtain ⟨h1, h2⟩ := enter_eq he
       show DeadOM g.k g.arch mem th'.vs th'.promises t
       rw [h1, h2]; exact hd)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
       obtain ⟨th', he, rfl⟩ := h
       obtain ⟨h1, h2⟩ := enter_eq he
       show DeadOM g.k g.arch mem th'.vs th'.promises t
       rw [h1, h2]; exact hd)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact evalOp_deadO hx hd
         | (split <;> exact evalOp_deadO hx hd)
         | exact stepRmw_deadO (th := mth _ _ _ _) hx hd
         | exact stepRmwPair_deadO (th := mth _ _ _ _) hx hd)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       exact injM_deadO hy (projM_deadO hx hd))

/-! ### The machine -/

def DeadAtO (k : Promises.Knobs) (arch : Arch) (c : Cfg) (i : Nat) (t : Ts) : Prop :=
  ∃ th, c.ths[i]? = some th ∧ DeadO k arch (stOf c.mem c.pairs th) t

theorem threadSteps_deadO {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat}
    {t : Ts} (h : c' ∈ threadSteps p k arch c i) (hd : DeadAtO k arch c i t) : DeadAtO k arch c' i t := by
  obtain ⟨th, hth, hd⟩ := hd
  simp only [threadSteps, hth, List.mem_map] at h
  obtain ⟨⟨mem, pairs, th'⟩, hr, rfl⟩ := h
  exact ⟨th', arr_set hth, tstep_deadO (g := gOf p k arch c i) hr hd⟩

theorem promise_deadO {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {a : Address} {v : Val}
    {w : Ts} {t : Ts} (hd : DeadAtO k arch c i t) : DeadAtO k arch (promise c i a v w) i t := by
  obtain ⟨th, hth, hd⟩ := hd
  refine ⟨{ th with promises := th.promises ++ [c.mem.size] }, ?_, ?_⟩
  · simp only [promise, hth]; exact arr_set hth
  · simp only [promise, hth]
    exact hd.mono (MemExt.push _ _) (List.mem_append_left _ hd.1) (VLe.rfl' _)

theorem solo_deadO {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c c' : Cfg} {t : Ts}
    (h : Solo p k arch i c c') (hd : DeadAtO k arch c i t) : DeadAtO k arch c' i t := by
  induction h with
  | refl => exact hd
  | thread hs _ ih => exact ih (threadSteps_deadO hs hd)
  | prom _ _ _ _ _ ih => exact ih (promise_deadO hd)
  | ext hs _ ih =>
      obtain ⟨th, hth, hd⟩ := hd
      obtain ⟨th0, th', h0, h1, hst, hv⟩ := extSteps_vle hs
      rw [hth] at h0; cases h0
      exact ih ⟨th', h1, by rw [hst]; exact DeadOM.mono hd (MemExt.rfl' _) hd.1 ⟨hv.vPreBase, hv.vCtrl, hv.vRd, hv.vWr⟩⟩

theorem certified_noDeadO {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {t : Ts}
    (hc : Certified p k arch c i) : ¬ DeadAtO k arch c i t := by
  intro hd
  obtain ⟨c', hs, hn⟩ := hc
  obtain ⟨th, hth, hd'⟩ := solo_deadO hs hd
  simp only [noPromises, hth, Option.map_some, Option.getD_some, List.isEmpty_iff] at hn
  have h1 : t ∈ th.promises := hd'.1
  rw [hn] at h1
  cases h1

/-- **L1 (the monotone part of `ob`).**  In a certified configuration every
outstanding promise of thread `i` is strictly above `obLow`: above `vPreBase`
and `vCtrl`, and on TSO with `tsoStoreOrder` above `vRd` and `vWr` too. -/
theorem certified_obAbove {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat}
    {th : TTh} {t : Ts} {m : Msg} (hc : Certified p k arch c i) (hth : c.ths[i]? = some th)
    (ht : t ∈ th.promises) (hm : c.mem[t]? = some m) : obLow k arch th.vs < t :=
  Nat.lt_of_not_le fun hle => certified_noDeadO hc ⟨th, hth, ht, m, hm, hle⟩

theorem le_obLow_base (k : Promises.Knobs) (arch : Arch) (vs : VState) :
    max vs.vPreBase vs.vCtrl ≤ obLow k arch vs := by
  unfold obLow; split
  · exact le_maxL (Nat.le_refl _)
  · exact Nat.le_refl _

theorem le_obLow_tso (k : Promises.Knobs) (vs : VState) (hk : k.tsoStoreOrder = true) :
    max vs.vRd vs.vWr ≤ obLow k .tso vs := by
  unfold obLow
  split
  · exact le_maxR (Nat.le_refl _)
  · rename_i hn; exact absurd (by simp [hk]) hn

/-- **L1, all of it, every architecture**: an outstanding promise of a
certified thread is above its `vPreBase`, its `vCtrl`, and its coherence view
at the promise's address. -/
theorem certified_promAboveAll {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat}
    {th : TTh} {t : Ts} {m : Msg} (hc : Certified p k arch c i) (hth : c.ths[i]? = some th)
    (ht : t ∈ th.promises) (hm : c.mem[t]? = some m) :
    th.vs.vPreBase < t ∧ th.vs.vCtrl < t ∧ th.vs.coh m.loc < t := by
  have h := Nat.lt_of_le_of_lt (le_obLow_base k arch th.vs) (certified_obAbove hc hth ht hm)
  exact ⟨Nat.lt_of_le_of_lt (Nat.le_max_left _ _) h, Nat.lt_of_le_of_lt (Nat.le_max_right _ _) h,
    certified_promAbove hc hth ht hm⟩

/-- **L1 on TSO** (with `tsoStoreOrder`): also above `vRd` and `vWr`. -/
theorem certified_promAboveTso {p : Prog} {k : Promises.Knobs} {c : Cfg} {i : Nat}
    {th : TTh} {t : Ts} {m : Msg} (hk : k.tsoStoreOrder = true) (hc : Certified p k .tso c i)
    (hth : c.ths[i]? = some th) (ht : t ∈ th.promises) (hm : c.mem[t]? = some m) :
    th.vs.vRd < t ∧ th.vs.vWr < t := by
  have h := Nat.lt_of_le_of_lt (le_obLow_tso k th.vs hk) (certified_obAbove hc hth ht hm)
  exact ⟨Nat.lt_of_le_of_lt (Nat.le_max_left _ _) h, Nat.lt_of_le_of_lt (Nat.le_max_right _ _) h⟩

/-! ## §7 L2: what a load reads is below its coherence view

Every rule that reads records the timestamp it read in the destination
register's `rts`, and raises `coh` at the address to at least that timestamp
(an RMW's write then moves `coh` further up, to its own write).  So once a
step has read `tr` at `b`, `tr ≤ coh b`, and if `tr` is (still) an
outstanding promise of the thread it is dead (`DeadP`), which a certified
configuration rules out (`certified_notRead`). -/

theorem ite_t {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem ite_f {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

theorem readable_get {mem : Memory} {a : Address} {t bound : Ts}
    (h : WeakMem.readable mem a t bound = true) : ∃ m, mem[t]? = some m ∧ m.loc = a := by
  unfold WeakMem.readable at h
  cases hm : mem[t]? with
  | none => simp [hm] at h
  | some m =>
      simp only [hm, Option.elim, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨m, rfl, h.1⟩

theorem next_ne (a : Address) : a.next ≠ a := by
  intro h
  have := congrArg WeakMem.Address.offset h
  simp [WeakMem.Address.next] at this

theorem stepFence_regs (th : Promises.Thread) (f : WeakMem.Fence) :
    (Promises.stepFence th f).regs = th.regs := by
  cases f <;> rfl

/-- What the leading `lockFence` of `Promises.stepRmw`/`stepRmwPair` keeps:
    everything but the two barrier views, and those only grow. -/
theorem lockF_prom (arch : Arch) (th : Promises.Thread) :
    (if arch = .tso then Promises.stepFence th .sy else th).promises = th.promises := by
  split <;> rfl

theorem lockF_regs (arch : Arch) (th : Promises.Thread) :
    (if arch = .tso then Promises.stepFence th .sy else th).regs = th.regs := by
  split <;> rfl

theorem lockF_coh (arch : Arch) (th : Promises.Thread) :
    (if arch = .tso then Promises.stepFence th .sy else th).vs.coh = th.vs.coh := by
  split <;> rfl

theorem lockF_relSt (arch : Arch) (th : Promises.Thread) :
    th.vs.vRelSt ≤ (if arch = .tso then Promises.stepFence th .sy else th).vs.vRelSt := by
  split
  · exact Nat.le_max_left _ _
  · exact Nat.le_refl _

/-- What a read leaves: the register's `rts` is a message at `a`, at most `coh a`. -/
def ReadAt (mem : Memory) (th : Promises.Thread) (dst : WeakMem.Reg) (a : Address) : Prop :=
  (∃ m, mem[(th.regs dst).rts]? = some m ∧ m.loc = a) ∧ (th.regs dst).rts ≤ th.vs.coh a

theorem readAt_lock {arch : Arch} {mem : Memory} {x : Promises.Thread} {dst : WeakMem.Reg}
    {a : Address} (h : ReadAt mem x dst a) :
    ReadAt mem (if arch = .tso then Promises.stepFence x .sy else x) dst a := by
  split
  · unfold ReadAt; rw [stepFence_regs, stepFence_coh]; exact h
  · exact h

theorem stepLoad_read {arch : Arch} {mem : Memory} {pairs : List Ts} {th th' : Promises.Thread}
    {dst : WeakMem.Reg} {a : Address} {deps : List WeakMem.Reg} {acq : Bool}
    (h : th' ∈ Promises.stepLoad arch mem pairs th dst a deps acq) :
    ReadAt mem th' dst a ∧ ∀ b, th.vs.coh b ≤ th'.vs.coh b := by
  simp only [Promises.stepLoad, List.mem_map, List.mem_filter, List.mem_range] at h
  obtain ⟨tr, ⟨_, hr⟩, rfl⟩ := h
  obtain ⟨m, hm, hl⟩ := readable_get hr
  refine ⟨⟨⟨m, ?_, hl⟩, ?_⟩, fun b => ?_⟩
  · dsimp only; rw [ite_t rfl]; exact hm
  · dsimp only; rw [ite_t rfl, ite_t rfl]; exact Nat.le_max_right _ _
  · show th.vs.coh b ≤ (if b = a then _ else _)
    split
    · rename_i he; subst he; exact Nat.le_max_left _ _
    · exact Nat.le_refl _

theorem stepLoadPair_read {arch : Arch} {mem : Memory} {pairs : List Ts} {th th' : Promises.Thread}
    {dst0 dst1 : WeakMem.Reg} {a : Address} {deps : List WeakMem.Reg} {acq : Bool}
    (hd : dst0 ≠ dst1) (h : th' ∈ Promises.stepLoadPair arch mem pairs th dst0 dst1 a deps acq) :
    ReadAt mem th' dst0 a ∧ ReadAt mem th' dst1 a.next ∧ ∀ b, th.vs.coh b ≤ th'.vs.coh b := by
  simp only [Promises.stepLoadPair, List.mem_flatMap, List.mem_filterMap, List.mem_filter,
    List.mem_range] at h
  obtain ⟨t0, ⟨_, hr0⟩, t1, ⟨_, hr1⟩, hs⟩ := h
  split at hs
  · cases hs
  simp only [Option.some.injEq] at hs
  subst hs
  obtain ⟨m0, hm0, hl0⟩ := readable_get hr0
  obtain ⟨m1, hm1, hl1⟩ := readable_get hr1
  have hn := next_ne a
  refine ⟨⟨⟨m0, ?_, hl0⟩, ?_⟩, ⟨⟨m1, ?_, hl1⟩, ?_⟩, fun b => ?_⟩
  · dsimp only; rw [ite_t rfl]; exact hm0
  · dsimp only; rw [ite_t rfl, ite_t rfl]; exact Nat.le_max_right _ _
  · dsimp only; rw [ite_f (Ne.symm hd), ite_t rfl]; exact hm1
  · dsimp only; rw [ite_f (Ne.symm hd), ite_t rfl, ite_f hn, ite_t rfl]
    exact Nat.le_max_right _ _
  · show th.vs.coh b ≤ (if b = a then _ else if b = a.next then _ else _)
    split
    · rename_i he; subst he; exact Nat.le_max_left _ _
    · split
      · rename_i he; rw [he]; exact Nat.le_max_left _ _
      · exact Nat.le_refl _

/-- What an RMW leaves in `dst`: a read at `a`, unless it was a successful
    non-acquire `CAS`, which leaves the comparand -- a constant, so no
    dependency and no message (`Promises.rmwDst`). -/
def RmwReadAt (mem : Memory) (th : Promises.Thread) (dst : WeakMem.Reg) (a : Address)
    (kind : WeakMem.RmwKind) (acq : Bool) : Prop :=
  ReadAt mem th dst a ∨ (acq = false ∧ (∃ c, kind = .cas c) ∧ (th.regs dst).rts = 0)

theorem rmwReadAt_lock {arch : Arch} {mem : Memory} {x : Promises.Thread} {dst : WeakMem.Reg}
    {a : Address} {kind : WeakMem.RmwKind} {acq : Bool} (h : RmwReadAt mem x dst a kind acq) :
    RmwReadAt mem (if arch = .tso then Promises.stepFence x .sy else x) dst a kind acq := by
  rcases h with h | ⟨ha, hc, hr⟩
  · exact Or.inl (readAt_lock h)
  · exact Or.inr ⟨ha, hc, by rw [lockF_regs]; exact hr⟩

theorem stepRmw_read_at {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', th') ∈ Promises.stepRmwAt k arch mem pairs th dst a kind newv deps acq rel) :
    RmwReadAt mem' th' dst a kind acq := by
  simp only [Promises.stepRmwAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨tr, ⟨htr, hr⟩, h⟩ := h
  obtain ⟨m, hm, hl⟩ := readable_get hr
  rcases Promises.Sim.rmwDst_cases kind acq mem[tr]! tr with he | ⟨ha, hc, he⟩
  case inr =>
    -- The comparand case: the register is the same in every branch.
    split at h
    · simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      apply rmwReadAt_lock
      refine Or.inr ⟨ha, hc, ?_⟩
      dsimp only; rw [ite_t rfl, he]
    · simp only [List.mem_append] at h
      rcases h with h | h
      · split at h
        · simp only [List.mem_singleton, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          apply rmwReadAt_lock
          refine Or.inr ⟨ha, hc, ?_⟩
          dsimp only; rw [ite_t rfl, he]
        · cases h
      · simp only [List.mem_filterMap] at h
        obtain ⟨tw, _, hf⟩ := h
        cases hm' : mem[tw]? with
        | none => simp [hm'] at hf
        | some pm =>
            simp only [hm', Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
            obtain ⟨_, rfl, rfl⟩ := hf
            apply rmwReadAt_lock
            refine Or.inr ⟨ha, hc, ?_⟩
            dsimp only; rw [ite_t rfl, he]
  refine Or.inl ?_
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    apply readAt_lock
    refine ⟨⟨m, ?_, hl⟩, ?_⟩
    · dsimp only; rw [ite_t rfl, he]; exact hm
    · dsimp only; rw [ite_t rfl, ite_t rfl, he]; exact Nat.le_max_right _ _
  · simp only [List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        apply readAt_lock
        refine ⟨⟨m, ?_, hl⟩, ?_⟩
        · dsimp only; rw [ite_t rfl, he]; exact MemExt.push _ _ _ _ hm
        · dsimp only; rw [ite_t rfl, ite_t rfl, he]; exact Nat.le_of_lt htr
      · cases h
    · simp only [List.mem_filterMap] at h
      obtain ⟨tw, _, hf⟩ := h
      cases hm' : mem[tw]? with
      | none => simp [hm'] at hf
      | some pm =>
          simp only [hm', Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
          obtain ⟨hcond, rfl, rfl⟩ := hf
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
          have hadj := rmwAdjacent_lt hcond.2
          apply readAt_lock
          refine ⟨⟨m, ?_, hl⟩, ?_⟩
          · dsimp only; rw [ite_t rfl, he]; exact hm
          · dsimp only; rw [ite_t rfl, ite_t rfl, he]; exact Nat.le_of_lt hadj

/-- **Restricted by the `CAS` fix (B6).**  This read `ReadAt mem' th' dst a`
    unconditionally until a successful non-acquire `CAS` stopped writing the
    value read's timestamp into `dst`; see `RmwReadAt`. -/
theorem stepRmw_read {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs th dst a kind newv deps acq rel) :
    RmwReadAt mem' th' dst a kind acq :=
  stepRmw_read_at (th := if arch = .tso then Promises.stepFence th .sy else th) h

theorem stepRmwPair_read_at {arch : Arch} {mem mem' : Memory} {pairs pairs' : List Ts}
    {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address} {cmp0 cmp1 : Val}
    {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool} (hd : dst0 ≠ dst1)
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPairAt arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel) :
    ReadAt mem' th' dst0 a ∧ ReadAt mem' th' dst1 a.next := by
  simp only [Promises.stepRmwPairAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨t0, ⟨ht0, hr0⟩, t1, ⟨ht1, hr1⟩, h⟩ := h
  obtain ⟨m0, hm0, hl0⟩ := readable_get hr0
  obtain ⟨m1, hm1, hl1⟩ := readable_get hr1
  have hn := next_ne a
  split at h
  · simp at h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨readAt_lock ⟨⟨m0, ?_, hl0⟩, ?_⟩, readAt_lock ⟨⟨m1, ?_, hl1⟩, ?_⟩⟩
    · dsimp only; rw [ite_t rfl]; exact hm0
    · dsimp only; rw [ite_t rfl, ite_t rfl]; exact Nat.le_max_right _ _
    · dsimp only; rw [ite_f (Ne.symm hd), ite_t rfl]; exact hm1
    · dsimp only; rw [ite_f (Ne.symm hd), ite_t rfl, ite_f hn, ite_t rfl]
      exact Nat.le_max_right _ _
  simp only [List.mem_append] at h
  rcases h with h | h
  · split at h
    · rename_i hadj
      simp only [Bool.and_eq_true] at hadj
      have a0 := rmwAdjacent_lt hadj.1
      have a1 := rmwAdjacent_lt hadj.2
      simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨readAt_lock ⟨⟨m0, ?_, hl0⟩, ?_⟩, readAt_lock ⟨⟨m1, ?_, hl1⟩, ?_⟩⟩
      · dsimp only; rw [ite_t rfl]; exact (MemExt.push _ _).trans (MemExt.push _ _) _ _ hm0
      · dsimp only; rw [ite_t rfl, ite_t rfl]; exact Nat.le_of_lt a0
      · dsimp only; rw [ite_f (Ne.symm hd), ite_t rfl]; exact (MemExt.push _ _).trans (MemExt.push _ _) _ _ hm1
      · dsimp only; rw [ite_f (Ne.symm hd), ite_t rfl, ite_f hn, ite_t rfl]
        exact Nat.le_of_lt a1
    · cases h
  · simp only [List.mem_filterMap] at h
    obtain ⟨tw, _, hf⟩ := h
    cases hm : mem[tw]? with
    | none => simp [hm] at hf
    | some pm0 =>
    cases hm' : mem[tw + 1]? with
    | none => simp [hm, hm'] at hf
    | some pm1 =>
    simp only [hm, hm', Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨hcond, rfl, rfl, rfl⟩ := hf
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
    have a0 := rmwAdjacent_lt hcond.1.2
    have a1 := rmwAdjacent_lt hcond.2
    refine ⟨readAt_lock ⟨⟨m0, ?_, hl0⟩, ?_⟩, readAt_lock ⟨⟨m1, ?_, hl1⟩, ?_⟩⟩
    · dsimp only; rw [ite_t rfl]; exact hm0
    · dsimp only; rw [ite_t rfl, ite_t rfl]; exact Nat.le_of_lt a0
    · dsimp only; rw [ite_f (Ne.symm hd), ite_t rfl]; exact hm1
    · dsimp only; rw [ite_f (Ne.symm hd), ite_t rfl, ite_f hn, ite_t rfl]
      exact Nat.le_of_lt a1

theorem stepRmwPair_read {arch : Arch} {mem mem' : Memory} {pairs pairs' : List Ts}
    {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address} {cmp0 cmp1 : Val}
    {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool} (hd : dst0 ≠ dst1)
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel) :
    ReadAt mem' th' dst0 a ∧ ReadAt mem' th' dst1 a.next :=
  stepRmwPair_read_at (th := if arch = .tso then Promises.stepFence th .sy else th) hd h

/-- **L2 for `loadUnits`.**  Word `j` of a load's result was read from a
message at `offs a (n + j)`, and the final coherence view there is at least
its timestamp (`rts`).  Coherence only grows along the load. -/
theorem loadUnits_read {arch : Arch} {pw : Word} {a : Address} {acq : Bool} :
    ∀ (us : List Acc) (n : Nat) (s : St) (r : St × List Word), r ∈ loadUnits arch pw a acq us n s →
      (∀ b, s.vs.coh b ≤ r.1.vs.coh b) ∧
      ∀ j w, r.2[j]? = some w →
        ∃ m, r.1.mem[w.rts]? = some m ∧ m.loc = offs a (n + j) ∧ w.rts ≤ r.1.vs.coh (offs a (n + j))
  | [], _, s, r, hr => by
      simp only [loadUnits, List.mem_singleton] at hr; subst hr
      exact ⟨fun _ => Nat.le_refl _, fun j w hw => by simp at hw⟩
  | .one :: us, n, s, r, hr => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, hth, ⟨s', ws⟩, hmem, rfl⟩ := hr
      obtain ⟨⟨⟨m, hm, hl⟩, hle⟩, hmono⟩ := stepLoad_read (th := mth s pw pw pw) hth
      obtain ⟨ih1, ih2⟩ := loadUnits_read us (n + 1) _ (s', ws) hmem
      have hfr := (TermMem.loadUnits_frame us (n + 1) _ (s', ws) hmem).1
      refine ⟨fun b => Nat.le_trans (hmono b) (ih1 b), fun j w hw => ?_⟩
      cases j with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hw
          subst hw
          refine ⟨m, ?_, by rw [hl, Nat.add_zero], ?_⟩
          · rw [hfr]; exact hm
          · rw [Nat.add_zero]; exact Nat.le_trans hle (ih1 _)
      | succ j =>
          simp only [List.getElem?_cons_succ] at hw
          obtain ⟨m', h1, h2, h3⟩ := ih2 j w hw
          rw [show n + (j + 1) = n + 1 + j by omega]
          exact ⟨m', h1, h2, h3⟩
  | .two :: us, n, s, r, hr => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, hth, ⟨s', ws⟩, hmem, rfl⟩ := hr
      obtain ⟨⟨⟨m0, hm0, hl0⟩, hle0⟩, ⟨⟨m1, hm1, hl1⟩, hle1⟩, hmono⟩ :=
        stepLoadPair_read (th := mth s pw pw pw) (by decide) hth
      obtain ⟨ih1, ih2⟩ := loadUnits_read us (n + 2) _ (s', ws) hmem
      have hfr := (TermMem.loadUnits_frame us (n + 2) _ (s', ws) hmem).1
      have hnx := TermMem.offs_next a n
      refine ⟨fun b => Nat.le_trans (hmono b) (ih1 b), fun j w hw => ?_⟩
      match j, hw with
      | 0, hw =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hw
          subst hw
          refine ⟨m0, ?_, by rw [hl0, Nat.add_zero], ?_⟩
          · rw [hfr]; exact hm0
          · rw [Nat.add_zero]; exact Nat.le_trans hle0 (ih1 _)
      | 1, hw =>
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hw
          subst hw
          rw [hnx] at hl1 hle1
          refine ⟨m1, ?_, hl1, Nat.le_trans hle1 (ih1 _)⟩
          rw [hfr]; exact hm1
      | j + 2, hw =>
          simp only [List.getElem?_cons_succ] at hw
          obtain ⟨m', h1, h2, h3⟩ := ih2 j w hw
          rw [show n + (j + 2) = n + 2 + j by omega]
          exact ⟨m', h1, h2, h3⟩

/-- **L2, state form.**  A word a load returned whose read timestamp is still an
outstanding promise names a dead promise. -/
theorem loadUnits_readDead {arch : Arch} {pw : Word} {a : Address} {acq : Bool} {us : List Acc}
    {n : Nat} {s : St} {r : St × List Word} {j : Nat} {w : Word}
    (hr : r ∈ loadUnits arch pw a acq us n s) (hw : r.2[j]? = some w) (hp : w.rts ∈ r.1.promises) :
    DeadP r.1 w.rts := by
  obtain ⟨m, hm, hl, hle⟩ := (loadUnits_read us n s r hr).2 j w hw
  exact ⟨hp, m, hm, by rw [hl]; exact hle⟩

/-- A read timestamp at most the coherence view, at an outstanding promise, is a
dead promise. -/
theorem readAt_dead {mem : Memory} {th : Promises.Thread} {dst : WeakMem.Reg} {a : Address}
    (h : ReadAt mem th dst a) (hp : (th.regs dst).rts ∈ th.promises) :
    DeadM mem th.vs th.promises (th.regs dst).rts := by
  obtain ⟨⟨m, hm, hl⟩, hle⟩ := h
  exact ⟨hp, m, hm, by rw [hl]; exact hle⟩

/-- **L2, machine form.**  In a certified configuration no message at or below
the thread's coherence view at its address is an outstanding promise of the
thread; in particular (`loadUnits_read`, `stepLoad_read`, `stepRmw_read`, …)
nothing a step has just read is. -/
theorem certified_notRead {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat}
    {th : TTh} {tr : Ts} {m : Msg} (hc : Certified p k arch c i) (hth : c.ths[i]? = some th)
    (hm : c.mem[tr]? = some m) (hle : tr ≤ th.vs.coh m.loc) : tr ∉ th.promises :=
  fun hp => Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hle (certified_promAbove hc hth hp hm))

/-- **L2 for a load step.**  If thread `i` steps by `let x = load a` and the
result is certified, no word the load bound to `x` was read from an
outstanding promise of `i`. -/
theorem certified_loadStep {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat}
    {th th' : TTh} {x : String} {acq : Bool} {a : At} {e : Expr}
    (hth : c.ths[i]? = some th) (hterm : th.term = .let_ x (.load acq a) e)
    (hs : c' ∈ threadSteps p k arch c i) (hc : Certified p k arch c' i)
    (hth' : c'.ths[i]? = some th') :
    ∃ ty ws, th'.env.head? = some (x, ty, ws) ∧ ∀ w ∈ ws, w.rts ∉ th'.promises := by
  simp only [threadSteps, hth, List.mem_map] at hs
  obtain ⟨⟨mem, pairs, th''⟩, hr, rfl⟩ := hs
  obtain rfl := Option.some.inj ((arr_set (y := th'') hth).symm.trans hth')
  simp only [tstep, hterm, List.mem_map] at hr
  obtain ⟨⟨s', ty, ws⟩, hx, he⟩ := hr
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  simp only [evalOp] at hx
  repeat' split at hx
  all_goals (try (simp at hx; done))
  all_goals
    simp only [List.mem_map, Prod.mk.injEq] at hx
    obtain ⟨⟨s2, ws2⟩, hl, rfl, rfl, rfl⟩ := hx
    refine ⟨_, ws2, rfl, fun w hw => ?_⟩
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hw
    obtain ⟨m, hm, hloc, hle⟩ := (loadUnits_read _ _ _ _ hl).2 j w hj
    exact certified_notRead hc (arr_set hth) hm (by rw [hloc]; exact hle)

#print axioms stepStore_deadO
#print axioms stepRmw_deadO
#print axioms stepRmwPair_deadO
#print axioms evalOp_deadO
#print axioms tstep_deadO
#print axioms solo_deadO
#print axioms certified_noDeadO
#print axioms certified_obAbove
#print axioms certified_promAboveAll
#print axioms certified_promAboveTso
#print axioms stepLoad_read
#print axioms stepLoadPair_read
#print axioms stepRmw_read
#print axioms stepRmwPair_read
#print axioms loadUnits_read
#print axioms loadUnits_readDead
#print axioms readAt_dead
#print axioms certified_notRead
#print axioms certified_loadStep

end TermCert

/-
Stage B, S3: the fulfil characterisation along certifying runs.

A promise leaves a thread's `promises` only through a single-word fulfil: a
`stepStore` issued by `storeUnits` at a `.one` unit, or a `stepRmw` (`fetch`,
`cas`).  Allocation stores never fulfil (the cells are fresh: fact (f)), pair
stores never touch `promises`, and a pair RMW cannot fulfil because no promise
is a pair start (README 32, `hpd`).  Along `Solo`, every promise of the thread
that disappears was fulfilled by one of its thread steps (`solo_fulfil`), so in
a certified configuration every outstanding promise is fulfilled along the
certifying run (`certified_fulfil`), and any property of all single-word writes
the run can issue holds of every outstanding promise (`certified_promQ`).
-/

namespace TermFul
open CoreLang CoreTerm TermRun TermCert
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-! ## §0 Generalities -/

theorem memExt_size {M M' : Memory} (h : MemExt M M') : M.size ≤ M'.size := by
  cases hs : M.size with
  | zero => exact Nat.zero_le _
  | succ n =>
      have hl : n < M.size := by omega
      have := h n _ (Array.getElem?_eq_getElem hl)
      have := TermMem.lt_of_get this
      omega

/-- An old message, seen in an extension, is the old message. -/
theorem memExt_back {M M' : Memory} {t : Nat} {m : Msg} (h : MemExt M M') (ht : t < M.size)
    (hm : M'[t]? = some m) : M[t]? = some m := by
  have h1 := Array.getElem?_eq_getElem ht
  rw [h t _ h1] at hm
  rw [h1, hm]

theorem memExt_fold (f : Nat → Msg) (n : Nat) (M : Memory) :
    MemExt M ((List.range n).foldl (fun m j => m.push (f j)) M) := by
  intro t m h
  rw [TermMem.fold_get]
  simp only [TermMem.lt_of_get h, ↓reduceIte]
  exact h

theorem getD_get {mem : Memory} {t : Nat} (h : t < mem.size) : mem[t]? = some mem[t]! := by
  simp [h]

theorem not_mem_erase {t tw : Nat} {P : List Nat} (ht : t ∈ P) (hn : t ∉ P.erase tw) : t = tw :=
  Classical.byContradiction fun hne => hn ((List.mem_erase_of_ne hne).2 ht)

theorem lockFence_prom (arch : Arch) (x : Promises.Thread) :
    (if arch = .tso then Promises.stepFence x .sy else x).promises = x.promises := by
  split
  · exact stepFence_prom x _
  · rfl

theorem lockFence_coh (arch : Arch) (x : Promises.Thread) :
    (if arch = .tso then Promises.stepFence x .sy else x).vs.coh = x.vs.coh := by
  split
  · exact stepFence_coh x _
  · rfl

/-- The word a scratch store writes is the data word. -/
theorem exprVal_dataE (s : St) (pw w : Word) : TermMem.exprVal (mth s pw w w) (dataE 1 w) = w.val := by
  unfold dataE
  split
  · rename_i h; simp [TermMem.exprVal, mth, regsOf, h]
  · rfl

theorem rmwNewVal_dataE (s : St) (pw w : Word) :
    Promises.rmwNewVal (mth s pw w w).regs (dataE 1 w) = w.val := by
  unfold dataE
  split
  · rename_i h; simp [Promises.rmwNewVal, mth, regsOf, h]
  · rfl

/-! ## §1 The machine's write rules -/

/-- **`stepStore`.**  Promises only shrink; a removed promise `t` was fulfilled:
its message is at the store's address with the store's value, and the guard
held (`storeMview ≤ view`, `storeOb < t`).  Memory is extended (append) or
unchanged (fulfil). -/
theorem stepStore_ful {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory}
    {th th' : Promises.Thread} {a : Address} {e : WeakMem.Expr} {deps : List WeakMem.Reg} {rel : Bool}
    (h : (mem', th') ∈ Promises.stepStore k arch mem th a e deps rel) :
    MemExt mem mem' ∧ th'.promises.Sublist th.promises ∧
      ∀ t, t ∈ th.promises → t ∉ th'.promises → mem' = mem ∧ ∃ m, mem[t]? = some m ∧
        m.loc = a ∧ m.val = TermMem.exprVal th e ∧ Promises.storeMview th e deps rel ≤ m.view ∧
        Promises.storeOb k arch th a e deps < t := by
  cases e <;>
  · simp only [Promises.stepStore, List.mem_append, List.mem_singleton, List.mem_filterMap] at h
    rcases h with h | ⟨tw, _, hf⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨MemExt.push _ _, List.Sublist.refl _, fun t ht hn => absurd ht hn⟩
    · cases hm : mem[tw]? with
      | none => simp [hm] at hf
      | some pm =>
          simp only [hm] at hf
          split at hf
          · rename_i hcond
            simp only [Option.some.injEq, Prod.mk.injEq] at hf
            obtain ⟨rfl, rfl⟩ := hf
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
            obtain ⟨⟨⟨hl, hv⟩, hmv⟩, hlt⟩ := hcond
            refine ⟨MemExt.rfl' _, List.erase_sublist, fun t ht hn => ?_⟩
            have e := not_mem_erase ht hn
            subst e
            exact ⟨rfl, pm, hm, hl, hv, hmv, hlt⟩
          · simp at hf

/-- **`stepRmw`.**  As `stepStore`; the fulfilled message carries the value
the RMW computes from the message `mr` it read (`kind.apply`), and the
view-independent part of the guard: above the release view, above `coh a`
and the read, adjacent to the read. -/
theorem stepRmw_ful_at {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', th') ∈ Promises.stepRmwAt k arch mem pairs th dst a kind newv deps acq rel) :
    MemExt mem mem' ∧ th'.promises.Sublist th.promises ∧
      ∀ t, t ∈ th.promises → t ∉ th'.promises → mem' = mem ∧ ∃ m tr mr, mem[t]? = some m ∧
        mem[tr]? = some mr ∧ WeakMem.rmwSucceeds kind mr.val = true ∧ m.loc = a ∧
        m.val = kind.apply mr.val (Promises.rmwNewVal th.regs newv) ∧ th.vs.vRelSt ≤ m.view ∧
        th.vs.coh a < t ∧ tr < t ∧ WeakMem.rmwAdjacent mem a tr t = true ∧ mr.loc = a := by
  simp only [Promises.stepRmwAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨tr, ⟨htr, hrd⟩, h⟩ := h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨MemExt.rfl' _, ?_, fun t ht hn => ?_⟩
    · rw [lockFence_prom]; exact List.Sublist.refl _
    · rw [lockFence_prom] at hn; exact absurd ht hn
  · rename_i hsucc
    simp only [List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨MemExt.push _ _, ?_, fun t ht hn => ?_⟩
        · rw [lockFence_prom]; exact List.Sublist.refl _
        · rw [lockFence_prom] at hn; exact absurd ht hn
      · cases h
    · simp only [List.mem_filterMap] at h
      obtain ⟨tw, _, hf⟩ := h
      cases hm : mem[tw]? with
      | none => simp [hm] at hf
      | some pm =>
          simp only [hm, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
          obtain ⟨hcond, rfl, rfl⟩ := hf
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
          obtain ⟨⟨⟨⟨hl, hv⟩, hmv⟩, hlt⟩, hadj⟩ := hcond
          refine ⟨MemExt.rfl' _, ?_, fun t ht hn => ?_⟩
          · rw [lockFence_prom]; exact List.erase_sublist
          · rw [lockFence_prom] at hn
            have e := not_mem_erase ht hn
            subst e
            refine ⟨rfl, pm, tr, mem[tr]!, hm, getD_get htr, ?_, hl, hv, ?_, ?_, ?_, hadj, ?_⟩
            · simpa using hsucc
            · exact Nat.le_trans (by maxle) hmv
            · exact Nat.lt_of_le_of_lt (by maxle) hlt
            · exact Nat.lt_of_le_of_lt (by maxle) hlt
            · simp only [WeakMem.readable, Bool.and_eq_true] at hrd
              rw [getD_get htr] at hrd
              simpa using hrd.1

theorem stepRmw_ful {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs th dst a kind newv deps acq rel) :
    MemExt mem mem' ∧ th'.promises.Sublist th.promises ∧
      ∀ t, t ∈ th.promises → t ∉ th'.promises → mem' = mem ∧ ∃ m tr mr, mem[t]? = some m ∧
        mem[tr]? = some mr ∧ WeakMem.rmwSucceeds kind mr.val = true ∧ m.loc = a ∧
        m.val = kind.apply mr.val (Promises.rmwNewVal th.regs newv) ∧ th.vs.vRelSt ≤ m.view ∧
        th.vs.coh a < t ∧ tr < t ∧ WeakMem.rmwAdjacent mem a tr t = true ∧ mr.loc = a :=
  by
  have hx := stepRmw_ful_at (th := if arch = .tso then Promises.stepFence th .sy else th) h
  rw [lockFence_prom, TermCert.lockF_regs, lockFence_coh] at hx
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨h1, h2, fun t ht hn => ?_⟩
  obtain ⟨e, m, tr, mr, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := h3 t ht hn
  exact ⟨e, m, tr, mr, a1, a2, a3, a4, a5, Nat.le_trans (TermCert.lockF_relSt arch th) a6, a7, a8, a9,
    a10⟩

/-- **`stepStorePair`** never touches promises, appends two messages at `a`,
`a.next`, registers the pair start, and sets coherence at both words to the
new messages. -/
theorem stepStorePair_shape (mem : Memory) (pairs : List Ts) (th : Promises.Thread) (a : Address)
    (e0 e1 : WeakMem.Expr) (deps : List WeakMem.Reg) (rel : Bool) :
    (Promises.stepStorePair mem pairs th a e0 e1 deps rel).2.2.promises = th.promises ∧
    (∃ m0 m1, (Promises.stepStorePair mem pairs th a e0 e1 deps rel).1 = (mem.push m0).push m1 ∧
      m0.loc = a ∧ m1.loc = a.next) ∧
    (Promises.stepStorePair mem pairs th a e0 e1 deps rel).2.1 = pairs ++ [mem.size] ∧
    (Promises.stepStorePair mem pairs th a e0 e1 deps rel).2.2.vs.coh a = mem.size ∧
    (Promises.stepStorePair mem pairs th a e0 e1 deps rel).2.2.vs.coh a.next = mem.size + 1 := by
  obtain ⟨q1, q2, q3, q4, -⟩ := TermMem.stepStorePair_eq mem pairs th a e0 e1 deps rel
  refine ⟨q4, ⟨_, _, q1, rfl, rfl⟩, q2, ?_, ?_⟩
  · rw [q3]; simp
  · rw [q3]; simp [next_ne a]

/-- **`stepRmwPair`, shape.**  Either it writes nothing (failed compare, or a
fulfil), or it appends two messages at `a`, `a.next`, registers the pair start
and sets coherence at both words to them. -/
theorem stepRmwPair_shape_at {arch : Arch} {mem mem' : Memory} {pairs pairs' : List Ts}
    {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address} {cmp0 cmp1 : Val}
    {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPairAt arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel) :
    (mem' = mem ∧ pairs' = pairs) ∨
    ((∃ m0 m1, mem' = (mem.push m0).push m1 ∧ m0.loc = a ∧ m1.loc = a.next) ∧
      pairs' = pairs ++ [mem.size] ∧ th'.promises = th.promises ∧
      th'.vs.coh a = mem.size ∧ th'.vs.coh a.next = mem.size + 1) := by
  simp only [Promises.stepRmwPairAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨t0, _, t1, _, h⟩ := h
  split at h
  · simp at h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, rfl⟩
  simp only [List.mem_append] at h
  rcases h with h | h
  · split at h
    · simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine Or.inr ⟨⟨_, _, rfl, rfl, rfl⟩, rfl, lockFence_prom _ _, ?_, ?_⟩
      · rw [lockFence_coh]; simp
      · rw [lockFence_coh]; simp [next_ne a]
    · cases h
  · simp only [List.mem_filterMap] at h
    obtain ⟨tw, _, hf⟩ := h
    split at hf
    · simp only [Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨-, rfl, rfl, rfl⟩ := hf
      exact Or.inl ⟨rfl, rfl⟩
    · cases hf

theorem stepRmwPair_shape {arch : Arch} {mem mem' : Memory} {pairs pairs' : List Ts}
    {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address} {cmp0 cmp1 : Val}
    {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel) :
    (mem' = mem ∧ pairs' = pairs) ∨
    ((∃ m0 m1, mem' = (mem.push m0).push m1 ∧ m0.loc = a ∧ m1.loc = a.next) ∧
      pairs' = pairs ++ [mem.size] ∧ th'.promises = th.promises ∧
      th'.vs.coh a = mem.size ∧ th'.vs.coh a.next = mem.size + 1) :=
  by
  have hx := stepRmwPair_shape_at (th := if arch = .tso then Promises.stepFence th .sy else th) h
  rwa [lockFence_prom] at hx

/-- **`stepRmwPair` never fulfils** in a state where no promise is a pair start
(README 32: `TermRun.promise` never registers a pair). -/
theorem stepRmwPair_prom_at {arch : Arch} {mem mem' : Memory} {pairs pairs' : List Ts}
    {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address} {cmp0 cmp1 : Val}
    {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPairAt arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel)
    (hpp : ∀ t, t ∈ th.promises → t ∉ pairs) : th'.promises = th.promises := by
  simp only [Promises.stepRmwPairAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨t0, _, t1, _, h⟩ := h
  split at h
  · simp at h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact lockFence_prom _ _
  simp only [List.mem_append] at h
  rcases h with h | h
  · split at h
    · simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact lockFence_prom _ _
    · cases h
  · simp only [List.mem_filterMap] at h
    obtain ⟨tw, htw, hf⟩ := h
    split at hf
    · simp only [Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨hcond, -, -, -⟩ := hf
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hcond
      exact absurd hcond.1.1.1.1.1.1.1.1.1.1 (hpp tw htw)
    · cases hf

theorem stepRmwPair_prom {arch : Arch} {mem mem' : Memory} {pairs pairs' : List Ts}
    {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address} {cmp0 cmp1 : Val}
    {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel)
    (hpp : ∀ t, t ∈ th.promises → t ∉ pairs) : th'.promises = th.promises :=
  by
  have hx := stepRmwPair_prom_at (th := if arch = .tso then Promises.stepFence th .sy else th) h (by rw [lockFence_prom]; exact hpp)
  rwa [lockFence_prom] at hx

/-! ## §2 State-level primitives -/

/-- Word `j` of the unit list `us` starts a single-word unit. -/
inductive OneAt : List Acc → Nat → Prop
  | here (us : List Acc) : OneAt (.one :: us) 0
  | cons (u : Acc) {us : List Acc} {j : Nat} : OneAt us j → OneAt (u :: us) (j + u.size)

theorem OneAt_lt {us : List Acc} {j : Nat} (h : OneAt us j) : j < nWords us := by
  induction h with
  | here _ => simp only [nWords, List.map_cons, List.sum_cons, Acc.size]; omega
  | cons u _ ih => simp only [nWords, List.map_cons, List.sum_cons] at ih ⊢; omega

/-- **`storeUnits`.**  Memory is extended, promises only shrink, and a removed
promise `t` was fulfilled by the `stepStore` of a single-word unit: word `j`
(`OneAt us j`) with data word `w`, at `offs a (i + j)`, in an intermediate state
`s0` (memory extending `s`'s, `t` still outstanding) whose guard held. -/
theorem storeUnits_ful {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s' ∈ storeUnits k arch pw a rel us ws i s →
      MemExt s.mem s'.mem ∧ s'.promises.Sublist s.promises ∧
      ∀ t, t ∈ s.promises → t ∉ s'.promises → ∃ j w s0 m, OneAt us j ∧ ws[j]? = some w ∧
        MemExt s.mem s0.mem ∧ t ∈ s0.promises ∧ s0.mem[t]? = some m ∧ m.loc = offs a (i + j) ∧
        m.val = w.val ∧ Promises.storeMview (mth s0 pw w w) (dataE 1 w) [0] rel ≤ m.view ∧
        Promises.storeOb k arch (mth s0 pw w w) (offs a (i + j)) (dataE 1 w) [0] < t
  | [], _, _, s, s', hs => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs
      exact ⟨MemExt.rfl' _, List.Sublist.refl _, fun t ht hn => absurd ht hn⟩
  | .one :: us, w :: ws, i, s, s', hs => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      obtain ⟨e1, sub1, rem1⟩ := stepStore_ful hst
      obtain ⟨e2, sub2, rem2⟩ := storeUnits_ful us ws (i + 1) _ s' hs
      refine ⟨e1.trans e2, sub2.trans sub1, fun t ht hn => ?_⟩
      by_cases h1 : t ∈ th.promises
      · obtain ⟨j, w', s0, m, hj, hw, he, h0, hm, hl, hv, hmv, hob⟩ := rem2 t h1 hn
        have ea : offs a (i + 1 + j) = offs a (i + (j + Acc.size .one)) := by
          simp only [Acc.size]; congr 1; omega
        refine ⟨j + Acc.size .one, w', s0, m, .cons .one hj, by simpa [Acc.size] using hw,
          e1.trans he, h0, hm, by rw [hl, ea], hv, hmv, by rw [← ea]; exact hob⟩
      · obtain ⟨-, m, hm, hl, hv, hmv, hob⟩ := rem1 t ht h1
        refine ⟨0, w, s, m, .here us, rfl, MemExt.rfl' _, ht, hm, hl, ?_, hmv, hob⟩
        rw [hv]; exact exprVal_dataE s pw w
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs => by
      simp only [storeUnits] at hs
      obtain ⟨p1, ⟨m0, m1, q1, -, -⟩, -, -, -⟩ := stepStorePair_shape s.mem s.pairs (mth s pw w0 w1)
        (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
        (dataE 2 w1) [0] rel = R at p1 q1 hs
      obtain ⟨mem', pairs', th⟩ := R
      simp only at p1 q1
      obtain ⟨e2, sub2, rem2⟩ := storeUnits_ful us ws (i + 2) _ s' hs
      have e1 : MemExt s.mem mem' := by rw [q1]; exact (MemExt.push _ _).trans (MemExt.push _ _)
      have p1' : th.promises = s.promises := p1
      refine ⟨e1.trans e2, p1' ▸ sub2, fun t ht hn => ?_⟩
      obtain ⟨j, w', s0, m, hj, hw, he, h0, hm, hl, hv, hmv, hob⟩ := rem2 t (p1' ▸ ht) hn
      have ea : offs a (i + 2 + j) = offs a (i + (j + Acc.size .two)) := by
        simp only [Acc.size]; congr 1; omega
      exact ⟨j + Acc.size .two, w', s0, m, .cons .two hj, by simpa [Acc.size] using hw,
        e1.trans he, h0, hm, by rw [hl, ea], hv, hmv, by rw [← ea]; exact hob⟩
  | .one :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, s', hs => by simp [storeUnits] at hs

theorem loadUnits_keep {arch : Arch} {pw : Word} {a : Address} {acq : Bool} :
    ∀ (us : List Acc) (k : Nat) (s : St) (r : St × List Word), r ∈ loadUnits arch pw a acq us k s →
      r.1.mem = s.mem ∧ r.1.pairs = s.pairs ∧ r.1.promises = s.promises
  | [], _, s, r, hr => by
      simp only [loadUnits, List.mem_singleton] at hr; subst hr; exact ⟨rfl, rfl, rfl⟩
  | .one :: us, k, s, r, hr => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, -, ⟨s', ws⟩, hmem, rfl⟩ := hr
      have := loadUnits_keep us (k + 1) _ (s', ws) hmem; exact this
  | .two :: us, k, s, r, hr => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, -, ⟨s', ws⟩, hmem, rfl⟩ := hr
      have := loadUnits_keep us (k + 2) _ (s', ws) hmem; exact this

theorem projM_keep {g : G} {s : St} {ty : Ty} {ws : List Word} {r : St × Nat × List Word}
    (h : r ∈ projM g s ty ws) : r.1.mem = s.mem ∧ r.1.pairs = s.pairs ∧ r.1.promises = s.promises := by
  unfold projM at h
  split at h
  · split at h
    · split at h
      · simp only [List.mem_flatMap] at h
        obtain ⟨⟨s1, tw⟩, h1, h⟩ := h
        obtain ⟨a1, b1, c1⟩ := loadUnits_keep _ _ _ _ h1
        repeat' split at h
        all_goals first
          | (simp at h; done)
          | (simp only [List.mem_map] at h
             obtain ⟨⟨s2, p⟩, h2, rfl⟩ := h
             obtain ⟨a2, b2, c2⟩ := loadUnits_keep _ _ _ _ h2
             exact ⟨a2.trans a1, b2.trans b1, c2.trans c1⟩)
      · cases h
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩

/-- A step that discharges no (in-range) promise. -/
def KeepR (s s' : St) : Prop :=
  MemExt s.mem s'.mem ∧ s'.promises.Sublist s.promises ∧
    ∀ t, t ∈ s.promises → t < s.mem.size → t ∈ s'.promises

theorem KeepR.refl (s : St) : KeepR s s := ⟨MemExt.rfl' _, List.Sublist.refl _, fun _ h _ => h⟩

theorem KeepR.trans {s1 s2 s3 : St} (h1 : KeepR s1 s2) (h2 : KeepR s2 s3) : KeepR s1 s3 :=
  ⟨h1.1.trans h2.1, h2.2.1.trans h1.2.1, fun t ht hl =>
    h2.2.2 t (h1.2.2 t ht hl) (Nat.lt_of_lt_of_le hl (memExt_size h1.1))⟩

theorem keepR_eq {s s' : St} (hm : s'.mem = s.mem) (hp : s'.promises = s.promises) : KeepR s s' := by
  unfold KeepR; rw [hm, hp]; exact KeepR.refl s

/-- **Allocation fulfils nothing**: its stores are at the fresh label, where
every older promise is dead (fact (f), `alloc_dead`). -/
theorem alloc_keep {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc}
    {ws : List Word} {s : St} {r : St × Word} (hr : r ∈ alloc k arch lbl us ws s) : KeepR s r.1 := by
  have hr0 := hr
  simp only [alloc, List.mem_map] at hr
  obtain ⟨s', hs, rfl⟩ := hr
  obtain ⟨e2, sub2, rem2⟩ := storeUnits_ful _ _ _ _ s' hs
  have e1 := memExt_fold (fun j => (⟨offs ⟨lbl, 0⟩ j, .undef, 0⟩ : Msg)) (nWords us) s.mem
  refine ⟨e1.trans e2, sub2, fun t ht hlt => Classical.byContradiction fun hn => ?_⟩
  obtain ⟨j, w, s0, m, hj, -, he, -, hm0, hl, -⟩ := rem2 t ht hn
  have hm : s.mem[t]? = some m := memExt_back (e1.trans he) hlt hm0
  have hd := alloc_dead hr0 ht hm (o := 0 + (0 + j)) hl (by have := OneAt_lt hj; omega)
  exact hn hd.1

theorem injM_keep {g : G} {s : St} {ty : Ty} {j : Nat} {p : List Word} {r : St × List Word}
    (h : r ∈ injM g s ty j p) : KeepR s r.1 := by
  unfold injM at h
  split at h
  · split at h
    · simp only [List.mem_map] at h
      obtain ⟨⟨s', pw⟩, hs, rfl⟩ := h
      have := alloc_keep hs
      dsimp only
      split
      · exact this
      · exact this
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact KeepR.refl _

/-! ## §3 Growth of memory and pairs -/

/-- Memory is extended; every new pair start is a new message. -/
def GrowM (mem : Memory) (pairs : List Ts) (mem' : Memory) (pairs' : List Ts) : Prop :=
  MemExt mem mem' ∧ ∀ q, q ∈ pairs' → q ∈ pairs ∨ (mem.size ≤ q ∧ q < mem'.size)

abbrev Grow (s s' : St) : Prop := GrowM s.mem s.pairs s'.mem s'.pairs

theorem GrowM.refl (mem : Memory) (pairs : List Ts) : GrowM mem pairs mem pairs :=
  ⟨MemExt.rfl' _, fun _ h => Or.inl h⟩

theorem GrowM.trans {m1 m2 m3 : Memory} {p1 p2 p3 : List Ts} (h1 : GrowM m1 p1 m2 p2)
    (h2 : GrowM m2 p2 m3 p3) : GrowM m1 p1 m3 p3 := by
  refine ⟨h1.1.trans h2.1, fun q hq => ?_⟩
  have s1 := memExt_size h1.1
  have s2 := memExt_size h2.1
  rcases h2.2 q hq with h | h
  · rcases h1.2 q h with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨h'.1, Nat.lt_of_lt_of_le h'.2 s2⟩
  · exact Or.inr ⟨Nat.le_trans s1 h.1, h.2⟩

theorem growM_mem {mem mem' : Memory} {pairs : List Ts} (h : MemExt mem mem') : GrowM mem pairs mem' pairs :=
  ⟨h, fun _ h => Or.inl h⟩

theorem growM_eq {mem mem' : Memory} {pairs pairs' : List Ts} (h1 : mem' = mem) (h2 : pairs' = pairs) :
    GrowM mem pairs mem' pairs' := by
  subst h1; subst h2; exact GrowM.refl _ _

theorem stepRmw_memExt {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts}
    {th : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool} {x : Memory × Promises.Thread}
    (h : x ∈ Promises.stepRmw k arch mem pairs th dst a kind newv deps acq rel) : MemExt mem x.1 :=
  (stepRmw_ful (mem' := x.1) (th' := x.2) h).1

theorem stepRmwPair_grow {arch : Arch} {mem : Memory} {pairs : List Ts}
    {th : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address} {cmp0 cmp1 : Val}
    {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    {x : Memory × List Ts × Promises.Thread}
    (h : x ∈ Promises.stepRmwPair arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel) :
    GrowM mem pairs x.1 x.2.1 := by
  rcases stepRmwPair_shape (mem' := x.1) (pairs' := x.2.1) (th' := x.2.2) h with ⟨h1, h2⟩ |
    ⟨⟨m0, m1, h1, -, -⟩, h2, -⟩
  · exact growM_eq h1 h2
  · refine ⟨by rw [h1]; exact (MemExt.push _ _).trans (MemExt.push _ _), fun q hq => ?_⟩
    rw [h2, List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | hq
    · exact Or.inl hq
    · subst hq; refine Or.inr ⟨Nat.le_refl _, ?_⟩
      rw [h1, Array.size_push, Array.size_push]; exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_succ _)

theorem storeUnits_grow {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s' ∈ storeUnits k arch pw a rel us ws i s →
      Grow s s'
  | [], _, _, s, s', hs => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs; exact GrowM.refl _ _
  | .one :: us, w :: ws, i, s, s', hs => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      exact (growM_mem (stepStore_ful hst).1).trans (storeUnits_grow us ws (i + 1) _ s' hs)
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs => by
      simp only [storeUnits] at hs
      obtain ⟨-, ⟨m0, m1, q1, -, -⟩, q2, -, -⟩ := stepStorePair_shape s.mem s.pairs (mth s pw w0 w1)
        (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
        (dataE 2 w1) [0] rel = R at q1 q2 hs
      obtain ⟨mem', pairs', th⟩ := R
      simp only at q1 q2
      refine GrowM.trans ?_ (storeUnits_grow us ws (i + 2) _ s' hs)
      refine ⟨by rw [q1]; exact (MemExt.push _ _).trans (MemExt.push _ _), fun q hq => ?_⟩
      change q ∈ pairs' at hq
      rw [q2, List.mem_append, List.mem_singleton] at hq
      rcases hq with hq | hq
      · exact Or.inl hq
      · subst hq; refine Or.inr ⟨Nat.le_refl _, ?_⟩; change _ < mem'.size; rw [q1]; simp only [Array.size_push]; omega
  | .one :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, s', hs => by simp [storeUnits] at hs

theorem alloc_grow {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc}
    {ws : List Word} {s : St} {r : St × Word} (hr : r ∈ alloc k arch lbl us ws s) : Grow s r.1 := by
  simp only [alloc, List.mem_map] at hr
  obtain ⟨s', hs, rfl⟩ := hr
  exact (growM_mem (memExt_fold _ _ _)).trans (storeUnits_grow _ _ _ _ s' hs)

theorem allocBuf_grow {lbl : AllocLabel} {n : Nat} {zero : Option (List Val)} {s : St} :
    Grow s (allocBuf lbl n zero s).1 := by
  unfold allocBuf
  exact growM_mem (memExt_fold _ _ _)

theorem injM_grow {g : G} {s : St} {ty : Ty} {j : Nat} {p : List Word} {r : St × List Word}
    (h : r ∈ injM g s ty j p) : Grow s r.1 := by
  unfold injM at h
  split at h
  · split at h
    · simp only [List.mem_map] at h
      obtain ⟨⟨s', pw⟩, hs, rfl⟩ := h
      have := alloc_grow hs
      dsimp only
      split
      · exact this
      · exact this
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact GrowM.refl _ _

theorem grow_load {s s' : St} (h : s'.mem = s.mem ∧ s'.pairs = s.pairs ∧ s'.promises = s.promises) :
    Grow s s' := growM_eq h.1 h.2.1

theorem evalOp_grow {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s op) : Grow s r.1 := by
  cases op <;> simp only [evalOp] at h
  all_goals (try simp only [ol, bind, Option.bind, pure, Option.map] at h)
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h
       first | exact GrowM.refl _ _ | exact allocBuf_grow)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact grow_load (loadUnits_keep _ _ _ _ hx)
         | exact storeUnits_grow _ _ _ _ _ hx
         | exact alloc_grow hx
         | exact growM_mem (stepRmw_memExt hx))
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       first
         | exact (grow_load (projM_keep hx)).trans (injM_grow hy)
         | exact (grow_load (loadUnits_keep _ _ _ _ hx)).trans (storeUnits_grow _ _ _ _ _ hy))
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         exact (grow_load (loadUnits_keep _ _ _ _ hx)).trans (storeUnits_grow _ _ _ _ _ hy)
       · simp at h)
    | (simp only [List.mem_filterMap] at h
       obtain ⟨x, hx, h⟩ := h
       cases hn : numOf x.2 <;> simp [hn] at h
       subst h; exact grow_load (loadUnits_keep _ _ _ _ hx))
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h; dsimp only; exact allocBuf_grow)

theorem enter_eqM {g : G} {th th' : TTh} {f : String} {ts : List Ty} {a : At}
    (h : enter g th f ts a = some th') : th'.promises = th.promises := (enter_eq h).2

theorem tstep_grow {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {r : Memory × List Ts × TTh} (h : r ∈ tstep g mem pairs th) : GrowM mem pairs r.1 r.2.1 := by
  simp only [tstep] at h
  split at h
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_singleton] at h; subst h; exact GrowM.refl _ _)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
       obtain ⟨th', -, rfl⟩ := h
       exact GrowM.refl _ _)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
       obtain ⟨th', -, rfl⟩ := h
       exact GrowM.refl _ _)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact evalOp_grow hx
         | exact growM_mem (stepRmw_memExt hx)
         | exact stepRmwPair_grow hx)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       exact (grow_load (projM_keep hx)).trans (injM_grow hy))

/-! ## §4 Operations: which single-word writes an operation issues -/

/-- `op`, evaluated in `env` at state `s`, issues `storeUnits _ _ pw b rel us ws 0`
(after its loads, if any): the operation's address word, base address, unit
list and data words.  Allocation (`new`, boxed `inl`/`inr`/`case`) is not here:
its stores never fulfil (`alloc_keep`); nor is `stp` (one `.two` unit). -/
def UnitsOp (g : G) (env : Env) (s : St) (op : Op) (pw : Word) (b : Address) (rel : Bool)
    (us : List Acc) (ws : List Word) : Prop :=
  match op with
  | .store rl a v _ => rel = rl ∧ ∃ t t' μ u, evalAt env a = some (t, [pw]) ∧
      evalAt env v = some (t', ws) ∧ cellOf t = some (μ, u) ∧ addrOf pw = some b ∧ accs u = some us
  | .xchg a v => rel = false ∧ ∃ t t' μ u, evalAt env a = some (t, [pw]) ∧
      evalAt env v = some (t', ws) ∧ cellOf t = some (μ, u) ∧ addrOf pw = some b ∧ accs u = some us
  | .xchgAt bb i v => rel = false ∧ ∃ t t1 t2 iws μ u j a0, evalAt env bb = some (t, [pw]) ∧
      evalAt env i = some (t1, iws) ∧ evalAt env v = some (t2, ws) ∧ bufElem t = some (μ, u) ∧
      numOf iws = some j ∧ addrOf pw = some a0 ∧ accs u = some us ∧ b = offs a0 (j * nWords us)
  | .xchgAtF bb i p v => rel = false ∧ ∃ t t1 t2 iws μ u j a0 us0 c o,
      evalAt env bb = some (t, [pw]) ∧ evalAt env i = some (t1, iws) ∧ evalAt env v = some (t2, ws) ∧
      bufElem t = some (μ, u) ∧ numOf iws = some j ∧ addrOf pw = some a0 ∧ accs u = some us0 ∧
      compOff u p = some (c, o) ∧ accs c = some us ∧ b = offs a0 (j * nWords us0 + o)
  | .bufInit bb i x => rel = false ∧ ∃ t t1 t2 iws μ u j a0 μ' n e' ψ,
      evalAt env bb = some (t, [pw]) ∧ evalAt env i = some (t1, iws) ∧ evalAt env x = some (t2, ws) ∧
      bufElem t = some (μ, u) ∧ numOf iws = some j ∧ addrOf pw = some a0 ∧ accs u = some us ∧
      t = .refine (.loc μ' (.array n e')) ψ ∧ b = offs a0 (j * nWords us)
  | .stl bb i v => rel = false ∧ us = [.one] ∧ ∃ t t1 t2 iws vs μ u j y a0 sg w s1 old x,
      evalAt env bb = some (t, [pw]) ∧ evalAt env i = some (t1, iws) ∧ evalAt env v = some (t2, vs) ∧
      bufElem t = some (μ, u) ∧ numOf iws = some j ∧ numOf vs = some y ∧ addrOf pw = some a0 ∧
      lanesOf u = some (sg, w) ∧ b = offs a0 (j / w.lanes) ∧
      (s1, old) ∈ loadUnits g.arch pw b false [.one] 0 s ∧ numOf old = some x ∧
      ws = [cst (.num (setLaneN w x (j % w.lanes) y))]
  | .stlw bb wi jl v => rel = false ∧ us = [.one] ∧ ∃ t t1 t2 t3 iws jws vs μ u i j y a0 sg w s1 old x,
      evalAt env bb = some (t, [pw]) ∧ evalAt env wi = some (t1, iws) ∧ evalAt env jl = some (t2, jws) ∧
      evalAt env v = some (t3, vs) ∧ bufElem t = some (μ, u) ∧ numOf iws = some i ∧
      numOf jws = some j ∧ numOf vs = some y ∧ addrOf pw = some a0 ∧ lanesOf u = some (sg, w) ∧
      b = offs a0 i ∧ (s1, old) ∈ loadUnits g.arch pw b false [.one] 0 s ∧ numOf old = some x ∧
      ws = [cst (.num (setLaneN w x (j % w.lanes) y))]
  | _ => False

/-- A single-word write `op` can issue, as the (address, value) it writes:
word `j` of a `storeUnits` call at a `.one` unit, or a `fetch`'s RMW (whose
value combines the message `mr` read with the operand `nw`). -/
def OpW (g : G) (env : Env) (s : St) (op : Op) (loc : Address) (val : Val) : Prop :=
  (∃ pw b rel us ws j w, UnitsOp g env s op pw b rel us ws ∧ OneAt us j ∧ ws[j]? = some w ∧
    loc = offs b j ∧ val = w.val) ∨
  (∃ o acq rel a v t t' pw nw, ∃ (tr : Nat) (mr : Msg), op = .fetch o acq rel a v ∧ evalAt env a = some (t, [pw]) ∧
    evalAt env v = some (t', [nw]) ∧ addrOf pw = some loc ∧ s.mem[tr]? = some mr ∧
    WeakMem.rmwSucceeds o.kind mr.val = true ∧ val = o.kind.apply mr.val nw.val ∧ mr.loc = loc)

/-- Promises shrink, and every removed one was fulfilled by a write in `W`. -/
def FulRes (s s' : St) (W : Address → Val → Prop) : Prop :=
  s'.promises.Sublist s.promises ∧
    ∀ t, t ∈ s.promises → t ∉ s'.promises → ∃ m, s.mem[t]? = some m ∧ W m.loc m.val

theorem ful_of_keep {s s' : St} {W : Address → Val → Prop} (hlt : ∀ t, t ∈ s.promises → t < s.mem.size)
    (h : KeepR s s') : FulRes s s' W :=
  ⟨h.2.1, fun t ht hn => absurd (h.2.2 t ht (hlt t ht)) hn⟩

theorem keepR_fence {s : St} {f : WeakMem.Fence} : KeepR s (fenceS s f) := keepR_eq rfl rfl

theorem allocBuf_keep {lbl : AllocLabel} {n : Nat} {zero : Option (List Val)} {s : St} :
    KeepR s (allocBuf lbl n zero s).1 := by
  refine ⟨allocBuf_grow.1, ?_, ?_⟩
  · unfold allocBuf; exact List.Sublist.refl _
  · unfold allocBuf; exact fun _ h _ => h

/-- A pair store fulfils nothing. -/
theorem storeUnits_keepTwo {k : Promises.Knobs} {arch : Arch} {pw : Word} {b : Address} {rel : Bool}
    {ws : List Word} {s s' : St} (hs : s' ∈ storeUnits k arch pw b rel [.two] ws 0 s) : KeepR s s' := by
  obtain ⟨e, sub, rem⟩ := storeUnits_ful _ _ _ _ _ hs
  refine ⟨e, sub, fun t ht _ => Classical.byContradiction fun hn => ?_⟩
  obtain ⟨j, -, -, -, hj, -⟩ := rem t ht hn
  cases hj with
  | cons _ h => cases h

theorem units_ful {k : Promises.Knobs} {arch : Arch} {g : G} {env : Env} {op : Op} {pw : Word}
    {b : Address} {rel : Bool} {us : List Acc} {ws : List Word} {s s1 s' : St}
    (hlt : ∀ t, t ∈ s.promises → t < s.mem.size) (hm1 : s1.mem = s.mem) (hp1 : s1.promises = s.promises)
    (hs : s' ∈ storeUnits k arch pw b rel us ws 0 s1) (hU : UnitsOp g env s op pw b rel us ws) :
    FulRes s s' (OpW g env s op) := by
  obtain ⟨-, sub, rem⟩ := storeUnits_ful _ _ _ _ _ hs
  refine ⟨hp1 ▸ sub, fun t ht hn => ?_⟩
  obtain ⟨j, w, s0, m, hj, hw, he, -, hm0, hl, hv, -⟩ := rem t (hp1 ▸ ht) hn
  refine ⟨m, memExt_back (hm1 ▸ he) (hlt t ht) hm0, ?_⟩
  unfold OpW
  exact Or.inl ⟨pw, b, rel, us, ws, j, w, hU, hj, hw, by rw [hl, Nat.zero_add], hv⟩


/-- Close `UnitsOp` / `OpW` goals left by `split`: unfold, then fill every
existential from the split hypotheses. -/
syntax "fillx" : tactic
macro_rules
  | `(tactic| fillx) => `(tactic| (repeat' (first | assumption | rfl | (apply Exists.intro) | (apply And.intro))))

theorem evalOp_store_ful {g : G} {env : Env} {σs : List Ty} {s : St} {rel : Bool} {a v : At}
    {o : Option At} {r : St × Ty × List Word} (hlt : ∀ t, t ∈ s.promises → t < s.mem.size)
    (h : r ∈ evalOp g env σs s (.store rel a v o)) : FulRes s r.1 (OpW g env s (.store rel a v o)) := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_map] at h
       obtain ⟨s', hs, rfl⟩ := h
       exact units_ful hlt rfl rfl hs (by dsimp only [UnitsOp]; fillx))

theorem evalOp_xchg_ful {g : G} {env : Env} {σs : List Ty} {s : St} {a v : At}
    {r : St × Ty × List Word} (hlt : ∀ t, t ∈ s.promises → t < s.mem.size)
    (h : r ∈ evalOp g env σs s (.xchg a v)) : FulRes s r.1 (OpW g env s (.xchg a v)) := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       obtain ⟨k1, -, k3⟩ := loadUnits_keep _ _ _ _ hx
       exact units_ful hlt k1 k3 hy (by dsimp only [UnitsOp]; fillx))

theorem evalOp_xchgAt_ful {g : G} {env : Env} {σs : List Ty} {s : St} {bb i v : At}
    {r : St × Ty × List Word} (hlt : ∀ t, t ∈ s.promises → t < s.mem.size)
    (h : r ∈ evalOp g env σs s (.xchgAt bb i v)) : FulRes s r.1 (OpW g env s (.xchgAt bb i v)) := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       obtain ⟨k1, -, k3⟩ := loadUnits_keep _ _ _ _ hx
       exact units_ful hlt k1 k3 hy (by dsimp only [UnitsOp]; fillx))

theorem evalOp_xchgAtF_ful {g : G} {env : Env} {σs : List Ty} {s : St} {bb i : At} {p : List Nat}
    {v : At} {r : St × Ty × List Word} (hlt : ∀ t, t ∈ s.promises → t < s.mem.size)
    (h : r ∈ evalOp g env σs s (.xchgAtF bb i p v)) :
    FulRes s r.1 (OpW g env s (.xchgAtF bb i p v)) := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       obtain ⟨k1, -, k3⟩ := loadUnits_keep _ _ _ _ hx
       exact units_ful hlt k1 k3 hy (by dsimp only [UnitsOp]; fillx))

theorem evalOp_bufInit_ful {g : G} {env : Env} {σs : List Ty} {s : St} {bb i x : At}
    {r : St × Ty × List Word} (hlt : ∀ t, t ∈ s.promises → t < s.mem.size)
    (h : r ∈ evalOp g env σs s (.bufInit bb i x)) : FulRes s r.1 (OpW g env s (.bufInit bb i x)) := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_map] at h
       obtain ⟨s', hs, rfl⟩ := h
       exact units_ful hlt rfl rfl hs (by dsimp only [UnitsOp]; fillx))

theorem evalOp_stl_ful {g : G} {env : Env} {σs : List Ty} {s : St} {bb i v : At}
    {r : St × Ty × List Word} (hlt : ∀ t, t ∈ s.promises → t < s.mem.size)
    (h : r ∈ evalOp g env σs s (.stl bb i v)) : FulRes s r.1 (OpW g env s (.stl bb i v)) := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         obtain ⟨k1, -, k3⟩ := loadUnits_keep _ _ _ _ hx
         exact units_ful hlt k1 k3 hy (by dsimp only [UnitsOp]; fillx)
       · simp at h)

theorem evalOp_stlw_ful {g : G} {env : Env} {σs : List Ty} {s : St} {bb wi jl v : At}
    {r : St × Ty × List Word} (hlt : ∀ t, t ∈ s.promises → t < s.mem.size)
    (h : r ∈ evalOp g env σs s (.stlw bb wi jl v)) : FulRes s r.1 (OpW g env s (.stlw bb wi jl v)) := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         obtain ⟨k1, -, k3⟩ := loadUnits_keep _ _ _ _ hx
         exact units_ful hlt k1 k3 hy (by dsimp only [UnitsOp]; fillx)
       · simp at h)

theorem evalOp_fetch_ful {g : G} {env : Env} {σs : List Ty} {s : St} {o : FetchOp} {acq rel : Bool}
    {a v : At} {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.fetch o acq rel a v)) :
    FulRes s r.1 (OpW g env s (.fetch o acq rel a v)) := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_map] at h
       obtain ⟨⟨mem', th'⟩, hx, rfl⟩ := h
       obtain ⟨-, sub, rem⟩ := stepRmw_ful hx
       refine ⟨sub, fun t ht hn => ?_⟩
       obtain ⟨-, m, tr, mr, hm, hmr, hsucc, hl, hv, -, -, -, -, hrl⟩ := rem t ht hn
       rw [rmwNewVal_dataE] at hv
       refine ⟨m, hm, Or.inr ?_⟩
       subst hl
       exact ⟨_, _, _, _, _, _, _, _, _, tr, mr, rfl, ‹_›, ‹_›, ‹_›, hmr, hsucc, hv, hrl⟩)

/-- **An operation's fulfils.**  Promises only shrink, and every promise an
operation discharges was fulfilled by a single-word write it issues (`OpW`). -/
theorem evalOp_ful {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op} {r : St × Ty × List Word}
    (hlt : ∀ t, t ∈ s.promises → t < s.mem.size) (h : r ∈ evalOp g env σs s op) :
    FulRes s r.1 (OpW g env s op) := by
  cases op
  case spawn => simp [evalOp] at h
  case store => exact evalOp_store_ful hlt h
  case xchg => exact evalOp_xchg_ful hlt h
  case xchgAt => exact evalOp_xchgAt_ful hlt h
  case xchgAtF => exact evalOp_xchgAtF_ful hlt h
  case bufInit => exact evalOp_bufInit_ful hlt h
  case stl => exact evalOp_stl_ful hlt h
  case stlw => exact evalOp_stlw_ful hlt h
  case fetch => exact evalOp_fetch_ful h
  all_goals
    apply ful_of_keep hlt
    simp only [evalOp] at h
    (try simp only [ol, bind, Option.bind, pure, Option.map] at h)
    (repeat' (first | (split at h) | (dsimp only at h; split at h)))
    all_goals first
      | (simp at h; done)
      | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
         subst h
         first | exact KeepR.refl _ | exact keepR_fence | exact allocBuf_keep)
      | (simp only [List.mem_map] at h
         obtain ⟨x, hx, rfl⟩ := h
         first
           | exact keepR_eq (loadUnits_keep _ _ _ _ hx).1 (loadUnits_keep _ _ _ _ hx).2.2
           | exact storeUnits_keepTwo hx
           | exact alloc_keep hx)
      | (simp only [List.mem_flatMap, List.mem_map] at h
         obtain ⟨x, hx, y, hy, rfl⟩ := h
         exact (keepR_eq (projM_keep hx).1 (projM_keep hx).2.2).trans (injM_keep hy))
      | (simp only [List.mem_filterMap] at h
         obtain ⟨x, hx, h⟩ := h
         cases hn : numOf x.2 <;> simp [hn] at h
         subst h; exact keepR_eq (loadUnits_keep _ _ _ _ hx).1 (loadUnits_keep _ _ _ _ hx).2.2)
      | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
         subst h; dsimp only; exact allocBuf_keep)

/-! ## §5 A thread step -/

/-- **The single-word writes a thread step can issue**, as (address, value):
an operation's (`OpW`, under `let_`), or a `cas`'s successful RMW, which
writes the new-value operand `nw`. -/
def SW (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (loc : Address) (val : Val) : Prop :=
  (∃ x op e, th.term = .let_ x op e ∧ OpW g th.env (stOf mem pairs th) op loc val) ∨
  (∃ acq rel w e v tn ok fail t1 t2 t3 pw ew nw, ∃ (tr : Nat) (mr : Msg),
    th.term = .cas acq rel w e v tn ok fail ∧ evalAt th.env w = some (t1, [pw]) ∧
    evalAt th.env e = some (t2, [ew]) ∧ evalAt th.env v = some (t3, [nw]) ∧ addrOf pw = some loc ∧
    mem[tr]? = some mr ∧ WeakMem.rmwSucceeds (.cas ew.val) mr.val = true ∧ val = nw.val)

theorem ful_mono {s s' : St} {W W' : Address → Val → Prop} (h : FulRes s s' W)
    (hW : ∀ l v, W l v → W' l v) : FulRes s s' W' :=
  ⟨h.1, fun t ht hn => let ⟨m, hm, hw⟩ := h.2 t ht hn; ⟨m, hm, hW _ _ hw⟩⟩

theorem keepR_of {s s' : St} (he : MemExt s.mem s'.mem) (hp : s'.promises = s.promises) : KeepR s s' := by
  refine ⟨he, ?_, ?_⟩
  · rw [hp]; exact List.Sublist.refl _
  · rw [hp]; exact fun _ h _ => h

theorem cas_ful {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {acq rel : Bool} {w e v : At}
    {tn : String} {ok fail : Expr} {t1 t2 t3 : Ty} {pw ew nw : Word} {b : Address}
    {x : Memory × Promises.Thread}
    (hterm : th.term = .cas acq rel w e v tn ok fail) (h1 : evalAt th.env w = some (t1, [pw]))
    (h2 : evalAt th.env e = some (t2, [ew])) (h3 : evalAt th.env v = some (t3, [nw]))
    (hb : addrOf pw = some b)
    (hx : x ∈ Promises.stepRmw g.k g.arch mem pairs (mth (stOf mem pairs th) pw nw nw) 1 b
      (.cas ew.val) (dataE 1 nw) [0] acq rel) (s'' : St) (hs : s''.promises = x.2.promises) :
    FulRes (stOf mem pairs th) s'' (SW g mem pairs th) := by
  obtain ⟨-, sub, rem⟩ := stepRmw_ful (mem' := x.1) (th' := x.2) hx
  refine ⟨by rw [hs]; exact sub, fun t ht hn => ?_⟩
  rw [hs] at hn
  obtain ⟨-, m, tr, mr, hm, hmr, hsucc, hl, hv, -⟩ := rem t ht hn
  rw [rmwNewVal_dataE] at hv
  refine ⟨m, hm, Or.inr ⟨acq, rel, w, e, v, tn, ok, fail, t1, t2, t3, pw, ew, nw, tr, mr, hterm, h1, h2,
    h3, by rw [hl]; exact hb, hmr, hsucc, hv⟩⟩

theorem tstep_ful {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    (hlt : ∀ t, t ∈ th.promises → t < mem.size) (hpp : ∀ t, t ∈ th.promises → t ∉ pairs)
    (h : r ∈ tstep g mem pairs th) : FulRes (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) (SW g mem pairs th) := by
  simp only [tstep] at h
  split at h
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_singleton] at h; subst h; exact ful_of_keep hlt (keepR_eq rfl rfl))
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
       obtain ⟨th', ⟨fr, -, he⟩, rfl⟩ := h
       have := enter_eqM he
       exact ful_of_keep hlt (keepR_eq rfl this))
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
       obtain ⟨th', he, rfl⟩ := h
       have := enter_eqM he
       exact ful_of_keep hlt (keepR_eq rfl this))
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact ful_mono (evalOp_ful hlt hx) (fun l v hw => Or.inl ⟨_, _, _, ‹_›, hw⟩)
         | (split <;> exact ful_mono (evalOp_ful hlt hx) (fun l v hw => Or.inl ⟨_, _, _, ‹_›, hw⟩))
         | exact cas_ful ‹_› ‹_› ‹_› ‹_› ‹_› hx _ rfl
         | exact ful_of_keep hlt (keepR_of (stepRmwPair_grow (x := x) hx).1
             (stepRmwPair_prom (mem' := x.1) (pairs' := x.2.1) (th' := x.2.2) hx hpp)))
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       exact ful_of_keep hlt ((keepR_eq (projM_keep hx).1 (projM_keep hx).2.2).trans (injM_keep hy)))

/-- **Task 1: the fulfil characterisation of a thread step.**  In a state whose
promises are messages (`hlt`) and not pair starts (`hpp`, README 32), a thread
step's promises are a sublist of the old ones, and every promise `t` it
discharges (message `m`) was fulfilled by a single-word write the step issues
at `m.loc` with value `m.val` (`SW`: the operation, its address word and its
data word), above the thread's coherence at `m.loc` and its `obLow`. -/
theorem tstep_fulfil {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    (hlt : ∀ t, t ∈ th.promises → t < mem.size) (hpp : ∀ t, t ∈ th.promises → t ∉ pairs)
    (h : r ∈ tstep g mem pairs th) :
    r.2.2.promises.Sublist th.promises ∧
      ∀ t, t ∈ th.promises → t ∉ r.2.2.promises → ∃ m, mem[t]? = some m ∧
        SW g mem pairs th m.loc m.val ∧ th.vs.coh m.loc < t ∧ obLow g.k g.arch th.vs < t := by
  obtain ⟨sub, rem⟩ := tstep_ful hlt hpp h
  refine ⟨sub, fun t ht hn => ?_⟩
  obtain ⟨m, hm, hw⟩ := rem t ht hn
  refine ⟨m, hm, hw, Nat.lt_of_not_le fun hle => hn ?_, Nat.lt_of_not_le fun hle => hn ?_⟩
  · exact (tstep_dead h ⟨ht, m, hm, hle⟩).1
  · exact (tstep_deadO h ⟨ht, m, hm, hle⟩).1

/-! ## §6 The machine: certifying runs -/

/-- Thread `i`'s outstanding promises (none if there is no thread `i`). -/
def promsOf (c : Cfg) (i : Nat) : List Ts := (c.ths[i]?.map (·.promises)).getD []

/-- Promise well-formedness: pair starts are messages, and thread `i`'s
promises are messages and not pair starts (stage A: `FreshL_promLt`,
`MemInv_nopair`; preserved by every step, `step_pwfAll`). -/
def PWF (c : Cfg) (i : Nat) : Prop :=
  (∀ q, q ∈ c.pairs → q < c.mem.size) ∧ ∀ t, t ∈ promsOf c i → t < c.mem.size ∧ t ∉ c.pairs

/-- The extern move keeps every thread's promises. -/
theorem promsOf_ext {c c' : Cfg} {i : Nat} (h : c' ∈ extSteps c i) (j : Nat) : promsOf c' j = promsOf c j := by
  unfold promsOf; rw [extSteps_promises h j]

theorem promsOf_some {c : Cfg} {i : Nat} {th : TTh} (h : c.ths[i]? = some th) :
    promsOf c i = th.promises := by
  simp [promsOf, h]

theorem threadSteps_inv {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat}
    (h : c' ∈ threadSteps p k arch c i) :
    ∃ th r, c.ths[i]? = some th ∧ r ∈ tstep (gOf p k arch c i) c.mem c.pairs th ∧
      c'.mem = r.1 ∧ c'.pairs = r.2.1 ∧ c'.ths[i]? = some r.2.2 ∧ c'.ths.size = c.ths.size := by
  cases hth : c.ths[i]? with
  | none => simp [threadSteps, hth] at h
  | some th =>
      simp only [threadSteps, hth, List.mem_map] at h
      obtain ⟨⟨mem, pairs, th'⟩, hr, rfl⟩ := h
      exact ⟨th, (mem, pairs, th'), rfl, hr, rfl, rfl, arr_set hth, by simp⟩

theorem promise_facts (c : Cfg) (i : Nat) (a : Address) (v : Val) (w : Ts) :
    MemExt c.mem (promise c i a v w).mem ∧ (promise c i a v w).pairs = c.pairs ∧
    (promise c i a v w).mem.size ≤ c.mem.size + 1 ∧
    (∀ t, t ∈ promsOf (promise c i a v w) i → t ∈ promsOf c i ∨ t = c.mem.size) ∧
    (∀ t, t ∈ promsOf c i → t ∈ promsOf (promise c i a v w) i) := by
  cases hth : c.ths[i]? with
  | none =>
      have e : promise c i a v w = c := by simp [promise, hth]
      rw [e]
      exact ⟨MemExt.rfl' _, rfl, Nat.le_succ _, fun t h => Or.inl h, fun t h => h⟩
  | some th =>
      have e1 : (promise c i a v w).mem = c.mem.push ⟨a, v, w⟩ := by simp [promise, hth]
      have e2 : (promise c i a v w).pairs = c.pairs := by simp [promise, hth]
      have hx : (promise c i a v w).ths[i]? = some { th with promises := th.promises ++ [c.mem.size] } := by
        simp only [promise, hth]; exact arr_set hth
      have e3 : promsOf (promise c i a v w) i = th.promises ++ [c.mem.size] := promsOf_some hx
      rw [e1, e2, e3, promsOf_some hth]
      refine ⟨MemExt.push _ _, rfl, by simp, fun t ht => ?_, fun t ht => List.mem_append_left _ ht⟩
      rcases List.mem_append.1 ht with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_singleton.1 h)

theorem promise_pwf {c : Cfg} {i : Nat} {a : Address} {v : Val} {w : Ts} (hw : PWF c i) :
    PWF (promise c i a v w) i := by
  obtain ⟨f1, f2, f3, f4, -⟩ := promise_facts c i a v w
  have hs := memExt_size f1
  refine ⟨fun q hq => ?_, fun t ht => ?_⟩
  · rw [f2] at hq; exact Nat.lt_of_lt_of_le (hw.1 q hq) hs
  · rw [f2]
    rcases f4 t ht with h | h
    · exact ⟨Nat.lt_of_lt_of_le (hw.2 t h).1 hs, (hw.2 t h).2⟩
    · subst h
      refine ⟨?_, fun hq => Nat.lt_irrefl _ (hw.1 _ hq)⟩
      have : (promise c i a v w).mem.size ≠ c.mem.size := by
        intro he
        obtain ⟨th, hth⟩ : ∃ th, c.ths[i]? = some th := by
          cases hth : c.ths[i]? with
          | none => simp [promsOf, promise, hth] at ht
          | some th => exact ⟨th, rfl⟩
        have : (promise c i a v w).mem = c.mem.push ⟨a, v, w⟩ := by simp [promise, hth]
        rw [this] at he; simp at he
      exact Nat.lt_of_le_of_ne hs (Ne.symm this)

theorem threadSteps_pwf {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat}
    (h : c' ∈ threadSteps p k arch c i) (hw : PWF c i) : PWF c' i := by
  obtain ⟨th, r, hth, hr, e1, e2, e3, -⟩ := threadSteps_inv h
  have hw2 : ∀ t, t ∈ th.promises → t < c.mem.size ∧ t ∉ c.pairs :=
    fun t ht => hw.2 t (by rw [promsOf_some hth]; exact ht)
  have hg := tstep_grow hr
  have hs := memExt_size hg.1
  have hsub := (tstep_ful (fun t ht => (hw2 t ht).1) (fun t ht => (hw2 t ht).2) hr).1
  refine ⟨fun q hq => ?_, fun t ht => ?_⟩
  · rw [e2] at hq; rw [e1]
    rcases hg.2 q hq with h | h
    · exact Nat.lt_of_lt_of_le (hw.1 q h) hs
    · exact h.2
  · rw [promsOf_some e3] at ht
    obtain ⟨l, np⟩ := hw2 t (hsub.subset ht)
    rw [e1, e2]
    refine ⟨Nat.lt_of_lt_of_le l hs, fun hq => ?_⟩
    rcases hg.2 t hq with h | h
    · exact np h
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le l h.1)

/-- **Task 2: fulfil characterisation along `Solo`.**  Every promise of thread
`i` outstanding in `c` but not in `c'` was fulfilled by a thread step
`c1 → c2` of the run: `c1` is reached from `c`, `t` is still outstanding at
`c1` (same message `m`), gone at `c2`, and the step issues a single-word write
of `m.val` at `m.loc` (`SW`) above `i`'s coherence and `obLow` at `c1`. -/
theorem solo_fulfil {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c c' : Cfg}
    (h : Solo p k arch i c c') : PWF c i → ∀ t, t ∈ promsOf c i → t ∉ promsOf c' i →
      ∃ m, c.mem[t]? = some m ∧ ∃ c1 c2 th1, Solo p k arch i c c1 ∧ c2 ∈ threadSteps p k arch c1 i ∧
        Solo p k arch i c2 c' ∧ c1.ths[i]? = some th1 ∧ c1.mem[t]? = some m ∧ t ∈ th1.promises ∧
        t ∉ promsOf c2 i ∧ SW (gOf p k arch c1 i) c1.mem c1.pairs th1 m.loc m.val ∧
        th1.vs.coh m.loc < t ∧ obLow k arch th1.vs < t := by
  induction h with
  | refl => intro _ t ht hn; exact absurd ht hn
  | @thread c0 c1 c2 hs hrest ih =>
      intro hw t ht hn
      obtain ⟨th, r, hth, hr, e1, e2, e3, -⟩ := threadSteps_inv hs
      have hw2 : ∀ t, t ∈ th.promises → t < c0.mem.size ∧ t ∉ c0.pairs :=
        fun t ht => hw.2 t (by rw [promsOf_some hth]; exact ht)
      have hlt : ∀ t, t ∈ th.promises → t < c0.mem.size := fun t ht => (hw2 t ht).1
      have hpp : ∀ t, t ∈ th.promises → t ∉ c0.pairs := fun t ht => (hw2 t ht).2
      have htt : t ∈ th.promises := by rwa [promsOf_some hth] at ht
      by_cases h1 : t ∈ promsOf c1 i
      · obtain ⟨m, hm, c3, c4, th3, hs3, hst, hs4, hth3, hm3, ht3, hn4, hsw, hc, ho⟩ :=
          ih (threadSteps_pwf hs hw) t h1 hn
        have hm0 : c0.mem[t]? = some m :=
          memExt_back (by rw [e1]; exact (tstep_grow hr).1) (hlt t htt) hm
        exact ⟨m, hm0, c3, c4, th3, .thread hs hs3, hst, hs4, hth3, hm3, ht3, hn4, hsw, hc, ho⟩
      · obtain ⟨-, rem⟩ := tstep_fulfil hlt hpp hr
        have hn' : t ∉ r.2.2.promises := by rwa [promsOf_some e3] at h1
        obtain ⟨m, hm, hsw, hc, ho⟩ := rem t htt hn'
        exact ⟨m, hm, c0, c1, th, .refl _, hs, hrest, hth, hm, htt, h1, hsw, hc, ho⟩
  | @prom c0 c2 a v w hw0 hrest ih =>
      intro hw t ht hn
      obtain ⟨f1, -, -, -, f5⟩ := promise_facts c0 i a v w
      obtain ⟨m, hm, c3, c4, th3, hs3, hst, hs4, hth3, hm3, ht3, hn4, hsw, hc, ho⟩ :=
        ih (promise_pwf hw) t (f5 t ht) hn
      exact ⟨m, memExt_back f1 (hw.2 t ht).1 hm, c3, c4, th3, .prom a v w hw0 hs3, hst, hs4, hth3,
        hm3, ht3, hn4, hsw, hc, ho⟩
  | @ext c0 c1 c2 hs hrest ih =>
      intro hw t ht hn
      have hp : promsOf c1 i = promsOf c0 i := promsOf_ext hs i
      have hw1 : PWF c1 i := by
        unfold PWF; rw [hp, extSteps_mem hs, extSteps_pairs hs]; exact hw
      obtain ⟨m, hm, c3, c4, th3, hs3, hst, hs4, hth3, hm3, ht3, hn4, hsw, hc, ho⟩ :=
        ih hw1 t (by rw [hp]; exact ht) hn
      exact ⟨m, by rw [← extSteps_mem hs]; exact hm, c3, c4, th3, .ext hs hs3, hst, hs4, hth3,
        hm3, ht3, hn4, hsw, hc, ho⟩

theorem noPromises_nil {c : Cfg} {i : Nat} (h : noPromises c i = true) : promsOf c i = [] := by
  unfold noPromises at h; unfold promsOf
  cases h' : c.ths[i]? with
  | none => rfl
  | some th =>
      simp only [h', Option.map_some, Option.getD_some, List.isEmpty_iff] at h ⊢
      exact h

/-- **Task 2, corollary: every outstanding promise of a certified thread is
fulfilled along its certifying run**, by a single-word write (`SW`). -/
theorem certified_fulfil {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {t : Ts}
    (hc : Certified p k arch c i) (hw : PWF c i) (ht : t ∈ promsOf c i) :
    ∃ m, c.mem[t]? = some m ∧ ∃ c1 c2 th1, Solo p k arch i c c1 ∧ c2 ∈ threadSteps p k arch c1 i ∧
      c1.ths[i]? = some th1 ∧ c1.mem[t]? = some m ∧ t ∈ th1.promises ∧ t ∉ promsOf c2 i ∧
      SW (gOf p k arch c1 i) c1.mem c1.pairs th1 m.loc m.val ∧
      th1.vs.coh m.loc < t ∧ obLow k arch th1.vs < t := by
  obtain ⟨c', hs, hn⟩ := hc
  have hn' : t ∉ promsOf c' i := by rw [noPromises_nil hn]; exact List.not_mem_nil
  obtain ⟨m, hm, c1, c2, th1, h1, h2, -, rest⟩ := solo_fulfil hs hw t ht hn'
  exact ⟨m, hm, c1, c2, th1, h1, h2, rest⟩

/-- **Task 3, the general form.**  Any property `Q` of every single-word write
that thread `i` can issue along runs from `c` holds of every outstanding
promise of `i` in a certified `c`.  Typing enters only through `hQ`. -/
theorem certified_promQ {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat}
    (Q : Address → Val → Prop) (hc : Certified p k arch c i) (hw : PWF c i)
    (hQ : ∀ c1 th1 loc val, Solo p k arch i c c1 → c1.ths[i]? = some th1 →
      SW (gOf p k arch c1 i) c1.mem c1.pairs th1 loc val → Q loc val)
    {t : Ts} {m : Msg} (ht : t ∈ promsOf c i) (hm : c.mem[t]? = some m) : Q m.loc m.val := by
  obtain ⟨m', hm', c1, c2, th1, h1, -, hth1, -, -, -, hsw, -⟩ := certified_fulfil hc hw ht
  rw [hm] at hm'
  cases hm'
  exact hQ c1 th1 _ _ h1 hth1 hsw

/-! ## §7 `PWF` holds of every reachable configuration -/

/-- `PWF` for every thread. -/
def PWFall (c : Cfg) : Prop := ∀ i, PWF c i

theorem set_other {α : Type} {xs : Array α} {i j : Nat} {y : α} (h : j ≠ i) :
    (xs.set! i y)[j]? = xs[j]? := by
  simp [Array.set!, Array.setIfInBounds]
  split
  · rw [Array.getElem?_set]; simp [Ne.symm h]
  · rfl

theorem step_pwfAll {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg}
    (h : Step p k arch c c') (hw : PWFall c) : PWFall c' := by
  cases h with
  | thread i hs _ =>
      intro j
      by_cases hj : j = i
      · subst hj; exact threadSteps_pwf hs (hw j)
      · obtain ⟨th, r, hth, hr, e1, e2, e3, -⟩ := threadSteps_inv hs
        have hg := tstep_grow hr
        have hs' := memExt_size hg.1
        have hw' := hw i
        refine ⟨(threadSteps_pwf hs hw').1, fun t ht => ?_⟩
        have hpj : promsOf c' j = promsOf c j := by
          simp only [threadSteps, hth, List.mem_map] at hs
          obtain ⟨_, _, rfl⟩ := hs
          unfold promsOf
          rw [set_other hj]
        rw [hpj] at ht
        obtain ⟨l, np⟩ := (hw j).2 t ht
        rw [e1, e2]
        refine ⟨Nat.lt_of_lt_of_le l hs', fun hq => ?_⟩
        rcases hg.2 t hq with h | h
        · exact np h
        · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le l h.1)
  | prom i a v w _ _ _ =>
      intro j
      by_cases hj : j = i
      · subst hj; exact promise_pwf (hw j)
      · obtain ⟨f1, f2, -, -, -⟩ := promise_facts c i a v w
        have hs := memExt_size f1
        have hpj : promsOf (promise c i a v w) j = promsOf c j := by
          unfold promsOf promise
          split
          · rfl
          · dsimp only; rw [set_other hj]
        refine ⟨(promise_pwf (a := a) (v := v) (w := w) (hw i)).1, fun t ht => ?_⟩
        rw [hpj] at ht
        rw [f2]
        exact ⟨Nat.lt_of_lt_of_le ((hw j).2 t ht).1 hs, ((hw j).2 t ht).2⟩

#print axioms stepStore_ful
#print axioms stepRmw_ful
#print axioms stepStorePair_shape
#print axioms stepRmwPair_shape
#print axioms stepRmwPair_prom
#print axioms storeUnits_ful
#print axioms alloc_keep
#print axioms evalOp_ful
#print axioms tstep_fulfil
#print axioms solo_fulfil
#print axioms certified_fulfil
#print axioms certified_promQ
#print axioms step_pwfAll

end TermFul

namespace TermCert
open CoreLang CoreTerm TermRun
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-! ## §7 (F2′ P1) View-dead promises: below the release view

Every fulfil of a promise `t` needs `mview ≤ mem[t].view`, and every write's
`mview` is at least the thread's `vRelSt` (`storeMview_relSt`; an RMW's
`wvs.vRelSt` only adds the read view).  `vRelSt` never decreases through a
step (only fences raise it).  So a promise whose message view is below
`vRelSt` can never be fulfilled, and a certified configuration has none
(`certified_relStLe`).  P1 follows: `publish`'s `fenceS .st` puts
`vRelSt ≥ vWr`, so an outstanding promise after a publish has view at least
the publishing thread's `vWr` (`certified_pub_vWrLe`). -/

/-- `t` is an outstanding promise whose message view is below `vRelSt`. -/
def DeadVM (mem : Memory) (vs : VState) (P : List Ts) (t : Ts) : Prop :=
  t ∈ P ∧ ∃ m, mem[t]? = some m ∧ m.view < vs.vRelSt

def DeadV (s : St) (t : Ts) : Prop :=
  DeadVM s.mem s.vs s.promises t

theorem DeadVM.mono {mem mem' : Memory} {vs vs' : VState} {P P' : List Ts} {t : Ts}
    (h : DeadVM mem vs P t) (hm : MemExt mem mem') (hp : t ∈ P') (hv : vs.vRelSt ≤ vs'.vRelSt) :
    DeadVM mem' vs' P' t := by
  obtain ⟨_, m, hm1, hm2⟩ := h
  exact ⟨hp, m, hm t m hm1, Nat.lt_of_lt_of_le hm2 hv⟩

/-- A fulfilled promise is not view-dead: its message view covers `mview ≥ vRelSt`. -/
theorem DeadVM.ne {mem : Memory} {vs : VState} {P : List Ts} {t tw : Ts} {pm : Msg} {mv : Nat}
    (h : DeadVM mem vs P t) (hm : mem[tw]? = some pm) (h1 : vs.vRelSt ≤ mv) (h2 : mv ≤ pm.view) :
    t ≠ tw := by
  rintro rfl
  obtain ⟨_, m, hm1, hm2⟩ := h
  rw [hm] at hm1
  cases hm1
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hm2 (Nat.le_trans h1 h2))

theorem stepFence_relSt (th : Promises.Thread) (f : WeakMem.Fence) :
    th.vs.vRelSt ≤ (Promises.stepFence th f).vs.vRelSt := by
  cases f <;> dsimp only [Promises.stepFence] <;> maxle

theorem deadVM_lock {arch' : Arch} {mem : Memory} {x : Promises.Thread} {t : Ts}
    (h : DeadVM mem x.vs x.promises t) :
    DeadVM mem (if arch' = .tso then Promises.stepFence x .sy else x).vs
      (if arch' = .tso then Promises.stepFence x .sy else x).promises t := by
  split
  · exact h.mono (MemExt.rfl' _) (by rw [stepFence_prom]; exact h.1) (stepFence_relSt x .sy)
  · exact h

theorem stepLoad_deadV {arch' : Arch} {mem : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {deps : List WeakMem.Reg}
    {acq : Bool} {t : Ts}
    (h : th' ∈ Promises.stepLoad arch' mem pairs th dst a deps acq)
    (hd : DeadVM mem th.vs th.promises t) : DeadVM mem th'.vs th'.promises t := by
  simp only [Promises.stepLoad, List.mem_map, List.mem_filter, List.mem_range] at h
  obtain ⟨tr, _, rfl⟩ := h
  exact hd.mono (MemExt.rfl' _) hd.1 (Nat.le_refl _)

theorem stepLoadPair_deadV {arch' : Arch} {mem : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address} {deps : List WeakMem.Reg}
    {acq : Bool} {t : Ts}
    (h : th' ∈ Promises.stepLoadPair arch' mem pairs th dst0 dst1 a deps acq)
    (hd : DeadVM mem th.vs th.promises t) : DeadVM mem th'.vs th'.promises t := by
  simp only [Promises.stepLoadPair, List.mem_flatMap, List.mem_filterMap, List.mem_filter,
    List.mem_range] at h
  obtain ⟨t0, _, t1, _, hs⟩ := h
  split at hs
  · cases hs
  · simp only [Option.some.injEq] at hs
    subst hs
    exact hd.mono (MemExt.rfl' _) hd.1 (Nat.le_refl _)

theorem stepStore_deadV {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory}
    {th th' : Promises.Thread} {a : Address} {e : WeakMem.Expr} {deps : List WeakMem.Reg}
    {rel : Bool} {t : Ts}
    (h : (mem', th') ∈ Promises.stepStore k arch mem th a e deps rel)
    (hd : DeadVM mem th.vs th.promises t) : DeadVM mem' th'.vs th'.promises t := by
  have hmv := TermMem.storeMview_relSt th e deps rel
  cases e <;>
  · simp only [Promises.stepStore, List.mem_append, List.mem_singleton, List.mem_filterMap] at h
    rcases h with h | ⟨tw, _, hf⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hd.mono (MemExt.push _ _) hd.1 (Nat.le_refl _)
    · cases hm : mem[tw]? with
      | none => simp [hm] at hf
      | some pm =>
          simp only [hm] at hf
          split at hf
          · rename_i hcond
            simp only [Option.some.injEq, Prod.mk.injEq] at hf
            obtain ⟨rfl, rfl⟩ := hf
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
            obtain ⟨⟨-, hle⟩, -⟩ := hcond
            exact hd.mono (MemExt.rfl' _) ((List.mem_erase_of_ne (hd.ne hm hmv hle)).2 hd.1) (Nat.le_refl _)
          · simp at hf

theorem stepStorePair_deadV {mem : Memory} {pairs : List Ts}
    {th : Promises.Thread} {a : Address} {e0 e1 : WeakMem.Expr} {deps : List WeakMem.Reg}
    {rel : Bool} {t : Ts} (hd : DeadVM mem th.vs th.promises t) :
    DeadVM (Promises.stepStorePair mem pairs th a e0 e1 deps rel).1
      (Promises.stepStorePair mem pairs th a e0 e1 deps rel).2.2.vs
      (Promises.stepStorePair mem pairs th a e0 e1 deps rel).2.2.promises t := by
  simp only [Promises.stepStorePair]
  exact hd.mono ((MemExt.push _ _).trans (MemExt.push _ _)) hd.1 (Nat.le_refl _)

theorem stepRmw_deadV_at {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool} {t : Ts}
    (h : (mem', th') ∈ Promises.stepRmwAt k arch mem pairs th dst a kind newv deps acq rel)
    (hd : DeadVM mem th.vs th.promises t) : DeadVM mem' th'.vs th'.promises t := by
  simp only [Promises.stepRmwAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨tr, _, h⟩ := h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    apply deadVM_lock
    exact hd.mono (MemExt.rfl' _) hd.1 (Nat.le_refl _)
  · simp only [List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        apply deadVM_lock
        exact hd.mono (MemExt.push _ _) hd.1 (Nat.le_refl _)
      · cases h
    · simp only [List.mem_filterMap] at h
      obtain ⟨tw, _, hf⟩ := h
      cases hm : mem[tw]? with
      | none => simp [hm] at hf
      | some pm =>
          simp only [hm, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
          obtain ⟨hcond, rfl, rfl⟩ := hf
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
          obtain ⟨⟨⟨-, hle⟩, -⟩, -⟩ := hcond
          apply deadVM_lock
          exact hd.mono (MemExt.rfl' _)
            ((List.mem_erase_of_ne (hd.ne hm (by maxle) hle)).2 hd.1) (Nat.le_refl _)

theorem stepRmw_deadV {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool} {t : Ts}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs th dst a kind newv deps acq rel)
    (hd : DeadVM mem th.vs th.promises t) : DeadVM mem' th'.vs th'.promises t :=
  stepRmw_deadV_at (th := if arch = .tso then Promises.stepFence th .sy else th) h (deadVM_lock hd)

theorem stepRmwPair_deadV_at {arch : Arch} {mem mem' : Memory}
    {pairs pairs' : List Ts} {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address}
    {cmp0 cmp1 : Val} {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool} {t : Ts}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPairAt arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel)
    (hd : DeadVM mem th.vs th.promises t) : DeadVM mem' th'.vs th'.promises t := by
  simp only [Promises.stepRmwPairAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨t0, _, t1, _, h⟩ := h
  split at h
  · simp at h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    apply deadVM_lock
    exact hd.mono (MemExt.rfl' _) hd.1 (Nat.le_refl _)
  simp only [List.mem_append] at h
  rcases h with h | h
  · split at h
    · simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      apply deadVM_lock
      exact hd.mono ((MemExt.push _ _).trans (MemExt.push _ _)) hd.1 (Nat.le_refl _)
    · cases h
  · simp only [List.mem_filterMap] at h
    obtain ⟨tw, _, hf⟩ := h
    cases hm : mem[tw]? with
    | none => simp [hm] at hf
    | some pm0 =>
    cases hm1 : mem[tw + 1]? with
    | none => simp [hm, hm1] at hf
    | some pm1 =>
    simp only [hm, hm1, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨hcond, rfl, rfl, rfl⟩ := hf
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hle0⟩, -⟩, -⟩, hle1⟩, -⟩, -⟩, -⟩ := hcond
    apply deadVM_lock
    exact hd.mono (MemExt.rfl' _)
      ((List.mem_erase_of_ne (hd.ne hm1 (by maxle) hle1)).2
        ((List.mem_erase_of_ne (hd.ne hm (by maxle) hle0)).2 hd.1)) (Nat.le_refl _)

theorem stepRmwPair_deadV {arch : Arch} {mem mem' : Memory}
    {pairs pairs' : List Ts} {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address}
    {cmp0 cmp1 : Val} {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool} {t : Ts}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel)
    (hd : DeadVM mem th.vs th.promises t) : DeadVM mem' th'.vs th'.promises t :=
  stepRmwPair_deadV_at (th := if arch = .tso then Promises.stepFence th .sy else th) h (deadVM_lock hd)

#print axioms stepRmwPair_deadV

/-! ### The state-level primitives, for `DeadV` -/

theorem loadUnits_deadV {arch' : Arch} {pw : Word} {a : Address} {acq : Bool} {t : Ts} :
    ∀ (us : List Acc) (n : Nat) (s : St) (r : St × List Word), r ∈ loadUnits arch' pw a acq us n s →
      DeadV s t → DeadV r.1 t
  | [], _, s, r, hr, hd => by
      simp only [loadUnits, List.mem_singleton] at hr; subst hr; exact hd
  | .one :: us, n, s, r, hr, hd => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, hth, ⟨s', ws⟩, hmem, rfl⟩ := hr
      exact loadUnits_deadV us (n + 1) _ (s', ws) hmem
        ⟨hd.1, (stepLoad_deadV (th := mth s pw pw pw) hth hd).2⟩
  | .two :: us, n, s, r, hr, hd => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, hth, ⟨s', ws⟩, hmem, rfl⟩ := hr
      exact loadUnits_deadV us (n + 2) _ (s', ws) hmem
        ⟨hd.1, (stepLoadPair_deadV (th := mth s pw pw pw) hth hd).2⟩

theorem storeUnits_deadV {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool}
    {t : Ts} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s' ∈ storeUnits k arch pw a rel us ws i s →
      DeadV s t → DeadV s' t
  | [], _, _, s, s', hs, hd => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs; exact hd
  | .one :: us, w :: ws, i, s, s', hs, hd => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      exact storeUnits_deadV us ws (i + 1) _ s' hs (stepStore_deadV (th := mth s pw w w) hst hd)
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs, hd => by
      simp only [storeUnits] at hs
      have h2 := stepStorePair_deadV (pairs := s.pairs) (th := mth s pw w0 w1) (a := offs a i)
        (e0 := dataE 1 w0) (e1 := dataE 2 w1) (deps := [0]) (rel := rel) hd
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
        (dataE 2 w1) [0] rel = R at h2 hs
      obtain ⟨mem', pairs', th⟩ := R
      exact storeUnits_deadV us ws (i + 2) _ s' hs h2
  | .one :: _, [], _, _, s', hs, _ => by simp [storeUnits] at hs
  | .two :: _, [], _, _, s', hs, _ => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, s', hs, _ => by simp [storeUnits] at hs

theorem fenceS_deadV {s : St} {f : WeakMem.Fence} {t : Ts}
    (hd : DeadV s t) : DeadV (fenceS s f) t :=
  DeadVM.mono hd (MemExt.rfl' _) hd.1 (stepFence_relSt (mth s _ _ _) f)

theorem alloc_presV {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc}
    {ws : List Word} {s : St} {t : Ts} {r : St × Word} (hr : r ∈ alloc k arch lbl us ws s)
    (hd : DeadV s t) : DeadV r.1 t := by
  simp only [alloc, List.mem_map] at hr
  obtain ⟨s', hs, rfl⟩ := hr
  exact storeUnits_deadV us ws 0 _ s' hs (DeadVM.mono hd (fold_ext _ _ _) hd.1 (Nat.le_refl _))

theorem allocBuf_presV {lbl : AllocLabel} {n : Nat} {zero : Option (List Val)} {s : St} {t : Ts}
    (hd : DeadV s t) : DeadV (allocBuf lbl n zero s).1 t :=
  DeadVM.mono hd (fold_ext _ _ _) hd.1 (Nat.le_refl _)

theorem injM_deadV {g : G} {s : St} {ty : Ty} {j : Nat} {p : List Word} {t : Ts}
    {r : St × List Word} (h : r ∈ injM g s ty j p) (hd : DeadV s t) : DeadV r.1 t := by
  unfold injM at h
  split at h
  · split at h
    · simp only [List.mem_map] at h
      obtain ⟨⟨s', pw⟩, hs, rfl⟩ := h
      have := alloc_presV hs hd
      dsimp only
      split
      · exact fenceS_deadV this
      · exact this
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact hd

theorem projM_deadV {g : G} {s : St} {ty : Ty} {ws : List Word}
    {t : Ts} {r : St × Nat × List Word} (h : r ∈ projM g s ty ws) (hd : DeadV s t) :
    DeadV r.1 t := by
  unfold projM at h
  split at h
  · split at h
    · split at h
      · simp only [List.mem_flatMap] at h
        obtain ⟨⟨s1, tw⟩, h1, h⟩ := h
        have d1 := loadUnits_deadV _ _ _ _ h1 hd
        repeat' split at h
        all_goals first
          | (simp at h; done)
          | (simp only [List.mem_map] at h
             obtain ⟨⟨s2, p⟩, h2, rfl⟩ := h
             exact loadUnits_deadV _ _ _ _ h2 d1)
      · cases h
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact hd

theorem evalOp_deadV {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op} {t : Ts}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s op) (hd : DeadV s t) : DeadV r.1 t := by
  cases op <;> simp only [evalOp] at h
  all_goals (try simp only [ol, bind, Option.bind, pure, Option.map] at h)
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h
       first | exact hd | exact fenceS_deadV hd | exact allocBuf_presV hd)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact loadUnits_deadV _ _ _ _ hx hd
         | exact storeUnits_deadV _ _ _ _ _ hx hd
         | exact alloc_presV hx hd
         | exact stepRmw_deadV (th := mth s _ _ _) hx hd)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       first
         | exact injM_deadV hy (projM_deadV hx hd)
         | exact storeUnits_deadV _ _ _ _ _ hy (loadUnits_deadV _ _ _ _ hx hd))
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       have d1 := loadUnits_deadV _ _ _ _ hx hd
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         exact storeUnits_deadV _ _ _ _ _ hy d1
       · simp at h)
    | (simp only [List.mem_filterMap] at h
       obtain ⟨x, hx, h⟩ := h
       have d1 := loadUnits_deadV _ _ _ _ hx hd
       cases hn : numOf x.2 <;> simp [hn] at h
       subst h; exact d1)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h; dsimp only; exact allocBuf_presV hd)

theorem tstep_deadV {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {t : Ts}
    {r : Memory × List Ts × TTh} (h : r ∈ tstep g mem pairs th)
    (hd : DeadV (stOf mem pairs th) t) : DeadV (stOf r.1 r.2.1 r.2.2) t := by
  simp only [tstep] at h
  split at h
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_singleton] at h; subst h; exact hd)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
       obtain ⟨th', ⟨fr, -, he⟩, rfl⟩ := h
       obtain ⟨h1, h2⟩ := enter_eq he
       show DeadVM mem th'.vs th'.promises t
       rw [h1, h2]; exact hd)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
       obtain ⟨th', he, rfl⟩ := h
       obtain ⟨h1, h2⟩ := enter_eq he
       show DeadVM mem th'.vs th'.promises t
       rw [h1, h2]; exact hd)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact evalOp_deadV hx hd
         | (split <;> exact evalOp_deadV hx hd)
         | exact stepRmw_deadV (th := mth _ _ _ _) hx hd
         | exact stepRmwPair_deadV (th := mth _ _ _ _) hx hd)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       exact injM_deadV hy (projM_deadV hx hd))
    | (simp only [List.mem_singleton] at h; subst h; exact fenceS_deadV (f := .st) hd)

/-! ### The machine -/

def DeadAtV (c : Cfg) (i : Nat) (t : Ts) : Prop :=
  ∃ th, c.ths[i]? = some th ∧ DeadV (stOf c.mem c.pairs th) t

theorem threadSteps_deadV {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat}
    {t : Ts} (h : c' ∈ threadSteps p k arch c i) (hd : DeadAtV c i t) : DeadAtV c' i t := by
  obtain ⟨th, hth, hd⟩ := hd
  simp only [threadSteps, hth, List.mem_map] at h
  obtain ⟨⟨mem, pairs, th'⟩, hr, rfl⟩ := h
  exact ⟨th', arr_set hth, tstep_deadV (g := gOf p k arch c i) hr hd⟩

theorem promise_deadV {c : Cfg} {i : Nat} {a : Address} {v : Val}
    {w : Ts} {t : Ts} (hd : DeadAtV c i t) : DeadAtV (promise c i a v w) i t := by
  obtain ⟨th, hth, hd⟩ := hd
  refine ⟨{ th with promises := th.promises ++ [c.mem.size] }, ?_, ?_⟩
  · simp only [promise, hth]; exact arr_set hth
  · simp only [promise, hth]
    exact hd.mono (MemExt.push _ _) (List.mem_append_left _ hd.1) (Nat.le_refl _)

theorem solo_deadV {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c c' : Cfg} {t : Ts}
    (h : Solo p k arch i c c') (hd : DeadAtV c i t) : DeadAtV c' i t := by
  induction h with
  | refl => exact hd
  | thread hs _ ih => exact ih (threadSteps_deadV hs hd)
  | prom _ _ _ _ _ ih => exact ih (promise_deadV hd)
  | ext hs _ ih =>
      obtain ⟨th, hth, hd⟩ := hd
      obtain ⟨th0, th', h0, h1, hst, hv⟩ := extSteps_vle hs
      rw [hth] at h0; cases h0
      exact ih ⟨th', h1, by rw [hst]; exact DeadVM.mono hd (MemExt.rfl' _) hd.1 hv.vRelSt⟩

theorem certified_noDeadV {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {t : Ts}
    (hc : Certified p k arch c i) : ¬ DeadAtV c i t := by
  intro hd
  obtain ⟨c', hs, hn⟩ := hc
  obtain ⟨th, hth, hd'⟩ := solo_deadV hs hd
  simp only [noPromises, hth, Option.map_some, Option.getD_some, List.isEmpty_iff] at hn
  have h1 : t ∈ th.promises := hd'.1
  rw [hn] at h1
  cases h1

/-- **(F2′ P1) Outstanding promises are at or above the release view.**  In a
certified configuration every outstanding promise of thread `i` has message
view at least `vRelSt`: no fulfil can cover a view below it. -/
theorem certified_relStLe {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat}
    {th : TTh} {t : Ts} {m : Msg} (hc : Certified p k arch c i) (hth : c.ths[i]? = some th)
    (ht : t ∈ th.promises) (hm : c.mem[t]? = some m) : th.vs.vRelSt ≤ m.view :=
  Nat.le_of_not_lt fun hlt => certified_noDeadV hc ⟨th, hth, ht, m, hm, hlt⟩

/-- `publish` is `fenceS .st`: memory and promises unchanged, `vRelSt ≥ vWr`. -/
theorem tstep_publish_relSt {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {y : String} {a : At}
    {e : Expr} {r : Memory × List Ts × TTh} (hterm : th.term = .let_ y (.publish a) e)
    (hr : r ∈ tstep g mem pairs th) :
    th.vs.vWr ≤ r.2.2.vs.vRelSt ∧ r.2.2.promises = th.promises ∧ r.1 = mem := by
  simp only [tstep, hterm, evalOp, List.mem_map] at hr
  obtain ⟨⟨s', t', ws⟩, hs, rfl⟩ := hr
  cases hev : evalAt th.env a with
  | none => simp [hev, ol] at hs
  | some q =>
    obtain ⟨t0, ws0⟩ := q
    simp only [hev, ol, bind, Option.bind, pure] at hs
    split at hs
    all_goals first
      | (simp at hs; done)
      | (cases hs with
         | head => exact ⟨show th.vs.vWr ≤ max th.vs.vRelSt th.vs.vWr from Nat.le_max_right _ _, rfl, rfl⟩
         | tail _ h => cases h)

/-- **(F2′ P1, no append before publish)**  Every promise still outstanding
when thread `i` publishes has message view at least the thread's `vWr` at the
publish: the publish's `fenceS .st` raises `vRelSt` to `vWr`
(`tstep_publish_relSt`), and the successor is certified
(`certified_relStLe`).  So an append at `t > w_B` before the publish kills a
planting promise of view `w_B`. -/
theorem certified_pub_vWrLe {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat}
    (hs : c' ∈ threadSteps p k arch c i) (hc' : Certified p k arch c' i)
    {th : TTh} (hth : c.ths[i]? = some th) {y : String} {a : At} {e : Expr}
    (hterm : th.term = .let_ y (.publish a) e) {t : Ts} {m : Msg} (ht : t ∈ th.promises)
    (hm : c.mem[t]? = some m) : th.vs.vWr ≤ m.view := by
  simp only [threadSteps, hth, List.mem_map] at hs
  obtain ⟨⟨mem, pairs, th'⟩, hr, rfl⟩ := hs
  obtain ⟨h1, h2, h3⟩ := tstep_publish_relSt hterm hr
  dsimp only at h1 h2 h3
  subst h3
  exact Nat.le_trans h1 (certified_relStLe hc' (arr_set hth) (by rw [h2]; exact ht) hm)

#print axioms DeadVM.mono
#print axioms DeadVM.ne
#print axioms stepFence_relSt
#print axioms deadVM_lock
#print axioms stepLoad_deadV
#print axioms stepLoadPair_deadV
#print axioms stepStore_deadV
#print axioms stepStorePair_deadV
#print axioms stepRmw_deadV
#print axioms loadUnits_deadV
#print axioms storeUnits_deadV
#print axioms fenceS_deadV
#print axioms alloc_presV
#print axioms allocBuf_presV
#print axioms injM_deadV
#print axioms projM_deadV
#print axioms evalOp_deadV
#print axioms tstep_deadV
#print axioms threadSteps_deadV
#print axioms promise_deadV
#print axioms solo_deadV
#print axioms certified_noDeadV
#print axioms certified_relStLe
#print axioms tstep_publish_relSt
#print axioms certified_pub_vWrLe

end TermCert

namespace TermCert
open CoreLang CoreTerm TermRun
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-! ## §8 (F2′ P3) No append inside a window bounded by a promise view

A thread step never adds a promise; it fulfils a promise `t` only by raising
`vWr` to at least `t`, and it appends only by raising `vWr` to at least the old
memory size (`AppUpM`).  So along a solo run from `c0` (promise steps
included) every message appended at or above `c0`'s size is still an
outstanding promise unless `vWr` has reached that size, and every promise
fulfilled in the run is at or below the final `vWr` (`WinInv`).  At a publish
inside the window of a planting promise of view `w < size`, P1 bounds `vWr`
by `w`; so the window's writes are exactly fulfils of promises already
outstanding at the plant, at indices `≤ vWr` at the publish
(`plant_pub_window`). -/

/-- One thread step's effect on memory, `vWr` and the promise set. -/
def AppUpM (mem : Memory) (vs : VState) (P : List Ts) (mem' : Memory) (vs' : VState)
    (P' : List Ts) : Prop :=
  vs.vWr ≤ vs'.vWr ∧ MemExt mem mem' ∧ (∀ t ∈ P', t ∈ P) ∧ (∀ t ∈ P, t ∉ P' → t ≤ vs'.vWr) ∧
    (mem.size < mem'.size → mem.size ≤ vs'.vWr)

def AppUp (s s' : St) : Prop := AppUpM s.mem s.vs s.promises s'.mem s'.vs s'.promises

theorem AppUpM.refl' (mem : Memory) (vs : VState) (P : List Ts) : AppUpM mem vs P mem vs P :=
  ⟨Nat.le_refl _, MemExt.rfl' _, fun _ h => h, fun _ h h' => absurd h h',
    fun h => absurd h (Nat.lt_irrefl _)⟩

theorem AppUpM.trans {m1 m2 m3 : Memory} {v1 v2 v3 : VState} {P1 P2 P3 : List Ts}
    (a : AppUpM m1 v1 P1 m2 v2 P2) (b : AppUpM m2 v2 P2 m3 v3 P3) : AppUpM m1 v1 P1 m3 v3 P3 := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := a
  obtain ⟨b1, b2, b3, b4, b5⟩ := b
  refine ⟨Nat.le_trans a1 b1, a2.trans b2, fun t h => a3 t (b3 t h), fun t h h' => ?_, fun h => ?_⟩
  · by_cases h2 : t ∈ P2
    · exact b4 t h2 h'
    · exact Nat.le_trans (a4 t h h2) b1
  · by_cases h2 : m1.size < m2.size
    · exact Nat.le_trans (a5 h2) b1
    · have e := TermFul.memExt_size a2
      have := b5 (by omega)
      omega

theorem AppUp.trans {s1 s2 s3 : St} (a : AppUp s1 s2) (b : AppUp s2 s3) : AppUp s1 s3 :=
  AppUpM.trans a b

theorem AppUpM.keep {mem : Memory} {vs vs' : VState} {P : List Ts} (h : vs.vWr ≤ vs'.vWr) :
    AppUpM mem vs P mem vs' P :=
  ⟨h, MemExt.rfl' _, fun _ h => h, fun _ h h' => absurd h h', fun h => absurd h (Nat.lt_irrefl _)⟩

theorem AppUpM.push {mem : Memory} {vs vs' : VState} {P : List Ts} (m : Msg)
    (h : vs.vWr ≤ vs'.vWr) (hs : mem.size ≤ vs'.vWr) : AppUpM mem vs P (mem.push m) vs' P :=
  ⟨h, MemExt.push _ _, fun _ h => h, fun _ h h' => absurd h h', fun _ => hs⟩

theorem AppUpM.push2 {mem : Memory} {vs vs' : VState} {P : List Ts} (m m' : Msg)
    (h : vs.vWr ≤ vs'.vWr) (hs : mem.size ≤ vs'.vWr) :
    AppUpM mem vs P ((mem.push m).push m') vs' P :=
  ⟨h, (MemExt.push _ _).trans (MemExt.push _ _), fun _ h => h, fun _ h h' => absurd h h',
    fun _ => hs⟩

theorem AppUpM.ful {mem : Memory} {vs vs' : VState} {P : List Ts} {t : Ts}
    (h : vs.vWr ≤ vs'.vWr) (ht : t ≤ vs'.vWr) : AppUpM mem vs P mem vs' (P.erase t) := by
  refine ⟨h, MemExt.rfl' _, fun u hu => List.mem_of_mem_erase hu, fun u hu hu' => ?_,
    fun h => absurd h (Nat.lt_irrefl _)⟩
  by_cases e : u = t
  · subst e; exact ht
  · exact absurd ((List.mem_erase_of_ne e).2 hu) hu'

theorem appUp_lock {arch' : Arch} {mem mem' : Memory} {vs : VState} {P : List Ts}
    {x : Promises.Thread} (h : AppUpM mem vs P mem' x.vs x.promises) :
    AppUpM mem vs P mem' (if arch' = .tso then Promises.stepFence x .sy else x).vs
      (if arch' = .tso then Promises.stepFence x .sy else x).promises := by
  split
  · obtain ⟨h1, h2, h3, h4, h5⟩ := h
    exact ⟨h1, h2, by rw [stepFence_prom]; exact h3, by rw [stepFence_prom]; exact h4, h5⟩
  · exact h

/-- `appUp_lock`'s converse on the *source* side: a fence before the step
    moves neither `vWr` nor the promises. -/
theorem appUp_unlock {arch' : Arch} {mem mem' : Memory} {vs' : VState} {P' : List Ts}
    {x : Promises.Thread}
    (h : AppUpM mem (if arch' = .tso then Promises.stepFence x .sy else x).vs
      (if arch' = .tso then Promises.stepFence x .sy else x).promises mem' vs' P') :
    AppUpM mem x.vs x.promises mem' vs' P' := by
  split at h <;> exact h

theorem stepStore_appUp {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory}
    {th th' : Promises.Thread} {a : Address} {e : WeakMem.Expr} {deps : List WeakMem.Reg}
    {rel : Bool} (h : (mem', th') ∈ Promises.stepStore k arch mem th a e deps rel) :
    AppUpM mem th.vs th.promises mem' th'.vs th'.promises := by
  cases e <;>
  · simp only [Promises.stepStore, List.mem_append, List.mem_singleton, List.mem_filterMap] at h
    rcases h with h | ⟨tw, _, hf⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact AppUpM.push _ (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    · cases hm : mem[tw]? with
      | none => simp [hm] at hf
      | some pm =>
          simp only [hm] at hf
          split at hf
          · simp only [Option.some.injEq, Prod.mk.injEq] at hf
            obtain ⟨rfl, rfl⟩ := hf
            exact AppUpM.ful (Nat.le_max_left _ _) (Nat.le_max_right _ _)
          · simp at hf

theorem stepRmw_appUp_at {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', th') ∈ Promises.stepRmwAt k arch mem pairs th dst a kind newv deps acq rel) :
    AppUpM mem th.vs th.promises mem' th'.vs th'.promises := by
  simp only [Promises.stepRmwAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨tr, _, h⟩ := h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    apply appUp_lock
    exact AppUpM.keep (Nat.le_refl _)
  · simp only [List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        apply appUp_lock
        exact AppUpM.push _ (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      · cases h
    · simp only [List.mem_filterMap] at h
      obtain ⟨tw, _, hf⟩ := h
      cases hm : mem[tw]? with
      | none => simp [hm] at hf
      | some pm =>
          simp only [hm, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
          obtain ⟨-, rfl, rfl⟩ := hf
          apply appUp_lock
          exact AppUpM.ful (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem stepRmw_appUp {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs th dst a kind newv deps acq rel) :
    AppUpM mem th.vs th.promises mem' th'.vs th'.promises :=
  appUp_unlock (stepRmw_appUp_at (th := if arch = .tso then Promises.stepFence th .sy else th) h)

theorem stepRmwPair_appUp_at {arch : Arch} {mem mem' : Memory}
    {pairs pairs' : List Ts} {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address}
    {cmp0 cmp1 : Val} {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPairAt arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel) :
    AppUpM mem th.vs th.promises mem' th'.vs th'.promises := by
  simp only [Promises.stepRmwPairAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨t0, _, t1, _, h⟩ := h
  split at h
  · simp at h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    apply appUp_lock
    exact AppUpM.keep (Nat.le_refl _)
  simp only [List.mem_append] at h
  rcases h with h | h
  · split at h
    · simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      apply appUp_lock
      exact AppUpM.push2 _ _ (Nat.le_max_left _ _)
        (Nat.le_trans (Nat.le_succ _) (Nat.le_max_right _ _))
    · cases h
  · simp only [List.mem_filterMap] at h
    obtain ⟨tw, _, hf⟩ := h
    cases hm : mem[tw]? with
    | none => simp [hm] at hf
    | some pm0 =>
    cases hm1 : mem[tw + 1]? with
    | none => simp [hm, hm1] at hf
    | some pm1 =>
    simp only [hm, hm1, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨-, rfl, rfl, rfl⟩ := hf
    apply appUp_lock
    exact AppUpM.trans (AppUpM.ful (t := tw) (Nat.le_max_left _ _)
        (Nat.le_trans (Nat.le_succ _) (Nat.le_max_right _ _)))
      (AppUpM.ful (Nat.le_refl _) (Nat.le_max_right _ _))

theorem stepRmwPair_appUp {arch : Arch} {mem mem' : Memory}
    {pairs pairs' : List Ts} {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address}
    {cmp0 cmp1 : Val} {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel) :
    AppUpM mem th.vs th.promises mem' th'.vs th'.promises :=
  appUp_unlock (stepRmwPair_appUp_at (th := if arch = .tso then Promises.stepFence th .sy else th) h)

#print axioms stepRmwPair_appUp

/-! ### The state-level primitives -/

theorem loadUnits_appUp {arch' : Arch} {pw : Word} {a : Address} {acq : Bool}
    {us : List Acc} {n : Nat} {s : St} {r : St × List Word} (hr : r ∈ loadUnits arch' pw a acq us n s) :
    AppUp s r.1 := by
  obtain ⟨e1, -, e3⟩ := TermFul.loadUnits_keep us n s r hr
  have e2 := TermMem.loadUnits_vWr us n s r hr
  show AppUpM s.mem s.vs s.promises r.1.mem r.1.vs r.1.promises
  rw [e1, e3]
  exact AppUpM.keep (Nat.le_of_eq e2.symm)

theorem storeUnits_appUp {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s' ∈ storeUnits k arch pw a rel us ws i s →
      AppUp s s'
  | [], _, _, s, s', hs => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs; exact AppUpM.refl' _ _ _
  | .one :: us, w :: ws, i, s, s', hs => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      exact AppUpM.trans (stepStore_appUp (th := mth s pw w w) hst)
        (storeUnits_appUp us ws (i + 1) _ s' hs)
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs => by
      simp only [storeUnits] at hs
      have h2 : AppUpM s.mem s.vs s.promises
          (Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
            (dataE 2 w1) [0] rel).1
          (Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
            (dataE 2 w1) [0] rel).2.2.vs
          (Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
            (dataE 2 w1) [0] rel).2.2.promises := by
        simp only [Promises.stepStorePair]
        exact AppUpM.push2 _ _ (Nat.le_max_left _ _)
          (Nat.le_trans (Nat.le_succ _) (Nat.le_max_right _ _))
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
        (dataE 2 w1) [0] rel = R at h2 hs
      obtain ⟨mem', pairs', th⟩ := R
      exact AppUpM.trans h2 (storeUnits_appUp us ws (i + 2) _ s' hs)
  | .one :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, s', hs => by simp [storeUnits] at hs

theorem fenceS_appUp (s : St) (f : WeakMem.Fence) : AppUp s (fenceS s f) := by
  show AppUpM s.mem s.vs s.promises s.mem (Promises.stepFence (mth s _ _ _) f).vs s.promises
  cases f <;> exact AppUpM.keep (Nat.le_refl _)

theorem fold_appUp (s : St) (n : Nat) (f : Nat → Msg) (vs : VState)
    (hv : vs.vWr = max s.vs.vWr (s.mem.size + n - 1)) :
    AppUpM s.mem s.vs s.promises ((List.range n).foldl (fun m j => m.push (f j)) s.mem) vs
      s.promises := by
  refine ⟨by rw [hv]; exact Nat.le_max_left _ _, fold_ext _ _ _, fun _ h => h,
    fun _ h h' => absurd h h', fun h => ?_⟩
  rw [TermMem.fold_size] at h
  rw [hv]
  have := Nat.le_max_right s.vs.vWr (s.mem.size + n - 1)
  omega

theorem allocBuf_appUp (lbl : AllocLabel) (n : Nat) (zero : Option (List Val)) (s : St) :
    AppUp s (allocBuf lbl n zero s).1 := by
  unfold allocBuf
  exact fold_appUp s n _ _ rfl

theorem alloc_appUp {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc}
    {ws : List Word} {s : St} {r : St × Word} (hr : r ∈ alloc k arch lbl us ws s) : AppUp s r.1 := by
  simp only [alloc, List.mem_map] at hr
  obtain ⟨s', hs, rfl⟩ := hr
  exact AppUpM.trans (fold_appUp s _ _ _ rfl) (storeUnits_appUp us ws 0 _ s' hs)

theorem injM_appUp {g : G} {s : St} {ty : Ty} {j : Nat} {p : List Word}
    {r : St × List Word} (h : r ∈ injM g s ty j p) : AppUp s r.1 := by
  unfold injM at h
  split at h
  · split at h
    · simp only [List.mem_map] at h
      obtain ⟨⟨s', pw⟩, hs, rfl⟩ := h
      have := alloc_appUp hs
      dsimp only
      split
      · exact AppUp.trans this (fenceS_appUp _ _)
      · exact this
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact AppUpM.refl' _ _ _

theorem projM_appUp {g : G} {s : St} {ty : Ty} {ws : List Word}
    {r : St × Nat × List Word} (h : r ∈ projM g s ty ws) : AppUp s r.1 := by
  unfold projM at h
  split at h
  · split at h
    · split at h
      · simp only [List.mem_flatMap] at h
        obtain ⟨⟨s1, tw⟩, h1, h⟩ := h
        have d1 := loadUnits_appUp h1
        repeat' split at h
        all_goals first
          | (simp at h; done)
          | (simp only [List.mem_map] at h
             obtain ⟨⟨s2, p⟩, h2, rfl⟩ := h
             exact AppUp.trans d1 (loadUnits_appUp h2))
      · cases h
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact AppUpM.refl' _ _ _

theorem evalOp_appUp {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s op) : AppUp s r.1 := by
  cases op <;> simp only [evalOp] at h
  all_goals (try simp only [ol, bind, Option.bind, pure, Option.map] at h)
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h
       first | exact AppUpM.refl' _ _ _ | exact fenceS_appUp _ _ | exact allocBuf_appUp _ _ _ _)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact loadUnits_appUp hx
         | exact storeUnits_appUp _ _ _ _ _ hx
         | exact alloc_appUp hx
         | exact stepRmw_appUp (th := mth s _ _ _) hx)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       first
         | exact AppUp.trans (projM_appUp hx) (injM_appUp hy)
         | exact AppUp.trans (loadUnits_appUp hx) (storeUnits_appUp _ _ _ _ _ hy))
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       have d1 := loadUnits_appUp hx
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         exact AppUp.trans d1 (storeUnits_appUp _ _ _ _ _ hy)
       · simp at h)
    | (simp only [List.mem_filterMap] at h
       obtain ⟨x, hx, h⟩ := h
       have d1 := loadUnits_appUp hx
       cases hn : numOf x.2 <;> simp [hn] at h
       subst h; exact d1)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h; dsimp only; exact allocBuf_appUp _ _ _ _)

/-- **(F2′ P3) A thread step** never adds a promise, fulfils only at or below
the new `vWr`, and appends only with the new `vWr` at least the old size. -/
theorem tstep_appUp {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {r : Memory × List Ts × TTh} (h : r ∈ tstep g mem pairs th) :
    AppUp (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) := by
  simp only [tstep] at h
  split at h
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_singleton] at h; subst h; exact AppUpM.refl' _ _ _)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
       obtain ⟨th', ⟨fr, -, he⟩, rfl⟩ := h
       obtain ⟨h1, h2⟩ := enter_eq he
       show AppUpM mem th.vs th.promises mem th'.vs th'.promises
       rw [h1, h2]; exact AppUpM.refl' _ _ _)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
       obtain ⟨th', he, rfl⟩ := h
       obtain ⟨h1, h2⟩ := enter_eq he
       show AppUpM mem th.vs th.promises mem th'.vs th'.promises
       rw [h1, h2]; exact AppUpM.refl' _ _ _)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact evalOp_appUp hx
         | (split <;> exact evalOp_appUp hx)
         | exact stepRmw_appUp (th := mth _ _ _ _) hx
         | exact stepRmwPair_appUp (th := mth _ _ _ _) hx)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       exact AppUp.trans (projM_appUp hx) (injM_appUp hy))
    | (simp only [List.mem_singleton] at h; subst h; exact fenceS_appUp _ .st)

/-! ### The window invariant along a solo run -/

/-- Along a solo run of thread `i` from `c0`: `vWr` and memory grow; every
outstanding promise is old or was appended in the run; every old promise no
longer outstanding is at or below `vWr`; and every message appended in the run
is still an outstanding promise, unless `vWr` has reached `c0`'s size. -/
def WinInv (c0 : Cfg) (i : Nat) (c : Cfg) : Prop :=
  ∃ th0 th, c0.ths[i]? = some th0 ∧ c.ths[i]? = some th ∧ th0.vs.vWr ≤ th.vs.vWr ∧
    MemExt c0.mem c.mem ∧ (∀ t ∈ th.promises, t ∈ th0.promises ∨ c0.mem.size ≤ t) ∧
    (∀ t ∈ th0.promises, t ∉ th.promises → t ≤ th.vs.vWr) ∧
    (∀ t, c0.mem.size ≤ t → t < c.mem.size → t ∈ th.promises ∨ c0.mem.size ≤ th.vs.vWr)

theorem winInv_refl {c0 : Cfg} {i : Nat} {th0 : TTh} (h : c0.ths[i]? = some th0) : WinInv c0 i c0 :=
  ⟨th0, th0, h, h, Nat.le_refl _, MemExt.rfl' _, fun _ ht => Or.inl ht, fun _ h h' => absurd h h',
    fun _ h1 h2 => absurd (Nat.lt_of_lt_of_le h2 h1) (Nat.lt_irrefl _)⟩

theorem winInv_thread {p : Prog} {k : Promises.Knobs} {arch : Arch} {c0 c c' : Cfg} {i : Nat}
    (hw : WinInv c0 i c) (hs : c' ∈ threadSteps p k arch c i) : WinInv c0 i c' := by
  obtain ⟨th0, th, h0, hth, v1, m1, p1, f1, a1⟩ := hw
  simp only [threadSteps, hth, List.mem_map] at hs
  obtain ⟨⟨mem, pairs, th'⟩, hr, rfl⟩ := hs
  obtain ⟨u1, u2, u3, u4, u5⟩ := tstep_appUp (g := gOf p k arch c i) hr
  dsimp only [stOf] at u1 u2 u3 u4 u5
  have hN := TermFul.memExt_size m1
  refine ⟨th0, th', h0, arr_set hth, Nat.le_trans v1 u1, m1.trans u2, fun t ht => p1 t (u3 t ht),
    fun t ht ht' => ?_, fun t ht1 ht2 => ?_⟩
  · by_cases h2 : t ∈ th.promises
    · exact u4 t h2 ht'
    · exact Nat.le_trans (f1 t ht h2) u1
  · by_cases h2 : t < c.mem.size
    · rcases a1 t ht1 h2 with h3 | h3
      · by_cases h4 : t ∈ th'.promises
        · exact Or.inl h4
        · exact Or.inr (Nat.le_trans ht1 (u4 t h3 h4))
      · exact Or.inr (Nat.le_trans h3 u1)
    · have h6 : t < mem.size := ht2
      have := u5 (by omega)
      exact Or.inr (by omega)

theorem winInv_prom {c0 c : Cfg} {i : Nat} {a : Address} {v : Val} {w : Ts}
    (hw : WinInv c0 i c) : WinInv c0 i (promise c i a v w) := by
  obtain ⟨th0, th, h0, hth, v1, m1, p1, f1, a1⟩ := hw
  have hN := TermFul.memExt_size m1
  refine ⟨th0, { th with promises := th.promises ++ [c.mem.size] }, h0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [promise, hth]; exact arr_set hth
  · exact v1
  · simp only [promise, hth]; exact m1.trans (MemExt.push _ _)
  · intro t ht
    simp only [List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact p1 t ht
    · exact Or.inr hN
  · intro t ht ht'
    simp only [List.mem_append, not_or] at ht'
    exact f1 t ht ht'.1
  · intro t ht1 ht2
    simp only [promise, hth, Array.size_push] at ht2
    simp only [List.mem_append, List.mem_singleton]
    by_cases h2 : t < c.mem.size
    · rcases a1 t ht1 h2 with h3 | h3
      · exact Or.inl (Or.inl h3)
      · exact Or.inr h3
    · exact Or.inl (Or.inr (by omega))

/-- The extern move keeps the window invariant (views, promises, memory unchanged). -/
theorem winInv_ext {c0 c c' : Cfg} {i : Nat} (hw : WinInv c0 i c) (hs : c' ∈ extSteps c i) : WinInv c0 i c' := by
  obtain ⟨th0, th, h0, hth, a1, a2, a3, a4, a5⟩ := hw
  obtain ⟨th1, e, v, w, b, h1, h2⟩ := extSteps_self hs
  rw [hth] at h1; cases h1
  obtain ⟨th2, th3, h3, h4, -, hv⟩ := extSteps_vle hs
  rw [hth] at h3; cases h3
  rw [h2] at h4; cases h4
  refine ⟨th0, _, h0, h2, Nat.le_trans a1 hv.vWr, by rw [extSteps_mem hs]; exact a2, a3,
    fun t ht1 ht2 => Nat.le_trans (a4 t ht1 ht2) hv.vWr, ?_⟩
  rw [extSteps_mem hs]
  intro t ht1 ht2
  rcases a5 t ht1 ht2 with h5 | h5
  · exact Or.inl h5
  · exact Or.inr (Nat.le_trans h5 hv.vWr)

theorem solo_winInv {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c0 c c' : Cfg}
    (h : Solo p k arch i c c') (hw : WinInv c0 i c) : WinInv c0 i c' := by
  induction h with
  | refl => exact hw
  | thread hs _ ih => exact ih (winInv_thread hw hs)
  | prom _ _ _ _ _ ih => exact ih (winInv_prom hw)
  | ext hs _ ih => exact ih (winInv_ext hw hs)

/-- **(F2′ P3) The plant-to-publish window.**  Thread `i` plants a promise `B`
(at index `cP.mem.size`, view `w < cP.mem.size`), runs solo to `c`, and
publishes there (successor certified) with `B` still outstanding.  Then
`vWr ≤ w` at the publish (P1), and in the window: every message appended is
still an outstanding promise of `i` (no thread step appended); every promise of
`i` at the plant that was fulfilled lies at or below `vWr` at the publish
(hence below the plant's size); and every outstanding promise was outstanding
at the plant or was planted in the window.  So every write of the window is
the fulfil of a promise outstanding at the plant, at an index `≤ vWr`. -/
theorem plant_pub_window {p : Prog} {k : Promises.Knobs} {arch : Arch} {cP c c' : Cfg} {i : Nat}
    {a0 : Address} {v0 : Val} {w : Ts} (hw : w < cP.mem.size)
    (hsolo : Solo p k arch i (promise cP i a0 v0 w) c)
    (hs : c' ∈ threadSteps p k arch c i) (hc' : Certified p k arch c' i)
    {thP th : TTh} (hthP : cP.ths[i]? = some thP) (hth : c.ths[i]? = some th)
    {y : String} {a : At} {e : Expr} (hterm : th.term = .let_ y (.publish a) e)
    (hB : cP.mem.size ∈ th.promises) :
    th.vs.vWr ≤ w ∧ MemExt cP.mem c.mem ∧
      (∀ t, cP.mem.size ≤ t → t < c.mem.size → t ∈ th.promises) ∧
      (∀ t ∈ thP.promises, t ∉ th.promises → t ≤ th.vs.vWr) ∧
      (∀ t ∈ th.promises, t ∈ thP.promises ∨ cP.mem.size ≤ t) := by
  have hW := solo_winInv (Solo.prom a0 v0 w hw hsolo) (winInv_refl hthP)
  obtain ⟨th0, th1, h0, h1, -, m1, p1, f1, a1⟩ := hW
  rw [hthP] at h0; cases h0
  rw [hth] at h1; cases h1
  have hmB : c.mem[cP.mem.size]? = some ⟨a0, v0, w⟩ := by
    have hext := solo_winInv hsolo (winInv_refl (c0 := promise cP i a0 v0 w)
      (th0 := { thP with promises := thP.promises ++ [cP.mem.size] })
      (by simp only [promise, hthP]; exact arr_set hthP))
    obtain ⟨-, -, -, -, -, m2, -⟩ := hext
    apply m2
    simp only [promise, hthP, Array.getElem?_push_size]
  have hv : th.vs.vWr ≤ w := certified_pub_vWrLe hs hc' hth hterm hB hmB
  refine ⟨hv, m1, fun t ht1 ht2 => ?_, f1, p1⟩
  rcases a1 t ht1 ht2 with h3 | h3
  · exact h3
  · exact absurd (Nat.lt_of_le_of_lt (Nat.le_trans h3 hv) hw) (Nat.lt_irrefl _)

/-! ### (F2′ P4) Holders above the placeholder -/

/-- A certified run's prefix is certified. -/
theorem solo_append {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c1 c2 c3 : Cfg}
    (h1 : Solo p k arch i c1 c2) (h2 : Solo p k arch i c2 c3) : Solo p k arch i c1 c3 := by
  induction h1 with
  | refl => exact h2
  | thread hs _ ih => exact Solo.thread hs (ih h2)
  | prom a v w hw _ ih => exact Solo.prom a v w hw (ih h2)
  | ext hs _ ih => exact Solo.ext hs (ih h2)

theorem certified_of_solo {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c c2 : Cfg}
    (h : Solo p k arch i c c2) (hc : Certified p k arch c2 i) : Certified p k arch c i := by
  obtain ⟨c3, h3, hn⟩ := hc
  exact ⟨c3, solo_append h h3, hn⟩

/-- **(F2′ P4) Holder above the placeholder.**  If thread `i`'s coherence view
at a word has reached `tp` (e.g. the allocation placeholder at `tp`, right
after the allocation), then every promise of `i` at that word outstanding now
lies strictly above `tp`, provided the run continues to a certified
configuration: a promise at or below `tp` is dead (`certified_promAbove`). -/
theorem holder_abovePlaceholder {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat}
    {c c2 : Cfg} (h : Solo p k arch i c c2) (hc2 : Certified p k arch c2 i)
    {th : TTh} (hth : c.ths[i]? = some th) {t tp : Ts} {m : Msg} (ht : t ∈ th.promises)
    (hm : c.mem[t]? = some m) (hp : tp ≤ th.vs.coh m.loc) : tp < t :=
  Nat.lt_of_le_of_lt hp (certified_promAbove (certified_of_solo h hc2) hth ht hm)

#print axioms solo_append
#print axioms certified_of_solo
#print axioms holder_abovePlaceholder

#print axioms AppUpM.trans
#print axioms AppUpM.ful
#print axioms appUp_lock
#print axioms stepStore_appUp
#print axioms stepRmw_appUp
#print axioms loadUnits_appUp
#print axioms storeUnits_appUp
#print axioms fenceS_appUp
#print axioms fold_appUp
#print axioms allocBuf_appUp
#print axioms alloc_appUp
#print axioms injM_appUp
#print axioms projM_appUp
#print axioms evalOp_appUp
#print axioms tstep_appUp
#print axioms winInv_thread
#print axioms winInv_prom
#print axioms solo_winInv
#print axioms plant_pub_window
#print axioms TermFul.promsOf_ext
#print axioms TermCert.winInv_ext

end TermCert
