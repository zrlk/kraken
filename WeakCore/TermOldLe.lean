/-
Old-message coherence persistence: a message `t` at `m.loc` whose coherence
view has reached it stays reached across a thread step (no `CohAt` needed).
A clone of `TermCert` §2–§4 without the promise-membership part.
-/
import WeakCore.TermCert

namespace TermOldLe
open CoreLang CoreTerm TermRun TermCert
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- `t` is a message whose coherence view at its address has reached it. -/
def OldM (mem : Memory) (vs : VState) (t : Ts) : Prop :=
  ∃ m, mem[t]? = some m ∧ t ≤ vs.coh m.loc

def OldP (s : St) (t : Ts) : Prop := OldM s.mem s.vs t

theorem OldM.lt {mem : Memory} {vs : VState} {t : Ts} (h : OldM mem vs t) : t < mem.size := by
  obtain ⟨m, hm, _⟩ := h
  exact TermMem.lt_of_get hm

theorem OldM.mono {mem mem' : Memory} {vs vs' : VState} {t : Ts}
    (h : OldM mem vs t) (hm : MemExt mem mem')
    (hc : ∀ m, mem[t]? = some m → t ≤ vs.coh m.loc → t ≤ vs'.coh m.loc) : OldM mem' vs' t := by
  obtain ⟨m, hm1, hm2⟩ := h
  exact ⟨m, hm t m hm1, hc m hm1 hm2⟩

theorem stepLoad_old {arch : Arch} {mem : Memory} {pairs : List Ts} {th th' : Promises.Thread}
    {dst : WeakMem.Reg} {a : Address} {deps : List WeakMem.Reg} {acq : Bool} {t : Ts}
    (h : th' ∈ Promises.stepLoad arch mem pairs th dst a deps acq)
    (hd : OldM mem th.vs t) : OldM mem th'.vs t := by
  simp only [Promises.stepLoad, List.mem_map, List.mem_filter, List.mem_range] at h
  obtain ⟨tr, _, rfl⟩ := h
  refine hd.mono (MemExt.rfl' _) fun m _ hle => ?_
  show t ≤ (if m.loc = a then _ else _)
  split
  · rename_i he; subst he; exact Nat.le_trans hle (Nat.le_max_left _ _)
  · exact hle

theorem stepLoadPair_old {arch : Arch} {mem : Memory} {pairs : List Ts} {th th' : Promises.Thread}
    {dst0 dst1 : WeakMem.Reg} {a : Address} {deps : List WeakMem.Reg} {acq : Bool} {t : Ts}
    (h : th' ∈ Promises.stepLoadPair arch mem pairs th dst0 dst1 a deps acq)
    (hd : OldM mem th.vs t) : OldM mem th'.vs t := by
  simp only [Promises.stepLoadPair, List.mem_flatMap, List.mem_filterMap, List.mem_filter,
    List.mem_range] at h
  obtain ⟨t0, _, t1, _, hs⟩ := h
  split at hs
  · cases hs
  · simp only [Option.some.injEq] at hs
    subst hs
    refine hd.mono (MemExt.rfl' _) fun m _ hle => ?_
    show t ≤ (if m.loc = a then _ else if m.loc = a.next then _ else _)
    split
    · rename_i he; subst he; exact Nat.le_trans hle (Nat.le_max_left _ _)
    · split
      · rename_i _ he; rw [he] at hle; exact Nat.le_trans hle (Nat.le_max_left _ _)
      · exact hle

theorem oldM_lock {arch : Arch} {mem : Memory} {x : Promises.Thread} {t : Ts}
    (h : OldM mem x.vs t) :
    OldM mem (if arch = .tso then Promises.stepFence x .sy else x).vs t := by
  split
  · unfold OldM at *; rw [stepFence_coh]; exact h
  · exact h

theorem stepStore_old {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {th th' : Promises.Thread}
    {a : Address} {e : WeakMem.Expr} {deps : List WeakMem.Reg} {rel : Bool} {t : Ts}
    (h : (mem', th') ∈ Promises.stepStore k arch mem th a e deps rel)
    (hd : OldM mem th.vs t) : OldM mem' th'.vs t := by
  have hob := storeOb_coh k arch th a e deps
  cases e <;>
  · simp only [Promises.stepStore, List.mem_append, List.mem_singleton, List.mem_filterMap] at h
    rcases h with h | ⟨tw, _, hf⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine hd.mono (MemExt.push _ _) fun m _ hle => ?_
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
            obtain ⟨m0, hm0, hle0⟩ := hd
            refine ⟨m0, hm0, ?_⟩
            show t ≤ (if m0.loc = a then tw else th.vs.coh m0.loc)
            split
            · rename_i he; rw [he] at hle0
              exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_trans hle0 hob) hlt)
            · exact hle0
          · simp at hf

theorem stepRmw_old_at {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool} {t : Ts}
    (h : (mem', th') ∈ Promises.stepRmwAt k arch mem pairs th dst a kind newv deps acq rel)
    (hd : OldM mem th.vs t) : OldM mem' th'.vs t := by
  simp only [Promises.stepRmwAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨tr, _, h⟩ := h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    apply oldM_lock
    refine hd.mono (MemExt.rfl' _) fun m _ hle => ?_
    show t ≤ (if m.loc = a then _ else _)
    split
    · rename_i he; rw [he] at hle; exact le_maxL hle
    · exact hle
  · simp only [List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        apply oldM_lock
        refine hd.mono (MemExt.push _ _) fun m _ hle => ?_
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
            obtain ⟨m0, hm0, hle0⟩ := hd
            apply oldM_lock
            refine ⟨m0, hm0, ?_⟩
            show t ≤ (if m0.loc = a then tw else if m0.loc = a then _ else _)
            split
            · rename_i he; rw [he] at hle0
              exact Nat.le_of_lt (Nat.lt_of_le_of_lt hle0 key)
            · exact hle0

theorem stepRmw_old {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool} {t : Ts}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs th dst a kind newv deps acq rel)
    (hd : OldM mem th.vs t) : OldM mem' th'.vs t :=
  stepRmw_old_at (th := if arch = .tso then Promises.stepFence th .sy else th) h (oldM_lock hd)

theorem stepStorePair_old {mem : Memory} {pairs : List Ts} {th : Promises.Thread} {a : Address}
    {e0 e1 : WeakMem.Expr} {deps : List WeakMem.Reg} {rel : Bool} {t : Ts}
    (hd : OldM mem th.vs t) :
    OldM (Promises.stepStorePair mem pairs th a e0 e1 deps rel).1
      (Promises.stepStorePair mem pairs th a e0 e1 deps rel).2.2.vs t := by
  obtain ⟨q1, -, q3, -, -⟩ := TermMem.stepStorePair_eq mem pairs th a e0 e1 deps rel
  have hlt := hd.lt
  refine hd.mono (by rw [q1]; exact (MemExt.push _ _).trans (MemExt.push _ _))
    fun m _ hle => ?_
  rw [q3]
  show t ≤ (if m.loc = a then _ else if m.loc = a.next then _ else _)
  split
  · exact Nat.le_of_lt hlt
  · split
    · exact Nat.le_succ_of_le (Nat.le_of_lt hlt)
    · exact hle

/-- The pair RMW.  Its fulfil branch discharges `tw` and `tw + 1` but checks
`ob < tw` only against the first word's coherence; the second word's promise
cannot be dead all the same, because the second read `t1` is readable (so no
message at `a.next` lies in `(t1, coh a.next]`) and adjacent to `tw + 1`
(`t1 < tw + 1`). -/
theorem stepRmwPair_old_at {arch : Arch} {mem mem' : Memory} {pairs pairs' : List Ts}
    {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address} {cmp0 cmp1 : Val}
    {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool} {t : Ts}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPairAt arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel)
    (hd : OldM mem th.vs t) : OldM mem' th'.vs t := by
  simp only [Promises.stepRmwPairAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨t0, ⟨_, hr0⟩, t1, ⟨_, hr1⟩, h⟩ := h
  split at h
  · simp at h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    apply oldM_lock
    refine hd.mono (MemExt.rfl' _) fun m _ hle => ?_
    show t ≤ (if m.loc = a then _ else if m.loc = a.next then _ else _)
    repeat' split
    all_goals first | exact hle | (rename_i he; rw [he] at hle; exact le_maxL hle)
  simp only [List.mem_append] at h
  rcases h with h | h
  · split at h
    · simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hlt := hd.lt
      apply oldM_lock
      refine hd.mono ((MemExt.push _ _).trans (MemExt.push _ _)) fun m _ hle => ?_
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
    obtain ⟨m0, hm0, hle0⟩ := hd
    apply oldM_lock
    refine ⟨m0, hm0, ?_⟩
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

theorem stepRmwPair_old {arch : Arch} {mem mem' : Memory} {pairs pairs' : List Ts}
    {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address} {cmp0 cmp1 : Val}
    {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool} {t : Ts}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel)
    (hd : OldM mem th.vs t) : OldM mem' th'.vs t :=
  stepRmwPair_old_at (th := if arch = .tso then Promises.stepFence th .sy else th) h (oldM_lock hd)

/-! ## §3 The state-level primitives -/

theorem OldP.lt {s : St} {t : Ts} (h : OldP s t) : t < s.mem.size := OldM.lt h

theorem loadUnits_old {arch : Arch} {pw : Word} {a : Address} {acq : Bool} {t : Ts} :
    ∀ (us : List Acc) (k : Nat) (s : St) (r : St × List Word), r ∈ loadUnits arch pw a acq us k s →
      OldP s t → OldP r.1 t
  | [], _, s, r, hr, hd => by
      simp only [loadUnits, List.mem_singleton] at hr; subst hr; exact hd
  | .one :: us, k, s, r, hr, hd => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, hth, ⟨s', ws⟩, hmem, rfl⟩ := hr
      exact loadUnits_old us (k + 1) _ (s', ws) hmem
        (stepLoad_old (th := mth s pw pw pw) hth hd)
  | .two :: us, k, s, r, hr, hd => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, hth, ⟨s', ws⟩, hmem, rfl⟩ := hr
      exact loadUnits_old us (k + 2) _ (s', ws) hmem
        (stepLoadPair_old (th := mth s pw pw pw) hth hd)

theorem storeUnits_old {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool}
    {t : Ts} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s' ∈ storeUnits k arch pw a rel us ws i s →
      OldP s t → OldP s' t
  | [], _, _, s, s', hs, hd => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs; exact hd
  | .one :: us, w :: ws, i, s, s', hs, hd => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      exact storeUnits_old us ws (i + 1) _ s' hs (stepStore_old (th := mth s pw w w) hst hd)
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs, hd => by
      simp only [storeUnits] at hs
      have h2 := stepStorePair_old (pairs := s.pairs) (th := mth s pw w0 w1) (a := offs a i)
        (e0 := dataE 1 w0) (e1 := dataE 2 w1) (deps := [0]) (rel := rel) hd
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
        (dataE 2 w1) [0] rel = R at h2 hs
      obtain ⟨mem', pairs', th⟩ := R
      exact storeUnits_old us ws (i + 2) _ s' hs h2
  | .one :: _, [], _, _, s', hs, _ => by simp [storeUnits] at hs
  | .two :: _, [], _, _, s', hs, _ => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, s', hs, _ => by simp [storeUnits] at hs

theorem fenceS_old {s : St} {f : WeakMem.Fence} {t : Ts} (hd : OldP s t) : OldP (fenceS s f) t := by
  show OldM s.mem (Promises.stepFence (mth s _ _ _) f).vs t
  unfold OldM; rw [stepFence_coh]; exact hd

/-- The cells `new` lays down: memory grows, and coherence at the new cells is
raised to them, above every existing message. -/
theorem allocPre_old {s : St} {lbl : AllocLabel} {n : Nat} {f : Nat → Msg} {t : Ts}
    (hd : OldP s t) :
    OldP { s with mem := (List.range n).foldl (fun m j => m.push (f j)) s.mem,
                   vs := { s.vs with coh := fun b =>
                     if b.label = lbl ∧ b.offset < n then s.mem.size + b.offset else s.vs.coh b },
                   nalloc := s.nalloc + 1 } t := by
  have hext : MemExt s.mem ((List.range n).foldl (fun m j => m.push (f j)) s.mem) := by
    intro t' m' h'
    rw [TermMem.fold_get]
    simp only [TermMem.lt_of_get h', ↓reduceIte]
    exact h'
  have hlt := hd.lt
  refine hd.mono hext fun m _ hle => ?_
  show t ≤ (if m.loc.label = lbl ∧ m.loc.offset < n then s.mem.size + m.loc.offset else s.vs.coh m.loc)
  split
  · exact Nat.le_trans (Nat.le_of_lt hlt) (Nat.le_add_right _ _)
  · exact hle

theorem alloc_preso {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc}
    {ws : List Word} {s : St} {t : Ts} {r : St × Word} (hr : r ∈ alloc k arch lbl us ws s)
    (hd : OldP s t) : OldP r.1 t := by
  simp only [alloc, List.mem_map] at hr
  obtain ⟨s', hs, rfl⟩ := hr
  exact storeUnits_old us ws 0 _ s' hs (allocPre_old hd)

theorem allocBuf_preso {lbl : AllocLabel} {n : Nat} {zero : Option (List Val)} {s : St} {t : Ts}
    (hd : OldP s t) : OldP (allocBuf lbl n zero s).1 t :=
  allocPre_old hd

theorem injM_old {g : G} {s : St} {ty : Ty} {j : Nat} {p : List Word} {t : Ts}
    {r : St × List Word} (h : r ∈ injM g s ty j p) (hd : OldP s t) : OldP r.1 t := by
  unfold injM at h
  split at h
  · split at h
    · simp only [List.mem_map] at h
      obtain ⟨⟨s', pw⟩, hs, rfl⟩ := h
      have := alloc_preso hs hd
      dsimp only
      split
      · exact fenceS_old this
      · exact this
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact hd

theorem projM_old {g : G} {s : St} {ty : Ty} {ws : List Word} {t : Ts}
    {r : St × Nat × List Word} (h : r ∈ projM g s ty ws) (hd : OldP s t) : OldP r.1 t := by
  unfold projM at h
  split at h
  · split at h
    · split at h
      · simp only [List.mem_flatMap] at h
        obtain ⟨⟨s1, tw⟩, h1, h⟩ := h
        have d1 := loadUnits_old _ _ _ _ h1 hd
        repeat' split at h
        all_goals first
          | (simp at h; done)
          | (simp only [List.mem_map] at h
             obtain ⟨⟨s2, p⟩, h2, rfl⟩ := h
             exact loadUnits_old _ _ _ _ h2 d1)
      · cases h
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact hd

theorem evalOp_old {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op} {t : Ts}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s op) (hd : OldP s t) : OldP r.1 t := by
  cases op <;> simp only [evalOp] at h
  all_goals (try simp only [ol, bind, Option.bind, pure, Option.map] at h)
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h
       first | exact hd | exact fenceS_old hd | exact allocBuf_preso hd)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact loadUnits_old _ _ _ _ hx hd
         | exact storeUnits_old _ _ _ _ _ hx hd
         | exact alloc_preso hx hd
         | exact stepRmw_old (th := mth s _ _ _) hx hd)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       first
         | exact injM_old hy (projM_old hx hd)
         | exact storeUnits_old _ _ _ _ _ hy (loadUnits_old _ _ _ _ hx hd))
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       have d1 := loadUnits_old _ _ _ _ hx hd
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         exact storeUnits_old _ _ _ _ _ hy d1
       · simp at h)
    | (simp only [List.mem_filterMap] at h
       obtain ⟨x, hx, h⟩ := h
       have d1 := loadUnits_old _ _ _ _ hx hd
       cases hn : numOf x.2 <;> simp [hn] at h
       subst h; exact d1)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h; dsimp only; exact allocBuf_preso hd)

/-! ## §4 A thread step -/

/-- **A thread step keeps a dead promise dead.** -/
theorem tstep_old {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {t : Ts}
    {r : Memory × List Ts × TTh} (h : r ∈ tstep g mem pairs th)
    (hd : OldP (stOf mem pairs th) t) : OldP (stOf r.1 r.2.1 r.2.2) t := by
  simp only [tstep] at h
  split at h
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_singleton] at h; subst h; exact hd)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
       obtain ⟨th', ⟨fr, -, he⟩, rfl⟩ := h
       obtain ⟨h1, -⟩ := TermCert.enter_eq he
       show OldM mem th'.vs t
       rw [h1]; exact hd)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
       obtain ⟨th', he, rfl⟩ := h
       obtain ⟨h1, -⟩ := TermCert.enter_eq he
       show OldM mem th'.vs t
       rw [h1]; exact hd)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact evalOp_old hx hd
         | exact stepRmw_old (th := mth _ _ _ _) hx hd
         | exact stepRmwPair_old (th := mth _ _ _ _) hx hd)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       exact injM_old hy (projM_old hx hd))
    | fail "T"

end TermOldLe
