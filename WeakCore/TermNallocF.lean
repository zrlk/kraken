/-
G1a helper: a thread step that is not an allocation (`new`, `newBuf`, `inl`, `inr`, `case`)
keeps the allocation count.  Depends on `TermRun` only.
-/
import WeakCore.TermRun

namespace TermNallocF
open CoreLang CoreTerm TermRun
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

theorem loadUnits_nallocF {arch : Arch} {pw : Word} {a : Address} {acq : Bool} :
    ∀ (us : List Acc) (k : Nat) (s : St) (r : St × List Word), r ∈ loadUnits arch pw a acq us k s →
      r.1.nalloc = s.nalloc
  | [], _, s, r, hr => by simp only [loadUnits, List.mem_singleton] at hr; subst hr; rfl
  | .one :: us, k, s, r, hr => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, -, ⟨s', ws⟩, hmem, rfl⟩ := hr
      have := loadUnits_nallocF us (k + 1) _ (s', ws) hmem; exact this
  | .two :: us, k, s, r, hr => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, -, ⟨s', ws⟩, hmem, rfl⟩ := hr
      have := loadUnits_nallocF us (k + 2) _ (s', ws) hmem; exact this

theorem storeUnits_nallocF {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s' ∈ storeUnits k arch pw a rel us ws i s →
      s'.nalloc = s.nalloc
  | [], _, _, s, s', hs => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs; rfl
  | .one :: us, w :: ws, i, s, s', hs => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, -, hs⟩ := hs
      have := storeUnits_nallocF us ws (i + 1) _ s' hs; exact this
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs => by
      simp only [storeUnits] at hs
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel = R at hs
      obtain ⟨mem', pairs', th⟩ := R
      simp only at hs
      have := storeUnits_nallocF us ws (i + 2) _ s' hs; exact this
  | .one :: _, [], _, _, _, hs => by simp [storeUnits] at hs
  | .two :: _, [], _, _, _, hs => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, _, hs => by simp [storeUnits] at hs

theorem enter_nallocF {g : G} {th th' : TTh} {f : String} {ts : List Ty} {a : At}
    (h : enter g th f ts a = some th') : th'.nalloc = th.nalloc := by
  unfold enter at h
  simp only [bind, Option.bind] at h
  repeat' (first | (split at h) | (dsimp only at h; split at h))
  all_goals first
    | (simp at h; done)
    | (simp only [pure, Option.some.injEq] at h; subst h; rfl)
    | (simp only [Option.some.injEq] at h; subst h; rfl)

/-- An operation other than `new`, `newBuf`, `inl` and `inr` keeps the allocation count. -/
theorem evalOp_nallocEq {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s op)
    (h1 : ∀ a T, op ≠ .new a T) (h2 : ∀ n τ, op ≠ .newBuf n τ) (h3 : ∀ τ a, op ≠ .inl τ a)
    (h4 : ∀ τ a, op ≠ .inr τ a) : r.1.nalloc = s.nalloc := by
  cases op
  case new a T => exact absurd rfl (h1 a T)
  case newBuf n τ => exact absurd rfl (h2 n τ)
  case inl τ a => exact absurd rfl (h3 τ a)
  case inr τ a => exact absurd rfl (h4 τ a)
  all_goals simp only [evalOp] at h
  all_goals (try simp only [ol, bind, Option.bind, pure, Option.map] at h)
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h
       rfl)
    | (simp only [List.mem_cons, List.not_mem_nil, or_false] at h
       subst h
       rfl)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact loadUnits_nallocF _ _ _ _ hx
         | exact storeUnits_nallocF _ _ _ _ _ hx
         | rfl)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       exact (storeUnits_nallocF _ _ _ _ _ hy).trans (loadUnits_nallocF _ _ _ _ hx))
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         exact (storeUnits_nallocF _ _ _ _ _ hy).trans (loadUnits_nallocF _ _ _ _ hx)
       · simp at h)
    | (simp only [List.mem_filterMap] at h
       obtain ⟨x, hx, h⟩ := h
       cases hn : numOf x.2 <;> simp [hn] at h
       subst h; exact loadUnits_nallocF _ _ _ _ hx)

/-- The terms whose step may allocate. -/
def NotAllocT (t : Expr) : Prop :=
  (∀ x a T e, t ≠ .let_ x (.new a T) e) ∧ (∀ x n τ e, t ≠ .let_ x (.newBuf n τ) e) ∧
  (∀ x τ a e, t ≠ .let_ x (.inl τ a) e) ∧ (∀ x τ a e, t ≠ .let_ x (.inr τ a) e) ∧
  (∀ a x e₁ y e₂, t ≠ .case a x e₁ y e₂)

/-- **A step that is not an allocation keeps the allocation count.** -/
theorem tstep_nallocEq {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {r : Memory × List Ts × TTh} (h : r ∈ tstep g mem pairs th) (hne : NotAllocT th.term) :
    r.2.2.nalloc = th.nalloc := by
  obtain ⟨n1, n2, n3, n4, n5⟩ := hne
  cases ht : th.term with
  | let_ x op e =>
      cases op with
      | new a T => exact absurd ht (n1 x a T e)
      | newBuf n τ => exact absurd ht (n2 x n τ e)
      | inl τ a => exact absurd ht (n3 x τ a e)
      | inr τ a => exact absurd ht (n4 x τ a e)
      | call f is a ts =>
          simp only [tstep, ht, ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
          obtain ⟨th', ⟨fr, -, he⟩, rfl⟩ := h
          have := enter_nallocF he
          exact this
      | callc f a =>
          simp only [tstep, ht] at h
          repeat' (first | (split at h) | (dsimp only at h; split at h))
          all_goals first
            | (simp at h; done)
            | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
               obtain ⟨th', ⟨fr, -, he⟩, rfl⟩ := h
               have := enter_nallocF he
               exact this)
      | _ =>
          simp only [tstep, ht, List.mem_map] at h
          obtain ⟨⟨s', t, ws⟩, hy, rfl⟩ := h
          exact evalOp_nallocEq hy (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
            (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
  | case a x e₁ y e₂ => exact absurd ht (n5 a x e₁ y e₂)
  | _ =>
      simp only [tstep, ht] at h
      repeat' (first | (split at h) | (dsimp only at h; split at h))
      all_goals first
        | (simp at h; done)
        | (simp only [List.mem_singleton] at h; subst h; rfl)
        | (simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; rfl)
        | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
           obtain ⟨th', he, rfl⟩ := h
           exact enter_nallocF he)
        | (simp only [List.mem_map] at h
           obtain ⟨x, hx, rfl⟩ := h
           rfl)

/-! ### Every step: the allocation count does not drop; the allocation records only grow -/

/-- An allocation raises the allocation count by one. -/
theorem alloc_nallocF {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc}
    {ws : List Word} {s : St} {r : St × Word} (hr : r ∈ alloc k arch lbl us ws s) : r.1.nalloc = s.nalloc + 1 := by
  simp only [alloc, List.mem_map] at hr
  obtain ⟨s', hs, rfl⟩ := hr
  exact storeUnits_nallocF _ _ _ _ s' hs

/-- An allocation's pointer word names the allocated label at offset zero. -/
theorem alloc_pwF {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc}
    {ws : List Word} {s : St} {r : St × Word} (hr : r ∈ alloc k arch lbl us ws s) : r.2 = cst (.loc ⟨lbl, 0⟩ 0) := by
  simp only [alloc, List.mem_map] at hr
  obtain ⟨s', -, rfl⟩ := hr
  rfl

theorem injM_nallocF {g : G} {s : St} {ty : Ty} {j : Nat} {p : List Word} {r : St × List Word}
    (h : r ∈ injM g s ty j p) : s.nalloc ≤ r.1.nalloc := by
  unfold injM at h
  split at h
  · split at h
    · simp only [List.mem_map] at h
      obtain ⟨⟨s', pw⟩, hs, rfl⟩ := h
      have h1 := alloc_nallocF hs
      have h2 : s.nalloc ≤ s'.nalloc := by dsimp only at h1; omega
      dsimp only
      split
      · exact h2
      · exact h2
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact Nat.le_refl _

theorem projM_nallocF {g : G} {s : St} {ty : Ty} {ws : List Word} {r : St × Nat × List Word}
    (h : r ∈ projM g s ty ws) : r.1.nalloc = s.nalloc := by
  unfold projM at h
  split at h
  · split at h
    · split at h
      · simp only [List.mem_flatMap] at h
        obtain ⟨⟨s1, tw⟩, h1, h⟩ := h
        have a1 := loadUnits_nallocF _ _ _ _ h1
        repeat' split at h
        all_goals first
          | (simp at h; done)
          | (simp only [List.mem_map] at h
             obtain ⟨⟨s2, p⟩, h2, rfl⟩ := h
             exact (loadUnits_nallocF _ _ _ _ h2).trans a1)
      · cases h
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    rfl

theorem evalOp_nallocLe {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s op) : s.nalloc ≤ r.1.nalloc := by
  cases op <;> simp only [evalOp] at h
  all_goals (try simp only [ol, bind, Option.bind, pure, Option.map] at h)
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h
       first | exact Nat.le_refl _ | exact Nat.le_succ _)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact Nat.le_of_eq (loadUnits_nallocF _ _ _ _ hx).symm
         | exact Nat.le_of_eq (storeUnits_nallocF _ _ _ _ _ hx).symm
         | (have h1 := alloc_nallocF hx; dsimp only at h1 ⊢; omega)
         | exact Nat.le_refl _)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       first
         | exact Nat.le_trans (Nat.le_of_eq (projM_nallocF hx).symm) (injM_nallocF hy)
         | exact Nat.le_trans (Nat.le_of_eq (loadUnits_nallocF _ _ _ _ hx).symm)
             (Nat.le_of_eq (storeUnits_nallocF _ _ _ _ _ hy).symm))
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         exact Nat.le_trans (Nat.le_of_eq (loadUnits_nallocF _ _ _ _ hx).symm)
             (Nat.le_of_eq (storeUnits_nallocF _ _ _ _ _ hy).symm)
       · simp at h)
    | (simp only [List.mem_filterMap] at h
       obtain ⟨x, hx, h⟩ := h
       split at h
       · simp only [Option.some.injEq] at h
         subst h
         exact Nat.le_of_eq (loadUnits_nallocF _ _ _ _ hx).symm
       · cases h)

/-- **A thread step does not lower the allocation count.** -/
theorem tstep_nallocLe {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {r : Memory × List Ts × TTh} (h : r ∈ tstep g mem pairs th) : th.nalloc ≤ r.2.2.nalloc := by
  simp only [tstep] at h
  split at h
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_singleton] at h; subst h; exact Nat.le_refl _)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
       obtain ⟨th', ⟨fr, -, he⟩, rfl⟩ := h
       exact Nat.le_of_eq (enter_nallocF he).symm)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
       obtain ⟨th', he, rfl⟩ := h
       exact Nat.le_of_eq (enter_nallocF he).symm)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact evalOp_nallocLe hx
         | exact Nat.le_refl _
         | (split <;> exact evalOp_nallocLe hx))
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       exact Nat.le_trans (Nat.le_of_eq (projM_nallocF hx).symm) (injM_nallocF hy))

theorem enter_tysF {g : G} {th th' : TTh} {f : String} {ts : List Ty} {a : At}
    (h : enter g th f ts a = some th') : th'.tys = th.tys := by
  unfold enter at h
  simp only [bind, Option.bind] at h
  repeat' (first | (split at h) | (dsimp only at h; split at h))
  all_goals first
    | (simp at h; done)
    | (simp only [pure, Option.some.injEq] at h; subst h; rfl)
    | (simp only [Option.some.injEq] at h; subst h; rfl)

/-- A step that is not a `new` keeps the thread's allocation records. -/
theorem tstep_tys_keep {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {r : Memory × List Ts × TTh} (h : r ∈ tstep g mem pairs th)
    (hnn : ∀ x a T e, th.term ≠ .let_ x (.new a T) e) : r.2.2.tys = th.tys := by
  simp only [tstep] at h
  split at h
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (exact absurd ‹th.term = _› (hnn _ _ _ _))
    | (simp only [List.mem_singleton] at h; subst h; rfl)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
       obtain ⟨th', ⟨fr, -, he⟩, rfl⟩ := h
       have h1 := enter_tysF he
       exact h1)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
       obtain ⟨th', he, rfl⟩ := h
       have h1 := enter_tysF he
       exact h1)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first | rfl | (split <;> rfl))
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       rfl)

/-- A `new` operation allocates at the thread's next fresh label and binds a pointer to it. -/
theorem evalOp_new_mem {g : G} {env : Env} {σs : List Ty} {s : St} {a : At} {T : Option Ty}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.new a T)) :
    r.1.nalloc = s.nalloc + 1 ∧ r.2.2 = [cst (.loc ⟨freshLabel g.lbase g.n g.i s.nalloc, 0⟩ 0)] := by
  simp only [evalOp] at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [List.mem_map] at h
      obtain ⟨⟨s', pw⟩, hal, rfl⟩ := h
      exact ⟨alloc_nallocF hal, congrArg (fun w => [w]) (alloc_pwF hal)⟩

/-- A `new` step appends at most one allocation record: at the label of the pointer it binds, with
the closed static type. -/
theorem tstep_new_tys {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {x : String} {a : At}
    {T : Option Ty} {e : Expr} {r : Memory × List Ts × TTh} (ht : th.term = .let_ x (.new a T) e)
    (h : r ∈ tstep g mem pairs th) :
    ∃ s' t ws, (s', t, ws) ∈ evalOp g th.env th.σs (stOf mem pairs th) (.new a T) ∧ r.2.2.nalloc = s'.nalloc ∧
      (r.2.2.tys = th.tys ∨ ∃ T' l tag f, T = some T' ∧ ws.map (·.val) = [Val.loc l tag] ∧
        r.2.2.tys = th.tys ++ [(l.label, close th.σs T', f)]) := by
  simp only [tstep, ht, List.mem_map] at h
  obtain ⟨⟨s', t, ws⟩, hin, rfl⟩ := h
  refine ⟨s', t, ws, hin, ?_⟩
  dsimp only
  split
  · next T' l tag hw => exact ⟨rfl, .inr ⟨T', l, tag, _, rfl, hw, rfl⟩⟩
  · exact ⟨rfl, .inl rfl⟩

/-- **The allocation records of a step's result extend the thread's.** -/
theorem tstep_tys_prefix {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {r : Memory × List Ts × TTh} (h : r ∈ tstep g mem pairs th) : ∃ new, r.2.2.tys = th.tys ++ new := by
  by_cases hn : ∃ x a T e, th.term = .let_ x (.new a T) e
  · obtain ⟨x, a, T, e, ht⟩ := hn
    obtain ⟨-, -, -, -, -, h1 | ⟨T', l, tag, f, -, -, h1⟩⟩ := tstep_new_tys ht h
    · exact ⟨[], by rw [h1, List.append_nil]⟩
    · exact ⟨_, h1⟩
  · exact ⟨[], by rw [tstep_tys_keep h (fun x a T e h => hn ⟨x, a, T, e, h⟩), List.append_nil]⟩

end TermNallocF

#print axioms TermNallocF.evalOp_nallocEq
#print axioms TermNallocF.tstep_nallocEq
