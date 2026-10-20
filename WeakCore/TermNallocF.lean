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
    (h1 : ∀ a, op ≠ .new a) (h2 : ∀ n τ, op ≠ .newBuf n τ) (h3 : ∀ τ a, op ≠ .inl τ a)
    (h4 : ∀ τ a, op ≠ .inr τ a) : r.1.nalloc = s.nalloc := by
  cases op
  case new a => exact absurd rfl (h1 a)
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
  (∀ x a e, t ≠ .let_ x (.new a) e) ∧ (∀ x n τ e, t ≠ .let_ x (.newBuf n τ) e) ∧
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
      | new a => exact absurd ht (n1 x a e)
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
          exact evalOp_nallocEq hy (fun _ h => nomatch h) (fun _ _ h => nomatch h)
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

end TermNallocF

#print axioms TermNallocF.evalOp_nallocEq
#print axioms TermNallocF.tstep_nallocEq
