import WeakCore.TermRun

/-!
# TermEnvExt: an allocating thread step extends the environment

A step that allocates (raises `nalloc`) is a `let` or a `case`: its new environment is the old one
under one new binding (`tstep_env_ext`).  Used by `TermBoxPV` to read a new box's payload views
off the pre-step environment.
-/

namespace TermEnvExt
open CoreLang CoreTerm TermRun
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

theorem mem_ol {α : Type} {x : α} {o : Option α} : x ∈ ol o ↔ o = some x := by
  cases o <;> simp [ol, eq_comm]

theorem enter_nalloc {g : G} {th th' : TTh} {f : String} {ts : List Ty} {a : At}
    (h : enter g th f ts a = some th') : th'.nalloc = th.nalloc := by
  unfold enter at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨d, -, ⟨t, ws⟩, -, rfl⟩ := h
  rfl

/-- **An allocating step extends the environment** by one binding. -/
theorem tstep_env_ext {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    (h : r ∈ tstep g mem pairs th) : r.2.2.nalloc = th.nalloc ∨ ∃ e, r.2.2.env = e :: th.env := by
  unfold tstep at h
  cases hterm : th.term with
  | let_ x op e =>
    rw [hterm] at h
    cases op
    case call f is a ts =>
      simp only [mem_ol, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
      obtain ⟨th', ⟨fr, -, hen⟩, rfl⟩ := h
      exact .inl (enter_nalloc hen : th'.nalloc = _)
    case callc f a =>
      simp only at h
      split at h
      · split at h
        · split at h
          · simp only [mem_ol, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
            obtain ⟨th', ⟨fr, -, hen⟩, rfl⟩ := h
            exact .inl (enter_nalloc hen : th'.nalloc = _)
          · cases h
        · cases h
      · cases h
    all_goals
      simp only [List.mem_map] at h
      obtain ⟨⟨s', t, ws⟩, -, rfl⟩ := h
      exact .inr ⟨_, rfl⟩
  | split a x y e =>
    rw [hterm] at h
    simp only at h
    split at h
    · split at h
      · rw [List.mem_singleton] at h; subst h; exact .inl rfl
      · cases h
    · cases h
  | unpack a i x e =>
    rw [hterm] at h
    simp only at h
    split at h
    · rw [List.mem_singleton] at h; subst h; exact .inl rfl
    · cases h
  | unpackT a α x e =>
    rw [hterm] at h
    simp only at h
    split at h
    · rw [List.mem_singleton] at h; subst h; exact .inl rfl
    · cases h
  | region a r' p' t' e =>
    rw [hterm] at h
    simp only at h
    split at h
    · rw [List.mem_singleton] at h; subst h; exact .inl rfl
    · rw [List.mem_singleton] at h; subst h; exact .inl rfl
    · cases h
  | openPub a r' p' c' e =>
    rw [hterm] at h
    simp only at h
    split at h
    · rw [List.mem_singleton] at h; subst h; exact .inl rfl
    · cases h
  | case a x e₁ y e₂ =>
    rw [hterm] at h
    simp only at h
    split at h
    · simp only [List.mem_flatMap, List.mem_map] at h
      obtain ⟨⟨s1, j, p⟩, -, ⟨s2, q⟩, -, rfl⟩ := h
      exact .inr ⟨_, rfl⟩
    · cases h
  | ifnull a e₁ y e₂ =>
    rw [hterm] at h
    simp only at h
    split at h
    · split at h
      · rw [List.mem_singleton] at h; subst h; exact .inl rfl
      · rw [List.mem_singleton] at h; subst h; exact .inl rfl
      · cases h
    · cases h
  | parity a k ev od =>
    rw [hterm] at h
    simp only at h
    split at h
    · split at h
      · rw [List.mem_singleton] at h; subst h; exact .inl rfl
      · cases h
    · cases h
  | ifeq a b yes no =>
    rw [hterm] at h
    simp only at h
    split at h
    · split at h
      · rw [List.mem_singleton] at h; subst h; exact .inl rfl
      · rw [List.mem_singleton] at h; subst h; exact .inl rfl
      · cases h
    · cases h
  | cas acq rel w e v t ok fail =>
    rw [hterm] at h
    simp only at h
    split at h
    · split at h
      · simp only [List.mem_map] at h
        obtain ⟨⟨mem', th'⟩, -, rfl⟩ := h
        left
        dsimp only
        split <;> rfl
      · cases h
    · cases h
  | casp acq rel w e0 e1 v0 v1 t ok fail =>
    rw [hterm] at h
    simp only at h
    split at h
    · split at h
      · simp only [List.mem_map] at h
        obtain ⟨⟨mem', pairs', th'⟩, -, rfl⟩ := h
        left
        dsimp only
        split <;> rfl
      · cases h
    · cases h
  | ret a =>
    rw [hterm] at h
    simp only at h
    split at h
    · rw [List.mem_singleton] at h; subst h; exact .inl rfl
    · cases h
  | tail f is a ts =>
    rw [hterm] at h
    simp only [mem_ol, Option.map_eq_some_iff] at h
    obtain ⟨th', hen, rfl⟩ := h
    exact .inl (enter_nalloc hen)

end TermEnvExt

#print axioms TermEnvExt.tstep_env_ext
#print axioms TermEnvExt.mem_ol
#print axioms TermEnvExt.enter_nalloc
