import WeakCore.TermCkDefs
import WeakCore.CoreTyping
import WeakCore.TermTv

/-! # TermCk0: environment lemmas for `rcarE`/`wrapOKE` (from TermA4P) -/

namespace TermA4
open CoreLang CoreTerm TermClose TermScope

/-! ## Environments: closed types, monotonicity -/

theorem getD_app_lt {env l : List Bool} {k : Nat} (h : k < env.length) :
    (env ++ l).getD k false = env.getD k false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_eq (env : List Bool) (x : Bool) : (env ++ [x]).getD env.length false = x := by
  simp [List.getD_eq_getElem?_getD]

theorem agree_cons {c : Nat} {e1 e2 : List Bool} {b1 b2 : Bool}
    (h : ∀ k, k < c → e1.getD k false = e2.getD k false) (hb : b1 = b2) :
    ∀ k, k < c + 1 → (b1 :: e1).getD k false = (b2 :: e2).getD k false := by
  intro k hk
  cases k with
  | zero => simpa using hb
  | succ k => simpa using h k (by omega)

/-- `rcarE` and `wrapOKE` read only the variables a type mentions. -/
theorem rw_tb : ∀ (t : Ty) (c : Nat) (e1 e2 : List Bool), tb c t = true →
    (∀ k, k < c → e1.getD k false = e2.getD k false) →
    rcarE e1 t = rcarE e2 t ∧ wrapOKE e1 t = wrapOKE e2 t := by
  intro t
  induction t with
  | tvar k => intro c e1 e2 ht h; simp only [tb, decide_eq_true_eq] at ht; exact ⟨by simp only [rcarE, h k ht], rfl⟩
  | prod a b iha ihb =>
      intro c e1 e2 ht h; simp only [tb, Bool.and_eq_true] at ht
      obtain ⟨a1, a2⟩ := iha c e1 e2 ht.1 h; obtain ⟨b1, b2⟩ := ihb c e1 e2 ht.2 h
      refine ⟨?_, ?_⟩ <;> simp only [rcarE, wrapOKE, a1, a2, b1, b2]
  | sum a b iha ihb =>
      intro c e1 e2 ht h; simp only [tb, Bool.and_eq_true] at ht
      obtain ⟨a1, a2⟩ := iha c e1 e2 ht.1 h; obtain ⟨b1, b2⟩ := ihb c e1 e2 ht.2 h
      refine ⟨?_, ?_⟩ <;> simp only [rcarE, wrapOKE, a1, a2, b1, b2]
  | code a b iha ihb =>
      intro c e1 e2 ht h; simp only [tb, Bool.and_eq_true] at ht
      obtain ⟨-, a2⟩ := iha c e1 e2 ht.1 h; obtain ⟨-, b2⟩ := ihb c e1 e2 ht.2 h
      refine ⟨?_, ?_⟩ <;> simp only [rcarE, wrapOKE, a2, b2]
  | array i t ih =>
      intro c e1 e2 ht h; simp only [tb] at ht; obtain ⟨-, h2⟩ := ih c e1 e2 ht h
      refine ⟨?_, ?_⟩ <;> simp only [rcarE, wrapOKE, h2]
  | ptr μ t ih =>
      intro c e1 e2 ht h; simp only [tb] at ht; obtain ⟨-, h2⟩ := ih c e1 e2 ht h
      refine ⟨?_, ?_⟩ <;> simp only [rcarE, wrapOKE, h2]
  | ptrOpt μ t ih =>
      intro c e1 e2 ht h; simp only [tb] at ht; obtain ⟨-, h2⟩ := ih c e1 e2 ht h
      refine ⟨?_, ?_⟩ <;> simp only [rcarE, wrapOKE, h2]
  | loc μ t ih =>
      intro c e1 e2 ht h; simp only [tb] at ht; obtain ⟨-, h2⟩ := ih c e1 e2 ht h
      refine ⟨?_, ?_⟩ <;> simp only [rcarE, wrapOKE, h2]
  | iall t ih =>
      intro c e1 e2 ht h; simp only [tb] at ht; obtain ⟨h1, h2⟩ := ih c e1 e2 ht h
      refine ⟨?_, ?_⟩ <;> simp only [rcarE, wrapOKE, h1, h2]
  | iex t ih =>
      intro c e1 e2 ht h; simp only [tb] at ht; obtain ⟨h1, h2⟩ := ih c e1 e2 ht h
      refine ⟨?_, ?_⟩ <;> simp only [rcarE, wrapOKE, h1, h2]
  | refine t ψ ih =>
      intro c e1 e2 ht h; simp only [tb] at ht; obtain ⟨h1, h2⟩ := ih c e1 e2 ht h
      refine ⟨?_, ?_⟩ <;> simp only [rcarE, wrapOKE, h1, h2]
  | tex κ t ih =>
      intro c e1 e2 ht h; simp only [tb] at ht
      obtain ⟨h1, h2⟩ := ih (c + 1) (false :: e1) (false :: e2) ht (agree_cons h rfl)
      refine ⟨?_, ?_⟩ <;> simp only [rcarE, wrapOKE, h1, h2]
  | mu t ih =>
      intro c e1 e2 ht h; simp only [tb] at ht
      have h0 := (ih (c + 1) (false :: e1) (false :: e2) ht (agree_cons h rfl)).1
      obtain ⟨h1, h2⟩ := ih (c + 1) _ _ ht (agree_cons h h0)
      simp only [rcarE, wrapOKE]; exact ⟨h1, h2⟩
  | _ => intro c e1 e2 _ _; exact ⟨rfl, rfl⟩

theorem rcarE_closed {t : Ty} (ht : tb 0 t = true) (e : List Bool) : rcarE e t = rcar t :=
  (rw_tb t 0 e [] ht (fun _ hk => absurd hk (Nat.not_lt_zero _))).1

theorem wrapOKE_closed {t : Ty} (ht : tb 0 t = true) (e : List Bool) : wrapOKE e t = wrapOK t :=
  (rw_tb t 0 e [] ht (fun _ hk => absurd hk (Nat.not_lt_zero _))).2

/-- `rcarE` is monotone in the environment. -/
theorem rcarE_mono : ∀ (t : Ty) (e1 e2 : List Bool),
    (∀ k, e1.getD k false = true → e2.getD k false = true) → rcarE e1 t = true → rcarE e2 t = true := by
  intro t
  induction t with
  | tvar k => intro e1 e2 h ht; simp only [rcarE] at ht ⊢; exact h k ht
  | prod a b iha ihb =>
      intro e1 e2 h ht; simp only [rcarE, Bool.or_eq_true] at ht ⊢
      exact ht.elim (fun x => .inl (iha e1 e2 h x)) (fun x => .inr (ihb e1 e2 h x))
  | sum a b iha ihb =>
      intro e1 e2 h ht; simp only [rcarE, Bool.or_eq_true] at ht ⊢
      exact ht.elim (fun x => .inl (iha e1 e2 h x)) (fun x => .inr (ihb e1 e2 h x))
  | iall t ih => intro e1 e2 h ht; simp only [rcarE] at ht ⊢; exact ih e1 e2 h ht
  | iex t ih => intro e1 e2 h ht; simp only [rcarE] at ht ⊢; exact ih e1 e2 h ht
  | refine t ψ ih => intro e1 e2 h ht; simp only [rcarE] at ht ⊢; exact ih e1 e2 h ht
  | tex κ t ih =>
      intro e1 e2 h ht; simp only [rcarE] at ht ⊢
      refine ih _ _ (fun k hk => ?_) ht
      cases k with
      | zero => simp at hk
      | succ k => simpa using h k (by simpa using hk)
  | mu t ih =>
      intro e1 e2 h ht; simp only [rcarE] at ht ⊢
      have h0 : ∀ k, (false :: e1).getD k false = true → (false :: e2).getD k false = true := by
        intro k hk
        cases k with
        | zero => simp at hk
        | succ k => simpa using h k (by simpa using hk)
      refine ih _ _ (fun k hk => ?_) ht
      cases k with
      | zero =>
          simp only [List.getD_cons_zero] at hk ⊢
          exact ih _ _ h0 hk
      | succ k => simpa using h k (by simpa using hk)
  | _ => intro e1 e2 _ ht; exact ht

/-! ## Substituting a closed type for the innermost bound type variable -/

section Subst
variable {ρ : Nat → Nat} {W W' : Nat → Ty}

theorem rcar_cl_ge (hs : ∀ k, W' (k + 1) = W k) (hWc : ∀ k, tb 0 (W k) = true) (hX : tb 0 (W' 0) = true) :
    ∀ (t : Ty) (c d : Nat) (env : List Bool), env.length = c →
      rcarE env (cl ρ W' c d t) = rcarE (env ++ [rcar (W' 0)]) (cl ρ W (c + 1) d t) := by
  intro t
  induction t with
  | tvar j =>
      intro c d env hl
      subst hl
      by_cases h1 : j < env.length
      · simp only [cl, h1, show j < env.length + 1 by omega, ite_true, rcarE]
        exact (getD_app_lt h1).symm
      · by_cases h2 : j = env.length
        · subst h2
          simp only [cl, Nat.lt_irrefl, ite_false, Nat.sub_self, Nat.lt_succ_self, ite_true, rcarE]
          rw [getD_app_eq, rcarE_closed hX]
        · have h3 : ¬ j < env.length + 1 := by omega
          have e : j - env.length = (j - (env.length + 1)) + 1 := by omega
          simp only [cl, h1, h3, ite_false]
          rw [e, hs, rcarE_closed (hWc _), rcarE_closed (hWc _)]
  | prod a b iha ihb =>
      intro c d env hl; simp only [cl, rcarE]; rw [iha c d env hl, ihb c d env hl]
  | sum a b iha ihb =>
      intro c d env hl; simp only [cl, rcarE]; rw [iha c d env hl, ihb c d env hl]
  | iall t ih => intro c d env hl; simp only [cl, rcarE]; exact ih c (d + 1) env hl
  | iex t ih => intro c d env hl; simp only [cl, rcarE]; exact ih c (d + 1) env hl
  | refine t ψ ih => intro c d env hl; simp only [cl, rcarE]; exact ih c d env hl
  | tex κ t ih =>
      intro c d env hl; simp only [cl, rcarE]
      exact ih (c + 1) d (false :: env) (by simp [hl])
  | mu t ih =>
      intro c d env hl; simp only [cl, rcarE]
      rw [ih (c + 1) d (false :: env) (by simp [hl])]
      exact ih (c + 1) d (_ :: env) (by simp [hl])
  | tok r st => intro c d env _; rcases st with _ | ⟨_, _⟩ <;> simp [cl, rcarE]
  | _ => intro c d env _; simp [cl, rcarE]

theorem wrap_cl_ge (hs : ∀ k, W' (k + 1) = W k) (hWc : ∀ k, tb 0 (W k) = true) (hX : tb 0 (W' 0) = true)
    (hXw : wrapOK (W' 0) = true) :
    ∀ (t : Ty) (c d : Nat) (env : List Bool), env.length = c →
      wrapOKE (env ++ [rcar (W' 0)]) (cl ρ W (c + 1) d t) = true → wrapOKE env (cl ρ W' c d t) = true := by
  intro t
  induction t with
  | tvar j =>
      intro c d env hl h
      subst hl
      by_cases h1 : j < env.length
      · simp [cl, h1, wrapOKE]
      · by_cases h2 : j = env.length
        · subst h2
          simp only [cl, Nat.lt_irrefl, ite_false, Nat.sub_self]
          rw [wrapOKE_closed hX]; exact hXw
        · have h3 : ¬ j < env.length + 1 := by omega
          have e : j - env.length = (j - (env.length + 1)) + 1 := by omega
          simp only [cl, h1, h3, ite_false] at h ⊢
          rw [e, hs, wrapOKE_closed (hWc _)]; rw [wrapOKE_closed (hWc _)] at h; exact h
  | prod a b iha ihb =>
      intro c d env hl h; simp only [cl, wrapOKE, Bool.and_eq_true] at h ⊢
      exact ⟨iha c d env hl h.1, ihb c d env hl h.2⟩
  | code a b iha ihb =>
      intro c d env hl h; simp only [cl, wrapOKE, Bool.and_eq_true] at h ⊢
      exact ⟨iha c d env hl h.1, ihb c d env hl h.2⟩
  | sum a b iha ihb =>
      intro c d env hl h; simp only [cl, wrapOKE, Bool.and_eq_true] at h ⊢
      rw [rcar_cl_ge hs hWc hX a c d env hl, rcar_cl_ge hs hWc hX b c d env hl]
      exact ⟨⟨⟨h.1.1.1, h.1.1.2⟩, iha c d env hl h.1.2⟩, ihb c d env hl h.2⟩
  | iex t ih =>
      intro c d env hl h; simp only [cl, wrapOKE, Bool.and_eq_true] at h ⊢
      rw [rcar_cl_ge hs hWc hX t c (d + 1) env hl]
      exact ⟨h.1, ih c (d + 1) env hl h.2⟩
  | refine t ψ ih =>
      intro c d env hl h; simp only [cl, wrapOKE, Bool.and_eq_true] at h ⊢
      rw [rcar_cl_ge hs hWc hX t c d env hl]
      exact ⟨h.1, ih c d env hl h.2⟩
  | tex κ t ih =>
      intro c d env hl h; simp only [cl, wrapOKE, Bool.and_eq_true] at h ⊢
      rw [rcar_cl_ge hs hWc hX t (c + 1) d (false :: env) (by simp [hl])]
      exact ⟨h.1, ih (c + 1) d (false :: env) (by simp [hl]) h.2⟩
  | mu t ih =>
      intro c d env hl h; simp only [cl, wrapOKE] at h ⊢
      rw [rcar_cl_ge hs hWc hX t (c + 1) d (false :: env) (by simp [hl])]
      exact ih (c + 1) d (_ :: env) (by simp [hl]) h
  | array i t ih => intro c d env hl h; simp only [cl, wrapOKE] at h ⊢; exact ih c d env hl h
  | ptr μ t ih => intro c d env hl h; simp only [cl, wrapOKE] at h ⊢; exact ih c d env hl h
  | ptrOpt μ t ih => intro c d env hl h; simp only [cl, wrapOKE] at h ⊢; exact ih c d env hl h
  | loc μ t ih => intro c d env hl h; simp only [cl, wrapOKE] at h ⊢; exact ih c d env hl h
  | iall t ih => intro c d env hl h; simp only [cl, wrapOKE] at h ⊢; exact ih c (d + 1) env hl h
  | tok r st => intro c d env _ _; rcases st with _ | ⟨_, _⟩ <;> simp [cl, wrapOKE]
  | _ => intro c d env _ _; simp [cl, wrapOKE]


end Subst

end TermA4
