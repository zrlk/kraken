import WeakCore.TermC1Defs
import WeakCore.TermStep

/-! # TermC1Drf: `drf1` under closing and folding (G8)

`PubCpl1` reads `drf1` where `PubCpl` read `rgnFree`.  The publish family proves `rgnFree` of the
closed cell type with `rgnFree_cl0` (closing) and `rgnFree_Fd` (folding, through `rgnFree_cl_shift`
and `rgnFree_unfold`).  These are the `drf1` counterparts.  `drf1` also looks behind references, so
closing needs every witness to be `drf1` (`hW`), not only the unguarded `share` ones.
-/

namespace TermC1

open CoreLang CoreTerm CoreTyping TermRun TermClose TermSound TermStep TermScope

theorem drfM_clM (ρ : Nat → Nat) (d : Nat) (μ : Mode) : drfM (clM ρ d μ) = drfM μ := by
  cases μ <;> rfl

/-- The `drf1_clK` premise under a type binder (`mu`/`tex`: the cut moves up by one). -/
theorem drf1_clK_up {W : Nat → Ty} {t : Ty} {c : Nat}
    (hW : ∀ k, c ≤ k → t.tyMentions (k + 1) = true → drf1 (W (k - c)) = true) :
    ∀ k, c + 1 ≤ k → t.tyMentions k = true → drf1 (W (k - (c + 1))) = true := by
  intro k hk hm
  have e1 : k = (k - 1) + 1 := by omega
  have e2 : k - (c + 1) = (k - 1) - c := by omega
  rw [e2]; rw [e1] at hm; exact hW (k - 1) (by omega) hm

/-- **Closing keeps `drf1`** (local form, as `rgnFree_clK`): only the witnesses of type variables
that occur free in `t` (`tyMentions`, at or above the cut `c`) need `drf1`. -/
theorem drf1_clK {ρ : Nat → Nat} {W : Nat → Ty} (t : Ty) :
    ∀ c d, (∀ k, c ≤ k → t.tyMentions k = true → drf1 (W (k - c)) = true) →
      drf1 t = true → drf1 (cl ρ W c d t) = true := by
  induction t with
  | tvar j =>
      intro c d hW _
      by_cases h : j < c
      · simp [cl, h, drf1]
      · simp only [cl, h, ↓reduceIte]; exact hW j (by omega) (by simp [Ty.tyMentions])
  | prod a b iha ihb | sum a b iha ihb | code a b _ iha ihb =>
      intro c d hW h; simp only [drf1, Bool.and_eq_true] at h
      simp only [cl, drf1, Bool.and_eq_true]
      exact ⟨iha c d (fun k hk hm => hW k hk (by simp [Ty.tyMentions, hm])) h.1,
        ihb c d (fun k hk hm => hW k hk (by simp [Ty.tyMentions, hm])) h.2⟩
  | array _ t ih | ptr _ t ih | ptrOpt _ t ih => intro c d hW h; simp only [drf1] at h; simp only [cl, drf1]; exact ih c d hW h
  | loc μ t ih =>
      intro c d hW h; simp only [drf1, Bool.and_eq_true] at h
      simp only [cl, drf1, drfM_clM, h.1, ih c d hW h.2, Bool.and_self]
  | mu t ih => intro c d hW h; simp only [drf1] at h; simp only [cl, drf1]; exact ih (c + 1) d (drf1_clK_up hW) h
  | tex κ t ih => intro c d hW h; simp only [drf1] at h; simp only [cl, drf1]; exact ih (c + 1) d (drf1_clK_up hW) h
  | iall t _ => intro c d _ h; simp [drf1] at h
  | iex t ih => intro c d hW h; simp only [drf1] at h; simp only [cl, drf1]; exact ih c (d + 1) hW h
  | refine t ψ ih => intro c d hW h; simp only [drf1] at h; simp only [cl, drf1]; exact ih c d hW h
  | _ => intro c d _ _; simp [cl, drf1]

/-- Closing keeps `drf1` when every witness has it (`drf1_clK` with the global premise). -/
theorem drf1_cl {ρ : Nat → Nat} {W : Nat → Ty} (hW : ∀ k, drf1 (W k) = true) (t : Ty) :
    ∀ c d, drf1 t = true → drf1 (cl ρ W c d t) = true :=
  fun c d => drf1_clK t c d (fun k _ _ => hW (k - c))

/-- `drf1_clK` at the top (`rgnFree_cl0`'s counterpart): only the witnesses of `t`'s free variables. -/
theorem drf1_cl0K (ρ : Nat → Nat) {W : Nat → Ty} {t : Ty}
    (hW : ∀ k, t.tyMentions k = true → drf1 (W k) = true)
    (h : drf1 t = true) : drf1 (cl ρ W 0 0 t) = true :=
  drf1_clK t 0 0 (fun k _ hm => by simpa using hW k hm) h

/-- `drf1_cl` at the top, global premise. -/
theorem drf1_cl0 (ρ : Nat → Nat) {W : Nat → Ty} (hW : ∀ k, drf1 (W k) = true) {t : Ty}
    (h : drf1 t = true) : drf1 (cl ρ W 0 0 t) = true :=
  drf1_cl0K ρ (fun k _ => hW k) h

/-- (`rgnFree_cl_shift`) Moving the outermost closed binder into the witnesses keeps `drf1`. -/
theorem drf1_cl_shift {ρ : Nat → Nat} {W W₁ : Nat → Ty} (h0 : drf1 (W₁ 0) = true)
    (hs : ∀ k, W₁ (k + 1) = W k) (t : Ty) :
    ∀ (c d : Nat), drf1 (cl ρ W (c + 1) d t) = true → drf1 (cl ρ W₁ c d t) = true := by
  induction t with
  | tvar k =>
      intro c d h
      simp only [cl] at h ⊢
      by_cases h1 : k < c
      · simp [h1, drf1]
      · by_cases h2 : k = c
        · subst h2; simpa using h0
        · have h3 : ¬ k < c + 1 := by omega
          have e : k - c = (k - (c + 1)) + 1 := by omega
          simp only [h1, h3, ↓reduceIte] at h ⊢
          rw [e, hs]; exact h
  | prod a b iha ihb | sum a b iha ihb | code a b _ iha ihb =>
      intro c d h; simp only [cl, drf1, Bool.and_eq_true] at h ⊢; exact ⟨iha c d h.1, ihb c d h.2⟩
  | loc μ t ih =>
      intro c d h; simp only [cl, drf1, Bool.and_eq_true] at h ⊢; exact ⟨h.1, ih c d h.2⟩
  | array _ t ih | ptr _ t ih | ptrOpt _ t ih => intro c d h; simp only [cl, drf1] at h ⊢; exact ih c d h
  | mu t ih => intro c d h; simp only [cl, drf1] at h ⊢; exact ih (c + 1) d h
  | tex κ t ih => intro c d h; simp only [cl, drf1] at h ⊢; exact ih (c + 1) d h
  | iall t _ => intro c d h; simp [cl, drf1] at h
  | iex t ih => intro c d h; simp only [cl, drf1] at h ⊢; exact ih c (d + 1) h
  | refine t ψ ih => intro c d h; simp only [cl, drf1] at h ⊢; exact ih c d h
  | _ => intro c d _; simp [cl, drf1]

/-- (`rgnFree_unfold`) Unfolding a closed `μ` type keeps `drf1`. -/
theorem drf1_unfold {ρ : Nat → Nat} {W : Nat → Ty} {s : Ty} (h : drf1 (cl ρ W 0 0 (.mu s)) = true) :
    drf1 (cl ρ W 0 0 (unfold1 (.mu s))) = true := by
  have e1 : unfold1 (.mu s) = substTs [.mu s] 0 0 s := substT_eq (.mu s) s 0 0
  have e2 := cl_substTs [.mu s] 0 0 (ρ := ρ) (W₀ := W) (W₁ := wcons (cl ρ W 0 0 (.mu s)) W)
    (fun k hk => absurd hk (Nat.not_lt_zero _))
    (fun j σ hj => by
      cases j with
      | zero => simp at hj; subst hj; simp [wcons]
      | succ j => simp at hj)
    (fun k => by simp [wcons]) s 0 0
  simp only [Nat.add_zero] at e2
  rw [e1, e2]
  have h1 : drf1 (cl ρ W (0 + 1) 0 s) = true := by simp only [cl, drf1] at h; exact h
  exact drf1_cl_shift (W₁ := wcons (cl ρ W 0 0 (.mu s)) W) (show drf1 (cl ρ W 0 0 (.mu s)) = true from h)
    (fun k => by simp [wcons]) s 0 0 h1

/-- (`rgnFree_Fd`) A folded type of a `drf1` type is `drf1`. -/
theorem drf1_Fd {T U : Ty} (h : Fd T U) (hU : drf1 U = true) : drf1 T = true := by
  revert hU
  induction h with
  | refl => exact id
  | fold _ _ _ _ ih => intro hU; exact ih (drf1_unfold hU)

/-- `drf` implies `drf1` (c1 only admits more). -/
theorem drf1_of_drf : ∀ t : Ty, drf t = true → drf1 t = true := by
  intro t
  induction t with
  | prod a b iha ihb | sum a b iha ihb | code a b _ iha ihb =>
      intro h; simp only [drf, drf1, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1, ihb h.2⟩
  | ptr μ t ih => intro h; simp only [drf, drf1, Bool.and_eq_true] at h ⊢; exact ih h.2
  | ptrOpt μ t ih => intro h; simp only [drf, drf1, Bool.and_eq_true] at h ⊢; exact ih h.2
  | loc μ t ih => intro h; simp only [drf, drf1, Bool.and_eq_true] at h ⊢; exact ⟨h.1, ih h.2⟩
  | array i t ih => intro h; simp only [drf, drf1] at h ⊢; exact ih h
  | mu t ih => intro h; simp only [drf, drf1] at h ⊢; exact ih h
  | tex κ t ih => intro h; simp only [drf, drf1] at h ⊢; exact ih h
  | iex t ih => intro h; simp only [drf, drf1] at h ⊢; exact ih h
  | refine t ψ ih => intro h; simp only [drf, drf1] at h ⊢; exact ih h
  | iall t _ => intro h; simp [drf] at h
  | _ => intro _; simp [drf1]

end TermC1

#print axioms TermC1.drfM_clM
#print axioms TermC1.drf1_clK_up
#print axioms TermC1.drf1_clK
#print axioms TermC1.drf1_cl
#print axioms TermC1.drf1_cl0K
#print axioms TermC1.drf1_cl0
#print axioms TermC1.drf1_cl_shift
#print axioms TermC1.drf1_unfold
#print axioms TermC1.drf1_Fd
#print axioms TermC1.drf1_of_drf
