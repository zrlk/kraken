import WeakCore.TermPdR

/-! # TermAffAt: non-affineness along `Fd` and `AtOff` (own-load leg 2)

An own load (`loadOwn`/`loadPub`) reads a cell whose type folds (`Fd`) a closed non-affine type.
Every `AtOff` component of such a cell type is non-affine (`affine_atOffA`), so a piece of a
loaded cell carries no resources: an own load never makes an `R ≠ 0` unit newly guarded.
-/

namespace TermAffAt
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys

/-- Substitution for a recursion variable does not make a type less affine. -/
theorem affine_of_substTA : ∀ (t s : Ty) (ke0 ke : KEnv),
    Ty.affineIn (ke0 ++ ke) (Ty.substT ke0.length s t) = false →
    Ty.affineIn (ke0 ++ none :: ke) t = false := by
  intro t
  induction t with
  | tvar k =>
      intro s ke0 ke h
      by_cases hk : k = ke0.length
      · subst hk
        simp only [Ty.affineIn, KEnv.ask, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem?_cons_zero, Bool.not_true]
      · have hb : (k == ke0.length) = false := beq_false_of_ne hk
        simp only [Ty.substT, hb, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hg : k > ke0.length
        · simp only [hg, ↓reduceIte] at h
          simp only [Ty.affineIn, KEnv.ask] at h ⊢
          obtain ⟨m, rfl⟩ : ∃ m, k = ke0.length + 1 + m := ⟨k - ke0.length - 1, by omega⟩
          rw [List.getElem?_append_right (by omega)] at h
          rw [List.getElem?_append_right (by omega)]
          rw [show ke0.length + 1 + m - 1 - ke0.length = m by omega] at h
          rw [show ke0.length + 1 + m - ke0.length = m + 1 by omega]
          simpa only [List.getElem?_cons_succ] using h
        · simp only [hg, ↓reduceIte] at h
          simp only [Ty.affineIn, KEnv.ask] at h ⊢
          rw [List.getElem?_append_left (by omega)] at h
          rw [List.getElem?_append_left (by omega)]
          exact h
  | prod a b iha ihb =>
      intro s ke0 ke h
      simp only [Ty.substT, Ty.affineIn, Bool.or_eq_false_iff] at h ⊢
      exact ⟨iha s ke0 ke h.1, ihb s ke0 ke h.2⟩
  | sum a b iha ihb =>
      intro s ke0 ke h
      simp only [Ty.substT, Ty.affineIn, Bool.or_eq_false_iff] at h ⊢
      exact ⟨iha s ke0 ke h.1, ihb s ke0 ke h.2⟩
  | array i t ih =>
      intro s ke0 ke h
      simp only [Ty.substT, Ty.affineIn] at h ⊢
      exact ih s ke0 ke h
  | refine t ψ ih =>
      intro s ke0 ke h
      simp only [Ty.substT, Ty.affineIn] at h ⊢
      exact ih s ke0 ke h
  | iall t ih =>
      intro s ke0 ke h
      simp only [Ty.substT, Ty.affineIn] at h ⊢
      exact ih (s.shiftI 0) ke0 ke h
  | iex t ih =>
      intro s ke0 ke h
      simp only [Ty.substT, Ty.affineIn] at h ⊢
      exact ih (s.shiftI 0) ke0 ke h
  | mu t ih =>
      intro s ke0 ke h
      simp only [Ty.substT, Ty.affineIn] at h ⊢
      have e := ih (s.shiftT 0) (none :: ke0) ke (by simpa only [List.cons_append, List.length_cons] using h)
      simpa only [List.cons_append] using e
  | tex κ t ih =>
      intro s ke0 ke h
      simp only [Ty.substT, Ty.affineIn] at h ⊢
      have e := ih (s.shiftT 0) (some κ :: ke0) ke (by simpa only [List.cons_append, List.length_cons] using h)
      simpa only [List.cons_append] using e
  | ptr m t ih => intro s ke0 ke h; cases m <;> simp_all [Ty.substT, Ty.affineIn]
  | ptrOpt m t ih => intro s ke0 ke h; cases m <;> simp_all [Ty.substT, Ty.affineIn]
  | loc m t ih => intro s ke0 ke h; cases m <;> simp_all [Ty.substT, Ty.affineIn]
  | _ => intro s ke0 ke h; simp_all [Ty.substT, Ty.affineIn]

#print axioms affine_of_substTA

/-- Unfolding a closed non-affine `μ` keeps it non-affine. -/
theorem affine_unfoldA {ρ : Nat → Nat} {W : Nat → Ty} (hW : ∀ k, Clo (W k)) {s : Ty}
    (h : Ty.affine (cl ρ W 0 0 (.mu s)) = false) : Ty.affine (cl ρ W 0 0 (unfold1 (.mu s))) = false := by
  rw [cl_unfold1 hW, cl_mu_eq]
  rw [cl_mu_eq] at h
  have hc : tb 0 (Ty.mu (cl ρ W 1 0 s)) = true := by
    have e := (Clo_cl hW ρ (.mu s)).1
    rwa [cl_mu_eq] at e
  have h2 : Ty.affineIn ([] ++ none :: []) (cl ρ W 1 0 s) = false := by
    simpa only [Ty.affine, Ty.affineIn, List.nil_append] using h
  have e := TermForWU.affine_substT (cl ρ W 1 0 s) (.mu (cl ρ W 1 0 s)) [] [] hc h h2
  simpa only [Ty.affine, unfold1, List.nil_append, List.length_nil] using e

#print axioms affine_unfoldA

/-- And folding back. -/
theorem affine_foldA {ρ : Nat → Nat} {W : Nat → Ty} (hW : ∀ k, Clo (W k)) {s : Ty}
    (h : Ty.affine (cl ρ W 0 0 (unfold1 (.mu s))) = false) : Ty.affine (cl ρ W 0 0 (.mu s)) = false := by
  rw [cl_unfold1 hW, cl_mu_eq] at h
  rw [cl_mu_eq]
  have h1 : Ty.affineIn ([] ++ []) (Ty.substT ([] : KEnv).length (.mu (cl ρ W 1 0 s)) (cl ρ W 1 0 s)) = false := by
    simpa only [Ty.affine, unfold1, List.nil_append, List.length_nil] using h
  have e := affine_of_substTA (cl ρ W 1 0 s) (.mu (cl ρ W 1 0 s)) [] [] h1
  simpa only [Ty.affine, Ty.affineIn, List.nil_append] using e

#print axioms affine_foldA

/-- **A type folding a non-affine type is non-affine.** -/
theorem affine_fdA {T X : Ty} (h : Fd T X) (hX : Ty.affine X = false) : Ty.affine T = false := by
  induction h with
  | refl => exact hX
  | fold hW _ _ _ ih => exact ih (affine_unfoldA hW hX)

#print axioms affine_fdA

/-- **Every `AtOff` component of a non-affine type is non-affine.** -/
theorem affine_atOffA {U V : Ty} {d : Nat} (h : AtOff U d V) (hU : Ty.affine U = false) :
    Ty.affine V = false := by
  induction h with
  | here _ => exact hU
  | fst _ ih =>
      simp only [Ty.affine, Ty.affineIn, Bool.or_eq_false_iff] at hU
      exact ih hU.1
  | snd _ _ ih =>
      simp only [Ty.affine, Ty.affineIn, Bool.or_eq_false_iff] at hU
      exact ih hU.2
  | elem _ _ _ ih => exact ih hU
  | mu hW _ _ ih => exact ih (affine_unfoldA hW hU)
  | fold hW _ _ _ ih => exact affine_foldA hW (ih hU)

#print axioms affine_atOffA

/-- **(own-load leg 2) A component of a loaded cell is non-affine**: the cell type folds the
closure of the load's non-affine pointee type `u` (`ownPtr_view`/`pubPtr_view`'s `Fd`). -/
theorem affine_loadCell {ρ : Nat → Nat} {W : Nat → Ty} (hW : ∀ k, Clo (W k))
    {ke : KEnv} {T u U : Ty} {o : Nat}
    (hWk : ∀ k, k < ke.length → ke.ask k true (·.copy) = true → Ty.affine (W k) = false)
    (hu : Ty.affineIn ke u = false) (htb : tb ke.length u = true)
    (hF : Fd T (cl ρ W 0 0 u)) (hat : AtOff T o U) : Ty.affine U = false := by
  exact affine_atOffA hat (affine_fdA hF (AffineCl.affine_cl0 ρ W ke hW hWk u hu htb))

#print axioms affine_loadCell

end TermAffAt
