import WeakCore.TermCk0
import WeakCore.TermA4R
import WeakCore.TermStep
import WeakCore.TermIall
import WeakCore.TermCut

/-! # TermA4P: the A1 piece discharge at hWbR (D4)

At a `wrapOK`, closed, `noOR` cell type, every positive-width solid piece `U` around a
non-word unit is key-free and own-free (`freeP_of_piece`), so (`valOfR_zero_fillP`) a typed word
at it fills a resource-free piece value.  `FreeP U` replaces `HWbRUp`'s first disjunct
`tb 0 U ∧ ¬ affine U` (agreed with).
-/

namespace TermA4
open CoreLang CoreTerm TermRun TermClose TermSound TermMem TermStep TermScope


/-! ## Substituting a closed type (the `noOR` half; the `rcar`/`wrapOK` halves are in TermCk0) -/

section Subst
variable {ρ : Nat → Nat} {W W' : Nat → Ty}

theorem noOR_cl_ge (hs : ∀ k, W' (k + 1) = W k) (hX : TermCut.noOR (W' 0) = true) :
    ∀ (t : Ty) (c d : Nat), TermCut.noOR (cl ρ W (c + 1) d t) = true → TermCut.noOR (cl ρ W' c d t) = true := by
  intro t
  induction t with
  | tvar k =>
      intro c d h
      simp only [cl] at h ⊢
      by_cases h1 : k < c
      · simp [h1, TermCut.noOR]
      · by_cases h2 : k = c
        · subst h2; simpa using hX
        · have h3 : ¬ k < c + 1 := by omega
          have e : k - c = (k - (c + 1)) + 1 := by omega
          simp only [h1, h3, ↓reduceIte] at h ⊢
          rw [e, hs]; exact h
  | ptr μ t _ => intro c d h; cases μ <;> simp_all [TermCut.noOR, cl, clM]
  | ptrOpt μ t _ => intro c d h; cases μ <;> simp_all [TermCut.noOR, cl, clM]
  | loc μ t _ => intro c d h; cases μ <;> simp_all [TermCut.noOR, cl, clM]
  | prod a b iha ihb =>
      intro c d h; simp only [cl, TermCut.noOR, Bool.and_eq_true] at h ⊢; exact ⟨iha c d h.1, ihb c d h.2⟩
  | sum a b iha ihb =>
      intro c d h; simp only [cl, TermCut.noOR, Bool.and_eq_true] at h ⊢; exact ⟨iha c d h.1, ihb c d h.2⟩
  | array i t ih => intro c d h; simp only [cl, TermCut.noOR] at h ⊢; exact ih c d h
  | mu t ih => intro c d h; simp only [cl, TermCut.noOR] at h ⊢; exact ih (c + 1) d h
  | tex κ t ih => intro c d h; simp only [cl, TermCut.noOR] at h ⊢; exact ih (c + 1) d h
  | iall t ih => intro c d h; simp only [cl, TermCut.noOR] at h ⊢; exact ih c (d + 1) h
  | iex t ih => intro c d h; simp only [cl, TermCut.noOR] at h ⊢; exact ih c (d + 1) h
  | refine t ψ ih => intro c d h; simp only [cl, TermCut.noOR] at h ⊢; exact ih c d h
  | tok r st => intro c d _; rcases st with _ | ⟨_, _⟩ <;> simp [cl, TermCut.noOR]
  | _ => intro c d _; simp [cl, TermCut.noOR]

end Subst

/-- Unfolding a closure of a `μ` type is closing its body with the `μ` type itself. -/
theorem cl_unfold (ρ : Nat → Nat) (W : Nat → Ty) (s : Ty) :
    cl ρ W 0 0 (unfold1 (.mu s)) = cl ρ (wcons (cl ρ W 0 0 (.mu s)) W) 0 0 s := by
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

/-- **The recursive variable's answer is the `μ` type's own** (the least fixpoint). -/
theorem rcar_mu_fix (t : Ty) : rcarE [rcarE [false] t] t = rcarE [false] t := by
  cases h : rcarE [false] t with
  | false => exact h
  | true =>
      refine rcarE_mono t [false] [true] (fun k hk => ?_) h
      cases k with
      | zero => simp at hk
      | succ k => simp at hk

theorem wrapOK_unfold {ρ : Nat → Nat} {W : Nat → Ty} (hW : ∀ k, Clo (W k)) {s : Ty}
    (h : wrapOK (cl ρ W 0 0 (.mu s)) = true) : wrapOK (cl ρ W 0 0 (unfold1 (.mu s))) = true := by
  rw [cl_unfold]
  have hX : tb 0 (cl ρ W 0 0 (.mu s)) = true := (Clo_cl hW ρ (.mu s)).1
  have hr : rcar (cl ρ W 0 0 (.mu s)) = rcarE [false] (cl ρ W (0 + 1) 0 s) := by
    show rcarE [] (cl ρ W 0 0 (.mu s)) = _
    simp only [cl, rcarE]
    exact rcar_mu_fix _
  have h1 : wrapOKE ([] ++ [rcar (wcons (cl ρ W 0 0 (.mu s)) W 0)]) (cl ρ W (0 + 1) 0 s) = true := by
    have e : wcons (cl ρ W 0 0 (.mu s)) W 0 = cl ρ W 0 0 (.mu s) := by simp [wcons]
    rw [e, hr]
    have h' := h
    simp only [wrapOK, cl, wrapOKE] at h'
    simpa using h'
  exact wrap_cl_ge (W' := wcons (cl ρ W 0 0 (.mu s)) W) (fun k => by simp [wcons]) (fun k => (hW k).1)
    (by simpa [wcons] using hX) (by simpa [wcons] using h) s 0 0 [] rfl h1

theorem noOR_unfold {ρ : Nat → Nat} {W : Nat → Ty} {s : Ty}
    (h : TermCut.noOR (cl ρ W 0 0 (.mu s)) = true) : TermCut.noOR (cl ρ W 0 0 (unfold1 (.mu s))) = true := by
  rw [cl_unfold]
  have h1 : TermCut.noOR (cl ρ W (0 + 1) 0 s) = true := by simp only [cl, TermCut.noOR] at h; exact h
  exact noOR_cl_ge (W' := wcons (cl ρ W 0 0 (.mu s)) W) (fun k => by simp [wcons])
    (by simpa [wcons] using h) s 0 0 h1

/-! ## Components -/

/-- A component of a `wrapOK`, `noOR`, closed type (other than a `μ` type) is one. -/
theorem AtOff_wrap {T U : Ty} {o : Nat} (h : AtOff T o U) :
    (∀ t, U ≠ .mu t) → Clo T → wrapOK T = true → TermCut.noOR T = true →
      Clo U ∧ wrapOK U = true ∧ TermCut.noOR U = true := by
  induction h with
  | here _ => exact fun _ hc hw hn => ⟨hc, hw, hn⟩
  | @fst a b u o _ ih =>
      intro hu hc hw hn
      simp only [wrapOK, wrapOKE, Bool.and_eq_true] at hw
      simp only [TermCut.noOR, Bool.and_eq_true] at hn
      refine ih hu ⟨by have := hc.1; simp only [tb, Bool.and_eq_true] at this; exact this.1,
        fun ρ W e f => ?_⟩ hw.1 hn.1
      have := hc.2 ρ W e f
      simp only [cl, Ty.prod.injEq] at this
      exact this.1
  | @snd a b u o us _ _ ih =>
      intro hu hc hw hn
      simp only [wrapOK, wrapOKE, Bool.and_eq_true] at hw
      simp only [TermCut.noOR, Bool.and_eq_true] at hn
      refine ih hu ⟨by have := hc.1; simp only [tb, Bool.and_eq_true] at this; exact this.2,
        fun ρ W e f => ?_⟩ hw.2 hn.2
      have := hc.2 ρ W e f
      simp only [cl, Ty.prod.injEq] at this
      exact this.2
  | @elem e u n j o us _ _ _ ih =>
      intro hu hc hw hn
      simp only [wrapOK, wrapOKE] at hw
      simp only [TermCut.noOR] at hn
      refine ih hu ⟨by have := hc.1; simp only [tb] at this; exact this, fun ρ W e' f => ?_⟩ hw hn
      have := hc.2 ρ W e' f
      simp only [cl, Ty.array.injEq] at this
      exact this.2
  | mu hW _ _ ih =>
      intro hu _ hw hn
      exact ih hu (Clo_cl hW _ _) (wrapOK_unfold hW hw) (noOR_unfold hn)
  | fold _ _ _ _ _ =>
      intro hu
      exact (hu _ rfl).elim

/-! ## The site lemma -/

/-- (D4) What `freeQW` needs of a piece: closed, and copyable or key- and own-free. -/
def FreeP (U : Ty) : Prop :=
  tb 0 U = true ∧ (Ty.affine U = false ∨ (rcar U = false ∧ TermCut.noOR U = true))

/-- **(D4) A piece of a `wrapOK` cell around a non-word unit is key- and own-free.** -/
theorem freeP_of_piece {E : TEnv} {l : WeakMem.AllocLabel} {cl0 : Cell} {o b : Nat} {U : Ty}
    {us : List Acc} (hW : wrapOK cl0.ty = true) (hclo : Clo cl0.ty) (hnor : TermCut.noOR cl0.ty = true)
    (hni : TermTv.noIallV cl0.ty = true)
    (hsto : E.sto l = some cl0) (hP : TermPiece.Piece cl0.ty b U) (hU : accs U = some us)
    (hb : b ≤ o) (ho : o < b + nWords us) (hnw : ¬ WordUnit E ⟨l, o⟩) : FreeP U := by
  obtain ⟨hat, hsol, -⟩ := hP
  obtain ⟨hcU, hwU, hnU⟩ := AtOff_wrap hat (fun t => hsol.2.2 t) hclo hW hnor
  refine ⟨hcU.1, .inr ⟨?_, hnU⟩⟩
  have hc1 := hcU.1
  have hniU := TermIall.noIallV_AtOff hat hni
  cases U with
  | sum a c =>
      simp only [wrapOK, wrapOKE, Bool.and_eq_true, Bool.not_eq_true'] at hwU
      simp only [rcar, rcarE, hwU.1.1.1, hwU.1.1.2, Bool.or_self]
  | iex t =>
      simp only [wrapOK, wrapOKE, Bool.and_eq_true, Bool.not_eq_true'] at hwU
      simpa [rcar, rcarE] using hwU.1
  | refine t ψ =>
      simp only [wrapOK, wrapOKE, Bool.and_eq_true, Bool.not_eq_true'] at hwU
      simpa [rcar, rcarE] using hwU.1
  | tex κ t =>
      simp only [wrapOK, wrapOKE, Bool.and_eq_true, Bool.not_eq_true'] at hwU
      simpa [rcar, rcarE] using hwU.1
  | prod a c => exact absurd rfl (hsol.1 a c)
  | mu t => exact absurd rfl (hsol.2.2 t)
  | tvar k => simp [tb] at hc1
  | iall t => simp [TermTv.noIallV] at hniU
  | word r P =>
      exfalso
      cases hg : P.ghost with
      | true => simp [accs, hg] at hU; subst hU; simp [nWords] at ho; omega
      | false =>
          simp [accs, hg] at hU; subst hU
          simp [nWords, Acc.size] at ho
          have e : o = b := by omega
          subst e
          exact hnw ⟨cl0, hsto, .inl ⟨r, P, hg, hat⟩⟩
  | word2 r P =>
      exfalso
      simp [accs] at hU; subst hU
      simp [nWords, Acc.size] at ho
      by_cases e : o = b
      · subst e; exact hnw ⟨cl0, hsto, .inr (.inl ⟨r, P, hat⟩)⟩
      · have e2 : o - 1 = b := by omega
        exact hnw ⟨cl0, hsto, .inr (.inr ⟨r, P, by show 1 ≤ o; omega, by rw [show (⟨l, o⟩ : WeakMem.Address).offset - 1 = b from e2]; exact hat⟩)⟩
  | tok r st => exfalso; simp [accs] at hU; subst hU; simp [nWords] at ho; omega
  | tok2 r P i j => exfalso; simp [accs] at hU; subst hU; simp [nWords] at ho; omega
  | tokE r P e => exfalso; simp [accs] at hU; subst hU; simp [nWords] at ho; omega
  | share r => exfalso; simp [accs] at hU; subst hU; simp [nWords] at ho; omega
  | _ => rfl

end TermA4

#print axioms TermA4.rcar_mu_fix
#print axioms TermA4.wrapOK_unfold
#print axioms TermA4.noOR_unfold
#print axioms TermA4.AtOff_wrap
#print axioms TermA4.freeP_of_piece
