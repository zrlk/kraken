import WeakCore.TermA4P

/-! # TermA4P2: the D4 piece discharge at `wrapTop`

`freeP_of_pieceT` restates `freeP_of_piece` at `wrapTop` (the A1 checker invariant's cell-type invariant,
`PfrWrapTop`) instead of `wrapOK`.
-/

namespace TermA4
open CoreLang CoreTerm TermRun TermClose TermSound TermMem TermStep TermScope

section SubstT
variable {ρ : Nat → Nat} {W W' : Nat → Ty}

theorem wrapT_cl_ge (hs : ∀ k, W' (k + 1) = W k) (hWc : ∀ k, tb 0 (W k) = true) (hX : tb 0 (W' 0) = true)
    (hXw : wrapTop (W' 0) = true) :
    ∀ (t : Ty) (c d : Nat) (env : List Bool), env.length = c →
      wrapTopE (env ++ [rcar (W' 0)]) (cl ρ W (c + 1) d t) = true → wrapTopE env (cl ρ W' c d t) = true := by
  intro t
  induction t with
  | tvar j =>
      intro c d env hl h
      subst hl
      by_cases h1 : j < env.length
      · simp [cl, h1, wrapTopE]
      · by_cases h2 : j = env.length
        · subst h2
          simp only [cl, Nat.lt_irrefl, ite_false, Nat.sub_self]
          rw [wrapTopE_closed hX]; exact hXw
        · have h3 : ¬ j < env.length + 1 := by omega
          have e : j - env.length = (j - (env.length + 1)) + 1 := by omega
          simp only [cl, h1, h3, ite_false] at h ⊢
          rw [e, hs, wrapTopE_closed (hWc _)]; rw [wrapTopE_closed (hWc _)] at h; exact h
  | prod a b iha ihb =>
      intro c d env hl h; simp only [cl, wrapTopE, Bool.and_eq_true] at h ⊢
      exact ⟨iha c d env hl h.1, ihb c d env hl h.2⟩
  | sum a b iha ihb =>
      intro c d env hl h; simp only [cl, wrapTopE, Bool.and_eq_true] at h ⊢
      rw [rcar_cl_ge hs hWc hX a c d env hl, rcar_cl_ge hs hWc hX b c d env hl]
      exact ⟨⟨⟨h.1.1.1, h.1.1.2⟩, iha c d env hl h.1.2⟩, ihb c d env hl h.2⟩
  | iex t ih =>
      intro c d env hl h; simp only [cl, wrapTopE, Bool.and_eq_true] at h ⊢
      rw [rcar_cl_ge hs hWc hX t c (d + 1) env hl]
      exact ⟨h.1, ih c (d + 1) env hl h.2⟩
  | refine t ψ ih =>
      intro c d env hl h; simp only [cl, wrapTopE, Bool.and_eq_true] at h ⊢
      rw [rcar_cl_ge hs hWc hX t c d env hl]
      exact ⟨h.1, ih c d env hl h.2⟩
  | tex κ t ih =>
      intro c d env hl h; simp only [cl, wrapTopE, Bool.and_eq_true] at h ⊢
      rw [rcar_cl_ge hs hWc hX t (c + 1) d (false :: env) (by simp [hl])]
      exact ⟨h.1, ih (c + 1) d (false :: env) (by simp [hl]) h.2⟩
  | mu t ih =>
      intro c d env hl h; simp only [cl, wrapTopE] at h ⊢
      rw [rcar_cl_ge hs hWc hX t (c + 1) d (false :: env) (by simp [hl])]
      exact ih (c + 1) d (_ :: env) (by simp [hl]) h
  | array i t ih => intro c d env hl h; simp only [cl, wrapTopE] at h ⊢; exact ih c d env hl h
  | iall t ih => intro c d env hl h; simp only [cl, wrapTopE] at h ⊢; exact ih c (d + 1) env hl h
  | tok r st => intro c d env _ _; rcases st with _ | ⟨_, _⟩ <;> simp [cl, wrapTopE]
  | _ => intro c d env _ _; simp [cl, wrapTopE]

end SubstT

theorem wrapTop_unfold {ρ : Nat → Nat} {W : Nat → Ty} (hW : ∀ k, Clo (W k)) {s : Ty}
    (h : wrapTop (cl ρ W 0 0 (.mu s)) = true) : wrapTop (cl ρ W 0 0 (unfold1 (.mu s))) = true := by
  rw [cl_unfold]
  have hX : tb 0 (cl ρ W 0 0 (.mu s)) = true := (Clo_cl hW ρ (.mu s)).1
  have hr : rcar (cl ρ W 0 0 (.mu s)) = rcarE [false] (cl ρ W (0 + 1) 0 s) := by
    show rcarE [] (cl ρ W 0 0 (.mu s)) = _
    simp only [cl, rcarE]
    exact rcar_mu_fix _
  have h1 : wrapTopE ([] ++ [rcar (wcons (cl ρ W 0 0 (.mu s)) W 0)]) (cl ρ W (0 + 1) 0 s) = true := by
    have e : wcons (cl ρ W 0 0 (.mu s)) W 0 = cl ρ W 0 0 (.mu s) := by simp [wcons]
    rw [e, hr]
    have h' := h
    simp only [wrapTop, cl, wrapTopE] at h'
    simpa using h'
  exact wrapT_cl_ge (W' := wcons (cl ρ W 0 0 (.mu s)) W) (fun k => by simp [wcons]) (fun k => (hW k).1)
    (by simpa [wcons] using hX) (by simpa [wcons] using h) s 0 0 [] rfl h1

/-- A component of a `wrapTop`, `noOR`, closed type (other than a `μ` type) is one. -/
theorem AtOff_wrapT {T U : Ty} {o : Nat} (h : AtOff T o U) :
    (∀ t, U ≠ .mu t) → Clo T → wrapTop T = true → TermCut.noOR T = true →
      Clo U ∧ wrapTop U = true ∧ TermCut.noOR U = true := by
  induction h with
  | here _ => exact fun _ hc hw hn => ⟨hc, hw, hn⟩
  | @fst a b u o _ ih =>
      intro hu hc hw hn
      simp only [wrapTop, wrapTopE, Bool.and_eq_true] at hw
      simp only [TermCut.noOR, Bool.and_eq_true] at hn
      refine ih hu ⟨by have := hc.1; simp only [tb, Bool.and_eq_true] at this; exact this.1,
        fun ρ W e f => ?_⟩ hw.1 hn.1
      have := hc.2 ρ W e f
      simp only [cl, Ty.prod.injEq] at this
      exact this.1
  | @snd a b u o us _ _ ih =>
      intro hu hc hw hn
      simp only [wrapTop, wrapTopE, Bool.and_eq_true] at hw
      simp only [TermCut.noOR, Bool.and_eq_true] at hn
      refine ih hu ⟨by have := hc.1; simp only [tb, Bool.and_eq_true] at this; exact this.2,
        fun ρ W e f => ?_⟩ hw.2 hn.2
      have := hc.2 ρ W e f
      simp only [cl, Ty.prod.injEq] at this
      exact this.2
  | @elem e u n j o us _ _ _ ih =>
      intro hu hc hw hn
      simp only [wrapTop, wrapTopE] at hw
      simp only [TermCut.noOR] at hn
      refine ih hu ⟨by have := hc.1; simp only [tb] at this; exact this, fun ρ W e' f => ?_⟩ hw hn
      have := hc.2 ρ W e' f
      simp only [cl, Ty.array.injEq] at this
      exact this.2
  | mu hW _ _ ih =>
      intro hu _ hw hn
      exact ih hu (Clo_cl hW _ _) (wrapTop_unfold hW hw) (noOR_unfold hn)
  | fold _ _ _ _ _ =>
      intro hu
      exact (hu _ rfl).elim

/-- **(D4, A1 checker invariant) A piece of a `wrapTop` cell around a non-word unit is key- and own-free.** -/
theorem freeP_of_pieceT {E : TEnv} {l : WeakMem.AllocLabel} {cl0 : Cell} {o b : Nat} {U : Ty}
    {us : List Acc} (hW : wrapTop cl0.ty = true) (hclo : Clo cl0.ty) (hnor : TermCut.noOR cl0.ty = true)
    (hni : TermTv.noIallV cl0.ty = true)
    (hsto : E.sto l = some cl0) (hP : TermPiece.Piece cl0.ty b U) (hU : accs U = some us)
    (hb : b ≤ o) (ho : o < b + nWords us) (hnw : ¬ WordUnit E ⟨l, o⟩) : FreeP U := by
  obtain ⟨hat, hsol, -⟩ := hP
  obtain ⟨hcU, hwU, hnU⟩ := AtOff_wrapT hat (fun t => hsol.2.2 t) hclo hW hnor
  refine ⟨hcU.1, .inr ⟨?_, hnU⟩⟩
  have hc1 := hcU.1
  have hniU := TermIall.noIallV_AtOff hat hni
  cases U with
  | sum a c =>
      simp only [wrapTop, wrapTopE, Bool.and_eq_true, Bool.not_eq_true'] at hwU
      simp only [rcar, rcarE, hwU.1.1.1, hwU.1.1.2, Bool.or_self]
  | iex t =>
      simp only [wrapTop, wrapTopE, Bool.and_eq_true, Bool.not_eq_true'] at hwU
      simpa [rcar, rcarE] using hwU.1
  | refine t ψ =>
      simp only [wrapTop, wrapTopE, Bool.and_eq_true, Bool.not_eq_true'] at hwU
      simpa [rcar, rcarE] using hwU.1
  | tex κ t =>
      simp only [wrapTop, wrapTopE, Bool.and_eq_true, Bool.not_eq_true'] at hwU
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

#print axioms TermA4.wrapT_cl_ge
#print axioms TermA4.wrapTop_unfold
#print axioms TermA4.AtOff_wrapT
#print axioms TermA4.freeP_of_pieceT
