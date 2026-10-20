import WeakCore.TermCkS2

/-! # TermCkX (was TermA4X): re-selection at the branch-fact formers (A1 checker invariant)

At `parity`, `ifeq` and `cas`/`casp` the declarative `Typed` may pick another rule, or other
facts, than the checker (Complete.lean §1).  `TypedR Q`: those rules of `Typed`, verbatim, with
each child premise `Typed p c e` replaced by `Q c e`.  `checkW_inv_*`: the checker's own
derivation, with `checkW` at every child (`CkQ`).  A step lemma cases on it instead of on `hT`.
-/

namespace TermA4
open CoreLang CoreTerm CoreTyping TermScope

/-- `Typed`'s `parity`/`ifeq`/`cas`/`casp` rules with child premises `Q`. -/
inductive TypedR (Q : Cx → Expr → Prop) (p : Prog) : Cx → Expr → Prop
  | parity {cx : Cx} {a : At} {k : String} {ev od : Expr} {i : Idx} {v : Nat} :
      IntIdx cx a i → EqI cx i (.var v) →
      Q { cx.push k with facts := (v + 1, .smul 2 (.var 0)) :: (cx.push k).facts } ev →
      Q { cx.push k with facts := (v + 1, .add (.smul 2 (.var 0)) (.lit 1)) :: (cx.push k).facts } od →
      TypedR Q p cx (.parity a k ev od)
  | ifeqPlain {cx : Cx} {a b : At} {yes no : Expr} :
      PlainEq cx a b → Q cx yes → Q cx no → TypedR Q p cx (.ifeq a b yes no)
  | ifeq {cx c' : Cx} {a b : At} {yes no : Expr} {i j : Idx} :
      IntIdx cx a i → IntIdx cx b j → Q cx yes → NoCx cx i j c' → Q c' no →
      TypedR Q p cx (.ifeq a b yes no)
  | ifeqRec {cx c' : Cx} {a b : At} {yes no : Expr} {i j t : Idx} {v : Nat} :
      IntIdx cx a i → IntIdx cx b j →
      ((EqI cx i (.var v) ∧ EqI cx j t) ∨ (EqI cx j (.var v) ∧ EqI cx i t)) →
      Q { cx with facts := (v, t) :: cx.facts } yes → NoCx cx i j c' → Q c' no →
      TypedR Q p cx (.ifeq a b yes no)
  | ifeqZero {cx c' : Cx} {a b : At} {yes no : Expr} {i j : Idx} {u s : Nat} :
      IntIdx cx a i → IntIdx cx b j → ZeroEq cx i j u s →
      Q { cx with facts := (u, .lit 0) :: cx.facts } yes → NoCx cx i j c' → Q c' no →
      TypedR Q p cx (.ifeq a b yes no)
  | casCell {cx c₁ c₂ : Cx} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr} {tw u te tv : Ty} :
      cx.peek w = .ok tw → wordOf tw = none →
      (cellOf tw = some (.pub, u) ∨ ∃ r, cellOf tw = some (.rgn r, u) ∧ HasCap cx r true) →
      u.rawWords = some 1 →
      affine cx.ke u = false → cx.peek e = .ok te → cx.use v = .ok (tv, c₁) →
      SubS c₁ te u → SubS c₁ tv u → (Ty.sensitiveIn c₁.ke u = true → acq = true ∧ rel = true) →
      c₁.bind t .unit = .ok c₂ → Q c₂ ok → Q c₁ fail →
      TypedR Q p cx (.cas acq rel w e v t ok fail)
  | casShare {cx c₂ : Cx} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr} {tw : Ty}
      {r i j k k' : Idx} {P : Proto} {c c' : Nat} {cl cl' : Clause} :
      cx.peek w = .ok tw → wordOf tw = some (r, P) → P.ghost = false → IntIdx cx e i → IntIdx cx v j →
      InState cx P i c k → P.clauses[c]? = some cl → InState cx P j c' k' → P.clauses[c']? = some cl' →
      cl.holds = true → Step cx P c k c' k' → cl'.holds = true →
      LendCx cx acq rel r t P c k c' k' c₂ → Q c₂ ok → Q cx fail →
      TypedR Q p cx (.cas acq rel w e v t ok fail)
  | casTake {cx c₂ : Cx} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr} {tw : Ty}
      {r i j k k' : Idx} {P : Proto} {c c' : Nat} {cl cl' : Clause} :
      cx.peek w = .ok tw → wordOf tw = some (r, P) → P.ghost = false → IntIdx cx e i → IntIdx cx v j →
      InState cx P i c k → P.clauses[c]? = some cl → InState cx P j c' k' → P.clauses[c']? = some cl' →
      cl.holds = true → Step cx P c k c' k' → cl'.holds = false → P.lends.contains c = false →
      P.lendsDown.contains c = false → acq = true →
      cx.bind t (.tok r (some (P, j))) = .ok c₂ →
      Q (if monotone P then { c₂ with unsealed := r :: c₂.unsealed } else c₂) ok →
      Q cx fail → TypedR Q p cx (.cas acq rel w e v t ok fail)
  | casEpoch {cx c₂ : Cx} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr} {tw : Ty}
      {r i j k k' : Idx} {P : Proto} {c c' : Nat} :
      cx.peek w = .ok tw → wordOf tw = some (r, P) → P.epoch = true → acq = true →
      IntIdx cx e i → IntIdx cx v j → InState cx P i c k → InState cx P j c' k' →
      Step cx P c k c' k' → cx.bind t (.tokE r (.word P) j) = .ok c₂ → Q c₂ ok → Q cx fail →
      TypedR Q p cx (.cas acq rel w e v t ok fail)
  | caspE {cx c₂ : Cx} {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String} {ok fail : Expr} {tw : Ty}
      {r i0 i1 j0 j1 : Idx} {P : ECounter} :
      cx.peek w = .ok tw → word2Of tw = none → epairOf tw = some (r, P) → rel = true →
      IntIdx cx e0 i0 → IntIdx cx e1 i1 → IntIdx cx v0 j0 → IntIdx cx v1 j1 → HasTokE cx r P j0 →
      cx.bind t .unit = .ok c₂ → Q c₂ ok → Q cx fail →
      TypedR Q p cx (.casp acq rel w e0 e1 v0 v1 t ok fail)
  | caspBump {cx c₂ : Cx} {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String} {ok fail : Expr} {tw : Ty}
      {r i0 i1 j0 j1 k0 k1 k0' k1' : Idx} {P : Proto2} {c c' : Nat} {cl cl' : Clause2} :
      cx.peek w = .ok tw → word2Of tw = some (r, P) →
      IntIdx cx e0 i0 → IntIdx cx e1 i1 → IntIdx cx v0 j0 → IntIdx cx v1 j1 →
      InState2 cx P i0 i1 c k0 k1 → P.clauses[c]? = some cl →
      InState2 cx P j0 j1 c' k0' k1' → P.clauses[c']? = some cl' →
      cl.holds = true → Step2 cx P c k0 k1 c' k0' k1' → cl'.holds = true →
      P.epoch = true → Bump2 cx k0 k0' → acq = true →
      cx.bind t (.tokE r (.pair P) j0) = .ok c₂ → Q c₂ ok → Q cx fail →
      TypedR Q p cx (.casp acq rel w e0 e1 v0 v1 t ok fail)
  | caspMove {cx c₂ : Cx} {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String} {ok fail : Expr} {tw : Ty}
      {r i0 i1 j0 j1 k0 k1 k0' k1' : Idx} {P : Proto2} {c c' : Nat} {cl cl' : Clause2} :
      cx.peek w = .ok tw → word2Of tw = some (r, P) →
      IntIdx cx e0 i0 → IntIdx cx e1 i1 → IntIdx cx v0 j0 → IntIdx cx v1 j1 →
      InState2 cx P i0 i1 c k0 k1 → P.clauses[c]? = some cl →
      InState2 cx P j0 j1 c' k0' k1' → P.clauses[c']? = some cl' →
      cl.holds = true → Step2 cx P c k0 k1 c' k0' k1' → cl'.holds = true →
      cx.bind t .unit = .ok c₂ → Q c₂ ok → Q cx fail →
      TypedR Q p cx (.casp acq rel w e0 e1 v0 v1 t ok fail)
  | caspTake {cx c₂ : Cx} {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String} {ok fail : Expr} {tw : Ty}
      {r i0 i1 j0 j1 k0 k1 k0' k1' : Idx} {P : Proto2} {c c' : Nat} {cl cl' : Clause2} :
      cx.peek w = .ok tw → word2Of tw = some (r, P) →
      IntIdx cx e0 i0 → IntIdx cx e1 i1 → IntIdx cx v0 j0 → IntIdx cx v1 j1 →
      InState2 cx P i0 i1 c k0 k1 → P.clauses[c]? = some cl →
      InState2 cx P j0 j1 c' k0' k1' → P.clauses[c']? = some cl' →
      cl.holds = true → Step2 cx P c k0 k1 c' k0' k1' → cl'.holds = false → acq = true →
      cx.bind t (.tok2 r P j0 j1) = .ok c₂ → Q c₂ ok → Q cx fail →
      TypedR Q p cx (.casp acq rel w e0 e1 v0 v1 t ok fail)

/-- The checker accepts the child. -/
def CkQ (p : Prog) (c : Cx) (e : Expr) : Prop := checkW p c e = .ok ()

theorem checkW_inv_parity {p : Prog} {cx : Cx} {a : At} {k : String} {ev od : Expr}
    (h : checkW p cx (.parity a k ev od) = .ok ()) : TypedR (CkQ p) p cx (.parity a k ev od) := by
  unfold CkQ
  simp only [checkW, bind_ok_iff] at h
  obtain ⟨i, hi, h⟩ := h
  split at h
  · rename_i v hv
    simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
    obtain ⟨_, h1, h2⟩ := h
    exact .parity (intIdx_sound hi) (asVar_eqI hv) h1 h2
  · simp at h

theorem checkW_inv_ifeq {p : Prog} {cx : Cx} {a b : At} {yes no : Expr}
    (h : checkW p cx (.ifeq a b yes no) = .ok ()) : TypedR (CkQ p) p cx (.ifeq a b yes no) := by
  unfold CkQ
  simp only [checkW] at h
  split at h
  · rename_i hpe
    simp only [bind_ok_iff] at h
    obtain ⟨_, h1, h2⟩ := h
    exact .ifeqPlain (plainEq_sound hpe) h1 h2
  simp only [bind_ok_iff] at h
  obtain ⟨i, hi, j, hj, h⟩ := h
  split at h
  · rename_i ni nj hni hnj
    split at h
    · simp only [bind_ok_iff] at h
      obtain ⟨_, h1, h2⟩ := h
      exact .ifeq (intIdx_sound hi) (intIdx_sound hj) h1 (noCx_sound hni hnj) h2
    · split at h
      · split at h
        · simp at h
        · simp only [bind_ok_iff] at h
          obtain ⟨_, h1, h2⟩ := h
          refine .ifeqRec (intIdx_sound hi) (intIdx_sound hj) (.inl ⟨?_, ?_⟩) h1 (noCx_sound hni hnj) h2
          · intro ρ hs
            have e1 := norm_sound _ ρ hs _ _ _ hni
            have e2 := asVar_ev ρ ni _ (by assumption)
            simp [ev]; omega
          · intro ρ hs
            have e1 := norm_sound _ ρ hs _ _ _ hnj
            simp; omega
      · split at h
        · simp at h
        · simp only [bind_ok_iff] at h
          obtain ⟨_, h1, h2⟩ := h
          refine .ifeqRec (intIdx_sound hi) (intIdx_sound hj) (.inr ⟨?_, ?_⟩) h1 (noCx_sound hni hnj) h2
          · intro ρ hs
            have e1 := norm_sound _ ρ hs _ _ _ hnj
            have e2 := asVar_ev ρ nj _ (by assumption)
            simp [ev]; omega
          · intro ρ hs
            have e1 := norm_sound _ ρ hs _ _ _ hni
            simp; omega
      · split at h
        · rename_i u hz
          simp only [bind_ok_iff] at h
          obtain ⟨_, h1, h2⟩ := h
          obtain ⟨s, hze⟩ := zeroVar_sound hni hnj hz
          exact .ifeqZero (intIdx_sound hi) (intIdx_sound hj) hze h1
            (noCx_sound hni hnj) h2
        · simp at h
  · simp at h

theorem checkW_inv_cas {p : Prog} {cx : Cx} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr}
    (h : checkW p cx (.cas acq rel w e v t ok fail) = .ok ()) :
    TypedR (CkQ p) p cx (.cas acq rel w e v t ok fail) := by
  unfold CkQ
  simp only [checkW, bind_ok_iff] at h
  obtain ⟨tw, htw, h⟩ := h
  split at h
  · rename_i hw
    simp only [bind_ok_iff] at h
    obtain ⟨u, hc, h⟩ := h
    split at h <;> (try (simp at h; done))
    rename_i hraw
    split at h <;> (try (simp at h; done))
    rename_i haff
    simp only [bind_ok_iff, Prod.exists] at h
    obtain ⟨te, hte, tv, c₁, h1, h⟩ := h
    try dsimp only at h
    split at h <;> (try (simp at h; done))
    rename_i hse
    split at h <;> (try (simp at h; done))
    rename_i hsv
    split at h <;> (try (simp at h; done))
    rename_i hsens
    simp only [bind_ok_iff] at h
    obtain ⟨c₂, h2, _, h3, h4⟩ := h
    exact .casCell htw hw (casCellTy_sound hc) (by simpa using hraw) (by simpa using haff) hte h1
      (sub_sound _ _ _ (by simpa using hse)) (sub_sound _ _ _ (by simpa using hsv))
      (fun hs => by simpa [hs] using hsens) h2 h3 h4
  · rename_i r P hw
    cases hep : P.epoch
    case true =>
      simp only [hep, ↓reduceIte] at h
      split at h <;> (try (simp at h; done))
      rename_i hacq
      simp only [bind_ok_iff, Prod.exists] at h
      obtain ⟨i, hi, j, hj, c, k, hc, c', k', hc', h⟩ := h
      try dsimp only at h
      split at h <;> (try (simp at h; done))
      rename_i hps
      simp only [bind_ok_iff] at h
      obtain ⟨c₂, h3, _, h4, h2⟩ := h
      exact .casEpoch htw hw hep (by simpa using hacq) (intIdx_sound hi) (intIdx_sound hj)
        (classifyM_sound _ _ _ _ _ hc) (classifyM_sound _ _ _ _ _ hc')
        (pstep_sound _ _ _ _ _ _ (by simpa using hps)) h3 h4 h2
    simp only [hep, Bool.false_eq_true, ↓reduceIte] at h
    cases hg : P.ghost
    case true => simp only [hg, ↓reduceIte] at h; simp at h
    simp only [hg, Bool.false_eq_true, ↓reduceIte] at h
    simp only [bind_ok_iff, Prod.exists] at h
    obtain ⟨i, hi, j, hj, c, k, hc, c', k', hc', cl, hcl, cl', hcl', h⟩ := h
    try dsimp only at h
    split at h <;> (try (simp at h; done))
    rename_i hh
    split at h <;> (try (simp at h; done))
    rename_i hps
    split at h
    · rename_i hh'
      simp only [bind_ok_iff] at h
      obtain ⟨c₂, h3, _, h4, h2⟩ := h
      exact .casShare htw hw (by simpa using hg) (intIdx_sound hi) (intIdx_sound hj)
        (classifyM_sound _ _ _ _ _ hc) (clauseM_ok hcl) (classifyM_sound _ _ _ _ _ hc')
        (clauseM_ok hcl') (by simpa using hh) (pstep_sound _ _ _ _ _ _ (by simpa using hps))
        hh' (lendCx_sound h3) h4 h2
    · rename_i hh'
      split at h <;> (try (simp at h; done))
      rename_i hlend
      split at h <;> (try (simp at h; done))
      rename_i hacq
      simp only [bind_ok_iff] at h
      obtain ⟨c₂, h3, _, h4, h2⟩ := h
      exact .casTake htw hw (by simpa using hg) (intIdx_sound hi) (intIdx_sound hj)
        (classifyM_sound _ _ _ _ _ hc) (clauseM_ok hcl) (classifyM_sound _ _ _ _ _ hc')
        (clauseM_ok hcl') (by simpa using hh) (pstep_sound _ _ _ _ _ _ (by simpa using hps))
        (by simpa using hh')
        (by simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hlend; exact hlend.1)
        (by simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hlend; exact hlend.2)
        (by simpa using hacq) h3 h4 h2

theorem checkW_inv_casp {p : Prog} {cx : Cx} {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String}
    {ok fail : Expr} (h : checkW p cx (.casp acq rel w e0 e1 v0 v1 t ok fail) = .ok ()) :
    TypedR (CkQ p) p cx (.casp acq rel w e0 e1 v0 v1 t ok fail) := by
  unfold CkQ
  simp only [checkW, bind_ok_iff] at h
  obtain ⟨tw, htw, h⟩ := h
  split at h
  · rename_i hw2
    split at h
    · simp at h
    · rename_i r P hw
      split at h <;> (try (simp at h; done))
      rename_i hrel
      simp only [bind_ok_iff] at h
      obtain ⟨i0, hi0, i1, hi1, j0, hj0, j1, hj1, h⟩ := h
      try dsimp only at h
      split at h <;> (try (simp at h; done))
      rename_i htk
      simp only [bind_ok_iff] at h
      obtain ⟨c₂, h3, _, h4, h2⟩ := h
      exact .caspE htw hw2 hw (by simpa using hrel) (intIdx_sound hi0) (intIdx_sound hi1)
        (intIdx_sound hj0) (intIdx_sound hj1) (hasTokE_sound (by simpa using htk)) h3
        h4 h2
  · rename_i r P hw
    simp only [bind_ok_iff, Prod.exists] at h
    obtain ⟨i0, hi0, i1, hi1, j0, hj0, j1, hj1, c, k0, k1, hc, c', k0', k1', hc', cl, hcl, cl', hcl', h⟩ := h
    try dsimp only at h
    split at h <;> (try (simp at h; done))
    rename_i hh
    split at h <;> (try (simp at h; done))
    rename_i hps
    split at h
    · rename_i hh'
      split at h
      · rename_i hb
        split at h <;> (try (simp at h; done))
        rename_i hacq
        simp only [bind_ok_iff] at h
        obtain ⟨c₂, h3, _, h4, h2⟩ := h
        obtain ⟨hep, hbump⟩ := bump2_sound cx P k0 k0' hb
        exact .caspBump htw hw (intIdx_sound hi0) (intIdx_sound hi1) (intIdx_sound hj0) (intIdx_sound hj1)
          (classify2M_sound _ _ _ _ _ _ _ hc) (clause2M_ok hcl) (classify2M_sound _ _ _ _ _ _ _ hc')
          (clause2M_ok hcl') (by simpa using hh) (pstep2_sound _ _ _ _ _ _ _ _ (by simpa using hps))
          hh' hep hbump (by simpa using hacq) h3 h4 h2
      · simp only [bind_ok_iff] at h
        obtain ⟨c₂, h3, _, h4, h2⟩ := h
        exact .caspMove htw hw (intIdx_sound hi0) (intIdx_sound hi1) (intIdx_sound hj0) (intIdx_sound hj1)
          (classify2M_sound _ _ _ _ _ _ _ hc) (clause2M_ok hcl) (classify2M_sound _ _ _ _ _ _ _ hc')
          (clause2M_ok hcl') (by simpa using hh) (pstep2_sound _ _ _ _ _ _ _ _ (by simpa using hps))
          hh' h3 h4 h2
    · rename_i hh'
      split at h <;> (try (simp at h; done))
      rename_i hacq
      simp only [bind_ok_iff] at h
      obtain ⟨c₂, h3, _, h4, h2⟩ := h
      exact .caspTake htw hw (intIdx_sound hi0) (intIdx_sound hi1) (intIdx_sound hj0) (intIdx_sound hj1)
        (classify2M_sound _ _ _ _ _ _ _ hc) (clause2M_ok hcl) (classify2M_sound _ _ _ _ _ _ _ hc')
        (clause2M_ok hcl') (by simpa using hh) (pstep2_sound _ _ _ _ _ _ _ _ (by simpa using hps))
        (by simpa using hh') (by simpa using hacq) h3 h4 h2

/-- (A1 checker invariant, entry frames) **`WitA` at the default witnesses**: an entry frame's `Cut`
environment keeps `TEnv`'s default `wit` (`.void`), which is `argTop`; no condition on `ke`. -/
theorem WitA_void {cx : Cx} {ω : Nat → Ty} (h : ∀ k, ω k = .void) : WitA cx ω :=
  fun k _ _ => by rw [h k]; rfl


end TermA4

