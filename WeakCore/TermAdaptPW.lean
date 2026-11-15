import WeakCore.TermCntEmb

/-!
# TermAdaptPW: `adapt` is invisible to counted words (K1a, for the `fulCntR_of`)

At a closing `cl ρ W 0 0`, `adapt r` only turns `own` reference modes into `rgn (lit n)` modes
(`mr_cl_adapt`), and every layout reading (`info`, `accs`, `wc`, `lnorm`, `armsOf`) ignores a
reference's mode (`MR`).  (M8) `sNo` does not: a region reference is pub, so `sNo` only grows along
`MR`, and the counted words (`pubWords`, `pubArm`) agree at a shallow-pub type (all words count).
-/

namespace TermAdaptPW
open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermPtrRts TermCntLoc
open TermClose (cl clM clI Clo)

/-! ## Closing an `adapt` -/

/-! ## Readings that ignore reference modes -/

/-- (M8) `sNo` grows along `MR` (`own` ↦ `rgn`, and a region reference is pub). -/
theorem mr_sNo {t t' : Ty} (h : MR t t') (hs : sNo t = true) : sNo t' = true := by
  revert hs
  induction h with
  | refl => exact id
  | ptr | ptrOpt | loc => intro _; simp [sNo, mPub]
  | prod _ _ iha ihb | sum _ _ iha ihb =>
    intro hs; simp only [sNo, Bool.and_eq_true] at hs ⊢; exact ⟨iha hs.1, ihb hs.2⟩
  | array _ _ ih | refine _ _ ih | iex _ ih | iall _ ih | mu _ ih =>
    intro hs; simp only [sNo] at hs ⊢; exact ih hs
  | tex _ _ ih => intro hs; simp only [sNo, Bool.and_eq_true] at hs ⊢; exact ⟨hs.1, ih hs.2⟩

theorem mr_lnorm {t t' : Ty} (h : MR t t') : lnorm t = lnorm t' := by
  induction h with
  | refl => rfl
  | ptr | ptrOpt | loc => rfl
  | prod _ _ iha ihb | sum _ _ iha ihb => simp only [lnorm, iha, ihb]
  | array => rfl
  | refine _ _ ih | iex _ ih | iall _ ih | mu _ ih | tex _ _ ih => simp only [lnorm, ih]

theorem mr_armsLen {t t' : Ty} (h : MR t t') : (armsOf t).length = (armsOf t').length := by
  induction h with
  | refl => rfl
  | ptr | ptrOpt | loc => rfl
  | prod => rfl
  | sum _ _ iha ihb => simp only [armsOf, List.length_append, iha, ihb]
  | array => rfl
  | refine _ _ ih | iex _ ih | iall _ ih | mu _ ih | tex _ _ ih => simp only [armsOf]; exact ih

/-- At a shallow-pub type every arm payload word counts. -/
theorem pubArm_of_sNo : ∀ (t : Ty) (j : Nat) (p : List Word), sNo t = true → pubArm t j p = p := by
  intro t
  induction t with
  | sum a b iha ihb =>
    intro j p h; simp only [sNo, Bool.and_eq_true] at h; simp only [pubArm]
    split
    · exact iha _ _ h.1
    · exact ihb _ _ h.2
  | refine t _ ih => intro j p h; simp only [sNo] at h; simp only [pubArm]; exact ih _ _ h
  | iall t ih => intro j p h; simp only [sNo] at h; simp only [pubArm]; exact ih _ _ h
  | iex t ih => intro j p h; simp only [sNo] at h; simp only [pubArm]; exact ih _ _ h
  | mu t ih => intro j p h; simp only [sNo] at h; simp only [pubArm]; exact ih _ _ h
  | tex κ t ih => intro j p h; simp only [sNo, Bool.and_eq_true] at h; simp only [pubArm]; exact ih _ _ h.2
  | _ => intro j p h; rw [pubArm.eq_def]; simp only []; exact pubWords_of_sNo h p

/-- (M8) Along `MR`, from a shallow-pub type: the counted words agree (all of them count on both sides). -/
theorem mr_pub {t t' : Ty} (h : MR t t') (hs : sNo t = true) :
    (∀ ws, pubWords t ws = pubWords t' ws) ∧ (∀ j p, pubArm t j p = pubArm t' j p) := by
  have hs' := mr_sNo h hs
  exact ⟨fun ws => by rw [pubWords_of_sNo hs, pubWords_of_sNo hs'],
    fun j p => by rw [pubArm_of_sNo t j p hs, pubArm_of_sNo t' j p hs']⟩

/-! ## The adapters -/

/-- **`adapt` keeps counted words** (at a closing that closes the region index; (M8) at a
shallow-pub closing). -/
theorem pubWords_cl_adaptG (u : Ty) (r : Idx) (ρ : Nat → Nat) (W : Nat → Ty) (c d : Nat)
    (hr : ∀ k, k < d → r.mentions k = false) (hs : sNo (cl ρ W c d u) = true) :
    (∀ L, pubWords (cl ρ W c d (adapt r u)) L = pubWords (cl ρ W c d u) L) ∧
    (∀ j p, pubArm (cl ρ W c d (adapt r u)) j p = pubArm (cl ρ W c d u) j p) ∧
    wc (cl ρ W c d (adapt r u)) = wc (cl ρ W c d u) := by
  have h := mr_cl_adapt ρ W u r c d hr
  exact ⟨fun L => ((mr_pub h hs).1 L).symm, fun j p => ((mr_pub h hs).2 j p).symm, (mr_wc h).symm⟩

/-- **The form** (`fulCntR_of`): at `cl ρ W 0 0`, (M8) shallow-pub, `adapt` keeps counted words and
the word count. -/
theorem pubWords_cl_adapt0 (u : Ty) (r : Idx) (ρ : Nat → Nat) (W : Nat → Ty) (hs : sNo (cl ρ W 0 0 u) = true) :
    (∀ L, pubWords (cl ρ W 0 0 (adapt r u)) L = pubWords (cl ρ W 0 0 u) L) ∧
    wc (cl ρ W 0 0 (adapt r u)) = wc (cl ρ W 0 0 u) := by
  have h := pubWords_cl_adaptG u r ρ W 0 0 (fun k hk => absurd hk (Nat.not_lt_zero k)) hs
  exact ⟨h.1, h.2.2⟩

end TermAdaptPW

#print axioms TermAdaptPW.pubWords_cl_adaptG
#print axioms TermAdaptPW.pubWords_cl_adapt0
