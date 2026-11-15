import WeakCore.TermC1Inv

/-! # TermC1Lem: region c1, small facts about the new definitions

* the `rgnOpOK1_*` facts are removed with `rgnOpOK1` itself.
* `noRes_of_not_affine` (g1): a copyable type carries no resource (`TermCut.noRes`), so region stores
  leave `HS` unchanged (`VRR_noRes`).
* `adapt_noOwn`: on a `noOwnIn` cell type `adapt r` is the identity.
-/

namespace TermC1

open CoreLang CoreTerm CoreTyping TermCut

/-- (g1) A copyable type (in any kind environment) carries no resource. -/
theorem noRes_of_not_affine : ∀ (t : Ty) {ke : KEnv}, Ty.affineIn ke t = false → noRes t = true := by
  intro t
  induction t with
  | prod a b iha ihb =>
      intro ke h
      simp only [Ty.affineIn, Bool.or_eq_false_iff] at h
      simp only [noRes, Bool.and_eq_true]
      exact ⟨iha h.1, ihb h.2⟩
  | sum a b iha ihb =>
      intro ke h
      simp only [Ty.affineIn, Bool.or_eq_false_iff] at h
      simp only [noRes, Bool.and_eq_true]
      exact ⟨iha h.1, ihb h.2⟩
  | refine t _ ih => intro ke h; simp only [Ty.affineIn] at h; simp only [noRes]; exact ih h
  | iall t ih => intro ke h; simp only [Ty.affineIn] at h; simp only [noRes]; exact ih h
  | iex t ih => intro ke h; simp only [Ty.affineIn] at h; simp only [noRes]; exact ih h
  | mu t ih => intro ke h; simp only [Ty.affineIn] at h; simp only [noRes]; exact ih h
  | tex κ t ih => intro ke h; simp only [Ty.affineIn] at h; simp only [noRes]; exact ih h
  | ptr μ t _ => intro ke h; cases μ <;> simp_all [Ty.affineIn, noRes]
  | ptrOpt μ t _ => intro ke h; cases μ <;> simp_all [Ty.affineIn, noRes]
  | loc μ t _ => intro ke h; cases μ <;> simp_all [Ty.affineIn, noRes]
  | _ => intro ke h; simp_all [Ty.affineIn, noRes]

/-- (g1) `affine` form, as `ruleA` states it (and `rgnPay` did while region payloads were copyable). -/
theorem noRes_of_affine_false {ke : KEnv} {t : Ty} (h : affine ke t = false) : noRes t = true :=
  noRes_of_not_affine t h

/-- (g1) A copyable `rgnPay` payload carries no resource. -/
theorem noRes_of_rgnPay {ke : KEnv} {u : Ty} (h : rgnPay ke u = true) (ha : affine ke u = false) :
    noRes u = true := by
  have _ := h
  exact noRes_of_affine_false ha

/-- On a `noOwnIn` cell type, `adapt r` is the identity. -/
theorem adapt_noOwn : ∀ (u : Ty) {ke : KEnv} {r : Idx}, Ty.noOwnIn ke u = true → adapt r u = u := by
  intro u
  induction u with
  | prod a b iha ihb =>
      intro ke r h
      simp only [Ty.noOwnIn, Bool.and_eq_true] at h
      simp only [adapt, iha h.1, ihb h.2]
  | sum a b iha ihb =>
      intro ke r h
      simp only [Ty.noOwnIn, Bool.and_eq_true] at h
      simp only [adapt, iha h.1, ihb h.2]
  | array i t ih => intro ke r h; simp only [Ty.noOwnIn] at h; simp only [adapt, ih h]
  | iex t ih => intro ke r h; simp only [Ty.noOwnIn] at h; simp only [adapt, ih h]
  | iall t ih => intro ke r h; simp only [Ty.noOwnIn] at h; simp only [adapt, ih h]
  | refine t ψ ih => intro ke r h; simp only [Ty.noOwnIn] at h; simp only [adapt, ih h]
  | mu t ih => intro ke r h; simp only [Ty.noOwnIn] at h; simp only [adapt, ih h]
  | tex κ t ih =>
      intro ke r h
      simp only [Ty.noOwnIn, Bool.and_eq_true] at h
      simp only [adapt, ih h.2]
  | ptr μ t _ => intro ke r h; cases μ <;> simp_all [Ty.noOwnIn, adapt]
  | ptrOpt μ t _ => intro ke r h; cases μ <;> simp_all [Ty.noOwnIn, adapt]
  | loc μ t _ => intro ke r h; cases μ <;> simp_all [Ty.noOwnIn, adapt]
  | _ => intro ke r h; simp [adapt]

end TermC1

#print axioms TermC1.noRes_of_not_affine
#print axioms TermC1.noRes_of_affine_false
#print axioms TermC1.noRes_of_rgnPay
#print axioms TermC1.adapt_noOwn
