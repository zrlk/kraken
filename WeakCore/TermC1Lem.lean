import WeakCore.TermC1Inv

/-! # TermC1Lem: region c1, small facts about the new definitions

* `noMonoSaw_not_tornLic`: no `monoSaw` entry ⇒ no `TornLic`, at every region/word/state.
* `rgnOpOK1_load` / `rgnOpOK1_store`: what an admitted region-cell load/store witnesses; the store's
  `HoldsSealed` is the `storeCap → storeRgn` reroute premise (`holdsSealed_sound`, CoreTyping L1125).
* `noRes_of_not_affine` (g1): a copyable type carries no resource (`TermCut.noRes`), so region stores
  leave `HS` unchanged (`VRR_noRes`).
* `adapt_noOwn`: on a `noOwnIn` cell type `adapt r` is the identity.
-/

namespace TermC1

open CoreLang CoreTerm CoreTyping TermCut

/-- Without an ordered observation of a monotone word in scope, no torn read is licensed. -/
theorem noMonoSaw_not_tornLic {cx : Cx} (h : cx.saws.any (monoSaw cx) = false) (r : Idx) (w : String)
    (s : Idx) : ¬ TornLic cx r w s := by
  intro ⟨hmem, t, b, r', P, hf, hw, _, hm, _⟩
  have hx := List.any_eq_false.mp h (w, s, true) hmem
  apply hx
  simp only [monoSaw, hf, hw, hm, Bool.true_and]

/-- (i1) An admitted region-cell load: a tok/share witness and no licensed torn read. -/
theorem rgnOpOK1_load {cx : Cx} {acq : Bool} {a : At} {r : Idx} {u : Ty}
    (h : rgnOpOK1 cx (.load acq a) = true) (hc : rgnCellAt cx a = some (r, u)) :
    (cx.hasTok r = true ∨ cx.hasShare r = true) ∧ ∀ q w s, ¬ TornLic cx q w s := by
  simp only [rgnOpOK1, hc, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1, fun q w s => noMonoSaw_not_tornLic h.2 q w s⟩

/-- (i1, g1) An admitted region-cell store: the sealed token (`HoldsSealed`, the reroute premise)
and a copyable cell type. -/
theorem rgnOpOK1_store {cx : Cx} {rel : Bool} {a v : At} {tk : Option At} {r : Idx} {u : Ty}
    (h : rgnOpOK1 cx (.store rel a v tk) = true) (hc : rgnCellAt cx a = some (r, u)) :
    HoldsSealed cx r ∧ affine cx.ke u = false := by
  simp only [rgnOpOK1, hc, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨holdsSealed_sound h.1.1 h.1.2, h.2⟩

/-- (i1) `xchg` is never admitted at a region cell. -/
theorem rgnOpOK1_xchg {cx : Cx} {a v : At} (h : rgnOpOK1 cx (.xchg a v) = true) :
    rgnCellAt cx a = none := by
  simp only [rgnOpOK1, Option.isNone_iff_eq_none] at h
  exact h

/-- (i1) `fetch` is never admitted at a region cell. -/
theorem rgnOpOK1_fetch {cx : Cx} {o : FetchOp} {acq rel : Bool} {a v : At}
    (h : rgnOpOK1 cx (.fetch o acq rel a v) = true) : rgnCellAt cx a = none := by
  simp only [rgnOpOK1, Option.isNone_iff_eq_none] at h
  exact h

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

/-- (g1) `affine` form, as `rgnOpOK1_store` and `rgnPay` state it. -/
theorem noRes_of_affine_false {ke : KEnv} {t : Ty} (h : affine ke t = false) : noRes t = true :=
  noRes_of_not_affine t h

/-- (g1) A `rgnPay` payload carries no resource. -/
theorem noRes_of_rgnPay {ke : KEnv} {u : Ty} (h : rgnPay ke u = true) : noRes u = true := by
  simp only [rgnPay, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact noRes_of_affine_false h.1.2

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

#print axioms TermC1.noMonoSaw_not_tornLic
#print axioms TermC1.rgnOpOK1_load
#print axioms TermC1.rgnOpOK1_store
#print axioms TermC1.rgnOpOK1_xchg
#print axioms TermC1.rgnOpOK1_fetch
#print axioms TermC1.noRes_of_not_affine
#print axioms TermC1.noRes_of_affine_false
#print axioms TermC1.noRes_of_rgnPay
#print axioms TermC1.adapt_noOwn
