import WeakCore.TermK2aDisp
import WeakCore.TermK2aCaseB

/-!
# TermK2aDispX: the step dispatch with box loads

`stepOKX_disp`: the `StepOKX` contract for every non-`ret` term.  A `case` goes through
`TermK2aCaseB.sum_caseTX` (box loads via `BoxLW`); every other term through
`TermK2aDisp.stepOK_disp`, whose box-arm premise is vacuous off `case`.
-/

namespace TermK2aDispX

open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermCert TermGlob TermTyped
open TermPtrRts TermOwnG0Defs TermK2a TermK2aLd TermK2aMain TermK2aBox
open TermCut (GEnv)
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **The dispatch with box loads**: `StepOKX` for a non-`ret` step, given `E.box ga = none`. -/
theorem stepOKX_disp {p : Prog} {g : G} {E : TEnv} {sto : Sto} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ga : AllocLabel} {r : Memory × List Ts × TTh} {Gl : AllocLabel → Prop}
    (hp : g.p = p) (hP : ProgT p) (hI : ThInvE p E th) (hM : MemInv g E (stOf mem pairs th))
    (h1 : ∀ l c, E.sto l = some c → sto l = some c) (hLay : ∀ l c, sto l = some c → LayT c.ty)
    (hG : GranuleWP sto mem pairs th.promises)
    (hPf : ∀ l f, E.pfr l = some f → Gl l) (hBx : ∀ l B, E.box l = some B → Gl l)
    (hsc : ScopeOK p th) (hnr : ∀ a, th.term ≠ .ret a)
    (hfa : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → l ≠ ga)
    (hGf : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l →
      (∃ b ∈ r.2.2.env, ∃ w ∈ pubWords b.2.1 b.2.2, Names l w) → Gl l)
    (hnp : ¬ PubAt th ga) (hGp : ∀ l, PubAt th l → Gl l) (hgb : E.box ga = none)
    (hr : r ∈ tstep g mem pairs th) (hA : PromAbove (stOf r.1 r.2.1 r.2.2)) :
    StepOKX E sto (stOf mem pairs th) ga Gl th r.2.2 := by
  by_cases hc : ∃ a x e₁ y e₂, th.term = .case a x e₁ y e₂
  · obtain ⟨a, x, e₁, y, e₂, ht⟩ := hc
    obtain ⟨ρ, η, cx, rfl, hE, hT, htv, hi, -⟩ := hI
    exact TermK2aCaseB.sum_caseTX (N := Gl) ht hT hi htv hE hM sto hPf hBx hgb hr hA hfa hGf hGf
  · exact stepOKX_of_stepOK (TermK2aDisp.stepOK_disp hp hP hI hM h1 hLay hG hPf hBx hsc hnr hfa hGf hnp hGp
      (fun a x e₁ y e₂ ht => (hc ⟨a, x, e₁, y, e₂, ht⟩).elim) hr hA)

end TermK2aDispX

#print axioms TermK2aDispX.stepOKX_disp
