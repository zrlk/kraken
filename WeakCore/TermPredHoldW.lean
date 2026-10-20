import WeakCore.TermPredHold
import WeakCore.TermMainDefs
import WeakCore.TermPlantFul

/-!
# TermPredHoldW: BH2′ of `bufInitHeld` from `PredHoldG`

A `bufInit` target is an own cell whose key the frame holds (`ownKey_frame`), hence unpublished
(`ownPub`); `PredHoldG` gives the first write at each predicted unit as an outstanding own
promise, and (H3) it is below every own promise there (`PromNotUndef`, `holder_min`).
-/

namespace TermPredHoldW

open CoreLang CoreTerm CoreTyping TermRun TermClose TermSound TermMem TermStep TermCut TermMain
  TermPredHold
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- A `bufInit` target is an unpublished own cell of the stepper. -/
theorem bufInit_ownNP {p : Prog} {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {i : Nat} {th : TTh}
    (hop : OwnPubG c Eg Tot HP HS) (hth : c.ths[i]? = some th) {S : AllocLabel → Prop} {ρ : Nat → Nat}
    {η : TEnv} {cx : Cx} {Rf Rs : Res} {K : TEnv → Nat → List Word → Res → Prop}
    (hCE : CE η = Cut Eg i S) (hsum : Rf + Rs = Tot i) (hT : Typed p cx th.term)
    (hi : FInvR ρ η th.σs K cx th.env Rf) (hsc : StepScope cx th.term ∨ StepScopeR th.σs cx th.term)
    {x : String} {b ia v : At} {e : Expr} (hterm : th.term = .let_ x (.bufInit b ia v) e) :
    ∀ rt w ad, evalAt th.env b = some (rt, [w]) → w.val = .loc ad 0 →
      (∃ cl, Eg.sto ad.label = some cl ∧ cl.owner = some i) ∧ ¬ Eg.pubd ad.label := by
  intro rt w ad he hw
  have hop' : OwnOpT cx th.term := Or.inl ⟨x, e, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨b, ia, v, hterm⟩))))⟩
  have htg : TermPlant.OpTgt th ad.label := ⟨b, rt, w, ad, 0, by rw [hterm]; rfl, he, hw, rfl⟩
  obtain ⟨cl, hs, ho, h1⟩ := TermPlantFul.ownKey_frame hT hi hsc hop' htg
  have hs' : (Cut Eg i S).sto ad.label = some cl := by rw [← hCE]; exact hs
  have hg := cutSto_sub hs'
  have ho' : cl.owner = some i := by
    have e2 : η.tid = i := by
      have := congrArg TEnv.tid hCE
      simp only [Cut_tid] at this
      rw [← this]; rfl
    rw [ho, e2]
  refine ⟨⟨cl, hg, ho'⟩, fun hpd => ?_⟩
  have h2 := ((hop ad.label hpd).2 (by rw [hg]; simp)).1 i th hth
  have e1 := congrArg (fun R : Res => R (.own ad.label)) hsum
  simp only [Res.add_apply] at e1 h2
  omega

/-- **BH2′ from `PredHoldG`.** -/
theorem bh2_of {p : Prog} {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {i : Nat} {th : TTh}
    (hPH : PredHoldG Eg c) (hNU : PromNotUndef c)
    (hop : OwnPubG c Eg Tot HP HS) (hth : c.ths[i]? = some th) {S : AllocLabel → Prop} {ρ : Nat → Nat}
    {η : TEnv} {cx : Cx} {Rf Rs : Res} {K : TEnv → Nat → List Word → Res → Prop}
    (hCE : CE η = Cut Eg i S) (hsum : Rf + Rs = Tot i) (hT : Typed p cx th.term)
    (hi : FInvR ρ η th.σs K cx th.env Rf) (hsc : StepScope cx th.term ∨ StepScopeR th.σs cx th.term)
    {x : String} {b ia v : At} {e : Expr} (hterm : th.term = .let_ x (.bufInit b ia v) e) :
    ∀ rt w ad, evalAt th.env b = some (rt, [w]) → w.val = .loc ad 0 → (CE η).pfr ad.label ≠ none →
      ∀ o, PredU (CE η) ⟨ad.label, o⟩ → ∃ h, FirstW (stOf c.mem c.pairs th).mem ⟨ad.label, o⟩ h ∧
        h ∈ (stOf c.mem c.pairs th).promises ∧ ∀ t m, t ∈ (stOf c.mem c.pairs th).promises →
          (stOf c.mem c.pairs th).mem[t]? = some m → m.loc = ⟨ad.label, o⟩ →
          (stOf c.mem c.pairs th).vs.coh ⟨ad.label, o⟩ < t → h ≤ t := by
  intro rt w ad he hw _ o hpu
  obtain ⟨hown, hnp⟩ := bufInit_ownNP hop hth hCE hsum hT hi hsc hterm rt w ad he hw
  rw [hCE] at hpu
  obtain ⟨h, hf, hh, -⟩ := hPH i th S ⟨ad.label, o⟩ hth hown hnp hpu
  exact ⟨h, hf, hh, fun t m ht hm hl _ => holder_min hf hm hl (hNU i th t m hth ht hm)⟩

#print axioms bufInit_ownNP
#print axioms bh2_of

end TermPredHoldW
