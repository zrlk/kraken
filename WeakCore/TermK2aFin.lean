import WeakCore.TermK2aDispX
import WeakCore.TermGranStep
import WeakCore.TermK2aLinkPw

/-!
# TermK2aFin: `PtrRtsThreadGL`'s conclusion, v3d draft

`ptrRtsThreadGL_v3d`: `PtrRtsThreadGL` (re-frozen to v3d: the v3c binder list, then
`g.p = p`, `ProgT p`, fresh labels are not `a`, `E.box a = none`, the stepper export `FootBP`), the
`ret` frame link (`hRL`, counted-word form, from `RetPw`) and the box-load separation `BoxSep` at the old `tmin` (the
`boxPlantSep` field's per-thread projection).  Staging premise:
`FulCntR` (owes `fulCntR_of`).
-/

namespace TermK2aFin

open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermCert TermGlob TermTyped
open TermPtrRts TermOwnG0Defs TermK2a TermK2aLd TermK2aMain TermK2aDisp TermK2aBox
open TermCut (GEnv)
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

theorem ptrRtsThreadGL_v3d {p : Prog} (hFC : FulCntR p) : PtrRtsThreadGL p := by
  intro g E E' Eg Eg' sto sto' mem pairs th a r hk h1 h2 h3 h4 p1 p2 p3 p4 p5 p6 hI hM hP hnp hr hF hI' hA
    hNF hL hsc hdrf hps hC hgw hfrS hLay hNC hNC4 hp hPT hfa hBN hB1 hB2 hRL hBS
  have hPf : ∀ l f, E.pfr l = some f → Eg'.pfr l ≠ none ∨ Eg'.box l ≠ none := by
    intro l f h
    obtain ⟨f', hf'⟩ := Option.ne_none_iff_exists'.1 (p1 l f h)
    exact .inl (by rw [p5 l f' hf']; simp)
  have hBx : ∀ l B, E.box l = some B → Eg'.pfr l ≠ none ∨ Eg'.box l ≠ none := by
    intro l B h
    obtain ⟨B', hB'⟩ := Option.ne_none_iff_exists'.1 (p2 l B h)
    exact .inr (by rw [p6 l B' hB']; simp)
  have hGp : ∀ l, PubAt th l → Eg'.pfr l ≠ none ∨ Eg'.box l ≠ none := by
    intro l h
    obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 (hB2 l h)
    exact .inl (p3 l f hf)
  have hGf : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l →
      (∃ b ∈ r.2.2.env, ∃ w ∈ pubWords b.2.1 b.2.2, Names l w) → Eg'.pfr l ≠ none ∨ Eg'.box l ≠ none := by
    intro l hl ⟨b, hb, w, hw, hn⟩
    rcases hB1 l hl b hb w hw hn with h | h
    · obtain ⟨B, hB⟩ := Option.ne_none_iff_exists'.1 h
      exact .inr (p4 l B hB)
    · exact (thLbl_mono hL p5 p6).1 _ _ _ h w hw l hn
  have hS : StepOKX E sto (stOf mem pairs th) a (fun l => Eg'.pfr l ≠ none ∨ Eg'.box l ≠ none) th r.2.2 := by
    by_cases hret : ∃ a0, th.term = .ret a0
    · obtain ⟨a0, h⟩ := hret
      exact stepOKX_of_stepOK (N := fun l => Eg'.pfr l ≠ none ∨ Eg'.box l ≠ none)
        (stepOK_of_stepB_nil (TermK2aLinkPw.stepB_retK (hRL a0 h) h hr))
    · exact TermK2aDispX.stepOKX_disp hp hPT hI hM h1 hLay hgw hPf hBx hsc (fun a0 h => hret ⟨a0, h⟩) hfa hGf
        hnp hGp hBN hr hA
  refine ⟨ptrRtsE_step hk h1 h3 hI hM hP hnp hr hNF fun t ht =>
      ⟨memRts_step hk h1 h3 h4 hI hM hr hF ht (hP t ht).1 (hP t ht).2,
        thRts_of_stepBX (hP t ht).2 (hC t ht) (hBS t ht) hS.1⟩,
    thLbl_of_stepOKX (thLbl_mono hL p5 p6) hS,
    memRtsC_stepGLR hFC hk h1 h3 h4 hI hM hP hnp hr hF hNF hC,
    TermGranStep.granuleWP_step h1 h3 hI hM hr hsc hgw hfrS (fun l c h => hLay l c (h1 l c h)) hNC hNC4⟩

end TermK2aFin

#print axioms TermK2aFin.ptrRtsThreadGL_v3d
