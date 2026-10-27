/-
**`PrintTop` is at the output extern's model terms** (DRAFT, with the
model-frame exemption `Scc.Sem.externModelTerms`): every term of
`printL`'s body followed down (`PrintSvc.printTerms`) is a model term or
its `ret ()`, which reads no variable. This is the `hTop` of
`r_componentsAE` (`Spike/Lib/A64ConsumerAEComp.lean` and its x86-64 twin)
at `Top := PrintTop` (`emitA_of_nodes`).

- `printTerms_model`: a term followed down from a term of `PrintShape` is
  one of its `modelTerms` or `ret ()`.
- `printTop_ext`: the `hTop`.
-/
import Spike.Lib.PrintSvcRun
import Scc.Sem.Correct

namespace Spike.Lib.PrintSvc

open CoreLang CoreTerm
open Spike.Lib Spike.Lib.PrintSrc

/-- **A term followed down is a model term or `ret ()`.** -/
theorem printTerms_model {t u : Expr} (ht : PrintShape t) (hu : u ∈ printTerms t) :
    u ∈ Scc.Sem.modelTerms t ∨ u = .ret .unit := by
  induction t
  case let_ x op b ih =>
    simp only [printTerms, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact .inl (by simp [Scc.Sem.modelTerms])
    · rcases ih ht.2 hu with h | h
      · exact .inl (by simp [Scc.Sem.modelTerms, h])
      · exact .inr h
  case split a x y b ih =>
    simp only [printTerms, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact .inl (by simp [Scc.Sem.modelTerms])
    · rcases ih ht hu with h | h
      · exact .inl (by simp [Scc.Sem.modelTerms, h])
      · exact .inr h
  case ifeq a b y n ihy ihn =>
    simp only [printTerms, List.mem_cons, List.mem_append] at hu
    rcases hu with rfl | hu | hu
    · exact .inl (by simp [Scc.Sem.modelTerms])
    · rcases ihy ht.1 hu with h | h
      · exact .inl (by simp [Scc.Sem.modelTerms, h])
      · exact .inr h
    · rcases ihn ht.2 hu with h | h
      · exact .inl (by simp [Scc.Sem.modelTerms, h])
      · exact .inr h
  case ret a =>
    simp only [printTerms, List.mem_cons, List.not_mem_nil, or_false] at hu
    subst hu
    simp only [PrintShape] at ht
    subst ht
    exact .inr rfl
  all_goals
    simp only [printTerms, List.mem_cons, List.not_mem_nil, or_false] at hu
    subst hu
    exact .inl (by simp [Scc.Sem.modelTerms])

/-- **`PrintTop` is at the extern's model terms or reads no variable** (the
`hTop` of `r_componentsAE`). -/
theorem printTop_ext {c : Ctl} (h : PrintTop c) :
    c.term ∈ Scc.Sem.externModelTerms ∨ Scc.Sem.exprFv c.term = [] := by
  rcases printTerms_model printShape_printLBody h with h' | h'
  · refine .inl ?_
    have e : Scc.Frontend.printLBody = printLBody := rfl
    unfold Scc.Sem.externModelTerms
    rw [e]
    exact List.mem_append_right _ h'
  · rw [h']
    exact .inr rfl

end Spike.Lib.PrintSvc
