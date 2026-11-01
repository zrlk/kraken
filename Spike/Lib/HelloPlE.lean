/-
**hello.w on AArch64: the source worker mid-`write` is placed** (row
5j-wit-E, `hplE`): at `EmitPh` the source worker's control is at a term of
`print`'s or `printL`'s body (`PTermE`), a model term of the output extern
or `ret ()` (`PrintSvc.printTerms_model`), so `PlacedSE` asks only its
frames placed; its frames are `EmitFrS`'s: none, a `D.Wi` pair's frames
(placed by `hplW`, row 5j-wit-W), or the frame of `print`'s call pushed from
a `D.Wi` control on an empty stack (placed by `hcall`, row 5j-wit-E-call).

- `pTermE_ext`: a `PTermE` term is in `externModelTerms` or reads no variable.
- `hplE_of`: `hplE` from `hplW` and `hcall`, at any placement `L w`.
-/
import Spike.Lib.HelloEmitPh
import Spike.Lib.A64PlacedSE
import Spike.Lib.PrintTopExt

namespace Spike.Lib.HelloPlE

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.WakeA64
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloW1 (WSideH)
open Spike.Lib.HelloSplit (workerCallH workerRestH)
open Spike.Lib.HelloEmitPh (EmitPh EmitFrS PTermE)

variable {ι : Type}

/-- **A term of `print`'s or `printL`'s body is a model term of the output
extern or `ret ()`** (`PrintSvc.printTerms_model`; `printTop_ext`'s
pattern, `print`'s and `printL`'s published bodies are `Scc.Frontend`'s). -/
theorem pTermE_ext {e : Expr} (h : PTermE e) : e ∈ externModelTerms ∨ exprFv e = [] := by
  have e1 : Scc.Frontend.printBody = PrintSrc.printBody := rfl
  have e2 : Scc.Frontend.printLPubBody = HelloPrintSrcPub.printLBodyP := rfl
  rcases h with h | h
  · rcases PrintSvc.printTerms_model HelloW1.printShape_printBody h with h' | h'
    · refine .inl ?_
      unfold externModelTerms
      rw [e1]
      simp [h']
    · rw [h']
      exact .inr rfl
  · rcases PrintSvc.printTerms_model HelloW1.printShape_printLBodyP h with h' | h'
    · refine .inl ?_
      unfold externModelTerms
      rw [e2]
      simp [h']
    · rw [h']
      exact .inr rfl

/-- **`hplE` from `hplW` and `hcall`**: at `EmitPh` (and any `D.Wi`), the
source worker is `PlacedSE` at the placement `L w`: its term by
`pTermE_ext` (`PlacedSE.of_ext`), its frames by `EmitFrS`: none placed
trivially, a `D.Wi` pair's by `hplW` (`PlacedSE.frames`), `print`'s call's
frame by `hcall`. -/
theorem hplE_of {D : WSideH ι} {Λ : Scc.Sem.Layout} {L : ι → Lbl}
    (hplW : ∀ w st c fs, D.Wi w st c fs → PlacedSE Λ (L w) st c fs)
    (hcall : ∀ w st c, D.Wi w st c [] → ∀ c', LocalRunS helloSrc c c' → c'.term = workerCallH →
      FramesPlaced Λ (L w) st [⟨"u", workerRestH, c'.env, [], .unit⟩]) :
    ∀ w tm sm t1 s1, EmitPh D w tm sm t1 s1 → PlacedSE Λ (L w) t1.st (Ctl.of s1) s1.stack := by
  intro w tm sm t1 s1 h
  refine PlacedSE.of_ext (pTermE_ext h.termE) ?_
  rcases h.frS with h0 | ⟨c0, fs0, hW, rfl | ⟨rfl, c', hr, ht, hfs⟩⟩
  · rw [h0]
    exact (FramesPlacedIn.nil (fun _ => False)).toFramesPlaced
  · exact (hplW w _ _ _ hW).frames
  · rw [hfs]
    exact hcall w _ _ hW c' hr ht

/-- info: 'Spike.Lib.HelloPlE.pTermE_ext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms pTermE_ext

/-- info: 'Spike.Lib.HelloPlE.hplE_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hplE_of

end Spike.Lib.HelloPlE
