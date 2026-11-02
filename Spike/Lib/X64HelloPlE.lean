/-
**hello.w on x86-64: the source worker mid-`write` is placed**
(`hplE`): at `EmitPh` the source worker's control is at a term of
`print`'s or `printL`'s body (`PTermE`), a model term of the output extern
or `ret ()` (`PrintSvc.printTerms_model`), so `PlacedSE` asks only its
frames placed; its frames are `EmitFrS`'s: none, a `D.Wi` pair's frames
(placed by `hplW`), or the frame of `print`'s call pushed from
a `D.Wi` control on an empty stack (placed by `hcall`).

- `pTermE_ext`: a `PTermE` term is in `externModelTerms` or reads no variable.
- `hplE_of`: `hplE` from `hplW` and `hcall`, at any placement `L w`.

x86-64 twin of `Spike/Lib/HelloPlE.lean` (same names, namespaces with the `X64` prefix).
Unlike AArch64, no `Scc.Cert.WideA64` facts are needed (the module opens
no width namespace); placement is `X64PlacedSE`'s.
-/
import Spike.Lib.X64HelloEmitPh
import Spike.Lib.X64PlacedSE
import Spike.Lib.PrintTopExt

namespace Spike.Lib.X64HelloPlE

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS
open Spike.Lib.X64WakeA64
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloW1 (WSideH)
open Spike.Lib.X64HelloSplit (workerCallH workerRestH)
open Spike.Lib.X64HelloEmitPh (EmitPh EmitFrS PTermE)

variable {ι : Type}

/-- **A term of `print`'s or `printL`'s body is a model term of the output
extern or `ret ()`** (`PrintSvc.printTerms_model`; `printTop_ext`'s
pattern, `print`'s and `printL`'s published bodies are `Scc.Frontend`'s). -/
theorem pTermE_ext {e : Expr} (h : PTermE e) : e ∈ externModelTerms ∨ exprFv e = [] := by
  have e1 : Scc.Frontend.printBody = PrintSrc.printBody := rfl
  have e2 : Scc.Frontend.printLPubBody = X64HelloPrintSrcPub.printLBodyP := rfl
  rcases h with h | h
  · rcases PrintSvc.printTerms_model X64HelloW1.printShape_printBody h with h' | h'
    · refine .inl ?_
      unfold externModelTerms
      rw [e1]
      simp [h']
    · rw [h']
      exact .inr rfl
  · rcases PrintSvc.printTerms_model X64HelloW1.printShape_printLBodyP h with h' | h'
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

/-- info: 'Spike.Lib.X64HelloPlE.pTermE_ext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms pTermE_ext

/-- info: 'Spike.Lib.X64HelloPlE.hplE_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hplE_of

end Spike.Lib.X64HelloPlE
