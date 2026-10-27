/-
**The heap abort path's phase check from `PlaceOK`** (x86-64):
`abortPhHeapOk` (`Spike/Lib/X64AbortPhH.lean`, `stubHN_w2`'s `hphs`) at the
record's `okPc`/`ph` and labels of an output passing `placeOKAt`, from A7's
`tailOffC` (`Spike/Lib/X64TailPh.lean`), as `abortPhOk_ofPlaceOK` from
`abortPhC`. The twin of AArch64's `Rt.abortPhHeapOk_ofPlaceOK`.
-/
import Spike.Lib.X64TailPh
import Spike.Lib.X64PhRec

namespace Spike.Lib.X64.PhRec

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}

/-- **The heap abort path's phase check** at the record's `okPc`/`ph` and
labels of an output passing `placeOKAt` (A7's `tailOffC`, every label it
reads at its `codeLabel` address in the loaded thread). -/
theorem abortPhHeapOk_ofPlaceOK (h : placeOKAt pcfg Λ o = true) (i : CoreTerm.Expr → String → Nat → Option Nat) :
    Spike.Lib.X64.StubW.abortPhHeapOk (okPc (RuntimeLayout.ofPlaceOK h i)) (ph (RuntimeLayout.ofPlaceOK h i))
      (RuntimeLayout.ofPlaceOK h i).lab = true := by
  haveI : Kraken.Executable.ValidLayout (Scc.Sem.X64.threadAt Scc.Sem.Entry.linux (Λ).code.lo
      o.prog (Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)).exe :=
    (RuntimeLayout.ofPlaceOK h i).valid
  have ht := Spike.Lib.X64.StubW.tailPhOk_of_tailOffC (tailOff_of_placeOKAt h)
    (lab := (RuntimeLayout.ofPlaceOK h i).lab) fun _ _ ha =>
    Scc.Cert.Rt.X64.label_threadAt_of_codeLabel_below (E := Scc.Sem.Entry.linux)
      (syms := Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)
          (by exact Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK_below h i ha) ha
  simp only [Spike.Lib.X64.StubW.tailPhOk, Bool.and_eq_true] at ht
  exact ht.1.1.2

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64.PhRec.abortPhHeapOk_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms abortPhHeapOk_ofPlaceOK

end Spike.Lib.X64.PhRec
