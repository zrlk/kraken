/-
**`scc_rt_print`'s phase check from `PlaceOK`** (x86-64): `printPhOk`
(`Spike/Lib/X64PrintPh.lean`, `printPc`'s and `printSt`'s `hph`) at the
record's `okPc`/`ph` and labels of an output passing `placeOKAt`, from A7's
`tailOffC` (`Spike/Lib/X64TailPh.lean`), as `PhRec.abortPhOk_ofPlaceOK` from
`abortPhC`.

- `printPhOk_of_stub`: `StubW.printPhOk` (A7's, which also puts the `ret`'s
  pc in the entry's phase) gives `printPhOk`.
- `printPhOk_of_placeOKAt`: the check at the record of an output passing
  `placeOKAt`.
-/
import Spike.Lib.X64PrintPh
import Spike.Lib.X64TailPh
import Spike.Lib.X64PhRec

namespace Spike.Lib.X64.PrintG

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.PhRec (okPc ph)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

/-- **A7's print check gives `printPhOk`** (it drops the `ret`'s phase). -/
theorem printPhOk_of_stub {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
    (h : Spike.Lib.X64.StubW.printPhOk okPc ph lab = true) : printPhOk okPc ph lab = true := by
  simp only [Spike.Lib.X64.StubW.printPhOk, Bool.and_eq_true] at h
  simp only [printPhOk, Spike.Lib.X64.AllocG.aBlk, Bool.and_eq_true]
  exact h.1

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}

/-- **`scc_rt_print`'s phase check** at the record's `okPc`/`ph` and labels
of an output passing `placeOKAt` (A7's `tailOffC`, every label it reads at
its `codeLabel` address in the loaded thread). -/
theorem printPhOk_of_placeOKAt (h : placeOKAt pcfg Λ o = true) (i : CoreTerm.Expr → String → Nat → Option Nat) :
    printPhOk (okPc (RuntimeLayout.ofPlaceOK h i)) (ph (RuntimeLayout.ofPlaceOK h i))
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
  exact printPhOk_of_stub ht.1.1.1.1

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64.PrintG.printPhOk_of_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printPhOk_of_placeOKAt

end Spike.Lib.X64.PrintG
