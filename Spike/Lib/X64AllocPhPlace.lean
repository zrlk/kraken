/-
**The allocator's phase and abort-target checks from `PlaceOK`** (x86-64):
`allocPhOk` (`Spike/Lib/X64AllocPh.lean`) and `allocAbOk`
(`Spike/Lib/X64AllocAbOk.lean`), `allocW2At_of`'s `hph` and `habk`, at the
record's `okPc`/`ph` and labels of an output passing `placeOKAt`, from A7's
`tailOffC` (`Spike/Lib/X64TailPh.lean`), as `abortPhHeapOk_ofPlaceOK`. The
twins of AArch64's `Rt.allocPhOk_ofPlaceOK`, `Rt.allocAbOk_ofPlaceOK`.

- `tailPhOk_ofPlaceOK`: A7's `tailPhOk` at the record;
- `allocPhOk_ofPlaceOK`, `allocAbOk_ofPlaceOK`: its allocator parts.
-/
import Spike.Lib.X64TailPh
import Spike.Lib.X64PhRec

namespace Spike.Lib.X64.PhRec

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}

/-- **A7's `tailPhOk`** at the record's `okPc`/`ph` and labels of an output
passing `placeOKAt` (`tailOffC`, every label it reads at its `codeLabel`
address in the loaded thread). -/
theorem tailPhOk_ofPlaceOK (h : placeOKAt pcfg Λ o = true) (i : CoreTerm.Expr → String → Nat → Option Nat) :
    Spike.Lib.X64.StubW.tailPhOk (okPc (RuntimeLayout.ofPlaceOK h i)) (ph (RuntimeLayout.ofPlaceOK h i))
      (RuntimeLayout.ofPlaceOK h i).lab = true := by
  haveI : Kraken.Executable.ValidLayout (Scc.Sem.X64.threadAt Scc.Sem.Entry.linux (Λ).code.lo
      o.prog (Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)).exe :=
    (RuntimeLayout.ofPlaceOK h i).valid
  exact Spike.Lib.X64.StubW.tailPhOk_of_tailOffC (tailOff_of_placeOKAt h)
    (lab := (RuntimeLayout.ofPlaceOK h i).lab) fun _ _ ha =>
    Scc.Cert.Rt.X64.label_threadAt_of_codeLabel_below (E := Scc.Sem.Entry.linux)
      (syms := Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)
          (by exact Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK_below h i ha) ha

/-- **The allocator's phase check** (`allocW2At_of`'s `hph`) at the record
of an output passing `placeOKAt`. -/
theorem allocPhOk_ofPlaceOK (h : placeOKAt pcfg Λ o = true) (i : CoreTerm.Expr → String → Nat → Option Nat) :
    Spike.Lib.X64.AllocG.allocPhOk (okPc (RuntimeLayout.ofPlaceOK h i)) (ph (RuntimeLayout.ofPlaceOK h i))
      (RuntimeLayout.ofPlaceOK h i).lab = true := by
  have ht := tailPhOk_ofPlaceOK h i
  simp only [Spike.Lib.X64.StubW.tailPhOk, Bool.and_eq_true] at ht
  exact ht.1.2

/-- **The allocator's targets off the write abort's pcs** (`allocW2At_of`'s
`habk`) at the record's labels of an output passing `placeOKAt`. -/
theorem allocAbOk_ofPlaceOK (h : placeOKAt pcfg Λ o = true) (i : CoreTerm.Expr → String → Nat → Option Nat) :
    Spike.Lib.X64.AllocG.allocAbOk (RuntimeLayout.ofPlaceOK h i).lab = true := by
  have ht := tailPhOk_ofPlaceOK h i
  simp only [Spike.Lib.X64.StubW.tailPhOk, Bool.and_eq_true] at ht
  exact ht.2

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64.PhRec.tailPhOk_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tailPhOk_ofPlaceOK

/-- info: 'Spike.Lib.X64.PhRec.allocPhOk_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocPhOk_ofPlaceOK

/-- info: 'Spike.Lib.X64.PhRec.allocAbOk_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocAbOk_ofPlaceOK

end Spike.Lib.X64.PhRec
