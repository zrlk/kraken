/-
**The refusal path's obligation at every allocation** (x86-64): `RefObl`
at every label `l` off the start's labels and every landed allocation
`b`, `n`, in the shape `X64WakeHB1.hB1_W` takes as `hobl`.

- `refObl_W`: `WakeRefStub.refObl_of` at wake's laid-out cells
  (`WakeSrcCtl.prog_W`), its threads-abort components discharged
  (`refAC`, `refAg`, `WakeRefAbSt.refAbSt`, `WakeRefNoWr.refNoWr`,
  `WakeRefAbW.refAbW`), mapped into `W1X` (`refMap`), the exit an abort site
  (`WakeRefEx.refEx`); the test and three blocks (`RefBlk`) and the lift to
  `ownGXW` (`RefLft`) are premises (`hblk`, `hlft`).

The AArch64 root discharges the refusal path inline (`WakeRefSeg.seg_refB`
at the root's `hobl`); x86-64 splits it into `RefStub`'s pieces, so this
module only joins them.

**Unlike AArch64**: the extra component `RefLft` (`Lft2`, no A64
counterpart: `W1X`'s state facts own `ownGXW`); the premises `hblk`, `hlft`
are carried until their proofs land. The allocation's landing (`hb`) is
not used by the pieces; it is kept to match `hobl`'s shape.
-/
import Spike.Lib.X64WakeRefAC
import Spike.Lib.X64WakeRefAg
import Spike.Lib.X64WakeRefAbSt
import Spike.Lib.X64WakeRefNoWr
import Spike.Lib.X64WakeRefAbW
import Spike.Lib.X64WakeRefMap
import Spike.Lib.X64WakeRefEx
import Spike.Lib.X64WakeRefBlk
import Spike.Lib.X64WakeRefLft

namespace Spike.Lib.X64.WakeRefOblW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (FragS PlaceWX)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lsize)
open Spike.Lib.X64WakeLoadT (L0T)
open Spike.Lib.X64.WakeRefStub (RefBlk RefLft refObl_of refAC refAg refMap)
open Spike.Lib.HeapLand (AllocLand)
open SccCode (wakeCells)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (asm : Asm) (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (cT : Loc) (Dt : State → Prop) (Ctx : FragS isa) (ls0 : Lsize)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **`hobl`**: the refusal path's obligation at every label off `L0T` and
every landed allocation, from the test and blocks (`hblk`) and the lift
(`hlft`); the other components are discharged. -/
theorem refObl_W (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells)
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) (hDt : ∀ s, Spike.Lib.X64.WakeWf.DtW s → Dt s)
    (hblk : ∀ l b n, L0T (Ly).Λ l = none →
      AllocLand (Spike.Lib.X64.WakeOD.arW hp i).heap (Spike.Lib.X64.WakeOD.arW hp i).cells b n →
      RefBlk asm hp i E Dt Ctx ls0 l b n)
    (hlft : ∀ l b, RefLft hp i l b) :
    ∀ l b n, L0T (Ly).Λ l = none →
      AllocLand (Spike.Lib.X64.WakeOD.arW hp i).heap (Spike.Lib.X64.WakeOD.arW hp i).cells b n →
      Spike.Lib.X64.WakeRefSeg.RefObl asm hp i E cT Dt Ctx ls0 l b n := fun l b n hl hb =>
  refObl_of asm hp i E cT Dt Ctx ls0 (Spike.Lib.X64.WakeSrcCtl.prog_W hp i hpa hwp ▸ (Ly).lays)
    (hblk l b n hl hb) (refAC hp i hpa hwp hlo ls0 n hl) (refAg hp i hpa hwp hlo l b)
    (Spike.Lib.X64.WakeRefAbSt.refAbSt hp i hpa hwp hlo l b)
    (Spike.Lib.X64.WakeRefNoWr.refNoWr hp i hpa hwp hlo ls0 l b n)
    (Spike.Lib.X64.WakeRefAbW.refAbW hp i hpa hwp hlo l b) (hlft l b)
    (refMap asm hp i E Dt Ctx ls0 hpa hwp hlo hDt l b n)
    (Spike.Lib.X64.WakeRefEx.refEx hp i asm hpa hwp hlo E cT ls0 l b n)

/-- **`hobl` at the root's `Dt := DtW`**: `refObl_W` with `hDt` closed. -/
theorem refObl_WD (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells)
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo)
    (hblk : ∀ l b n, L0T (Ly).Λ l = none →
      AllocLand (Spike.Lib.X64.WakeOD.arW hp i).heap (Spike.Lib.X64.WakeOD.arW hp i).cells b n →
      RefBlk asm hp i E Spike.Lib.X64.WakeWf.DtW Ctx ls0 l b n)
    (hlft : ∀ l b, RefLft hp i l b) :
    ∀ l b n, L0T (Ly).Λ l = none →
      AllocLand (Spike.Lib.X64.WakeOD.arW hp i).heap (Spike.Lib.X64.WakeOD.arW hp i).cells b n →
      Spike.Lib.X64.WakeRefSeg.RefObl asm hp i E cT Spike.Lib.X64.WakeWf.DtW Ctx ls0 l b n :=
  refObl_W asm hp i E cT _ Ctx ls0 hpa hwp hlo (fun _ h => h) hblk hlft

/-- **`hobl` at `Dt := DtW` with the test and blocks closed**:
`refObl_WD` with `hblk` by `WakeRefStub.refBlk`, the lift `hlft` a premise. -/
theorem refObl_WC (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells)
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hlft : ∀ l b, RefLft hp i l b) :
    ∀ l b n, L0T (Ly).Λ l = none →
      AllocLand (Spike.Lib.X64.WakeOD.arW hp i).heap (Spike.Lib.X64.WakeOD.arW hp i).cells b n →
      Spike.Lib.X64.WakeRefSeg.RefObl asm hp i E cT Spike.Lib.X64.WakeWf.DtW Ctx ls0 l b n :=
  refObl_WD asm hp i E cT Ctx ls0 hpa hwp hlo
    (fun _ _ _ hl _ => Spike.Lib.X64.WakeRefStub.refBlk asm hp i E _ Ctx ls0 hpa hwp hlo hA13 hl) hlft

/-- **`hobl` closed** at `Dt := DtW`: `refObl_WC` with the lift by
`WakeRefLft.refLft`. -/
theorem refObl_WF (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells)
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) :
    ∀ l b n, L0T (Ly).Λ l = none →
      AllocLand (Spike.Lib.X64.WakeOD.arW hp i).heap (Spike.Lib.X64.WakeOD.arW hp i).cells b n →
      Spike.Lib.X64.WakeRefSeg.RefObl asm hp i E cT Spike.Lib.X64.WakeWf.DtW Ctx ls0 l b n :=
  refObl_WC asm hp i E cT Ctx ls0 hpa hwp hlo hA13
    (Spike.Lib.X64.WakeRefLft.refLft hp i hpa hwp hlo hA13)

end Spike.Lib.X64.WakeRefOblW

/-- info: 'Spike.Lib.X64.WakeRefOblW.refObl_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefOblW.refObl_W

/-- info: 'Spike.Lib.X64.WakeRefOblW.refObl_WD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefOblW.refObl_WD

/-- info: 'Spike.Lib.X64.WakeRefOblW.refObl_WC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefOblW.refObl_WC

/-- info: 'Spike.Lib.X64.WakeRefOblW.refObl_WF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefOblW.refObl_WF
