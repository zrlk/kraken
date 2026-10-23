/-
**The atomic accesses' phases from `placeOK` at `ret0`** (x86-64;
`Spike/Lib/X64PhPinsOfPlaceOK.lean`): the three phase indices at `ret0P`,
and the bits the owned counters read from them.
-/
import Spike.Lib.X64PhPinsOfPlaceOK

namespace Spike.Lib.X64.PhRec.PinsTest

open Scc.Cert.PlaceOK.X64 (atTables)

open Spike.Lib.X64.Rt (ret0P)
open SccCode (ret0Imms)
open Scc.Cert.PlaceOK.X64.Test (ret0_placeOK)

example : ph ret0P (Spike.Lib.X64.Flow.Ret0.AllocTcb.rmwPc ret0P.lab).toBitVec.toNat = 13 :=
  hphT_ofPlaceOK (atTables ret0_placeOK) ret0Imms
example : ph ret0P (Spike.Lib.X64.Flow.Ret0.StackTake.swpPc ret0P.lab).toBitVec.toNat = 12 :=
  hphL_ofPlaceOK (atTables ret0_placeOK) ret0Imms
example : ph ret0P (Spike.Lib.X64.Flow.Ret0.StackTake.nextPc ret0P.lab).toBitVec.toNat = 12 :=
  hphN_ofPlaceOK (atTables ret0_placeOK) ret0Imms

example := hphT1_ofPlaceOK (atTables ret0_placeOK) ret0Imms
example := hphL1_ofPlaceOK (atTables ret0_placeOK) ret0Imms
example := hphU0_ofPlaceOK (atTables ret0_placeOK) ret0Imms
example := hphU1_ofPlaceOK (atTables ret0_placeOK) ret0Imms
example := hphN1_ofPlaceOK (atTables ret0_placeOK) ret0Imms
example := hphS0_ofPlaceOK (atTables ret0_placeOK) ret0Imms
example := hphS1_ofPlaceOK (atTables ret0_placeOK) ret0Imms

/-- The bits `hownT_of_ph`, `hownL_of_ph` and `hownN_of_ph` read. -/
example : ph ret0P (Spike.Lib.X64.Flow.Ret0.AllocTcb.rmwPc ret0P.lab).toBitVec.toNat % 2 = 1 ∧
    ph ret0P (Spike.Lib.X64.Flow.Ret0.StackTake.swpPc ret0P.lab).toBitVec.toNat / 2 % 2 = 0 ∧
    ph ret0P (Spike.Lib.X64.Flow.Ret0.StackTake.nextPc ret0P.lab).toBitVec.toNat / 4 % 2 = 1 := by
  rw [hphT_ofPlaceOK (atTables ret0_placeOK) ret0Imms, hphL_ofPlaceOK (atTables ret0_placeOK) ret0Imms,
    hphN_ofPlaceOK (atTables ret0_placeOK) ret0Imms]
  decide

end Spike.Lib.X64.PhRec.PinsTest
