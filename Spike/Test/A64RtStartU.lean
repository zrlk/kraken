/-
**`scc_rt_start`'s obligations at `ret0`'s placed record**
(`Spike/Lib/Rt/A64RtStartU.lean`): the generic lemma applies at the record of
`ret0_placeOK`; a wrong phase row of `scc_rt_start` fails the table.
-/
import Spike.Lib.Rt.A64RtStartU
import Spike.Test.A64RtPhRec

namespace Spike.Lib.A64.Rt.StartUTest

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (rtPhOk)
open Spike.Lib.A64.Rt (startAllUW_gen startPhTab)
open Spike.Lib.A64.Rt.PhRecOfTest (ret0P_rtPhOk)
open Scc.Cert.PlaceOK.A64.Test (ret0_placeOK)
open SccCode (ret0Imms)
open SccCode (ret0Λ ret0Prog)

/-- `scc_rt_start`'s obligations at `ret0`'s placed record. -/
example := @startAllUW_gen _ _ _ (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms ret0P_rtPhOk

/-- `.sp2` is in phase `12`, not `13`: the wrong row fails. -/
example : rtPhOk ret0Λ.code.lo ret0Prog ret0Λ (startPhTab ++ [.ph Code.Start.sp2L 0 13]) = false := by
  decide +kernel

/-- The rows themselves pass. -/
example : rtPhOk ret0Λ.code.lo ret0Prog ret0Λ startPhTab = true := by
  decide +kernel

end Spike.Lib.A64.Rt.StartUTest
