/-
**The phase structures at `ret0`'s placed record** (`Spike/Lib/Rt/A64RtPhRec.lean`):
`ret0`'s program passes the table at the record of `ret0_placeOK`, and the
projections give each function's phase structure there.
-/
import Spike.Lib.Rt.A64RtPhRec
import Spike.Test.A64RtPhTab
import Spike.Test.A64Ret0PlaceOK

namespace Spike.Lib.A64.Rt.PhRecOfTest

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (rtPhOk)
open Spike.Lib.A64.Rt (RuntimeLayout rtPhTab)
open Spike.Lib.A64.Rt.PhRecOf
open Scc.Cert.PlaceOK.A64.Test (ret0_placeOK)
open SccCode (ret0Imms)

/-- `ret0`'s placed record. -/
abbrev ret0P : RuntimeLayout := RuntimeLayout.ofPlaceOK (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms

/-- `ret0`'s program passes the table at its placed record. -/
theorem ret0P_rtPhOk : rtPhOk ret0P.Λ.code.lo ret0P.prog ret0P.Λ (rtPhTab none) = true :=
  Spike.Lib.A64.Rt.PhTabTest.ret0_rtPhOk_none

/-- The switch's facts at `ret0`. -/
example := swPh_ofPlaceOK (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms ret0P_rtPhOk

/-- `scc_rt_thread_init`'s facts at `ret0`. -/
example := tiPh_ofPlaceOK (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms ret0P_rtPhOk

/-- `scc_rt_alloc_tcb`'s facts at `ret0`. -/
example := tcbPh_ofPlaceOK (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms ret0P_rtPhOk

/-- `scc_rt_stack_take`'s facts at `ret0`. -/
example := takePh_ofPlaceOK (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms ret0P_rtPhOk

/-- The record's TCB words are off its counters at `ret0`. -/
example : Spike.Lib.A64.PhRec.TcbSep ret0P := tcbSep (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms

/-- The `.rodata` range is off the stack pool at `ret0`. -/
example : ret0P.Λ.rodata.Disjoint ret0P.Λ.stackPool := rodata_stackPool_disjoint_ofPlaceOK
    (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms

end Spike.Lib.A64.Rt.PhRecOfTest
