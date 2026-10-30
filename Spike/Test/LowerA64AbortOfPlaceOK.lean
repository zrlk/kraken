/-
**The overflow exit call's site premises at `ret0`'s placement check**
(`Spike/Lib/LowerA64/AbortOfPlaceOK.lean`): the generic discharges hold at
`ret0_placeOK`; the overflow exit call is the third of A6's resolved sites,
the hand address; the heap exit call is not at it, and a site list with a
repeated address is not distinct (so `sites7` carries content).
-/
import Spike.Lib.LowerA64.AbortOfPlaceOK
import Spike.Test.A64PhRec

namespace Spike.Test.LowerA64AbortOfPlaceOK

open Spike.Lib.LowerA64
open Scc.Cert.PlaceOK.A64.Test (ret0_placeOK)
open SccCode (ret0Λ ret0Prog ret0Imms)

/-- **Oracle**: the overflow exit call resolves at the third hand site. -/
example : Scc.Cert.Link.A64.codeOf ret0Λ.code.lo ret0Prog "scc_rt_abort_overflow_exit" = some 4198512 := by
  decide +kernel

/-- **`sites7` at `ret0`.** -/
example := sites7 (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK)

/-- The site premises at `ret0`'s placement check. -/
example := hprog_ofPlaceOK (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms
example := hrel_ofPlaceOK (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms
example := htk_ofPlaceOK (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms
example := hk_ofPlaceOK (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms
example {rS : Scc.Sem.Range} := hKex_ofPlaceOK (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms (rS := rS)
example := hms_ofPlaceOK (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms (rd := fun _ => True)
    (G := fun _ _ => True)
  (own := fun _ => []) (lbl := fun _ => none) (lsize := fun _ => 0)

/-- **Negative**: the heap exit call is not at the overflow exit call. -/
example : Scc.Cert.Link.A64.codeOf ret0Λ.code.lo ret0Prog "scc_rt_abort_heap_exit" ≠ some 4198512 := by
  decide +kernel

/-- **Negative**: a repeated site is not distinct. -/
example : ¬ [4196192, 4196248, 4198512, 4198512].Nodup := by decide

end Spike.Test.LowerA64AbortOfPlaceOK
