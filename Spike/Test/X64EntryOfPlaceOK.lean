/-
**`_start` at `ret0.x` from `placeOK`** (`Spike/Lib/Rt/X64EntryOfPlaceOK.lean`):
`_start`'s obligations (`entryW_ofPlaceOK`) and segment
(`entry_segW_ofPlaceOK`) at the record of `ret0.x`'s placed output, with no
premise but the source's facts and the callee's segment; and `_start`'s
facts `entryW_ofPlaceOK` reads from A6 at `ret0`: phase `13`, not the
take's.
-/
import Spike.Lib.Rt.X64EntryOfPlaceOK
import Spike.Test.X64Ret0PlaceOK

namespace Spike.Lib.X64.Rt.EntryOfPlaceOKTest

open Scc.Cert.PlaceOK.X64 (atTables)

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64 Spike.Lib.X64Consumer
open Spike.Lib.X64.Rt

/-- The Linux entry state is admissible at `ret0`'s record. -/
theorem ret0_ok : Scc.Sem.Entry.linux.Ok
    Spike.Lib.X64.Rt.ret0P.Λ :=
  RuntimeLayout.linux_ok_ofPlaceOK (atTables Scc.Cert.PlaceOK.X64.Test.ret0_placeOK) SccCode.ret0Imms

/-- **`_start`'s obligations at `ret0.x`'s record**, in the entry stack. -/
example {rS : Scc.Sem.Range} {lbl : Lbl} {Dt : State → Prop} {c0 : Ctl}
    (hC0 : CFacts Spike.Lib.X64.Rt.ret0P.Λ lbl c0) :=
  entryW_ofPlaceOK (atTables Scc.Cert.PlaceOK.X64.Test.ret0_placeOK) SccCode.ret0Imms (rS := rS) (Dt := Dt)
    (F := fun _ => True) (entryR_ok ret0_ok) (by decide) (by decide) hC0

/-- **`_start`'s segment at `ret0.x`'s record.** -/
example {p : CoreTerm.Prog} {lbl : Lbl} {ms : MemSide isa} {Dt : State → Prop} {c0 : Ctl}
    (hC0 : CFacts Spike.Lib.X64.Rt.ret0P.Λ lbl c0) :=
  entry_segW_ofPlaceOK (atTables Scc.Cert.PlaceOK.X64.Test.ret0_placeOK) SccCode.ret0Imms (p := p) (ms := ms)
    (Dt := Dt)
    (Q := fun _ _ => False) ret0_ok hC0

/-- `_start`'s pcs have phase `13` at `ret0`, and `13` is not the take's
phase (`Tk`), the facts `entryW_ofPlaceOK` reads. -/
example : Scc.Cert.Rt.X64.rtPhOk SccCode.ret0Λ.code.lo SccCode.ret0Cells SccCode.ret0Λ
    [.ph "_start" 0 13, .ph "_start" 2 13, .ph "_start" 6 13] = true := by decide +kernel
example : ¬ (13 / 8 % 2 = 0) := by decide

end Spike.Lib.X64.Rt.EntryOfPlaceOKTest
