import Spike.Lib.Rt.A64EntryOfPlaceOK
import Spike.Test.A64Ret0PlaceOK

/-!
# `_start` at `ret0`'s placed output (AArch64)

`entryW_ofPlaceOK` at the record of `ret0`'s placed output: `_start`'s block
inside the run's facts with no premise but the source's facts; and the
table facts it reads at `ret0`: the block's check and phase `13`, not the
take's.
-/

namespace Spike.Lib.A64.Rt.Test

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64Consumer (CFacts Lbl)

/-- The Linux entry state is admissible at `ret0`'s record. -/
theorem ret0_ok : Scc.Sem.Entry.linux.Ok
    (RuntimeLayout.ofPlaceOK
        (Scc.Cert.PlaceOK.A64.atTables Scc.Cert.PlaceOK.A64.Test.ret0_placeOK) SccCode.ret0Imms).Λ :=
  RuntimeLayout.linux_ok_ofPlaceOK
      (Scc.Cert.PlaceOK.A64.atTables Scc.Cert.PlaceOK.A64.Test.ret0_placeOK) SccCode.ret0Imms

/-- **`_start`'s block at `ret0`'s record.** -/
example {rS : Scc.Sem.Range} {lbl : Lbl} {Dt : State → Prop} {c0 : Ctl}
    (hC0 : CFacts (RuntimeLayout.ofPlaceOK
        (Scc.Cert.PlaceOK.A64.atTables Scc.Cert.PlaceOK.A64.Test.ret0_placeOK) SccCode.ret0Imms).Λ lbl c0) :=
  entryW_ofPlaceOK (Scc.Cert.PlaceOK.A64.atTables Scc.Cert.PlaceOK.A64.Test.ret0_placeOK) SccCode.ret0Imms (rS := rS)
      (Dt := Dt)
    (F := fun _ => True) (entryR_ok ret0_ok) (entryR_al ret0_ok) (by decide) (by decide) hC0

/-- The facts `entryW_ofPlaceOK` reads, at `ret0`. -/
example : Scc.Cert.Rt.A64.rtPhOk SccCode.ret0Λ.code.lo SccCode.ret0Prog SccCode.ret0Λ
    [.blk "_start" 0 Code.Start.entryB none none, .ph "_start" 0 13] = true := by decide +kernel
example : ¬ (13 / 8 % 2 = 0) := by decide

end Spike.Lib.A64.Rt.Test
