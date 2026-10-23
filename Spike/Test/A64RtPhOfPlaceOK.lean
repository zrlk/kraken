/-
**`rtNodesOk_of_placeOK` on `ret0.w`** (`Spike/Lib/Rt/A64RtPhOfPlaceOK.lean`):
the runtime rows of `ret0.w`'s placement data pass their phase checks from
`ret0_placeOK` alone, at the hand labels, phases and off-site pcs
(`Spike/Lib/A64Ret0I.lean`), each row's dead targets those off its entry's
phase (the hand oracle's `ret0Dead`, `Spike/Test/A64RtNodes.lean`).
-/
import Spike.Lib.Rt.A64RtPhOfPlaceOK
import Spike.Test.A64RtNodes
import Spike.Test.A64Ret0PhasesPlaceOK

namespace Spike.Lib.A64.Rt.Test

open Spike.Lib.A64.Rt Spike.Lib.A64.Flow.Ret0.Inst
open Scc.Cert.PlaceOK.A64.Test (ret0_placeOK ret0Place codeLo_canonical ret0_phOf ret0_okPcOf')

/-- The hand dead sets are those off each row's entry's phase. -/
theorem ret0Dead_eq : ret0Dead = offPh ph labT := rfl

/-- **`ret0.w`'s runtime rows pass their phase checks**, from `ret0_placeOK`. -/
theorem ret0_rtNodesOk_ofPlaceOK : RtNodesOk okPc ph ret0Dead labT ret0Ra ret0RtRows := by
  have h := rtNodesOk_of_placeOK (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0_labT (by decide +kernel) ret0Ra
      (gs := ret0RtRows)
    (fun g hg => (List.mem_filter.mp hg).1)
  simp only [codeLo_canonical] at h
  rw [ret0_phOf, ret0_okPcOf'] at h
  exact h

end Spike.Lib.A64.Rt.Test
