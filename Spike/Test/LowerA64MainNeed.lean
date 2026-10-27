import Spike.Lib.LowerA64.MainNeed

/-!
`main`'s stack need and callee room from the placement check (AArch64,
`Spike/Lib/LowerA64/MainNeed.lean`): its axioms, `needDA` / `MainNeedOkA`
at `main`'s rows of `ret0.w` and `call1.w` (label, frame, need), and the
configuration side `CfgNeedOkA`.
-/

namespace Spike.Lib.LowerA64.TestMainNeed

open Spike.Lib.LowerA64

/--
info: 'Spike.Lib.LowerA64.mainRoom_of_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mainRoom_of_placeOKAt

-- `ret0`: `main`'s frame 32, no calls: the room is the frame and the `48`.
#guard needDA 32 == 80
#guard MainNeedOkA [("scc_rt_main", 48, 80), ("wc_main", 32, 32)] "wc_main"
-- `call1`: `main` (frame 64) calls `pick` (32): need 96, room 144.
#guard needDA 96 == 144
#guard MainNeedOkA [("scc_rt_main", 48, 144), ("wc_pick", 32, 32), ("wc_main", 64, 96)] "wc_main"
-- Rounded up to 8.
#guard needDA 81 == 136
-- The largest need that fits, and fail-closed past it or without a row.
#guard MainNeedOkA [("wc_main", 48, 12240)] "wc_main"
#guard !MainNeedOkA [("wc_main", 48, 12241)] "wc_main"
#guard !MainNeedOkA [("scc_rt_main", 48, 80)] "wc_main"

#guard CfgNeedOkA Scc.Cert.PlaceOK.Config.canonical
#guard CfgNeedOkA { Scc.Cert.PlaceOK.Config.canonical with needBudget := 12288, entries := ["scc_rt_main"] }
#guard CfgNeedOkA { needBudget := 12288 }
#guard !CfgNeedOkA { needBudget := 12289 }
#guard !CfgNeedOkA { needBudget := 16288 }
#guard !CfgNeedOkA { entries := [] }

end Spike.Lib.LowerA64.TestMainNeed
