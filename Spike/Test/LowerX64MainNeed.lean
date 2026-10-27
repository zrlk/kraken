import Spike.Lib.LowerX64.MainNeed

/-!
`main`'s stack need bound from the placement check
(`Spike/Lib/LowerX64/MainNeed.lean`): its axioms, and the configuration
side `CfgNeedOk` at the canonical configuration and at the certificates'
(`needBudget := 12288`, `entries := ["scc_rt_main"]`).
-/

namespace Spike.Lib.LowerX64.TestMainNeed

open Spike.Lib.LowerX64

/--
info: 'Spike.Lib.LowerX64.mainNeedOk_of_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mainNeedOk_of_placeOKAt

#guard CfgNeedOk Scc.Cert.PlaceOK.Config.canonical
#guard CfgNeedOk { Scc.Cert.PlaceOK.Config.canonical with needBudget := 12288, entries := ["scc_rt_main"] }
-- The largest budget that fits, and fail-closed past it or without `scc_rt_main` an entry.
#guard CfgNeedOk { needBudget := 12288 }
#guard !CfgNeedOk { needBudget := 12289 }
#guard !CfgNeedOk { entries := [] }

-- `mainNeedOk_of_rows` at `call1`'s rows: `scc_rt_main` (frame 40, need 136) calls `wc_main` (48 + 8, 88).
example : MainNeedOk [("scc_rt_main", 40, 136), ("wc_pick", 24, 24), ("wc_main", 56, 88)] "wc_main"
    { fn := "wc_main", slots := [], size := 48 } := by decide

end Spike.Lib.LowerX64.TestMainNeed
