import Spike.Lib.LowerA64.MainPh
import Spike.Test.LowerA64MainSeg
import Spike.Test.LowerA64PhCheck

/-!
# `mainPh_ofPlaceOK` at `ret0.w` (AArch64)

The generic statement (`Spike/Lib/LowerA64/MainPh.lean`) instantiated at
`ret0.w`, at the lowering's immediates: every hypothesis discharged by the
program's own facts (the acceptance, the pipeline's success, `ret0_placeOK`),
so the phase facts are satisfiable. Negatives: the local overflow block's
phase check fails with no pc allowed or with `scc_rt_abort` in another phase
than the block, so the conjunct carries content.
-/

namespace Spike.Test.LowerA64MainPh

open Spike.Lib.LowerA64 Spike.Test.LowerInv Spike.Test.LowerA64MainSeg
open Spike.Lib.A64.Flow.Ret0.Inst (okPc ph)
open Spike.Test.LowerA64PhCheck (labA)

/-- **`mainPh_ofPlaceOK` at `ret0.w`**: `main`'s code and phase facts. -/
example := mainPh_ofPlaceOK (cfg := { arch := .arm }) main0_accepted (lowerAll?_ok ret0_lowerAll?_ok)
  (Scc.Cert.PlaceOK.A64.atTables Spike.Test.A64Ret0PlaceOKE.ret0_placeOK) (Spike.Lib.LowerNode.immsOf main0)

/-- The layout's labels at `ret0.w`'s placement are the code labels. -/
example := lab_ofPlaceOK
  (Scc.Cert.PlaceOK.A64.atTables Spike.Test.A64Ret0PlaceOKE.ret0_placeOK) (Spike.Lib.LowerNode.immsOf main0)

/- The local overflow block passes at the hand tables. -/
#guard Spike.Lib.A64Consumer.blkPh okPc ph (fun _ => false) labA (labA ".L18_wc_main.abort_overflow") 0
  Spike.Lib.A64.Abort.Local.lb

/- **Negative**: no pc allowed: fails. -/
#guard !Spike.Lib.A64Consumer.blkPh (fun _ => false) ph (fun _ => false) labA (labA ".L18_wc_main.abort_overflow")
  0 Spike.Lib.A64.Abort.Local.lb

/- **Negative**: `scc_rt_abort` in another phase than the block: fails. -/
#guard !Spike.Lib.A64Consumer.blkPh okPc
  (fun pc => if pc == (labA "scc_rt_abort").toBitVec.toNat then ph pc + 1 else ph pc) (fun _ => false) labA
  (labA ".L18_wc_main.abort_overflow") 0 Spike.Lib.A64.Abort.Local.lb

/--
info: 'Spike.Lib.LowerA64.mainPh_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mainPh_ofPlaceOK

end Spike.Test.LowerA64MainPh
