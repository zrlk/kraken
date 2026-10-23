import Spike.Lib.LowerX64.MainPh
import Spike.Test.LowerX64MainSeg
import Spike.Test.LowerX64PhCheck

/-!
# `mainPh_ofPlaceOK` at `ret0.w` (x86-64)

The twin of `Spike/Test/LowerA64MainPh.lean`: the generic statement
(`Spike/Lib/LowerX64/MainPh.lean`) instantiated at `ret0.w`, at the
lowering's immediates, every hypothesis discharged by the program's own
facts (the acceptance, the pipeline's success, `ret0_placeOK`), so the phase
facts are satisfiable. Negatives: the local overflow block's phase check
fails with no pc allowed or with `scc_rt_abort` in another phase than the
block, so the conjunct carries content.
-/

namespace Spike.Test.LowerX64MainPh

open Scc.Cert.PlaceOK.X64 (atTables)

open Spike.Lib.LowerX64 Spike.Test.LowerX64MainSeg Spike.Test.LowerX64Ret0Oracle
open Spike.Lib.X64.Flow.Ret0.Inst (okPc ph)
open Spike.Test.LowerX64PhCheck (labA)

/-- **`mainPh_ofPlaceOK` at `ret0.w`**: `main`'s code and phase facts. -/
example := mainPh_ofPlaceOK (cfg := { arch := .x64 }) main0_accepted (lowerAll?_ok ret0_lowerAll?_ok)
  (labelOffs := SccCode.ret0Asm.labelOffs) (by rw [main0_src]; exact (atTables Spike.Test.X64Ret0PlaceOKE.ret0_placeOK))
  (Spike.Lib.LowerNode.immsOf main0)

/-- `scc_rt_main`'s return label is the one A9's phase part reads. -/
example : Spike.Lib.X64.Rt.bareMC.sp0 = raL := bareMC_sp0

/- The local overflow block passes at the hand tables. -/
#guard Spike.Lib.X64Consumer.blkPh okPc ph (fun _ => false) labA (labA ".Lwc_main.ovf" + Int64.ofNat 0) 0
  Spike.Lib.X64.Abort.Local.lb

/- **Negative**: no pc allowed: fails. -/
#guard !Spike.Lib.X64Consumer.blkPh (fun _ => false) ph (fun _ => false) labA (labA ".Lwc_main.ovf" + Int64.ofNat 0)
  0 Spike.Lib.X64.Abort.Local.lb

/- **Negative**: `scc_rt_abort` in another phase than the block: fails. -/
#guard !Spike.Lib.X64Consumer.blkPh okPc
  (fun pc => if pc == (labA "scc_rt_abort").toBitVec.toNat then ph pc + 1 else ph pc) (fun _ => false) labA
  (labA ".Lwc_main.ovf" + Int64.ofNat 0) 0 Spike.Lib.X64.Abort.Local.lb

/--
info: 'Spike.Lib.LowerX64.mainPh_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mainPh_ofPlaceOK

end Spike.Test.LowerX64MainPh
