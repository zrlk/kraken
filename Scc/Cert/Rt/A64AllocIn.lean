import Scc.Cert.Rt.LayoutA64
import Spike.Lib.A64Alloc

/-!
# `scc_rt_alloc` in an emitted AArch64 program

`allocIn prog` checks the allocator's code (`Spike/Lib/A64Alloc.lean`'s
blocks and single instructions) at its labels and offsets in a directive
list, and the prologue's fall-through to `.0_entry` (`labelGap`). It is the
code premise of `seg_alloc_ofW` (`Spike/Lib/A64Hello1Rodata.lean`). The
text is the runtime's, the same in every program, so A7 checks it with the
rest of the runtime's fixed code (`Scc/Cert/Rt/A64RtIn.lean`) and
`PlaceOK.A64.allocIn_of_placeOKAt` gives it from the placement check.

The labels are scc's (`.L2_scc_rt_alloc.*`: the runtime's functions come
first in every program, in a fixed order).
-/

namespace Spike.Lib.A64.Flow

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (blockAt labelGap)
open Spike.Lib.A64.Alloc

/-- **The code of `scc_rt_alloc` in `prog`**: its blocks and single
instructions at their labels and offsets, and the prologue's fall-through. -/
def allocIn (prog : List Directive) : Bool :=
  blockAt prog "scc_rt_alloc" 0 b0 &&
  blockAt prog ".L2_scc_rt_alloc.0_entry" 0 b1 &&
  blockAt prog ".L2_scc_rt_alloc.0_entry" 4 b2 &&
  blockAt prog ".L2_scc_rt_alloc.1_cnt" 0 [iAdrpC.toDir] &&
  blockAt prog ".L2_scc_rt_alloc.1_cnt" 1 [iAddC.toDir] &&
  blockAt prog ".L2_scc_rt_alloc.1_cnt" 2 b3 &&
  blockAt prog ".L2_scc_rt_alloc.1_cnt" 5 [iRmw] &&
  blockAt prog ".L2_scc_rt_alloc.1_cnt" 6 b4 &&
  blockAt prog ".L2_scc_rt_alloc.1_cnt" 15 b5 &&
  blockAt prog ".L2_scc_rt_alloc.2_slow" 0 b6 &&
  blockAt prog ".L2_scc_rt_alloc.2_slow" 4 b7 &&
  blockAt prog ".L2_scc_rt_alloc.4_full" 0 b9 &&
  blockAt prog ".L2_scc_rt_alloc.5_ok" 0 b11 &&
  blockAt prog ".L2_scc_rt_alloc.5_ok" 8 [iAdrpH.toDir] &&
  blockAt prog ".L2_scc_rt_alloc.5_ok" 9 [iAddH.toDir] &&
  blockAt prog ".L2_scc_rt_alloc.5_ok" 10 b12 &&
  blockAt prog ".L2_scc_rt_alloc.5_ok" 41 [iHdr] &&
  blockAt prog ".L2_scc_rt_alloc.5_ok" 42 b13 &&
  blockAt prog ".L2_scc_rt_alloc.5_ok" 54 [iRet.toDir] &&
  labelGap prog "scc_rt_alloc" ".L2_scc_rt_alloc.0_entry" 7

end Spike.Lib.A64.Flow
