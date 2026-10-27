import Spike.Lib.LowerX64.StartSegN

/-!
The start segment with the user function's depth a parameter
(`Spike/Lib/LowerX64/StartSegN.lean`): its axioms, and `needD` /
`MainNeedOk` at the rows of `main` in the stack need tables of `ret0.w`,
`call1.w` and `chain5.w` (label, frame below the entry stack pointer,
need; `main`'s frames 16, 48 and 48 bytes), as `scc --arch x64` lays them
out.
-/

namespace Spike.Lib.LowerX64.TestStartSegN

open Spike.Lib.LowerX64

/--
info: 'Spike.Lib.LowerX64.x64_start_segW1D' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms x64_start_segW1D

/--
info: 'Spike.Lib.LowerX64.x64_start_segW1_ofD' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms x64_start_segW1_ofD

/-- A frame of `n` bytes of the function `wc_main`. -/
def frm (n : Nat) : Scc.Emit.X64.Frame := { fn := "wc_main", slots := [], size := n }

-- `ret0`: no calls, the need is the frame (`fr.size + 8`), the depth the frame's.
#guard needD (frm 16) 24 == 64
#guard MainNeedOk [("scc_rt_main", 40, 72), ("wc_main", 24, 24)] "wc_main" (frm 16)
-- `call1`: `main` calls `pick` (need 24): `48 + 8 + 8 + 24 = 88`.
#guard needD (frm 48) 88 == 128
#guard MainNeedOk [("scc_rt_main", 40, 136), ("wc_pick", 24, 24), ("wc_main", 56, 88)] "wc_main" (frm 48)
-- `chain5`: the chain `main → f4 → … → f0`, need 536.
#guard needD (frm 48) 536 == 576
#guard MainNeedOk [("scc_rt_main", 40, 584), ("wc_f0", 24, 24), ("wc_f1", 104, 136), ("wc_f2", 104, 248),
  ("wc_f3", 104, 360), ("wc_f4", 104, 472), ("wc_main", 56, 536)] "wc_main" (frm 48)
-- Fail-closed: no row, or a need past the first stack.
#guard !MainNeedOk [("scc_rt_main", 40, 72)] "wc_main" (frm 16)
#guard !MainNeedOk [("wc_main", 56, 16300)] "wc_main" (frm 48)

end Spike.Lib.LowerX64.TestStartSegN
