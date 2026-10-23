/-
**The start's segment at `ret0`'s placement check** (`Spike/Lib/LowerX64/StartSeg.lean`):
`x64_start_segW` specialises to `ret0_placeOK`'s layout; its region is the
hand `_start` call's callee region (`entryC`, whose segment `entry_segW`
takes as its continuation); the switch region's depth `swL` fits the first
stack at the largest frame `x64_start_segW` admits (`4096`), and would not
at a frame of a whole stack; `ec_facts` gives that region's premises at any
admissible entry state.
-/
import Spike.Lib.LowerX64.StartSeg
import Spike.Test.X64PhRec

namespace Spike.Test.LowerX64StartSeg

open Scc.Cert.PlaceOK.X64 (atTables)

open Spike.Lib Spike.Lib.LowerX64
open Spike.Lib.X64.Rt (entryR)

/-- `x64_start_segW` at `ret0`'s placement check. -/
example := @x64_start_segW _ _ _ (atTables Scc.Cert.PlaceOK.X64.Test.ret0_placeOK) SccCode.ret0Imms

/-- **Its region is the hand `_start` call's callee region** (`entryC`,
the region of `entry_segW`'s continuation `hS`). -/
example : (Spike.Lib.X64.Rt.entryR Scc.Sem.Entry.linux).callee (-8)
    (-296) 8 = Spike.Lib.X64.Flow.Ret0.Inst.entryC := rfl

/-- **`ec_facts` at `ret0P`**, at the Linux entry state and at the 64 KiB
witness entry state, for the first stack's switch range `rS0`: the region
premises of `scc_rt_start`'s segments at `EC E`. -/
example := ec_facts Spike.Lib.X64.Rt.ret0P
  (Spike.Lib.X64.Rt.RuntimeLayout.linux_ok_ofPlaceOK
    (atTables Scc.Cert.PlaceOK.X64.Test.ret0_placeOK) SccCode.ret0Imms)
  (Spike.Lib.X64.Rt.rS0_sub _)
example := ec_facts Spike.Lib.X64.Rt.ret0P
  (Spike.Lib.X64.Rt.RuntimeLayout.witness_ok_ofPlaceOK
    (atTables Scc.Cert.PlaceOK.X64.Test.ret0_placeOK) SccCode.ret0Imms)
  (Spike.Lib.X64.Rt.rS0_sub _)

/-- **Oracle**: `EC E`'s bounds are exactly `scc_rt_start`'s frame needs. -/
example : ((entryR Scc.Sem.Entry.linux).callee (-8) (-296) 8).lo = -296 ∧
    ((entryR Scc.Sem.Entry.linux).callee (-8) (-296) 8).hi = 8 := ⟨rfl, rfl⟩

/-- **Oracle**: at the largest admitted frame the switch region is inside
the first stack (`swL_ok`), with room for `startU_segW`'s depth. -/
example : swL 4096 = 4200 ∧ swL 4096 ≤ 16384 ∧
    8 + 8 + Spike.Lib.X64.Rt.bareMC.Z.toInt + 8 + ((4096 : Nat) + 48 : Int) ≤ swL 4096 :=
  ⟨rfl, (swL_ok (by decide) (by decide)).2.2.2.1, (swL_ok (by decide) (by decide)).1⟩

/-- **Negative**: a frame of a whole stack does not fit. -/
example : ¬ (swL 16384 ≤ 16384) := by decide

end Spike.Test.LowerX64StartSeg
