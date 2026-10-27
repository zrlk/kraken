/-
**`CalleePre2`'s region and return-address facts at `scc_rt_main`'s calls**
(x86-64; the twin of `Spike/Lib/LowerA64/CalleeRgn2.lean`): at the setup
call's and `main`'s call sites of `h0_ofPlaceOK_setupFN`
(`setupCallWS_ofFnSpec` / `mainCallWSF_ofHeld`'s `hpre`), the callee's
region is `R.callee (-8 - Z - 8 - 0) (-D) 8`; its `OK` and the frame
condition's stability are `hpre`'s own hypotheses, so only `hlo` and `hhi`
are left, from the callee's frame and return slot inside the interface's
depth `D` (`calleeRgn`). The return address of the setup call is
`fnCode2Of`'s phase anchor `raL` itself (`raOk_setup`).

- `calleeRgn`: `hlo` and `hhi` of `CalleePre2` at `R.callee k (-D) 8`
  from `8 + size ≤ D`;
- `raOk_setup`: the setup call's return address `(setupMC sw).sp0` has
  the phase of `raL` (`fnCode2Of`'s `RaOk`): the same label.

`main`'s call returns to `(setupMC sw).sp1`, whose phase the checked table
`mainPhTabS` does not relate to `sp0`'s (`call fn`'s target only is
checked); `RaOk` there is from the runtime's code check instead
(`raOk_main`, `Spike/Lib/LowerX64/RaMain2.lean`).
-/
import Spike.Lib.Region
import Spike.Lib.X64PhRec
import Spike.Lib.Rt.X64CodeInSetup
import Spike.Lib.LowerX64.PhCheck

namespace Spike.Lib.LowerX64

open Spike.Lib

/-- **The callee's region bounds** (`CalleePre2.hlo`, `.hhi` at
`R.callee k (-D) 8`): the frame `sz` and the return slot inside the depth
`D`. -/
theorem calleeRgn {R : Region} {k D sz : Int} (hD : 8 + sz ≤ D) :
    (R.callee k (-D) 8).lo ≤ -8 - sz ∧ 8 ≤ (R.callee k (-D) 8).hi :=
  ⟨by show -D ≤ -8 - sz; omega, Int.le_refl 8⟩

open Spike.Lib.X64.Rt (RuntimeLayout setupMC) in
/-- **The setup call's return address has the phase anchor's phase**
(`fnCode2Of`'s `RaOk` at `(setupMC sw).sp0`): `setupMC`'s `sp0` is `raL`. -/
theorem raOk_setup (Ly : RuntimeLayout) (sw : Nat) :
    Spike.Lib.X64.PhRec.ph Ly (Int64.ofBitVec (Ly.lab (setupMC sw).sp0).toBitVec).toBitVec.toNat =
      Spike.Lib.X64.PhRec.ph Ly (Ly.lab raL).toBitVec.toNat := by
  simp only [Int64.ofBitVec_toBitVec]
  rfl

/-- info: 'Spike.Lib.LowerX64.calleeRgn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms calleeRgn

/-- info: 'Spike.Lib.LowerX64.raOk_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms raOk_setup

end Spike.Lib.LowerX64
