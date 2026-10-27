/-
**`CalleePre2`'s region and return-address facts at `scc_rt_main`'s calls**
(AArch64): at the setup call's and `main`'s call sites of
`h0_ofPlaceOK_setupFN` (`setupCallWS_ofFnSpec` / `mainCallWSF_ofHeld`'s
`hpre`), the callee's region is `R.callee (-Z) (-D) 0`; its `OK`, its
base's alignment and the frame condition's stability are `hpre`'s own
hypotheses, so only `hlo` and `hhi` are left, from the callee's frame
inside the interface's depth `D` (`calleeRgn`). The return address of the
setup call is `fnCode2Of`'s phase anchor `bareMC.e0 + 4` itself
(`raOk_setup`).

- `calleeRgn`: `hlo` and `hhi` of `CalleePre2` at `R.callee k (-D) 0`
  from `frame ≤ D`;
- `raOk_setup`: the setup call's return address `(setupMC sw).e0 + 4` has
  the phase of `bareMC.e0 + 4` (`fnCode2Of`'s `RaOk`): the same label.

`main`'s call returns to `(setupMC sw).sp1`, whose phase the checked table
`mainPhTabS` does not relate to `sp0`'s (`bl fn`'s target only is checked);
`RaOk` there is from the runtime's code check instead (`raOk_main`,
`Spike/Lib/LowerA64/RaMain2.lean`).
-/
import Spike.Lib.Region
import Spike.Lib.A64PhRec
import Spike.Lib.Rt.A64CodeInSetup

namespace Spike.Lib.LowerA64

open Spike.Lib

/-- **The callee's region bounds** (`CalleePre2.hlo`, `.hhi` at
`R.callee k (-D) 0`): the frame `fr` inside the depth `D`. -/
theorem calleeRgn {R : Region} {k D fr : Int} (hD : fr ≤ D) :
    (R.callee k (-D) 0).lo ≤ -fr ∧ 0 ≤ (R.callee k (-D) 0).hi :=
  ⟨by show -D ≤ -fr; omega, Int.le_refl 0⟩

open Spike.Lib.A64.Rt (RuntimeLayout setupMC bareMC) in
/-- **The setup call's return address has the phase anchor's phase**
(`fnCode2Of`'s `RaOk` at `(setupMC sw).e0 + 4`): `setupMC`'s and `bareMC`'s
`e0` are the same label. -/
theorem raOk_setup (Ly : RuntimeLayout) (sw : Nat) :
    Spike.Lib.A64.PhRec.ph Ly (Int64.ofBitVec (Ly.lab (setupMC sw).e0 + 4).toBitVec).toBitVec.toNat =
      Spike.Lib.A64.PhRec.ph Ly (Int64.ofBitVec (Ly.lab bareMC.e0 + 4).toBitVec).toBitVec.toNat :=
  rfl

/-- info: 'Spike.Lib.LowerA64.calleeRgn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms calleeRgn

/-- info: 'Spike.Lib.LowerA64.raOk_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms raOk_setup

end Spike.Lib.LowerA64
