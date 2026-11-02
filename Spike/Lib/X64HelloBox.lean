/-
**hello.w's box landing on x86-64: main's thread pointer as a number** (the twin of `Spike/Lib/A64HelloBox.lean`).

- `tv_toNat`: main's thread pointer, the first TCB `pinA + 8`, as a number at the layout `ofPlaceWX h (immsH Λ0 i0)`.

**Where this differs from AArch64** (forced by the x86-64 shape): the layout is `RuntimeLayout.ofPlaceWX` at the
x86-64 placement `PlaceWX` and immediates `X64.HelloImms.immsH` (AArch64: `ofPlaceW`, `A64.HelloPh.C0S.immsH`); the
segments' pinned base is `X64.Flow.Ret0.pinA`. Only `tv_toNat` is live in the hello proof: A64's `BoxH`, `box_regH`
and `box_landingH` are dead and not twinned, and so this module imports none of A64's `LandR1` closure.
-/
import Spike.Lib.X64PlaceWRt
import Spike.Lib.Rt.X64StartArith
import Spike.Lib.X64HelloImms

namespace Spike.Lib.X64.HelloPh.Box

open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Flow.Ret0 (pinA)
open Spike.Lib.PlaceWX

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw (Spike.Lib.X64.HelloImms.immsH Λ0 i0)

/-- main's thread pointer as a number: the first TCB, `pinA + 8`. -/
theorem tv_toNat : (pinA (Ly).lab + 0#64 + 8#64).toNat = (Ly).pinA.toNat + 8 := by
  have hpin : (Ly).pinA.toNat < 2 ^ 32 := (Ly).words_small _ (Ly).pin_mem
  rw [Spike.Lib.X64.Rt.pinA_lab0, BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

end Spike.Lib.X64.HelloPh.Box

/-- info: 'Spike.Lib.X64.HelloPh.Box.tv_toNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Box.tv_toNat
