/-
**hello.w's handed stack fits the child stub** (AArch64): at the placed layout the child's
stack `r1W hp i` (`r1Of`, the second stack) lies in the stack pool (`StartPlaceLy.hsub1_W`, from A13's data part),
so its top is in the address space, 16-aligned, with at least the stub's 272 bytes (`StackB.childB_r1Of`):
`HelloWiI.hWiH_I`'s `htop`, `hal`, `hsz` at `r1c := r1W hp i`.

- `r1_fit_H`: the three facts at the instance.
-/
import Spike.Lib.A64HelloStackB
import Spike.Lib.A64WakeStartPlaceLy

namespace Spike.Lib.HelloR1Fit

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- (row 5j-misc-r1) **`hWiH_I`'s handed-stack facts at the instance**, from A13's data part. -/
theorem r1_fit_H
    (hA13 : Scc.Cert.Spawn.A64.a13data (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp i).Λ o.prog o.secs = true) :
    (Spike.Lib.WakeOSide.r1W hp i).lo + (Spike.Lib.WakeOSide.r1W hp i).size < 2 ^ 64 ∧
      ((Spike.Lib.WakeOSide.r1W hp i).lo + (Spike.Lib.WakeOSide.r1W hp i).size) % 16 = 0 ∧
      272 ≤ (Spike.Lib.WakeOSide.r1W hp i).size :=
  Spike.Lib.A64.HelloPh.StackB.childB_r1Of _ (Spike.Lib.A64.WakePh.StartPlaceLy.hsub1_W hp i hA13)

end Spike.Lib.HelloR1Fit

/-- info: 'Spike.Lib.HelloR1Fit.r1_fit_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloR1Fit.r1_fit_H
