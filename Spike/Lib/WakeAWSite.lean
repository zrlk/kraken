/-
**The take site's address `aW` is the layout's `scc_rt_take_site`**
(AArch64; `WakeOSide.aW`, `h1`'s outside move): `WakeH1Inv.K1W`'s take at
`WakeOSide.aW hp i E` is `wcMidW_wcG`'s at `(Ly).lab siteL`, given the
layout's marks put the take site at `siteL` (`hsite`, `PlaceW.site_ofPlaceW`).

- `aW_site`: `aW hp i E = (Ly).lab siteL` (`WakeOSide.ha_W`,
  `AbOffW.marks_target`).

No absolute address appears in this file.
-/
import Spike.Lib.WakeOSide
import Spike.Lib.A64WakeAbOffW

namespace Spike.Lib.WakeOSide

open Scc.Sem Scc.Sem.A64
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.WakeLabels (wakeProg)

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ0 o)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

/-- **The take site's address is the layout's `scc_rt_take_site`**: both are
the take mark of the layout (`ha_W`, `marks_target`, `hsite`). -/
theorem aW_site (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg)
    (hpL : textProgram SccCertificate.asm = .ok (Ly).prog)
    (hsite : (Spike.Lib.A64.PhRec.μ (Ly)).site .take =
      some ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) (E : Entry) :
    aW hp i E = (Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL := by
  have h := ha_W hp i hpa hwp E
  rw [Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpL, hsite] at h
  exact Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq (Option.some.inj h).symm)

end Place

end Spike.Lib.WakeOSide

/-- info: 'Spike.Lib.WakeOSide.aW_site' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeOSide.aW_site
