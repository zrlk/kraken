/-
**The take site's address `aW` is the layout's `scc_rt_take_site`**
(x86-64; `X64WakeOSide.aW`, `h1`'s outside move): `h1`'s take at
`X64WakeOSide.aW hp i E` is at `(Ly).lab siteL`.

- `aW_site`: `aW hp i E = (Ly).lab siteL` (`X64WakeOSide.ha_W`,
  `AbOffW.marks_target`, `PlaceWX.site_ofPlaceWX`).

x86-64 twin of `Spike/Lib/WakeAWSite.lean` (same name, namespace
`Spike.Lib.X64WakeOSide`).

**Unlike AArch64**: `aW_site` takes only `{asm} (hpa : cellsOf asm = some
o.prog)`; A64's `hwp`, `hpL` and `hsite` are not needed, the take mark at
`siteL` being `PlaceWX.site_ofPlaceWX` (A64: the premise `hsite`).

No absolute address appears in this file.
-/
import Spike.Lib.X64WakeOSide

namespace Spike.Lib.X64WakeOSide

open Scc.Sem Scc.Sem.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib (PlaceWX)

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceWX pcfg Λ0 o)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **The take site's address is the layout's `scc_rt_take_site`**: both are
the take mark of the layout (`ha_W`, `marks_target`, `site_ofPlaceWX`). -/
theorem aW_site {asm : Asm} (hpa : cellsOf asm = some o.prog) (E : Entry) :
    aW hp i E = (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL := by
  have h := ha_W hp i hpa E
  rw [Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpa, PlaceWX.site_ofPlaceWX hp i] at h
  exact Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq (Option.some.inj h).symm)

end Place

end Spike.Lib.X64WakeOSide

/-- info: 'Spike.Lib.X64WakeOSide.aW_site' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOSide.aW_site
