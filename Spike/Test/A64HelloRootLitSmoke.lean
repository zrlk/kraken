import Spike.Lib.A64HelloRootLit

/-!
# hello's root at the static link `helloΛ`: a smoke check of `RootLit`'s layout premises

`RootLit.hello_root_lit` is generic in the layout `Λ0`; its binding instance is the linked executable's layout
(row hello-elf). This module only checks that the layout premises are satisfiable at the static link
`SccCode.helloΛ` (code base `0x400000`), as `WakeFinalCAO`'s sanity check does for wake: `PlaceW` (A1, A2, A4,
A6, A8), `hstat`, `NtZ` and A13's data part, each by `decide +kernel` (or `rfl`). `hlo` fails there
(`hlo_helloΛ_false`): it holds only at a layout whose `.text` is at `A64HelloPh.lo = 0x210550`.
-/

namespace Spike.Test.A64HelloRootLitSmoke

open Spike.Lib.A64.HelloPh.RootLit (pcfgH oH)
open SccCode (helloΛ)

/-- **A1 at `helloΛ`**. -/
theorem a1_H : Scc.Cert.PlaceOK.A64.a1 oH ⟨helloΛ⟩ = true := by decide +kernel

/-- **A2 at `helloΛ`**. -/
theorem a2_H : Scc.Cert.PlaceOK.A64.a2 oH ⟨helloΛ⟩ = true := by decide +kernel

/-- **A4 at `pcfgH`**. -/
theorem a4_H : Scc.Cert.PlaceOK.A64.a4 pcfgH oH ⟨helloΛ⟩ = true := by decide +kernel

/-- **A6 at `helloΛ`**. -/
theorem a6_H : Scc.Cert.PlaceOK.A64.a6 oH ⟨helloΛ⟩ = true := by decide +kernel

/-- **A8 at `helloΛ`**. -/
theorem a8_H : Scc.Cert.PlaceOK.A64.a8 oH ⟨helloΛ⟩ = true := by decide +kernel

/-- **`PlaceW` at the static link** (`hello_root_lit`'s `hp` at `Λ0 := helloΛ`). -/
theorem placeW_H : Spike.Lib.PlaceW pcfgH helloΛ oH := ⟨a1_H, a2_H, a4_H, a6_H, a8_H⟩

/-- `hstat` at the static link. -/
theorem hstat_H : helloΛ.static = fun _ => none := rfl

/-- `hnz` at the static link: `scc_rt_nthreads` starts at `0`. -/
theorem hnz_H : Spike.Lib.WakeOInit.NtZ helloΛ oH = true := by decide +kernel

/-- `hA13` at the static link, at the root's immediates `ImmsH.iH helloΛ`. -/
theorem hA13_H :
    Scc.Cert.Spawn.A64.a13data (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW placeW_H
      (Spike.Lib.A64.HelloPh.C0S.immsH helloΛ SccCode.helloImms)).Λ oH.prog oH.secs = true := by
  decide +kernel

/-- **`hlo` fails at the static link**: its code is at `0x400000`, not at hello's phase base `0x210550`. -/
theorem hlo_helloΛ_false : helloΛ.code.lo ≠ Spike.Lib.A64.WakePh.lo := by decide +kernel

end Spike.Test.A64HelloRootLitSmoke

/-- info: 'Spike.Test.A64HelloRootLitSmoke.placeW_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.A64HelloRootLitSmoke.placeW_H

/-- info: 'Spike.Test.A64HelloRootLitSmoke.hA13_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.A64HelloRootLitSmoke.hA13_H
