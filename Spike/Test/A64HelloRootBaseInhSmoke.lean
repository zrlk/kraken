import Spike.Lib.A64HelloRootBaseInh

/-!
# hello's root base at a concrete layout: `RootBaseInh.LayoutE` is not vacuous

`LayoutE` (the linked executable's facts the root's bundles need) at a concrete layout without the executable:
`Λ1`, the listing's static link (`Scc.Cert.Link.link`) at the canonical bases but with the code at hello's phase
base `WakePh.lo = 0x210550`, where `RootLit`'s static link `helloΛ` fails `hlo`
(`A64HelloRootLitSmoke.hlo_helloΛ_false`). Every field by `decide +kernel` (or `rfl`); `premE` at `Λ1` is the
root's premise bundle there. The binding instance is the linked executable's layout `Λe` (row hello-elf).
-/

namespace Spike.Test.A64HelloRootBaseInhSmoke

open Spike.Lib.A64.HelloPh.RootLit (pcfgH oH)
open Spike.Lib.A64.HelloPh.RootBaseInh (LayoutE)
open Spike.Lib.A64.HelloPh.ImmsMe (iRdM)

/-- The canonical bases with the code at hello's phase base. -/
def B1 : Scc.Cert.Link.Bases := { Scc.Cert.Link.canonical with codeLo := 0x210550 }

/-- **The listing's static link with the code at `0x210550`.** -/
def Λ1 : Scc.Sem.Layout :=
  Scc.Cert.Link.link B1 SccCode.helloSecs (Scc.Cert.Link.A64.codeOf 0x210550 SccCode.helloProg)

/-- A1 at `Λ1`. -/
theorem a1_1 : Scc.Cert.PlaceOK.A64.a1 oH ⟨Λ1⟩ = true := by decide +kernel

/-- A2 at `Λ1`. -/
theorem a2_1 : Scc.Cert.PlaceOK.A64.a2 oH ⟨Λ1⟩ = true := by decide +kernel

/-- A4 at `Λ1`. -/
theorem a4_1 : Scc.Cert.PlaceOK.A64.a4 pcfgH oH ⟨Λ1⟩ = true := by decide +kernel

/-- A6 at `Λ1`. -/
theorem a6_1 : Scc.Cert.PlaceOK.A64.a6 oH ⟨Λ1⟩ = true := by decide +kernel

/-- A8 at `Λ1`. -/
theorem a8_1 : Scc.Cert.PlaceOK.A64.a8 oH ⟨Λ1⟩ = true := by decide +kernel

/-- `PlaceW` at `Λ1`. -/
theorem placeW_1 : Spike.Lib.PlaceW pcfgH Λ1 oH := ⟨a1_1, a2_1, a4_1, a6_1, a8_1⟩

/-- **`LayoutE` at `Λ1`**: `hlo`, `hnz`, A13's data part and `hinit2` by `decide +kernel`, `hstat` by `rfl`. -/
theorem layoutE_1 : LayoutE Λ1 where
  hp := placeW_1
  hlo := by decide +kernel
  hstat := rfl
  hnz := by decide +kernel
  hA13 := by decide +kernel
  hinit2 := by decide +kernel

/-- **The root's premise bundle at `Λ1`**, from the listing's parse. -/
noncomputable example (hparse : Scc.Cert.Link.A64.parsesTo SccCode.helloAsm SccCode.helloProg SccCode.helloSecs = true)
    (E : Scc.Sem.Entry) (ls : Spike.Lib.A64Consumer.Lsize) :
    Spike.Lib.A64.HelloPh.HelloRootPrem (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW placeW_1 (iRdM Λ1))
      (Spike.Lib.WakeLoadT.L0T (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW placeW_1 (iRdM Λ1)).Λ) :=
  layoutE_1.premE hparse E ls

end Spike.Test.A64HelloRootBaseInhSmoke

/-- info: 'Spike.Test.A64HelloRootBaseInhSmoke.layoutE_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.A64HelloRootBaseInhSmoke.layoutE_1
