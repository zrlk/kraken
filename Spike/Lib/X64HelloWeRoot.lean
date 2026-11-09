/-
**The root's immediates** (x86-64; the twin of `Spike/Lib/A64HelloWeRoot.lean`): at the root's layout
`ofPlaceWX hp (HelloImms.immsH Λ0 i0)`,

- `rdImms_root`, `hme_root`, `hzI_root`, `hm_root`: the root's `hRdI`, `hme`, `hzI`, `hm` at the certificate's
  table `i0 := HelloImms.i0M Λ0` (`HelloImms.rdImms_iRdM`, `hmeC_iRdM`, `hm_iRdM`, `HabCtlA.hz_i0M`).

## Differences from the AArch64 version

- The root's `hWe` (AArch64 `hWe_root`, `hWe_rootRdH`, at `ownGH`) is at `ownGHXW`: `X64HelloWeRootX.hWe_rootX`.
-/
import Spike.Lib.X64HelloWeS
import Spike.Lib.X64HelloRootPlug
import Spike.Lib.X64HelloHrdR
import Spike.Lib.X64HelloLand
import Spike.Lib.X64HelloHabCtlA
import Spike.Lib.X64HelloLandRU

namespace Spike.Lib.X64.HelloPh.WeRoot

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Rt (RuntimeLayout)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : Spike.Lib.PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

/-! ## The root's immediates at `i0 := HelloImms.i0M Λ0` -/

/-- **`hRdI`** at the root's table (`HelloImms.rdImms_iRdM`). -/
theorem rdImms_root :
    Spike.Lib.X64.HelloPh.RdPlS.RdImms
      (RuntimeLayout.ofPlaceWX hp (Spike.Lib.X64.HelloImms.immsH Λ0 (Spike.Lib.X64.HelloImms.i0M Λ0))).Λ :=
  have h := Spike.Lib.X64.HelloImms.rdImms_iRdM hp
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- **`hme`** at the root's table (`HelloImms.hmeC_iRdM`). -/
theorem hme_root :
    (RuntimeLayout.ofPlaceWX hp (Spike.Lib.X64.HelloImms.immsH Λ0 (Spike.Lib.X64.HelloImms.i0M Λ0))).Λ.imms
      Spike.Lib.SrcCalls.setupCont "me" 0 =
      some (Spike.Lib.X64WakeLoadT.tcb0
        (RuntimeLayout.ofPlaceWX hp (Spike.Lib.X64.HelloImms.immsH Λ0 (Spike.Lib.X64.HelloImms.i0M Λ0))).Λ) :=
  Spike.Lib.X64.HelloImms.hmeC_iRdM hp

/-- **`hzI`** at the root's table (`HabCtlA.hz_i0M`). -/
theorem hzI_root : Spike.Lib.X64.HelloImms.i0M Λ0 Spike.Lib.X64HelloMainPreSrc.newTerm "z" 0 = some 0 :=
  Spike.Lib.X64.HelloPh.HabCtlA.hz_i0M Λ0

/-- **`hm`** at the root's table (`HelloImms.hm_iRdM`). -/
theorem hm_root :
    (RuntimeLayout.ofPlaceWX hp (Spike.Lib.X64.HelloImms.immsH Λ0 (Spike.Lib.X64.HelloImms.i0M Λ0))).Λ.imms
      Spike.Lib.X64HelloRodataSrc.eB "m" 0 = some 2 :=
  Spike.Lib.X64.HelloImms.hm_iRdM hp

end Spike.Lib.X64.HelloPh.WeRoot

/-- info: 'Spike.Lib.X64.HelloPh.WeRoot.rdImms_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WeRoot.rdImms_root

/-- info: 'Spike.Lib.X64.HelloPh.WeRoot.hme_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WeRoot.hme_root

/-- info: 'Spike.Lib.X64.HelloPh.WeRoot.hzI_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WeRoot.hzI_root

/-- info: 'Spike.Lib.X64.HelloPh.WeRoot.hm_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WeRoot.hm_root
