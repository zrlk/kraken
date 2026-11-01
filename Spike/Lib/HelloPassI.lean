/-
**hello.w on AArch64: the root's `pass` premise at the placed instance** (row hello-pass):
`HelloW1.PassH (DH hp i G0 P (ZI hp i) X hseg) helloPassT`, the worker side's store point at the target pc predicate
`A64HelloPass.helloPassT` (`PcIn helloPostRuns`), for the root's `passT`.

The proof is `HelloPassH.passH_DR` (row 5j-k: `PassH` at `helloDR` from `PassZ` at the segment's `Z` and `c`'s
word an untagged locative) at the instance: the pointer word by `HelloAssemblyI.cwvH`, `PassZ helloPassT` at
`ZI`'s `ZHR` by `A64HelloZR.passZ_ZHR`. Like wake's root, hello fixes its `passT` to the named pc-side predicate;
the root (`hello_root_lit`) plugs `passT := helloPassT` and `pass := passH_root`.

Differences from `passH_DR`: the instance's `DH` (`helloDH` at the placed layout, the records' memory side,
`lBH`, `13`, `2`) at `Z := ZI hp i`, generic in `G0`, `P` and `hseg`; `passH_root` at the root's `G0H`, `PI`,
`hsegI`.

- `passH_I`: `PassH` at `DH hp i G0 P (ZI hp i) X hseg`, `passT := helloPassT`.
- `passH_root`: at the root's `G0H hp i`, `PI hp i (G0H hp i)`, `XI hp i`, `hsegXI hp i (G0H hp i) hpa hhp`.
-/
import Spike.Lib.HelloSegI
import Spike.Lib.HelloPassH
import Spike.Lib.A64HelloZR
import Spike.Lib.HelloAssemblyIM

namespace Spike.Lib.HelloPassI

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSegTCS (SegTCS)
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Spike.Lib.A64.Flow.Worker (NNH)
open Spike.Lib.A64.Flow.Worker.Hello.Pass (helloPassT)
open Spike.Lib.A64.Flow.Worker.Hello.Z (passZ_ZHR)
open Spike.Lib.HelloAssemblyI (ιH LH endH SRH GH DH ZI PI XI hsegXI cwvH)
open Spike.Lib.HelloAssemblyIM (G0H)
open SccCode (helloProg)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **The root's `pass` at the instance's worker side**, `passT := helloPassT`, generic in the records' value
invariant `G0`, the segment's entry `P` and its proof `hseg` (see the module doc). -/
theorem passH_I (G0 : ιH hp i → Loc → Val → Prop) (P X : ιH hp i → FragS isaLSE2)
    (hseg : ∀ w, SegTCSX (fun s c fs => NNH (LH hp i).exe (endH hp i) s ∧ ZI hp i w s c fs) (X w) helloSrc
      (SRH hp i w).lbl (fun _ => HelloMsW.msWH (LH hp i) (GH hp i G0) (SRH hp i) w) (P w) (fun _ _ _ => False)) :
    HelloW1.PassH (DH hp i G0 P (ZI hp i) X hseg) helloPassT :=
  HelloPassH.passH_DR _ _ _ _ _ _ _ _ _ hseg _ _ _ _ (cwvH hp i) fun _ => passZ_ZHR

/-- **The root's `pass`** at its `G0H`, `PI`, `XI`, `hsegXI` (`hello_root_inv`'s / `hello_root_lit`'s premise at
`passT := helloPassT`). -/
theorem passH_root {asm : String} (hpa : textProgram asm = .ok o.prog) (hhp : textProgram asm = .ok helloProg) :
    HelloW1.PassH (DH hp i (G0H hp i) (PI hp i (G0H hp i)) (ZI hp i) (XI hp i) (hsegXI hp i (G0H hp i) hpa hhp))
      helloPassT :=
  passH_I hp i _ _ _ _

end Inst

end Spike.Lib.HelloPassI

/-- info: 'Spike.Lib.HelloPassI.passH_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloPassI.passH_I

/-- info: 'Spike.Lib.HelloPassI.passH_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloPassI.passH_root
