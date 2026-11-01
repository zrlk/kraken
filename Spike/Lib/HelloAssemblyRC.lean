/-
**hello.w on AArch64: the placed assembly at the root, its context fixed**:
`HelloAssemblyRV.hello_obligations_RV` at the root's immediate table `C0S.immsH Λ0 i0`, with `helloDR`'s context
`Ctx := Land.CtxRH` (the root's: `wc_rodata`'s and `wc_main`'s counter adds and the box's store; at `rd := True`
and the memory side's sizes `ls`, as `msBotH`'s) and main's frame `frM := frH c0S.env`.

- `hello_obligations_RC`: the statement (`type_of%` of `hello_obligations_RV` at those choices). The start's
  obligations into `CtxRH` are `Land.hctx_rdH`/`hctx_rdU` (`HrdS.hrd_WSHF`'s `hctx`), `Land.hctx_mainH`/
  `hctx_mainU` (`WcWfR.wcPreW_WSgH`'s) and `Land.hctx_stH` (`Land3.hwr_stH`'s `hCtx`).
-/
import Spike.Lib.HelloAssemblyRV
import Spike.Lib.A64HelloLand

namespace Spike.Lib.HelloAssemblyRC

variable {asm : String}

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib (FragS)
open Spike.Lib.A64Consumer (Lsize)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSegTCS (SegTCS)
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Spike.Lib.A64.Flow.Worker (NNH)
open Spike.Lib.HelloAssemblyI (LH ιH endH SRH GH)
open Spike.Lib.HelloAssemblyIM (G0H)
open Spike.Lib.A64.HelloPh.Land (CtxRH)
open Spike.Lib.A64.HelloPh.C0S (c0S)
open Spike.Lib.HelloAssemblyRV (hello_obligations_RV)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The root's immediate table at the certificate's table `i0` (as `StartH0U`). -/
local notation "IH" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

variable (P Z X : ιH hp (IH) → FragS isaLSE2)
  /- row: 5j-misc (as `hello_obligations_IM`'s `hseg`) -/
  (hseg : ∀ w, SegTCSX (fun s c fs => NNH (LH hp (IH)).exe (endH hp (IH)) s ∧ Z w s c fs) (X w) helloSrc
    (SRH hp (IH) w).lbl (fun _ => Spike.Lib.HelloMsW.msWH (LH hp (IH)) (GH hp (IH) (G0H hp (IH))) (SRH hp (IH)) w) (P w)
    (fun _ _ _ => False))

/-- **The assembly at the root, `Ctx := CtxRH`, `frM := frH c0S.env`** (see the module doc). -/
theorem hello_obligations_RC {arch : WeakMem.Arch} {B : Scc.Sem.Budget} {E : Scc.Sem.Entry} {passT : State → Prop}
    {AbT} {ls : Lsize}
    {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {W2 inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} :
    type_of% (@hello_obligations_RV asm pcfg o Λ0 hp (IH) P Z X hseg arch B E passT AbT
      (CtxRH (asm := asm) hp i0 E (fun _ => True) ls) ls (Spike.Lib.HelloRdCf.frH c0S.env) W1 inv1 W2 inv2) :=
  @hello_obligations_RV asm pcfg o Λ0 hp (IH) P Z X hseg arch B E passT AbT
    (CtxRH (asm := asm) hp i0 E (fun _ => True) ls) ls (Spike.Lib.HelloRdCf.frH c0S.env) W1 inv1 W2 inv2

end Inst

/-- info: 'Spike.Lib.HelloAssemblyRC.hello_obligations_RC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello_obligations_RC

end Spike.Lib.HelloAssemblyRC
