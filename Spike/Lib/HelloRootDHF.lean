/-
**The root's worker-side rows at the switch's instance** (hello.w, DH := helloDRF switch; AArch64): the rows
`hello_obligations_RV` asks of the worker side that `HelloWorkerDHF` does not state directly, at
`DH hp i G0 (PF hp i G0) (ZF hp i μ) (XF hp i μ) (hsegFH …)`, each from `DHF_zhr` (the invariant inside
`NNH ∧ WideX ∧ Pend ZHR`) or `DHF_flag` by `Z` monotonicity (no new `helloDRF` variants).

- `DHF_hhalt1`: at a system call the worker's instruction runs (as `HelloHaltMapW.hhalt1_DR`).
- `DHF_hRW1`: every instruction is `RelW1` (as `HelloWorkerRR.hRW1_DR`).
- `DHF_pass`: `PassH` at `helloPassT` (as `HelloPassI.passH_I`; `PassZ` at `ZHR`).
- `DHF_hZ`: `ZStoreOk` at `ZF` (`ZF`'s first conjunct is `ZHR`; `Z.zStoreOk_ZHR`).
- `DHF_hmapW`: no unmapped touch (as `HelloMapWF.hmapW_DRF_H`, at `DHF_flag`).
-/
import Spike.Lib.HelloWorkerDHF
import Spike.Lib.HelloMapWF
import Spike.Lib.HelloPassI
import Spike.Lib.HelloWorkerRW1

namespace Spike.Lib.HelloRootDHF

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.Inv2Core
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.A64Consumer (K0)
open Spike.Lib.A64.Flow.Worker.Hello.AbObl (MarksL)
open Spike.Lib.HelloAssemblyI (ιH LH endH SRH GH DH cwvH)
open Spike.Lib.HelloWorkerDHF (PF ZF XF hsegFH DHF_zhr DHF_flag)
open Scc.Cert.Link.A64 (codeOf)
open SccCode (helloProg)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (G0 : ιH hp i → Loc → Val → Prop)
  (hI : Spike.Lib.A64.HelloPh.XHFSeg.ImmsKid (LH hp i).Λ) {asm : String}
  (hpa : textProgram asm = .ok o.prog) (hhp : textProgram asm = .ok helloProg) {μ : Marks}
  (hlab : ∀ l x, codeOf Spike.Lib.A64.HelloPh.lo helloProg l = some x →
    (_root_.Executable.labels (LH hp i).exe).label l = Int64.ofNat x)
  (hμ : MarksL μ (_root_.Executable.labels (LH hp i).exe).label)

set_option hygiene false in
local notation "DF" => DH hp i G0 (PF hp i G0) (ZF hp i μ) (XF hp i μ) (hsegFH hp i G0 hI hpa hhp hlab hμ)

include hI hpa hhp hlab hμ

/-- **`hhalt1` at the instance**: at a system call the worker's instruction runs (`DHF_zhr`'s `NNH` and pending
`ZHR`, as `HelloHaltMapW.hhalt1_DR`). -/
theorem DHF_hhalt1 : ∀ w s c fs, (DF).Wi w s c fs → abi.atSys s = true → (isaLSE2.exec s).isSome := by
  haveI hv := (LH hp i).valid
  intro w s c fs h ha
  obtain ⟨⟨he, hn, -, -⟩, -, _, _, -, hz⟩ := DHF_zhr hp i G0 hI hpa hhp hlab hμ w s c fs h
  exact Spike.Lib.A64.Flow.Worker.Wake.EndOff.exec_isSome_atSvc (he ▸ hv) ha
    (by rw [hn]; exact hz.1.1.2.2.2)

/-- **`hRW1` at the instance**: every instruction of a worker's state is `RelW1` (`DHF_zhr`'s pending `ZHR`, as
`HelloWorkerRR.hRW1_DR`). -/
theorem DHF_hRW1 : ∀ w s c fs e, (DF).Wi w s c fs → isaLSE2.exec s = some e → EvTree.RelW1 Arch.armv8 e :=
  fun w s c fs e h he =>
    Spike.Lib.A64.Flow.Worker.Hello.Z.relW1_of_pend (fun _ _ _ h => h.2)
      (DHF_zhr hp i G0 hI hpa hhp hlab hμ w s c fs h).2.2 e he

/-- **`pass` at the instance** (`helloPassT`): `PassH` from `DHF_zhr`'s pending `ZHR` (`passZ_ZHR`) and `c`'s word
an untagged locative (`cwvH`), as `HelloPassI.passH_I`. -/
theorem DHF_pass : HelloW1.PassH (DF) Spike.Lib.A64.Flow.Worker.Hello.Pass.helloPassT :=
  HelloPassH.passH_of_pend (fun w => ⟨_, cwvH hp i w⟩)
    (fun w s c fs h => (DHF_zhr hp i G0 hI hpa hhp hlab hμ w s c fs h).2.2)
    fun _ => Spike.Lib.A64.Flow.Worker.Hello.Z.passZ_ZHR

omit hI hpa hhp hlab hμ in
/-- **`hZ` at the instance**: `ZStoreOk` at `ZF` (its first conjunct `ZHR`, `Z.zStoreOk_ZHR`). -/
theorem DHF_hZ : HelloW1Store.ZStoreOk (LH hp i).exe (ZF hp i μ) :=
  fun w s c h => Spike.Lib.A64.Flow.Worker.Hello.Z.zStoreOk_ZHR w s c h.1

/-- **`hmapW` at the instance**: no step of a worker's state touches a location `K0` leaves unmapped
(`DHF_flag`, as `HelloMapWF.hmapW_DRF_H`). -/
theorem DHF_hmapW : ∀ w s c fs, (DF).Wi w s c fs → abi.atSys s = false → ∀ e, isaLSE2.exec s = some e →
    ¬ Kernel.Touches (fun l w => Kernel.mapped (K0 (LH hp i).Λ) w l = false) e :=
  HelloHaltMapW.hmapW_ofH (fun _ _ => rfl) (fun w _ _ _ h => HelloHaltMapW.mp_msWH w h)
    fun w s c fs h c₁ fs₁ hr => by
      obtain ⟨b, hl, -, hT⟩ := w.2.1.2.2.2.1
      exact Spike.Lib.WakeLabMapped.labMapped_flagB
        (DHF_flag hp i G0 hI hpa hhp hlab hμ w s c fs h c₁ fs₁ hr) hl hT w.2.1.2.2.2.2

end Inst

end Spike.Lib.HelloRootDHF

/-- info: 'Spike.Lib.HelloRootDHF.DHF_hhalt1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloRootDHF.DHF_hhalt1

/-- info: 'Spike.Lib.HelloRootDHF.DHF_hRW1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloRootDHF.DHF_hRW1

/-- info: 'Spike.Lib.HelloRootDHF.DHF_pass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloRootDHF.DHF_pass

/-- info: 'Spike.Lib.HelloRootDHF.DHF_hZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloRootDHF.DHF_hZ

/-- info: 'Spike.Lib.HelloRootDHF.DHF_hmapW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloRootDHF.DHF_hmapW
