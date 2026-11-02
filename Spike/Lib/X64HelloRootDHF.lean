/-
**The root's worker-side rows at the switch's instance** (hello.w on x86-64, `DH := helloDRF`; the twin of
`Spike/Lib/HelloRootDHF.lean`): the rows the root asks of the worker side that `X64HelloWorkerDHF` does not state
directly, at `DH hp i G0 (PF hp i G0) (ZF hp i μ) (XF hp i μ) (hsegFH …)`, each from `DHF_zhr` (the invariant
inside `NNH ∧ WideX ∧ Pend ZHR`) or `DHF_flag` by `Z` monotonicity.

- `DHF_hhalt1`: at a system call the worker's instruction runs (as `X64HelloHaltMapW.hhalt1_DR`).
- `DHF_hRW1`: every instruction is `RelW1 tso` (`Z.relW1_of_pend`).
- `DHF_pass`: `PassH` at `helloPassT` (`PassZ` at `ZHR`).
- `DHF_hZ`: `ZStoreOk` at `ZF` (`ZF`'s first conjunct is `ZHR`; `Z.zStoreOk_ZHR`).
- `DHF_hmapW`: no unmapped touch (`X64HelloHaltMapW.hmapW_ofH` at `DHF_flag`).

## Unlike AArch64

- The loader's parses are `cellsOf asm = some …`, the labels' check `Scc.Sem.X64.codeLabel` (as
  `X64HelloWorkerDHF`); the system call is `syscall` (`EndOff.exec_isSome_atSyscall`, AArch64 `svc`); `hRW1` is at
  `Arch.tso` (AArch64 `Arch.armv8`).
- The A64 module's imports of `HelloMapWF`, `HelloPassI` and `HelloWorkerRW1` reach no constant used here and have
  no x86-64 twin in this module; the lemmas come from `X64HelloHaltMapW`, `X64HelloPassH`, `X64HelloZStore`.
-/
import Spike.Lib.X64HelloWorkerDHF
import Spike.Lib.X64HelloHaltMapW
import Spike.Lib.X64HelloZStore
import Spike.Lib.X64WakeEndOff
import Spike.Lib.X64WakeLabMapped

namespace Spike.Lib.X64HelloRootDHF

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.Inv2Core
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64Consumer (K0)
open Spike.Lib.X64.Flow.Worker.Hello.AbObl (MarksL)
open Spike.Lib.X64HelloAssemblyI (ιH LH endH SRH GH DH cwvH)
open Spike.Lib.X64HelloWorkerDHF (PF ZF XF hsegFH DHF_zhr DHF_flag)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (G0 : ιH hp i → Loc → Val → Prop)
  (hI : Spike.Lib.X64.HelloPh.XHFSeg.ImmsKid (LH hp i).Λ) {asm : Asm}
  (hpa : cellsOf asm = some o.prog) (hhp : cellsOf asm = some SccCode.helloCells) {μ : Marks}
  (hlab : ∀ l x, Scc.Sem.X64.codeLabel Spike.Lib.X64.HelloPh.lo SccCode.helloCells l = some x →
    (_root_.Executable.labels (LH hp i).exe).label l = Int64.ofNat x)
  (hμ : MarksL μ (_root_.Executable.labels (LH hp i).exe).label)

set_option hygiene false in
local notation "DF" => DH hp i G0 (PF hp i G0) (ZF hp i μ) (XF hp i μ) (hsegFH hp i G0 hI hpa hhp hlab hμ)

include hI hpa hhp hlab hμ

/-- **`hhalt1` at the instance**: at a system call the worker's instruction runs (`DHF_zhr`'s `NNH` and pending
`ZHR`, as `X64HelloHaltMapW.hhalt1_DR`). -/
theorem DHF_hhalt1 : ∀ w s c fs, (DF).Wi w s c fs → abi.atSys s = true → (isa.exec s).isSome := by
  haveI hv := (LH hp i).valid
  intro w s c fs h ha
  obtain ⟨⟨he, hn, -, -⟩, -, _, _, -, hz⟩ := DHF_zhr hp i G0 hI hpa hhp hlab hμ w s c fs h
  exact Spike.Lib.X64.Flow.Worker.Wake.EndOff.exec_isSome_atSyscall (he ▸ hv) ha
    (by rw [hn]; exact hz.1.1.2.2.2)

/-- **`hRW1` at the instance**: every instruction of a worker's state is `RelW1 tso` (`DHF_zhr`'s pending `ZHR`,
`Z.relW1_of_pend`). -/
theorem DHF_hRW1 : ∀ w s c fs e, (DF).Wi w s c fs → isa.exec s = some e → EvTree.RelW1 Arch.tso e :=
  fun w s c fs e h he =>
    Spike.Lib.X64.Flow.Worker.Hello.Z.relW1_of_pend (fun _ _ _ h => h.2)
      (DHF_zhr hp i G0 hI hpa hhp hlab hμ w s c fs h).2.2 e he

/-- **`pass` at the instance** (`helloPassT`): `PassH` from `DHF_zhr`'s pending `ZHR` (`passZ_ZHR`) and `c`'s word
an untagged locative (`cwvH`). -/
theorem DHF_pass : X64HelloW1.PassH (DF) Spike.Lib.X64.Flow.Worker.Hello.Pass.helloPassT :=
  X64HelloPassH.passH_of_pend (fun w => ⟨_, cwvH hp i w⟩)
    (fun w s c fs h => (DHF_zhr hp i G0 hI hpa hhp hlab hμ w s c fs h).2.2)
    fun _ => Spike.Lib.X64.Flow.Worker.Hello.Z.passZ_ZHR

omit hI hpa hhp hlab hμ in
/-- **`hZ` at the instance**: `ZStoreOk` at `ZF` (its first conjunct `ZHR`, `Z.zStoreOk_ZHR`). -/
theorem DHF_hZ : X64HelloW1Store.ZStoreOk (LH hp i).exe (ZF hp i μ) :=
  fun w s c h => Spike.Lib.X64.Flow.Worker.Hello.Z.zStoreOk_ZHR w s c h.1

/-- **`hmapW` at the instance**: no step of a worker's state touches a location `K0` leaves unmapped
(`DHF_flag`, `X64HelloHaltMapW.hmapW_ofH`). -/
theorem DHF_hmapW : ∀ w s c fs, (DF).Wi w s c fs → abi.atSys s = false → ∀ e, isa.exec s = some e →
    ¬ Kernel.Touches (fun l w => Kernel.mapped (K0 (LH hp i).Λ) w l = false) e :=
  X64HelloHaltMapW.hmapW_ofH (fun _ _ => rfl) (fun w _ _ _ h => X64HelloHaltMapW.mp_msWH w h.1)
    fun w s c fs h c₁ fs₁ hr => by
      obtain ⟨b, hl, -, hT⟩ := w.2.1.2.2.2.1
      exact Spike.Lib.X64WakeLabMapped.labMapped_flagB
        (DHF_flag hp i G0 hI hpa hhp hlab hμ w s c fs h c₁ fs₁ hr) hl hT w.2.1.2.2.2.2

end Inst

end Spike.Lib.X64HelloRootDHF

/-- info: 'Spike.Lib.X64HelloRootDHF.DHF_hhalt1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloRootDHF.DHF_hhalt1

/-- info: 'Spike.Lib.X64HelloRootDHF.DHF_hRW1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloRootDHF.DHF_hRW1

/-- info: 'Spike.Lib.X64HelloRootDHF.DHF_pass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloRootDHF.DHF_pass

/-- info: 'Spike.Lib.X64HelloRootDHF.DHF_hZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloRootDHF.DHF_hZ

/-- info: 'Spike.Lib.X64HelloRootDHF.DHF_hmapW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloRootDHF.DHF_hmapW
