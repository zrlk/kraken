/-
**hello.w on AArch64: `HelloRowsW1.toW`'s side facts at the placed instance**
(the relation `HelloAssemblyI.QH`, the worker side `DH`, the target's marks
at the placed layout; `HelloRowsV1.HelloRowsW1.toWV`'s premises other than
`hwf`, `hE`, `hms`, `hKR`).

- `hown_I`: `QH`'s ownership is wake's (`rfl`).
- `hml_I`: main has not returned while the process runs
  (`HelloLive.mainLiveH`).
- `hAbX_I`: the abort phase's `exit_group` at an abort site
  (`HelloAbExit.abExit_DR` with `exitSite_P`; the program is hello's, `ho`).
- `hlbl_I`: the worker side's labels are the records' (`rfl`).
- `hfz_I`: the buffer frozen (`HelloEmitFrzI.byteFrz_I`).
- `hbo_I`: the worker's byte output is `ByteOutP` (`HelloMsW.msWH_bo`).
- `hES_I`: the emit row's shape (`HelloEmitShapeF.emitShapeF_I`).
- `hNP_I`: a certified worker at a no-promise state has no promise
  (`WakeP.noProm_prom`).
-/
import Spike.Lib.HelloRowsV1
import Spike.Lib.HelloEmitFrzI
import Spike.Lib.HelloEmitShapeF
import Spike.Lib.HelloLive

namespace Spike.Lib.HelloSideI

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSegTCS (SegTCS)
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Spike.Lib.A64.Flow.Worker (NNH AbW)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.HelloAssemblyI (LH ιH endH SRH GH PaH DH MH QH μH)
open Spike.Lib.HelloEmitStep (ByteFrz)
open Spike.Lib.HelloByteOutP (ByteOutP)
open SccCode (helloProg)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (G0 : ιH hp i → Loc → Val → Prop) (P Z X : ιH hp i → FragS isaLSE2)
  (hseg : ∀ w, SegTCSX (fun s c fs => NNH (LH hp i).exe (endH hp i) s ∧ Z w s c fs) (X w) helloSrc (SRH hp i w).lbl
    (fun _ => Spike.Lib.HelloMsW.msWH (LH hp i) (GH hp i G0) (SRH hp i) w) (P w) (fun _ _ _ => False))
  {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {E : Entry} {asm : String}
  (hpa : textProgram asm = .ok o.prog) {passT : State → Prop} {Dd : HelloO.ODataH} {r1c : Range}

/-- `QH`'s ownership is wake's. -/
theorem hown_I : (QH hp i G0 P Z X hseg arch R1 E hpa passT Dd r1c).own = WakeOwn.wakeOwn := rfl

/-- main has not returned while the process runs (`HelloLive.mainLiveH`). -/
theorem hml_I : ∀ t s, (QH hp i G0 P Z X hseg arch R1 E hpa passT Dd r1c).Post (LH hp i).Λ t s →
    t.2.exited = none → SrcSem.mainExit s = [] :=
  HelloLive.mainLiveH

/-- **The abort phase's `exit_group` is at an abort site** of the target's
marks (`abExit_DR`, the exit call by `exitSite_P`), of a text parsing to
hello's program. -/
theorem hAbX_I (ho : o.prog = helloProg) (hpa' : textProgram asm = .ok o.prog) :
    HelloStep1Sys.AbExit (DH hp i G0 P Z X hseg) ((target (kernel 2) E).marks asm (LH hp i).Λ)
      (AbW (LH hp i).exe) :=
  haveI := (LH hp i).valid
  HelloAbExit.abExit_DR (by rw [← ho]; exact (LH hp i).lays) rfl (HelloAbExit.exitSite_P hp i ho hpa')

/-- The worker side's labels are the records'. -/
theorem hlbl_I : ∀ w, (DH hp i G0 P Z X hseg).lbl w = ((QH hp i G0 P Z X hseg arch R1 E hpa passT Dd r1c).SR w).lbl :=
  fun _ => rfl

/-- The buffer is frozen (`byteFrz_I`). -/
theorem hfz_I : ByteFrz (QH hp i G0 P Z X hseg arch R1 E hpa passT Dd r1c) (DH hp i G0 P Z X hseg) (LH hp i).Λ :=
  HelloEmitFrzI.byteFrz_I hp i E asm

/-- The worker's byte output is `ByteOutP` at its labels. -/
theorem hbo_I : ∀ w fs, ((DH hp i G0 P Z X hseg).ms w fs).bo = ByteOutP helloSrc ((DH hp i G0 P Z X hseg).lbl w) :=
  fun _ _ => rfl

/-- The emit row's shape (`emitShapeF_I`). -/
theorem hES_I : HelloEmitShapeF.EmitShapeF (DH hp i G0 P Z X hseg) :=
  HelloEmitShapeF.emitShapeF_I hp i G0 P Z X hseg

/-- A certified worker at a no-promise state has no promise. -/
theorem hNP_I : ∀ w x (t : Thread isaLSE2) mem,
    ((QH hp i G0 P Z X hseg arch R1 E hpa passT Dd r1c).P w).noProm t.st →
    CertOkC Arch.armv8 (certSem abi Arch.armv8 ((target (kernel 2) E).marks asm (LH hp i).Λ) x 1) 1 t mem →
      t.prom = [] :=
  fun _ _ _ _ hn hc => WakeP.noProm_prom hn hc

/-- info: 'Spike.Lib.HelloSideI.hml_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hml_I

/-- info: 'Spike.Lib.HelloSideI.hAbX_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hAbX_I

/-- info: 'Spike.Lib.HelloSideI.hfz_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hfz_I

/-- info: 'Spike.Lib.HelloSideI.hES_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hES_I

/-- info: 'Spike.Lib.HelloSideI.hNP_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hNP_I

end Spike.Lib.HelloSideI
