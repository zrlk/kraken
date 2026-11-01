/-
**hello.w on AArch64: `post_step1` under the run invariant, assembled**
(row B8-gen1; `HelloAssembly.HelloRowsW.post_step1`, whose shape reads
`WakeRunInv.RunInv` for the worker's `write`'s private keys):
`HelloStep1.post_step1H` with its three parts discharged by the print and
emit phases' rows, and `PrivAt` by `HelloStep1.privAt_of_runInv`.

- `PrintStep1`: `HelloStep1D.printStep1_of`, its kernel system calls by
  `HelloStep1Sys.sysStepP_of` (the abort phase's `exit_group` at an abort
  site, `AbExit`), its promises by `HelloProm1.post_prom1H`, `PrintWr0` by
  `HelloStep1D.printWr0_of`.
- `EmitStep1`: `HelloEmitW1.emitStep1_of` with `write1StepE_of`, the
  returns by `emitRetP_of`; `print`'s `write` (`Write1StepP`, the system
  call row's input) by `write1StepP_of`.
- `StoreWr0`: `HelloStep1.storeWr0_of`.

- `post_step1RI`: `HelloRowsW.post_step1`'s shape from `HelloCompat` and
  the instance's side facts (`hms`, `hown`, `hKR`, `hml`, `hAbX`, `hlbl`,
  `hfz`, `hbo`, `hES`, `hNP`) at an entry `E` with `E.clear Λ`.
- `post_step1RIX`: the same at the abort phase `Worker.AbW exe`, `AbExit`
  by `HelloAbExit.abExit_of` from `ExitSite` and `SvcNoExit`.
-/
import Spike.Lib.HelloStep1
import Spike.Lib.HelloProm1
import Spike.Lib.HelloEmitW1
import Spike.Lib.HelloAbExit

namespace Spike.Lib.HelloStep1RI

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloW1 (WSideH)
open Spike.Lib.HelloAssembly (HelloCompat)
open Spike.Lib.HelloKRE (KRHE)
open Spike.Lib.HelloEmitShapeF (EmitShapeF)
open Spike.Lib.HelloEmitStep (ByteFrz)
open Spike.Lib.HelloByteOutP (ByteOutP)

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {Q : WakeRel} {μ : Marks} {D : WSideH Q.ι}
  {M : WakeM0.MSide Q.ι} {AbW : isaLSE2.State → Prop} {hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0}
  {hem : HelloW1Store.NoWrite D} {r0 r1 : Q.ι → Range}

/-- **A step of the worker after the spawn keeps `Post`, under the run
invariant** (`HelloRowsW.post_step1`'s shape): `post_step1H` with
`PrintStep1` by `printStep1_of`, `EmitStep1` by `emitStep1_of`, `StoreWr0`
by `storeWr0_of`; `PrivAt` from `RunInv` at a clear entry. -/
theorem post_step1RI (hC : HelloCompat Q D M μ Λ arch AbW hcw hem) (hwf : Λ.WF)
    (hms : ∀ w fs, D.ms w fs = D.ms w []) (hown : Q.own = WakeOwn.wakeOwn) (hKR : Q.KR = KRHE D r0 r1)
    (hml : ∀ t s, Q.Post Λ t s → t.2.exited = none → SrcSem.mainExit s = [])
    (hAbX : HelloStep1Sys.AbExit D μ AbW) (hlbl : ∀ w, D.lbl w = (Q.SR w).lbl) (hfz : ByteFrz Q D Λ)
    (hbo : ∀ w fs, (D.ms w fs).bo = ByteOutP helloSrc (D.lbl w)) (hES : EmitShapeF D)
    (hNP : ∀ w x (t : Thread isaLSE2) mem, (Q.P w).noProm t.st →
      CertOkC Arch.armv8 (certSem abi Arch.armv8 μ x 1) 1 t mem → t.prom = [])
    {E : Entry} (hE : E.clear Λ = true) :
    ∀ t es t' s, Q.Post Λ t s → WakeRunInv.RunInv Λ E t → ¬ Q.atUnpk t s → ¬ Q.atTexit t s →
      (machine (kernel 2)).Step μ 1 t es t' →
      ∃ s', (srcS helloSrc arch).Run s (obs es) s' ∧ Q.Post Λ t' s' := by
  have hpt1 := hC.1.pt1
  have hRet := HelloEmitW1.emitRetP_of hC.1 hKR hpt1 hES hown hNP
  have hw1 := HelloEmitW1.write1StepP_of hC.1 hKR hpt1 hlbl hfz hown hbo hES hRet
  have hpe := HelloEmitW1.emitStep1_of hpt1
    (HelloEmitW1.write1StepE_of hC.1 hKR hpt1 hlbl hfz hown hbo hES hRet) hml
  have hpr := HelloStep1D.printStep1_of hC hwf hms hown hml
    (HelloStep1Sys.sysStepP_of hC hms hown hKR hAbX hw1) (HelloProm1.post_prom1H hC hwf hms hown hKR)
    (HelloStep1D.printWr0_of hKR)
  intro t es t' s hP hri
  exact HelloStep1.post_step1H hwf hpr hpe (HelloStep1.storeWr0_of hKR hC) hC t es t' s hP
    (HelloStep1.privAt_of_runInv hE hri)

/-- **`post_step1RI` at the abort phase `Worker.AbW exe`**: `AbExit` by
`HelloAbExit.abExit_of` from the exit call's abort site (`ExitSite`) and
no `exit_group` at the stub's `write` (`SvcNoExit`). -/
theorem post_step1RIX {exe : _root_.Executable}
    (hC : HelloCompat Q D M μ Λ arch (A64.Flow.Worker.AbW exe) hcw hem) (hwf : Λ.WF)
    (hms : ∀ w fs, D.ms w fs = D.ms w []) (hown : Q.own = WakeOwn.wakeOwn) (hKR : Q.KR = KRHE D r0 r1)
    (hml : ∀ t s, Q.Post Λ t s → t.2.exited = none → SrcSem.mainExit s = [])
    (hx : HelloAbExit.ExitSite exe μ) (hsvc : HelloAbExit.SvcNoExit D exe)
    (hlbl : ∀ w, D.lbl w = (Q.SR w).lbl) (hfz : ByteFrz Q D Λ)
    (hbo : ∀ w fs, (D.ms w fs).bo = ByteOutP helloSrc (D.lbl w)) (hES : EmitShapeF D)
    (hNP : ∀ w x (t : Thread isaLSE2) mem, (Q.P w).noProm t.st →
      CertOkC Arch.armv8 (certSem abi Arch.armv8 μ x 1) 1 t mem → t.prom = [])
    {E : Entry} (hE : E.clear Λ = true) :
    ∀ t es t' s, Q.Post Λ t s → WakeRunInv.RunInv Λ E t → ¬ Q.atUnpk t s → ¬ Q.atTexit t s →
      (machine (kernel 2)).Step μ 1 t es t' →
      ∃ s', (srcS helloSrc arch).Run s (obs es) s' ∧ Q.Post Λ t' s' :=
  post_step1RI hC hwf hms hown hKR hml (HelloAbExit.abExit_of hx hsvc) hlbl hfz hbo hES hNP hE

/-- info: 'Spike.Lib.HelloStep1RI.post_step1RI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms post_step1RI

/-- info: 'Spike.Lib.HelloStep1RI.post_step1RIX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms post_step1RIX

end Spike.Lib.HelloStep1RI
