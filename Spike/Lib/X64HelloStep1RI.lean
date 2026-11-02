/-
**hello.w on x86-64: `post_step1` under the run invariant, assembled** (the twin of
`Spike/Lib/HelloStep1RI.lean`; `X64HelloAssembly.HelloRowsW.post_step1`, whose shape reads
`X64WakeRunInv.RunInv` for the worker's `write`'s private keys): `X64HelloStep1.post_step1H` with its three parts
discharged by the print and emit phases' rows, and `PrivAt` by `X64HelloStep1.privAt_of_runInv`.

- `PrintStep1`: `X64HelloStep1D.printStep1_of`, its kernel system calls by `X64HelloStep1Sys.sysStepP_of` (the
  abort phase's `exit_group` at an abort site, `AbExit`), its promises by `X64HelloProm1.post_prom1H`,
  `PrintWr0` by `X64HelloStep1D.printWr0_of`.
- `EmitStep1`: `X64HelloEmitW1.emitStep1_of` with `write1StepE_of`, the returns by `emitRetP_of`; `print`'s
  `write` (`Write1StepP`, the system call row's input) by `write1StepP_of`.
- `StoreWr0`: `X64HelloStep1.storeWr0_of`.

- `post_step1RI`: `HelloRowsW.post_step1`'s shape from `HelloCompat` and the instance's side facts (`hms`,
  `hown`, `hKR`, `hml`, `hAbX`, `hlbl`, `hfz`, `hbo`, `hES`, `hNP`) at an entry `E` with `E.clear Λ`.

## Unlike AArch64

- The promise-freedom premise `hNP` is at `Arch.tso` (AArch64 `Arch.armv8`) and the instruction set `isa`.
- AArch64's `post_step1RIX` (at the abort phase `Worker.AbW exe`) is dead and not twinned.
-/
import Spike.Lib.X64HelloStep1
import Spike.Lib.X64HelloProm1
import Spike.Lib.X64HelloEmitW1
import Spike.Lib.X64HelloOwn1

namespace Spike.Lib.X64HelloStep1RI

open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloW1 (WSideH)
open Spike.Lib.X64HelloAssembly (HelloCompat)
open Spike.Lib.X64HelloKRE (KRHE)
open Spike.Lib.X64HelloEmitShapeF (EmitShapeF)
open Spike.Lib.X64HelloEmitStep (ByteFrz)
open Spike.Lib.X64HelloByteOutP (ByteOutP)

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {Q : WakeRel} {μ : Marks} {D : WSideH Q.ι}
  {M : X64WakeM0.MSide Q.ι} {AbW : isa.State → Prop} {hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0}
  {hem : X64HelloW1Store.NoWrite D} {r0 r1 : Q.ι → Range}

/-- **A step of the worker after the spawn keeps `Post`, under the run invariant** (`HelloRowsW.post_step1`'s
shape): `post_step1H` with `PrintStep1` by `printStep1_of`, `EmitStep1` by `emitStep1_of`, `StoreWr0` by
`storeWr0_of`; `PrivAt` from `RunInv` at a clear entry. -/
theorem post_step1RI (hC : HelloCompat Q D M μ Λ arch AbW hcw hem) (hwf : Λ.WF)
    (hms : ∀ w fs, D.ms w fs = D.ms w []) (hown : X64HelloOwn1.Own1H Q D Λ) (hKR : Q.KR = KRHE D r0 r1)
    (hml : ∀ t s, Q.Post Λ t s → t.2.exited = none → SrcSem.mainExit s = [])
    (hAbX : X64HelloStep1Sys.AbExit D μ AbW) (hlbl : ∀ w, D.lbl w = (Q.SR w).lbl) (hfz : ByteFrz Q D Λ)
    (hbo : ∀ w fs, (D.ms w fs).bo = ByteOutP helloSrc (D.lbl w)) (hES : EmitShapeF D)
    (hNP : ∀ w x (t : Thread isa) mem, (Q.P w).noProm t.st →
      CertOkC Arch.tso (certSem abi Arch.tso μ x 1) 1 t mem → t.prom = [])
    {E : Entry} (hE : E.clear Λ = true) :
    ∀ t es t' s, Q.Post Λ t s → X64WakeRunInv.RunInv Λ E t → ¬ Q.atUnpk t s → ¬ Q.atTexit t s →
      (machine (kernel 2)).Step μ 1 t es t' →
      ∃ s', (srcS helloSrc arch).Run s (obs es) s' ∧ Q.Post Λ t' s' := by
  have hpt1 := hC.1.pt1
  have hRet := X64HelloEmitW1.emitRetP_of hC.1 hKR hpt1 hES hown hNP
  have hw1 := X64HelloEmitW1.write1StepP_of hC.1 hKR hpt1 hlbl hfz hown hbo hES hRet
  have hpe := X64HelloEmitW1.emitStep1_of hpt1
    (X64HelloEmitW1.write1StepE_of hC.1 hKR hpt1 hlbl hfz hown hbo hES hRet) hml
  have hpr := X64HelloStep1D.printStep1_of hC hwf hms hown hml
    (X64HelloStep1Sys.sysStepP_of hC hms hown hKR hAbX hw1) (X64HelloProm1.post_prom1H hC hwf hms hown hKR)
    (X64HelloStep1D.printWr0_of hKR)
  intro t es t' s hP hri
  exact X64HelloStep1.post_step1H hwf hpr hpe (X64HelloStep1.storeWr0_of hKR hC) hC t es t' s hP
    (X64HelloStep1.privAt_of_runInv hE hri)

/-- info: 'Spike.Lib.X64HelloStep1RI.post_step1RI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms post_step1RI

end Spike.Lib.X64HelloStep1RI
