/-
**hello.w on x86-64: `HelloRowsWV` with `post_step1` discharged** (the twin of `Spike/Lib/HelloRowsV1.lean`): the
open rows other than `hconv` and `post_step1` (`HelloRowsW1`), and `HelloRowsWV` from them by
`X64HelloStep1RI.post_step1RI` at hello's `KR` (`hKR`), the link's well-formedness (`hwf`), a clear entry (`hE`)
and the worker side's facts read by the print and emit phases' rows (`hms`, `hown`, `hml`, `hAbX`, `hlbl`, `hfz`,
`hbo`, `hES`, `hNP`).

- `HelloRowsW1`: `HelloRowsWV`'s fields other than `post_step1`.
- `HelloRowsW1.toWV`: `HelloRowsWV` with `post_step1 := post_step1RI …`.
- `HelloRowsW1.toW`: `HelloRowsW`, through `HelloRowsWV.toW` (`hconv`).

## Unlike AArch64

- The program is an `asm : Asm` (as in `X64HelloAssembly`), the instruction set `isa`, and the promise-freedom
  premise `hNP` and the worker's `RelW1` (`hW1`) are at `Arch.tso` (AArch64 `Arch.armv8`).
-/
import Spike.Lib.X64HelloRowsV
import Spike.Lib.X64HelloStep1RI
import Spike.Lib.X64HelloOwn1

namespace Spike.Lib.X64HelloRowsV1

open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakePreTi Spike.Lib.Handover
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloW1 (WSideH)
open Spike.Lib.X64HelloW1Store (NoWrite)
open Spike.Lib.X64HelloAssembly (HelloCompat HelloRowsW)
open Spike.Lib.X64HelloRowsV (HelloRowsWV)
open Spike.Lib.X64HelloKRE (KRHE)
open Spike.Lib.X64HelloEmitShapeF (EmitShapeF)
open Spike.Lib.X64HelloEmitStep (ByteFrz)
open Spike.Lib.X64HelloByteOutP (ByteOutP)

/-- **The open rows of `HelloRowsWV` other than `post_step1`** (the fields and rows as there). -/
structure HelloRowsW1 (arch : WeakMem.Arch) (Λ : Scc.Sem.Layout) (B : Budget) (asm : Asm) (Q : WakeRel)
    (E : Entry) (D : WSideH Q.ι) (M : X64WakeM0.MSide Q.ι) (AbW : isa.State → Prop)
    (hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0) (hem : NoWrite D) (Ab Ac : State → Prop)
    (Tw : Cfg → List Ev → Prop) : Prop where
  /-- As `HelloRowsW.post_abort`. -/
  post_abort : HelloCompat Q D M ((target (kernel 2) E).marks asm Λ) Λ arch AbW hcw hem →
    ∀ tr t s tid es t' k, (srcS helloSrc arch).Reach (obs tr) s → Q.Post Λ t s →
      TiPre Ab Ac t tr ∧ Tw t tr →
      (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) tid t es t' → Ev.abort k ∈ es →
      ∃ w i, Components (machine (kernel 2)) Λ w t s ∧ w.thr i = some tid ∧
        AbortJustified B (srcS helloSrc arch) tr s i k
  /-- As `HelloRowsW.post_wit`. -/
  post_wit : ∀ t s, Q.Post Λ t s → X64WakeRunInv.RunInv Λ E t → ∃ w, Components (machine (kernel 2)) Λ w t s
  /-- As `HelloRowsW.tw_load`. -/
  tw_load : ∀ t0, (target (kernel 2) E).load asm Λ = some t0 → Tw t0 []
  /-- As `HelloRowsW.tw_step`. -/
  tw_step : HelloCompat Q D M ((target (kernel 2) E).marks asm Λ) Λ arch AbW hcw hem →
    ∀ tid t es t' s pre, Q.Rw Λ t s →
    (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) tid t es t' → Tw t pre → Tw t' (pre ++ es)

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : Asm} {Q : WakeRel} {E : Entry}
  {D : WSideH Q.ι} {M : X64WakeM0.MSide Q.ι} {r0 r1 : Q.ι → Range} {AbW : isa.State → Prop}
  {hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0} {hem : NoWrite D} {Ab Ac : State → Prop}
  {Tw : Cfg → List Ev → Prop}

/-- **`HelloRowsWV` from the other rows, `post_step1` by `X64HelloStep1RI.post_step1RI`** (at the target's
marks). -/
theorem HelloRowsW1.toWV (R : HelloRowsW1 arch Λ B asm Q E D M AbW hcw hem Ab Ac Tw) (hwf : Λ.WF)
    (hE : E.clear Λ = true) (hms : ∀ w fs, D.ms w fs = D.ms w []) (hown : X64HelloOwn1.Own1H Q D Λ)
    (hKR : Q.KR = KRHE D r0 r1) (hml : ∀ t s, Q.Post Λ t s → t.2.exited = none → SrcSem.mainExit s = [])
    (hAbX : X64HelloStep1Sys.AbExit D ((target (kernel 2) E).marks asm Λ) AbW)
    (hlbl : ∀ w, D.lbl w = (Q.SR w).lbl) (hfz : ByteFrz Q D Λ)
    (hbo : ∀ w fs, (D.ms w fs).bo = ByteOutP helloSrc (D.lbl w)) (hES : EmitShapeF D)
    (hNP : ∀ w x (t : Thread isa) mem, (Q.P w).noProm t.st →
      CertOkC Arch.tso (certSem abi Arch.tso ((target (kernel 2) E).marks asm Λ) x 1) 1 t mem →
        t.prom = []) :
    HelloRowsWV arch Λ B asm Q E D M AbW hcw hem Ab Ac Tw where
  post_step1 := fun hC =>
    X64HelloStep1RI.post_step1RI hC hwf hms hown hKR hml hAbX hlbl hfz hbo hES hNP hE
  post_abort := R.post_abort
  post_wit := R.post_wit
  tw_load := R.tw_load
  tw_step := R.tw_step

/-- **`HelloRowsW` from the other rows**: `HelloRowsW1.toWV`, then `HelloRowsWV.toW` (`hconv` by
`X64HelloConv1.hconvH`). -/
theorem HelloRowsW1.toW (R : HelloRowsW1 arch Λ B asm Q E D M AbW hcw hem Ab Ac Tw) (hwf : Λ.WF)
    (hE : E.clear Λ = true) (hms : ∀ w fs, D.ms w fs = D.ms w []) (hown : X64HelloOwn1.Own1H Q D Λ)
    (hPT0 : Q.PT0 = X64WakeM0.PT0 M) (hKR : Q.KR = KRHE D r0 r1)
    (hml : ∀ t s, Q.Post Λ t s → t.2.exited = none → SrcSem.mainExit s = [])
    (hAbX : X64HelloStep1Sys.AbExit D ((target (kernel 2) E).marks asm Λ) AbW)
    (hlbl : ∀ w, D.lbl w = (Q.SR w).lbl) (hfz : ByteFrz Q D Λ)
    (hbo : ∀ w fs, (D.ms w fs).bo = ByteOutP helloSrc (D.lbl w)) (hES : EmitShapeF D)
    (hNP : ∀ w x (t : Thread isa) mem, (Q.P w).noProm t.st →
      CertOkC Arch.tso (certSem abi Arch.tso ((target (kernel 2) E).marks asm Λ) x 1) 1 t mem →
        t.prom = [])
    (hW1 : ∀ w s c fs e, D.Wi w s c fs → isa.exec s = some e → EvTree.RelW1 Arch.tso e) :
    HelloRowsW arch Λ B asm Q E D M AbW hcw hem Ab Ac Tw :=
  (R.toWV hwf hE hms hown hKR hml hAbX hlbl hfz hbo hES hNP).toW hwf hms hown hPT0 hKR hW1

/-- info: 'Spike.Lib.X64HelloRowsV1.HelloRowsW1.toWV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HelloRowsW1.toWV

/-- info: 'Spike.Lib.X64HelloRowsV1.HelloRowsW1.toW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HelloRowsW1.toW

end Spike.Lib.X64HelloRowsV1
