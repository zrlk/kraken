/-
**hello.w: `HelloRowsWV` with `post_step1` discharged** (`post_step1` wired):
the open rows other than `hconv` and `post_step1` (`HelloRowsW1`), and
`HelloRowsWV` from them by `HelloStep1RI.post_step1RI` at hello's `KR`
(`hKR`), the link's well-formedness (`hwf`), a clear entry (`hE`) and the
worker side's facts read by the print and emit phases' rows (`hms`, `hown`,
`hml`, `hAbX`, `hlbl`, `hfz`, `hbo`, `hES`, `hNP`).

- `HelloRowsW1`: `HelloRowsWV`'s fields other than `post_step1`.
- `HelloRowsW1.toWV`: `HelloRowsWV` with `post_step1 := post_step1RI …`.
- `HelloRowsW1.toW`: `HelloRowsW`, through `HelloRowsWV.toW` (`hconv`).
-/
import Spike.Lib.HelloRowsV
import Spike.Lib.HelloStep1RI

namespace Spike.Lib.HelloRowsV1

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakePreTi Spike.Lib.Handover
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloW1 (WSideH)
open Spike.Lib.HelloW1Store (NoWrite)
open Spike.Lib.HelloAssembly (HelloCompat HelloRowsW)
open Spike.Lib.HelloRowsV (HelloRowsWV)
open Spike.Lib.HelloKRE (KRHE)
open Spike.Lib.HelloEmitShapeF (EmitShapeF)
open Spike.Lib.HelloEmitStep (ByteFrz)
open Spike.Lib.HelloByteOutP (ByteOutP)

/-- **The open rows of `HelloRowsWV` other than `post_step1`** (the fields
and rows as there). -/
structure HelloRowsW1 (arch : WeakMem.Arch) (Λ : Scc.Sem.Layout) (B : Budget) (asm : String) (Q : WakeRel)
    (E : Entry) (D : WSideH Q.ι) (M : WakeM0.MSide Q.ι) (AbW : isaLSE2.State → Prop)
    (hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0) (hem : NoWrite D) (Ab Ac : State → Prop)
    (Tw : Cfg → List Ev → Prop) : Prop where
  /-- row: 5i (as `HelloRowsW.post_abort`). -/
  post_abort : HelloCompat Q D M ((target (kernel 2) E).marks asm Λ) Λ arch AbW hcw hem →
    ∀ tr t s tid es t' k, (srcS helloSrc arch).Reach (obs tr) s → Q.Post Λ t s →
      TiPre Ab Ac t tr ∧ Tw t tr →
      (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) tid t es t' → Ev.abort k ∈ es →
      ∃ w i, Components (machine (kernel 2)) Λ w t s ∧ w.thr i = some tid ∧
        AbortJustified B (srcS helloSrc arch) tr s i k
  /-- row: 5j-wit (as `HelloRowsW.post_wit`). -/
  post_wit : ∀ t s, Q.Post Λ t s → WakeRunInv.RunInv Λ E t → ∃ w, Components (machine (kernel 2)) Λ w t s
  /-- row: 5i (as `HelloRowsW.tw_load`). -/
  tw_load : ∀ t0, (target (kernel 2) E).load asm Λ = some t0 → Tw t0 []
  /-- row: 5i (as `HelloRowsW.tw_step`). -/
  tw_step : HelloCompat Q D M ((target (kernel 2) E).marks asm Λ) Λ arch AbW hcw hem →
    ∀ tid t es t' s pre, Q.Rw Λ t s →
    (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) tid t es t' → Tw t pre → Tw t' (pre ++ es)

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : String} {Q : WakeRel} {E : Entry}
  {D : WSideH Q.ι} {M : WakeM0.MSide Q.ι} {r0 r1 : Q.ι → Range} {AbW : isaLSE2.State → Prop}
  {hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0} {hem : NoWrite D} {Ab Ac : State → Prop}
  {Tw : Cfg → List Ev → Prop}

/-- **`HelloRowsWV` from the other rows, `post_step1` by
`HelloStep1RI.post_step1RI`** (at the target's marks). -/
theorem HelloRowsW1.toWV (R : HelloRowsW1 arch Λ B asm Q E D M AbW hcw hem Ab Ac Tw) (hwf : Λ.WF)
    (hE : E.clear Λ = true) (hms : ∀ w fs, D.ms w fs = D.ms w []) (hown : Q.own = WakeOwn.wakeOwn)
    (hKR : Q.KR = KRHE D r0 r1) (hml : ∀ t s, Q.Post Λ t s → t.2.exited = none → SrcSem.mainExit s = [])
    (hAbX : HelloStep1Sys.AbExit D ((target (kernel 2) E).marks asm Λ) AbW)
    (hlbl : ∀ w, D.lbl w = (Q.SR w).lbl) (hfz : ByteFrz Q D Λ)
    (hbo : ∀ w fs, (D.ms w fs).bo = ByteOutP helloSrc (D.lbl w)) (hES : EmitShapeF D)
    (hNP : ∀ w x (t : Thread isaLSE2) mem, (Q.P w).noProm t.st →
      CertOkC Arch.armv8 (certSem abi Arch.armv8 ((target (kernel 2) E).marks asm Λ) x 1) 1 t mem →
        t.prom = []) :
    HelloRowsWV arch Λ B asm Q E D M AbW hcw hem Ab Ac Tw where
  post_step1 := fun hC =>
    HelloStep1RI.post_step1RI hC hwf hms hown hKR hml hAbX hlbl hfz hbo hES hNP hE
  post_abort := R.post_abort
  post_wit := R.post_wit
  tw_load := R.tw_load
  tw_step := R.tw_step

/-- **`HelloRowsW` from the other rows**: `HelloRowsW1.toWV`, then
`HelloRowsWV.toW` (`hconv` by `HelloConv1.hconvH`). -/
theorem HelloRowsW1.toW (R : HelloRowsW1 arch Λ B asm Q E D M AbW hcw hem Ab Ac Tw) (hwf : Λ.WF)
    (hE : E.clear Λ = true) (hms : ∀ w fs, D.ms w fs = D.ms w []) (hown : Q.own = WakeOwn.wakeOwn)
    (hPT0 : Q.PT0 = WakeM0.PT0 M) (hKR : Q.KR = KRHE D r0 r1)
    (hml : ∀ t s, Q.Post Λ t s → t.2.exited = none → SrcSem.mainExit s = [])
    (hAbX : HelloStep1Sys.AbExit D ((target (kernel 2) E).marks asm Λ) AbW)
    (hlbl : ∀ w, D.lbl w = (Q.SR w).lbl) (hfz : ByteFrz Q D Λ)
    (hbo : ∀ w fs, (D.ms w fs).bo = ByteOutP helloSrc (D.lbl w)) (hES : EmitShapeF D)
    (hNP : ∀ w x (t : Thread isaLSE2) mem, (Q.P w).noProm t.st →
      CertOkC Arch.armv8 (certSem abi Arch.armv8 ((target (kernel 2) E).marks asm Λ) x 1) 1 t mem →
        t.prom = [])
    (hW1 : ∀ w s c fs e, D.Wi w s c fs → isaLSE2.exec s = some e → EvTree.RelW1 Arch.armv8 e) :
    HelloRowsW arch Λ B asm Q E D M AbW hcw hem Ab Ac Tw :=
  (R.toWV hwf hE hms hown hKR hml hAbX hlbl hfz hbo hES hNP).toW hwf hms hPT0 hKR hW1

/-- info: 'Spike.Lib.HelloRowsV1.HelloRowsW1.toWV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HelloRowsW1.toWV

/-- info: 'Spike.Lib.HelloRowsV1.HelloRowsW1.toW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HelloRowsW1.toW

end Spike.Lib.HelloRowsV1
