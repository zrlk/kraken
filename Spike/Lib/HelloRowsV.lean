/-
**hello.w: `HelloRowsW` with `hconv` discharged** (row B8-genV wired): the
open rows other than `hconv` (`HelloRowsWV`), and `HelloRowsW` from them by
`HelloConv1.hconvH` at hello's `PT0`/`KR` (`hPT0`, `hKR`), the link's
well-formedness (`hwf`), a frame-independent memory side (`hms`) and the
worker's `RelW1` (`hW1`, row B8-genV-hW1).

- `HelloRowsWV`: `HelloRowsW`'s fields other than `hconv`.
- `HelloRowsWV.toW`: `HelloRowsW` with `hconv := hconvH …`.
-/
import Spike.Lib.HelloAssembly
import Spike.Lib.HelloConv1

namespace Spike.Lib.HelloRowsV

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakePreTi Spike.Lib.Handover
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloW1 (WSideH)
open Spike.Lib.HelloW1Store (NoWrite)
open Spike.Lib.HelloAssembly (HelloCompat HelloRowsW)
open Spike.Lib.HelloKRE (KRHE)
open Spike.Lib.A64HelloWriteK (KRH)

/-- **The open rows of `HelloRowsW` other than `hconv`** (the fields and
rows as there). -/
structure HelloRowsWV (arch : WeakMem.Arch) (Λ : Scc.Sem.Layout) (B : Budget) (asm : String) (Q : WakeRel)
    (E : Entry) (D : WSideH Q.ι) (M : WakeM0.MSide Q.ι) (AbW : isaLSE2.State → Prop)
    (hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0) (hem : NoWrite D) (Ab Ac : State → Prop)
    (Tw : Cfg → List Ev → Prop) : Prop where
  /-- row: B8-gen1 (as `HelloRowsW.post_step1`). -/
  post_step1 : HelloCompat Q D M ((target (kernel 2) E).marks asm Λ) Λ arch AbW hcw hem →
    ∀ t es t' s, Q.Post Λ t s → WakeRunInv.RunInv Λ E t → ¬ Q.atUnpk t s → ¬ Q.atTexit t s →
      (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) 1 t es t' →
      ∃ s', (srcS helloSrc arch).Run s (obs es) s' ∧ Q.Post Λ t' s'
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

/-- **`HelloRowsW` from the other rows, `hconv` by `HelloConv1.hconvH`.** -/
theorem HelloRowsWV.toW (R : HelloRowsWV arch Λ B asm Q E D M AbW hcw hem Ab Ac Tw) (hwf : Λ.WF)
    (hms : ∀ w fs, D.ms w fs = D.ms w []) (hPT0 : Q.PT0 = WakeM0.PT0 M) (hKR : Q.KR = KRHE D r0 r1)
    (hW1 : ∀ w s c fs e, D.Wi w s c fs → isaLSE2.exec s = some e → EvTree.RelW1 Arch.armv8 e) :
    HelloRowsW arch Λ B asm Q E D M AbW hcw hem Ab Ac Tw where
  post_step1 := R.post_step1
  hconv := fun hC => HelloConv1.hconvH hC hwf hms hPT0 hKR hW1
  post_abort := R.post_abort
  post_wit := R.post_wit
  tw_load := R.tw_load
  tw_step := R.tw_step

/-- info: 'Spike.Lib.HelloRowsV.HelloRowsWV.toW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HelloRowsWV.toW

end Spike.Lib.HelloRowsV
