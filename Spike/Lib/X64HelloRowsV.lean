/-
**hello.w on x86-64: `HelloRowsW` with `hconv` discharged**: the
open obligations other than `hconv` (`HelloRowsWV`), and `HelloRowsW` from them by
`X64HelloConv1.hconvH` at hello's `PT0`/`KR` (`hPT0`, `hKR`), the link's
well-formedness (`hwf`), a frame-independent memory side (`hms`) and the
worker's `RelW1` (`hW1`).

- `HelloRowsWV`: `HelloRowsW`'s fields other than `hconv`.
- `HelloRowsWV.toW`: `HelloRowsW` with `hconv := hconvH …`.

x86-64 twin of `Spike/Lib/HelloRowsV.lean` (same names, namespaces with the `X64` prefix).
Unlike AArch64, the program is an `asm : Asm` (as in `X64HelloAssembly`).
-/
import Spike.Lib.X64HelloAssembly
import Spike.Lib.X64HelloConv1

namespace Spike.Lib.X64HelloRowsV

open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakePreTi Spike.Lib.Handover
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloW1 (WSideH)
open Spike.Lib.X64HelloW1Store (NoWrite)
open Spike.Lib.X64HelloAssembly (HelloCompat HelloRowsW)
open Spike.Lib.X64HelloKRE (KRHE)
open Spike.Lib.X64HelloWriteK (KRH)

/-- **The open obligations of `HelloRowsW` other than `hconv`** (the fields
as there). -/
structure HelloRowsWV (arch : WeakMem.Arch) (Λ : Scc.Sem.Layout) (B : Budget) (asm : Asm) (Q : WakeRel)
    (E : Entry) (D : WSideH Q.ι) (M : X64WakeM0.MSide Q.ι) (AbW : isa.State → Prop)
    (hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0) (hem : NoWrite D) (Ab Ac : State → Prop)
    (Tw : Cfg → List Ev → Prop) : Prop where
  /-- As `HelloRowsW.post_step1`. -/
  post_step1 : HelloCompat Q D M ((target (kernel 2) E).marks asm Λ) Λ arch AbW hcw hem →
    ∀ t es t' s, Q.Post Λ t s → X64WakeRunInv.RunInv Λ E t → ¬ Q.atUnpk t s → ¬ Q.atTexit t s →
      (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) 1 t es t' →
      ∃ s', (srcS helloSrc arch).Run s (obs es) s' ∧ Q.Post Λ t' s'
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

/-- **`HelloRowsW` from the other obligations, `hconv` by `X64HelloConv1.hconvH`.** -/
theorem HelloRowsWV.toW (R : HelloRowsWV arch Λ B asm Q E D M AbW hcw hem Ab Ac Tw) (hwf : Λ.WF)
    (hms : ∀ w fs, D.ms w fs = D.ms w []) (hown : X64HelloOwn1.Own1H Q D Λ) (hPT0 : Q.PT0 = X64WakeM0.PT0 M)
    (hKR : Q.KR = KRHE D r0 r1) (hW1 : ∀ w s c fs e, D.Wi w s c fs → isa.exec s = some e → EvTree.RelW1 Arch.tso e) :
    HelloRowsW arch Λ B asm Q E D M AbW hcw hem Ab Ac Tw where
  post_step1 := R.post_step1
  hconv := fun hC => X64HelloConv1.hconvH hC hwf hms hown hPT0 hKR hW1
  post_abort := R.post_abort
  post_wit := R.post_wit
  tw_load := R.tw_load
  tw_step := R.tw_step

/-- info: 'Spike.Lib.X64HelloRowsV.HelloRowsWV.toW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HelloRowsWV.toW

end Spike.Lib.X64HelloRowsV
