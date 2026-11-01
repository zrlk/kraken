/-
**hello.w on AArch64: `h1`'s invariant as a greatest fixed point** (the
twin of wake's `A64WakeH1Inv` for `H1StmtHF`, generic in `h1`'s fragment
`W1` and its per-state facts `X`).

- `inv1G W1 X K L0 ms1`: the greatest closed invariant inside `W1 ∧ X`
  (`A64GfpS.GfpS`).
- `segInvS_inv1G`: it is a segment inside `W1`; `x_of_inv1G`: its pairs
  hold `X`.
- `inv1G_of_segWS`: the start of a segment inside `W1 ∧ X` with no exit is
  in it (how the landing gets in).
- `h1StmtHF_of`: `H1StmtHF` at `inv1G`, given `X` off the clone's pc and
  the landing `Rd` in `inv1G` at the frames `fr`; `h1StmtHF_of_segWS`: the
  landing given as a segment inside `W1 ∧ X` from `Rd` at `fr` with no exit.
-/
import Spike.Lib.A64HelloWcInv3F
import Spike.Lib.A64GfpS
import Spike.Lib.A64WakeH1Inv

namespace Spike.Lib.HelloPreA.H1Gfp

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (pcOf)
open Spike.Lib
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl)
open Spike.Lib.A64ConsumerA (SegInvS)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.A64GfpS (GfpS)

variable {W1 X : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {K : State → State → Prop} {ar : Arena} {L0 : Lbl}
  {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2} {L : RuntimeLayout}
  {Rd : WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop} {fr : List TermRun.Frame}

/-- **`h1`'s invariant**: the greatest closed invariant inside `W1 ∧ X`. -/
def inv1G (W1 X : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) (K : State → State → Prop) (L0 : Lbl)
    (ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2) :
    WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2 := fun l b n =>
  GfpS (fun s c fs => W1 l b n s c fs ∧ X l b n s c fs) K helloSrc (A64ConsumerA.upd L0 l b) (ms1 l b n)

/-- **`inv1G` is a segment inside `W1`.** -/
theorem segInvS_inv1G (l : WeakMem.AllocLabel) (b n : Nat) :
    SegInvS (W1 l b n) K helloSrc (A64ConsumerA.upd L0 l b) (ms1 l b n) (inv1G W1 X K L0 ms1 l b n) :=
  WakeH1Inv.segInvS_weakW A64GfpS.segInvS_gfpS fun _ _ _ h => h.1

/-- **`X` at `inv1G`'s pairs.** -/
theorem x_of_inv1G {l : WeakMem.AllocLabel} {b n : Nat} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (h : inv1G W1 X K L0 ms1 l b n s c fs) : X l b n s c fs :=
  (A64GfpS.segInvS_gfpS s c fs h).1.2

/-- **The start of a segment inside `W1 ∧ X` with no exit is in `inv1G`**
(`gfpS_of_segWS`). -/
theorem inv1G_of_segWS {l : WeakMem.AllocLabel} {b n : Nat} {P : FragS isaLSE2}
    (h : SegWS (fun s c fs => W1 l b n s c fs ∧ X l b n s c fs) K helloSrc (A64ConsumerA.upd L0 l b)
      (ms1 l b n) P (fun _ _ _ => False)) :
    ∀ s c fs, P s c fs → inv1G W1 X K L0 ms1 l b n s c fs :=
  A64GfpS.gfpS_of_segWS h

/-- **`H1StmtHF` at `inv1G`**, given `X` off the clone's pc and the landing
`Rd` in `inv1G` at the frames `fr`. -/
theorem h1StmtHF_of (hX : ∀ l b n s c fs, X l b n s c fs → pcOf s ≠ clonePcH L)
    (hB : ∀ l b n, L0 l = none → AllocLand ar.heap ar.cells b n →
      ∀ s c, Rd l b n s c → inv1G W1 X K L0 ms1 l b n s c fr) :
    H1StmtHF W1 K ar L0 ms1 L Rd (inv1G W1 X K L0 ms1) fr :=
  fun l b n hl hb => ⟨segInvS_inv1G l b n, hB l b n hl hb, fun s c fs h => hX l b n s c fs (x_of_inv1G h)⟩

/-- **`H1StmtHF` at `inv1G`**, the landing a segment inside `W1 ∧ X` from
`Rd` at `fr` with no exit. -/
theorem h1StmtHF_of_segWS (hX : ∀ l b n s c fs, X l b n s c fs → pcOf s ≠ clonePcH L)
    (hB : ∀ l b n, L0 l = none → AllocLand ar.heap ar.cells b n →
      SegWS (fun s c fs => W1 l b n s c fs ∧ X l b n s c fs) K helloSrc (A64ConsumerA.upd L0 l b)
        (ms1 l b n) (Frag.at (Rd l b n) fr) (fun _ _ _ => False)) :
    H1StmtHF W1 K ar L0 ms1 L Rd (inv1G W1 X K L0 ms1) fr :=
  h1StmtHF_of hX fun l b n hl hb s c hR => inv1G_of_segWS (hB l b n hl hb) s c fr ⟨hR, rfl⟩

end Spike.Lib.HelloPreA.H1Gfp

/-- info: 'Spike.Lib.HelloPreA.H1Gfp.segInvS_inv1G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloPreA.H1Gfp.segInvS_inv1G

/-- info: 'Spike.Lib.HelloPreA.H1Gfp.x_of_inv1G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloPreA.H1Gfp.x_of_inv1G

/-- info: 'Spike.Lib.HelloPreA.H1Gfp.inv1G_of_segWS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloPreA.H1Gfp.inv1G_of_segWS

/-- info: 'Spike.Lib.HelloPreA.H1Gfp.h1StmtHF_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloPreA.H1Gfp.h1StmtHF_of

/--
info: 'Spike.Lib.HelloPreA.H1Gfp.h1StmtHF_of_segWS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.HelloPreA.H1Gfp.h1StmtHF_of_segWS
