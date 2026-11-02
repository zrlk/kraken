/-
**hello.w on x86-64: `h1`'s invariant as a greatest fixed point** (the twin of
`Spike/Lib/A64HelloH1Gfp.lean`; wake's `X64WakeH1Inv` for `H1StmtHF`, generic in `h1`'s fragment `W1` and its
per-state facts `X`).

- `inv1G W1 X K L0 ms1`: the greatest closed invariant inside `W1 ∧ X`
  (`X64SegWPub.GfpSP`).
- `segInvSP_inv1G`: it is a segment inside `W1`; `x_of_inv1G`: its pairs
  hold `X`.
- `inv1G_of_segWSP`, `inv1G_of_segWS`: the start of a segment inside
  `W1 ∧ X` with no exit is in it (how the landing gets in).
- `h1StmtHF_of`: `H1StmtHF` at `inv1G`, given `X` off the clone's pc and
  the landing `Rd` in `inv1G` at the frames `fr`; `h1StmtHF_of_segWS`: the
  landing given as a segment inside `W1 ∧ X` from `Rd` at `fr` with no exit
  (`h1StmtHF_of_segWSP`: as a `SegWSP`).

## Differences from the AArch64 version

- Over x86-64's `isa`, `X64ConsumerA`, `X64HelloSrc.helloSrc` and `X64HelloPreA`'s `H1StmtHF`, `clonePcH`.
- The invariant is `X64SegWPub.GfpSP` (rows may start after the source's publication: rodata publishes its buffer
  inside `h1`'s segment and x86-64 has no fence instruction to carry it), so `segInvS_inv1G` is
  `segInvSP_inv1G` (with `SegInvSP.weakW`), and the landing may be given as a `SegWSP` (`inv1G_of_segWSP`,
  `h1StmtHF_of_segWSP`); a `SegWS` gives one by `SegWS.toP`. The statements are otherwise the AArch64 ones.
-/
import Spike.Lib.X64HelloWcInv3F

namespace Spike.Lib.X64HelloPreA.H1Gfp

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (pcOf)
open Spike.Lib
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl)
open Spike.Lib.X64SegWPub (SegInvSP SegWSP GfpSP)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.X64HelloSrc (helloSrc)

variable {W1 X : WeakMem.AllocLabel → Nat → Nat → FragS isa} {K : State → State → Prop} {ar : Arena} {L0 : Lbl}
  {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa} {L : RuntimeLayout}
  {Rd : WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop} {fr : List TermRun.Frame}

/-- **`h1`'s invariant**: the greatest closed invariant inside `W1 ∧ X`. -/
def inv1G (W1 X : WeakMem.AllocLabel → Nat → Nat → FragS isa) (K : State → State → Prop) (L0 : Lbl)
    (ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa) :
    WeakMem.AllocLabel → Nat → Nat → FragS isa := fun l b n =>
  GfpSP (fun s c fs => W1 l b n s c fs ∧ X l b n s c fs) K helloSrc (X64ConsumerA.upd L0 l b) (ms1 l b n)

/-- **`inv1G` is a segment inside `W1`.** -/
theorem segInvSP_inv1G (l : WeakMem.AllocLabel) (b n : Nat) :
    SegInvSP (W1 l b n) K helloSrc (X64ConsumerA.upd L0 l b) (ms1 l b n) (inv1G W1 X K L0 ms1 l b n) :=
  X64SegWPub.SegInvSP.weakW X64SegWPub.segInvSP_gfpSP fun _ _ _ h => h.1

/-- **`X` at `inv1G`'s pairs.** -/
theorem x_of_inv1G {l : WeakMem.AllocLabel} {b n : Nat} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (h : inv1G W1 X K L0 ms1 l b n s c fs) : X l b n s c fs :=
  (X64SegWPub.segInvSP_gfpSP s c fs h).1.2

/-- **The start of a segment inside `W1 ∧ X` with no exit is in `inv1G`**
(`gfpSP_of_segWSP`). -/
theorem inv1G_of_segWSP {l : WeakMem.AllocLabel} {b n : Nat} {P : FragS isa}
    (h : SegWSP (fun s c fs => W1 l b n s c fs ∧ X l b n s c fs) K helloSrc (X64ConsumerA.upd L0 l b)
      (ms1 l b n) P (fun _ _ _ => False)) :
    ∀ s c fs, P s c fs → inv1G W1 X K L0 ms1 l b n s c fs :=
  X64SegWPub.gfpSP_of_segWSP h

/-- `inv1G_of_segWSP` from a `SegWS`. -/
theorem inv1G_of_segWS {l : WeakMem.AllocLabel} {b n : Nat} {P : FragS isa}
    (h : SegWS (fun s c fs => W1 l b n s c fs ∧ X l b n s c fs) K helloSrc (X64ConsumerA.upd L0 l b)
      (ms1 l b n) P (fun _ _ _ => False)) :
    ∀ s c fs, P s c fs → inv1G W1 X K L0 ms1 l b n s c fs :=
  inv1G_of_segWSP h.toP

/-- **`H1StmtHF` at `inv1G`**, given `X` off the clone's pc and the landing
`Rd` in `inv1G` at the frames `fr`. -/
theorem h1StmtHF_of (hX : ∀ l b n s c fs, X l b n s c fs → pcOf s ≠ clonePcH L)
    (hB : ∀ l b n, L0 l = none → AllocLand ar.heap ar.cells b n →
      ∀ s c, Rd l b n s c → inv1G W1 X K L0 ms1 l b n s c fr) :
    H1StmtHF W1 K ar L0 ms1 L Rd (inv1G W1 X K L0 ms1) fr :=
  fun l b n hl hb => ⟨segInvSP_inv1G l b n, hB l b n hl hb, fun s c fs h => hX l b n s c fs (x_of_inv1G h)⟩

/-- **`H1StmtHF` at `inv1G`**, the landing a segment inside `W1 ∧ X` from
`Rd` at `fr` with no exit. -/
theorem h1StmtHF_of_segWS (hX : ∀ l b n s c fs, X l b n s c fs → pcOf s ≠ clonePcH L)
    (hB : ∀ l b n, L0 l = none → AllocLand ar.heap ar.cells b n →
      SegWS (fun s c fs => W1 l b n s c fs ∧ X l b n s c fs) K helloSrc (X64ConsumerA.upd L0 l b)
        (ms1 l b n) (Frag.at (Rd l b n) fr) (fun _ _ _ => False)) :
    H1StmtHF W1 K ar L0 ms1 L Rd (inv1G W1 X K L0 ms1) fr :=
  h1StmtHF_of hX fun l b n hl hb s c hR => inv1G_of_segWS (hB l b n hl hb) s c fr ⟨hR, rfl⟩

/-- **`H1StmtHF` at `inv1G`**, the landing a `SegWSP` inside `W1 ∧ X` from
`Rd` at `fr` with no exit. -/
theorem h1StmtHF_of_segWSP (hX : ∀ l b n s c fs, X l b n s c fs → pcOf s ≠ clonePcH L)
    (hB : ∀ l b n, L0 l = none → AllocLand ar.heap ar.cells b n →
      SegWSP (fun s c fs => W1 l b n s c fs ∧ X l b n s c fs) K helloSrc (X64ConsumerA.upd L0 l b)
        (ms1 l b n) (Frag.at (Rd l b n) fr) (fun _ _ _ => False)) :
    H1StmtHF W1 K ar L0 ms1 L Rd (inv1G W1 X K L0 ms1) fr :=
  h1StmtHF_of hX fun l b n hl hb s c hR => inv1G_of_segWSP (hB l b n hl hb) s c fr ⟨hR, rfl⟩

end Spike.Lib.X64HelloPreA.H1Gfp

/-- info: 'Spike.Lib.X64HelloPreA.H1Gfp.segInvSP_inv1G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloPreA.H1Gfp.segInvSP_inv1G

/-- info: 'Spike.Lib.X64HelloPreA.H1Gfp.x_of_inv1G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloPreA.H1Gfp.x_of_inv1G

/-- info: 'Spike.Lib.X64HelloPreA.H1Gfp.inv1G_of_segWS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloPreA.H1Gfp.inv1G_of_segWS

/-- info: 'Spike.Lib.X64HelloPreA.H1Gfp.h1StmtHF_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloPreA.H1Gfp.h1StmtHF_of

/--
info: 'Spike.Lib.X64HelloPreA.H1Gfp.h1StmtHF_of_segWS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64HelloPreA.H1Gfp.h1StmtHF_of_segWS
/-- info: 'Spike.Lib.X64HelloPreA.H1Gfp.inv1G_of_segWSP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloPreA.H1Gfp.inv1G_of_segWSP

/--
info: 'Spike.Lib.X64HelloPreA.H1Gfp.h1StmtHF_of_segWSP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64HelloPreA.H1Gfp.h1StmtHF_of_segWSP
