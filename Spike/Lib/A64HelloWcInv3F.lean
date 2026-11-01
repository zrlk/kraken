/-
**`h1`'s statement with rodata's landing at its frames** (hello.w, AArch64): `HelloPreA.H1StmtH` asks rodata's landing
`Rd l b n` in `inv1 l b n` at the frames `[]`, but rodata is
`scc_rt_main`'s setup call, so the allocator returns under the frame `[frH c0S.env]` and `msOfA`'s `xa` asks the
landing at that frame. `H1StmtHF … fr` asks it at the frames `fr`; the clone facts are `H1StmtH`'s.

`H1StmtH` is kept as is (its users, `A64HelloHClW`, read only the clone component, which `H1StmtHF` has too; the
twins below take `H1StmtHF`).

- `H1StmtHF`: the statement at the landing's frames `fr`.
- `i3_cloneInvHF`: `i3_cloneInvH` from `H1StmtHF`.
- `land_I3aHF`: rodata's landing is in `I3` at the extended placement, at the frames `fr`.
-/
import Spike.Lib.A64HelloWcInv3

namespace Spike.Lib.HelloPreA

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (pcOf)
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (SegInvS I3)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.HelloSrc (helloSrc)

/-- **`h1` with rodata's landing at the frames `fr`** (`H1StmtH` with `[]` replaced by `fr`): for every fresh `l`
the arena places at `b` with `n` words, the segment after rodata's allocation with its invariant `inv1 l b n`,
containing rodata's landing `Rd l b n` at the frames `fr`, never at the clone. -/
def H1StmtHF (W1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) (K : State → State → Prop) (ar : Arena)
    (L0 : Lbl) (ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2)
    (L : RuntimeLayout) (Rd : WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop)
    (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) (fr : List TermRun.Frame) : Prop :=
  ∀ l b n, L0 l = none → AllocLand ar.heap ar.cells b n →
    SegInvS (W1 l b n) K helloSrc (A64ConsumerA.upd L0 l b) (ms1 l b n) (inv1 l b n) ∧
    (∀ s c, Rd l b n s c → inv1 l b n s c fr) ∧
    ∀ s c fs, inv1 l b n s c fs → pcOf s ≠ clonePcH L

section Stmt

variable {W0 : FragS isaLSE2} {K : State → State → Prop} {L0 : Lbl} {ls0 : Lsize}
  {ms0 : List TermRun.Frame → MemSide isaLSE2} {L : RuntimeLayout} {endPc : Int64} {Start inv0 : FragS isaLSE2}
  {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {ar : Arena}
  {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
  {Rd : WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
  {fr : List TermRun.Frame}
  {W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
  {ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
  {Box : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop}
  {inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}

/-- **`i3_cloneInvH` from `H1StmtHF`**: every pair of `I3` at the clone is in `CloneInvH` at its placement. -/
theorem i3_cloneInvHF (h0 : H0StmtH W0 K L0 ms0 L Start inv0) (h1 : H1StmtHF W1 K ar L0 ms1 L Rd inv1 fr)
    (h2 : H2StmtH W2 K ar L0 ms2 L endPc Box inv2)
    {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hI : I3 ar L0 ls0 inv0 inv1 inv2 lbl lsize s c fs) (hpc : pcOf s = clonePcH L) :
    CloneInvH L endPc lbl s c fs := by
  rcases hI with ⟨-, -, hi⟩ | ⟨l, b, n, hl, hb, -, -, hi⟩ | ⟨l, b, n, l', b', n', hl, hb, hl', hb', rfl, -, hi⟩
  · exact absurd hpc (h0.2.2 s c fs hi)
  · exact absurd hpc ((h1 l b n hl hb).2.2 s c fs hi)
  · exact (h2 l b n l' b' n' hl hb hl' hb').2.2 s c fs hi hpc

/-- **Rodata's landing is in `I3`** at the extended placement, at the frames `fr` (`msOfA`'s `xa` at `fr`). -/
theorem land_I3aHF (h1 : H1StmtHF W1 K ar L0 ms1 L Rd inv1 fr) {l : WeakMem.AllocLabel} {b n : Nat} {s : State}
    {c : Ctl} (hl : L0 l = none) (hb : AllocLand ar.heap ar.cells b n) (hR : Rd l b n s c) :
    I3 ar L0 ls0 inv0 inv1 inv2 (A64ConsumerA.upd L0 l b) (A64ConsumerA.updN ls0 l n) s c fr :=
  Spike.Lib.A64ConsumerA.land_I3a hl hb ((h1 l b n hl hb).2.1 s c hR)

end Stmt

end Spike.Lib.HelloPreA

/-- info: 'Spike.Lib.HelloPreA.i3_cloneInvHF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloPreA.i3_cloneInvHF

/-- info: 'Spike.Lib.HelloPreA.land_I3aHF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloPreA.land_I3aHF
