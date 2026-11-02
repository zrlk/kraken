/-
**`h1`'s statement with rodata's landing at its frames, on x86-64** (the twin of
`Spike/Lib/A64HelloWcInv3F.lean`): `X64HelloPreA.H1StmtH` asks rodata's landing `Rd l b n` in `inv1 l b n` at the
frames `[]`, but rodata is `scc_rt_main`'s setup call, so the allocator returns under a non-empty frame list and
`msOfA`'s `xa` asks the landing at that frame. `H1StmtHF … fr` asks it at the frames `fr`; the clone facts are
`H1StmtH`'s.

- `H1StmtHF`: the statement at the landing's frames `fr`.
- `land_I3aHF`: rodata's landing is in `I3` at the extended placement, at the frames `fr`.

## Differences from the AArch64 version

- Over x86-64's `X64ConsumerA` (`SegInvS`, `I3`, `upd`, `updN`, `land_I3a`) and `X64HelloSrc.helloSrc`.
- The segment is a `SegInvSP` (rows may start after the source's publication), as `H1StmtH`'s.
- A64's `i3_cloneInvHF` is dead and not twinned.
-/
import Spike.Lib.X64HelloWcInv3

namespace Spike.Lib.X64HelloPreA

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (pcOf)
open Spike.Lib Spike.Lib.X64.Flow
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (SegInvS I3)
open Spike.Lib.X64SegWPub (SegInvSP)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.X64HelloSrc (helloSrc)

/-- **`h1` with rodata's landing at the frames `fr`** (`H1StmtH` with `[]` replaced by `fr`): for every fresh `l`
the arena places at `b` with `n` words, the segment after rodata's allocation with its invariant `inv1 l b n`,
containing rodata's landing `Rd l b n` at the frames `fr`, never at the clone. -/
def H1StmtHF (W1 : WeakMem.AllocLabel → Nat → Nat → FragS isa) (K : State → State → Prop) (ar : Arena)
    (L0 : Lbl) (ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa)
    (L : RuntimeLayout) (Rd : WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop)
    (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa) (fr : List TermRun.Frame) : Prop :=
  ∀ l b n, L0 l = none → AllocLand ar.heap ar.cells b n →
    SegInvSP (W1 l b n) K helloSrc (X64ConsumerA.upd L0 l b) (ms1 l b n) (inv1 l b n) ∧
    (∀ s c, Rd l b n s c → inv1 l b n s c fr) ∧
    ∀ s c fs, inv1 l b n s c fs → pcOf s ≠ clonePcH L

section Stmt

variable {K : State → State → Prop} {L0 : Lbl} {ls0 : Lsize} {L : RuntimeLayout} {inv0 : FragS isa}
  {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {ar : Arena}
  {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
  {Rd : WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
  {fr : List TermRun.Frame}
  {inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}

/-- **Rodata's landing is in `I3`** at the extended placement, at the frames `fr` (`msOfA`'s `xa` at `fr`). -/
theorem land_I3aHF (h1 : H1StmtHF W1 K ar L0 ms1 L Rd inv1 fr) {l : WeakMem.AllocLabel} {b n : Nat} {s : State}
    {c : Ctl} (hl : L0 l = none) (hb : AllocLand ar.heap ar.cells b n) (hR : Rd l b n s c) :
    I3 ar L0 ls0 inv0 inv1 inv2 (X64ConsumerA.upd L0 l b) (X64ConsumerA.updN ls0 l n) s c fr :=
  Spike.Lib.X64ConsumerA.land_I3a hl hb ((h1 l b n hl hb).2.1 s c hR)

end Stmt

end Spike.Lib.X64HelloPreA

/-- info: 'Spike.Lib.X64HelloPreA.land_I3aHF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloPreA.land_I3aHF
