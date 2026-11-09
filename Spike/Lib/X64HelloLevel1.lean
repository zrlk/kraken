/-
**hello's level 1 from rodata's landing, generic part** (x86-64; the twin of `Spike/Lib/A64HelloLevel1.lean`'s
live part): the allocator's landing `Ea` under `wc_rodata`'s frame `fr` (level 0's hand-off,
`StartH0H1.RdLandHg`'s shape), and the invariant at `wc_rodata`'s `.x15` its images imply.

The landing is the allocator's return past the source's `new` (`Ea ms₀ q l b w`, `ms₀` the memory side the
allocation was taken at, level 0's). Leaving the allocator's region (`StartWcS.xa_post`, `at_leave`), it is
`wc_rodata`'s `.x15` (`pN … .s0`) at an invariant `Jp` the landings imply (`hJp`).

- `LandF`: the landing at the caller's state `m0`, `σC`, under `fr` (`RdLandHg`'s body, any `ms₀`, `R`, `F`).
- `JpL`, `jpL_of`: the canonical `Jp` (the landings' images at `.x15`), for which `hJp` holds by definition.

## Differences from the AArch64 version

- `HelloRd.rN` takes `wc_rodata`'s region (`mR R`, for `%rbp`), and the allocator's call keeps `wc_rodata`'s frame
  outside the allocator's region up to `8` (`CKept (mR R) (-48) (-160) 8`; AArch64: `0`).
- The landing's image is at `.x15` (AArch64: `.sp0`).
- `land_segWS` is not twinned: it is dead in hello.
-/
import Spike.Lib.X64HelloStartWcS

namespace Spike.Lib.X64.HelloPh.Level1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib (MemSide Region)
open Spike.Lib.X64 (At enter leave CKept Abs)
open Spike.Lib.X64.Flow.Hello1 (AG mR mF aR)
open Spike.Lib.X64.Flow.HelloRd (rN)
open Spike.Lib.X64.Alloc (Ea)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

section Gen

variable {ms₀ : MemSide isa} {R : Region}

/-- **The allocator's landing under `wc_rodata`'s frame** at the caller's state `m0`, `σC` (`RdLandHg`'s body):
some call `q` at `ms₀`, a frame condition `F'` inside `wc_rodata`'s and its call context's, the landing `Ea` at
the label `l`, base `b`, words `w`. -/
def LandF (ms₀ : MemSide isa) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (J0 J1 : FAS → Ctl → Prop) (m0 : MachineData) (σC : FAS) (l : WeakMem.AllocLabel) (b w : Nat)
    (s : State) (c : Ctl) : Prop :=
  ∃ q : AG ms₀ (_root_.Executable.labels exe).label, ∃ F' : MachineData → Prop,
    (∀ m, F' m → mF R F m0 σC m) ∧
    (∀ m, F' m → ∃ mC σ c, Abs (mR R) ⟨-48, []⟩ mC σ ∧
      (rN (_root_.Executable.labels exe).label (mR R) J0 J1 .call).J σ c ∧
      (Spike.Lib.X64.Alloc.N (_root_.Executable.labels exe).label ms₀ q.1 .e).J (enter (-48) σ) c ∧
      CKept (mR R) (-48) (-160) 8 mC m) ∧
    At exe endPc (aR (mR R)) F' (Ea ms₀ q.1 l b w) s c

/-- **The landings' images at `.x15`**: `wc_rodata`'s state after leaving the allocator at a landing of `q` at
`l`, `b`, `w` (`xa_post`'s `hJp` holds for it by definition, `jpL_of`). -/
def JpL (ms₀ : MemSide isa) (lab : Label → Int64) (J0 J1 : FAS → Ctl → Prop) (l : WeakMem.AllocLabel)
    (b w : Nat) (σ' : FAS) (c : Ctl) : Prop :=
  ∃ (q : AG ms₀ lab) (σx σ : FAS) (c0 : Ctl), (Ea ms₀ q.1 l b w).J σx c ∧ (rN lab (mR R) J0 J1 .call).J σ c0 ∧
    (Spike.Lib.X64.Alloc.N lab ms₀ q.1 .e).J (enter (-48) σ) c0 ∧ σ' = leave (aR (mR R)) (-48) σ σx

/-- **`xa_post`'s `hJp` at `JpL`**. -/
theorem jpL_of {lab : Label → Int64} {J0 J1 : FAS → Ctl → Prop} {l : WeakMem.AllocLabel} {b w : Nat}
    (q : AG ms₀ lab) :
    ∀ σx σ c0 c, (Ea ms₀ q.1 l b w).J σx c → (rN lab (mR R) J0 J1 .call).J σ c0 →
      (Spike.Lib.X64.Alloc.N lab ms₀ q.1 .e).J (enter (-48) σ) c0 →
      JpL (R := R) ms₀ lab J0 J1 l b w (leave (aR (mR R)) (-48) σ σx) c :=
  fun σx σ c0 _ hx h1 h2 => ⟨q, σx, σ, c0, hx, h1, h2, rfl⟩

end Gen

end Spike.Lib.X64.HelloPh.Level1

/-- info: 'Spike.Lib.X64.HelloPh.Level1.jpL_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Level1.jpL_of
