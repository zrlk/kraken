/-
**Placements reachable by allocations** (ISA-neutral; the multi-level
fragment of the allocation-capable consumers, `Spike/Lib/X64SegInstN.lean`
and its AArch64 twin): from the labels' placement `L0`, `ls0`, every fresh
label the arena can hand out (`AllocLand`) placed in turn. A program that
allocates any number of times has its fragment at every such placement,
`IN`; an allocation row at a reachable placement lands at the next one
(`Reach.step`), inside `IN` again.

- `upd`, `updN`: the placement and sizes with `l` placed at `b` with `n`
  bytes (as `msOfA`'s allocation fragment writes them).
- `Reach`: the placements reachable from `L0`, `ls0`.
- `IN`: a placement-indexed family of fragments at the reachable
  placements.
- `Reach.placed`: a label placed at a reachable placement is placed at
  `L0` with its size, or lands in the arena with its size; `Reach.mono`:
  the placement only grows.
-/
import Spike.Lib.SegS
import Spike.Lib.Arena
import Spike.Lib.HeapLand

namespace Spike.Lib.AllocReach

open CoreLang CoreTerm
open Kraken.Promising
open Spike.Lib.HeapLand (AllocLand)

/-- The placement with `l` placed at `b` (as `msOfA`'s allocation fragment
writes it). -/
def upd (L : WeakMem.AllocLabel → Option Nat) (l : WeakMem.AllocLabel) (b : Nat) :
    WeakMem.AllocLabel → Option Nat :=
  fun l' => if l' = l then some b else L l'

/-- The sizes with `l` of `n` bytes (as `msOfA`'s allocation fragment
writes them). -/
def updN (ls : WeakMem.AllocLabel → Nat) (l : WeakMem.AllocLabel) (n : Nat) : WeakMem.AllocLabel → Nat :=
  fun l' => if l' = l then n else ls l'

/-- **The placements reachable from `L0`, `ls0`**: each step places a label
not yet placed at a base `b` with `n` bytes that the arena can hand out
(`AllocLand`). -/
inductive Reach (ar : Arena) (L0 : WeakMem.AllocLabel → Option Nat) (ls0 : WeakMem.AllocLabel → Nat) :
    (WeakMem.AllocLabel → Option Nat) → (WeakMem.AllocLabel → Nat) → Prop
  | base : Reach ar L0 ls0 L0 ls0
  | step {L : WeakMem.AllocLabel → Option Nat} {ls : WeakMem.AllocLabel → Nat} {l : WeakMem.AllocLabel}
      {b n : Nat} : Reach ar L0 ls0 L ls → L l = none → AllocLand ar.heap ar.cells b n →
      Reach ar L0 ls0 (upd L l b) (updN ls l n)

/-- **The multi-level fragment**: the family `inv` at the placements
reachable from `L0`, `ls0`. -/
def IN {I : ISA} (ar : Arena) (L0 : WeakMem.AllocLabel → Option Nat) (ls0 : WeakMem.AllocLabel → Nat)
    (inv : (WeakMem.AllocLabel → Option Nat) → (WeakMem.AllocLabel → Nat) → FragS I) :
    (WeakMem.AllocLabel → Option Nat) → (WeakMem.AllocLabel → Nat) → FragS I :=
  fun L ls s c fs => Reach ar L0 ls0 L ls ∧ inv L ls s c fs

namespace Reach

variable {ar : Arena} {L0 L : WeakMem.AllocLabel → Option Nat} {ls0 ls : WeakMem.AllocLabel → Nat}

/-- **A label placed at a reachable placement** is placed at `L0` with its
size there, or its base and size land in the arena (`AllocLand`). -/
theorem placed (h : Reach ar L0 ls0 L ls) {l : WeakMem.AllocLabel} {b : Nat} (hl : L l = some b) :
    (L0 l = some b ∧ ls l = ls0 l) ∨ AllocLand ar.heap ar.cells b (ls l) := by
  induction h with
  | base => exact .inl ⟨hl, rfl⟩
  | @step L ls l' b' n' _ _ hland ih =>
    unfold upd at hl
    unfold updN
    by_cases he : l = l'
    · subst he
      simp only [ite_true, Option.some.injEq] at hl ⊢
      subst hl
      exact .inr hland
    · simp only [he, ite_false] at hl ⊢
      exact ih hl

/-- **The placement only grows**: a label placed at `L0` is placed alike at
every reachable placement. -/
theorem mono (h : Reach ar L0 ls0 L ls) {l : WeakMem.AllocLabel} {b : Nat} (hl : L0 l = some b) :
    L l = some b := by
  induction h with
  | base => exact hl
  | @step L ls l' b' n' _ hn _ ih =>
    unfold upd
    by_cases he : l = l'
    · subst he; rw [ih] at hn; cases hn
    · simp only [he, ite_false]; exact ih

end Reach

/--
info: 'Spike.Lib.AllocReach.Reach.placed' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Reach.placed

end Spike.Lib.AllocReach
