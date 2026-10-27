/-
**Every placed label inside the arena** (`LblArena`, ISA-neutral): each label
the placement `lbl` places at `b` with `lsize l` words lies past the arena's
first header word and inside its cells (`AllocLand`'s first two conjuncts).
The entry placement places no label (`lay2`'s `static := none`), and an
allocation places a fresh label where the arena hands it out
(`allocLand_of_ea`), so `LblArena` holds at every placement reachable by
allocations; with the arena inside the heap it gives `LblRange`, and a
label's word below its size is an arena word.

- `LblArena`: every placed label's words inside the arena's cells;
- `LblArena.none`: at the empty placement;
- `LblArena.alloc`: kept by placing a label where the arena hands it out
  (`AllocReach.upd`, `updN`, as `msOfA`'s `xa` and `Reach.step` write it);
- `LblArena.reach`: at every placement reachable from one where it holds;
- `LblArena.word`: a placed label's word below its size lies in the arena;
- `LblArena.lblRange`: `LblRange` from the arena inside the heap;
- `LblArena.heap`: a placed label's word's bytes in the heap.
-/
import Spike.Lib.AllocReach
import Spike.Lib.Src.LblRange

namespace Spike.Lib

open Scc.Sem (Range Layout lrange)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.AllocReach (upd updN Reach)
open Spike.Lib.LowerNode (LblRange)

/-- **Every placed label inside the arena**: the label `l` placed at `b`
with `lsize l` words lies past the arena's first header word and inside
its cells (`AllocLand`'s placement conjuncts). -/
def LblArena (ar : Arena) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) : Prop :=
  ∀ l b, lbl l = some b → ar.heap + 8 ≤ b ∧ b + 8 * lsize l ≤ ar.heap + 16 * ar.cells

namespace LblArena

variable {ar : Arena} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}

/-- **The empty placement** (the entry's, `static := none`) is inside the
arena. -/
theorem none (ar : Arena) (lsize : WeakMem.AllocLabel → Nat) : LblArena ar (fun _ => Option.none) lsize :=
  fun _ _ h => by cases h

/-- **An allocation keeps the placement inside the arena**: the label `l`
placed at `b` with `n` words where the arena hands it out (`AllocLand`). -/
theorem alloc (h : LblArena ar lbl lsize) {l : WeakMem.AllocLabel} {b n : Nat}
    (hl : AllocLand ar.heap ar.cells b n) : LblArena ar (upd lbl l b) (updN lsize l n) := by
  intro l' b' h'
  unfold upd at h'
  unfold updN
  by_cases he : l' = l
  · simp only [he, ite_true, Option.some.injEq] at h' ⊢
    subst h'
    exact ⟨hl.1, hl.2.1⟩
  · simp only [he, ite_false] at h' ⊢
    exact h l' b' h'

/-- **At every reachable placement**, from the placement it starts at. -/
theorem reach {L0 : WeakMem.AllocLabel → Option Nat} {ls0 : WeakMem.AllocLabel → Nat}
    (h0 : LblArena ar L0 ls0) (h : Reach ar L0 ls0 lbl lsize) : LblArena ar lbl lsize := by
  induction h with
  | base => exact h0
  | step _ _ hland ih => exact ih.alloc hland

/-- **A placed label's word below its size is an arena word**: at
`a = b + 8 · k` with `k < lsize l`, its eight bytes lie past the arena's
first header word and inside its cells. -/
theorem word (h : LblArena ar lbl lsize) {l : WeakMem.AllocLabel} {b k a : Nat} (hl : lbl l = some b)
    (hk : k < lsize l) (ha : a = b + 8 * k) : ar.heap + 8 ≤ a ∧ a + 8 ≤ ar.heap + 16 * ar.cells := by
  have := h l b hl
  subst ha
  omega

/-- **`LblRange` from the arena inside the heap**: every placed label's
range inside the heap. -/
theorem lblRange {Λ : Layout} (h : LblArena ar lbl lsize)
    (hs : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap) : LblRange Λ lbl lsize := by
  intro l b hl
  left
  have := h l b hl
  unfold Range.Sub lrange at *
  simp only at hs ⊢
  omega

/-- **A placed label's word below its size lies in the heap**, byte by
byte, with the arena inside the heap. -/
theorem heap {Λ : Layout} (h : LblArena ar lbl lsize) (hs : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap)
    {l : WeakMem.AllocLabel} {b k a : Nat} (hl : lbl l = some b) (hk : k < lsize l) (ha : a = b + 8 * k) :
    ∀ i < 8, Λ.heap.contains (a + i) := by
  intro i hi
  have := h.word hl hk ha
  unfold Range.Sub at hs
  unfold Range.contains
  simp only at hs
  omega

end LblArena

/--
info: 'Spike.Lib.LblArena.reach' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LblArena.reach

/--
info: 'Spike.Lib.LblArena.lblRange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LblArena.lblRange

/--
info: 'Spike.Lib.LblArena.heap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LblArena.heap

end Spike.Lib
