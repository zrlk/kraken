/-
**The counter floor against the two-allocation counterexample**
(ISA-generic): a concrete arena placement after one allocation, where the
allocator's size fact (`AllocW2`'s `hsz`) and header fact (`Call.OK.hdr`)
stated over every old count are false, and stated above the counter's floor
(`MemSide.lo`, at the arena's memory side `AllocLo.LoOf`) hold.

The arena: at `0`, `16` cells. A call of `2` one-word elements, no trace
words: `3` units (two words and the header's cell share), its base `8` past
the object's start (`off = 8`), its header at `16 · o` (`hdrAt`).

- `hsz_unrestricted_false`: one label `l1` placed at `8` of `1` word (a
  reachable placement: one allocation of one word at cursor `0`); the size
  fact over every old count asks, at the old count `0`, `2 ≤ 1`.
- `hsz_floor`: the same fact above the floor at the cursor past that
  allocation (`3`) holds: `hsz'_of_loOf`, and directly, the stale count `0`
  is below the floor (`not_loOf_stale`).
- `hdr_unrestricted_false`: one label of `2` words at `8` covers the header
  address `16` of the old count `1`, so a header fact over every old count
  fitting the cells asks a placed address be runtime memory; above the floor
  at an old count the free range is no placed label's (`hdr_floor`).
- the x86-64 arena memory side's `lo` is `LoOf` (`msOfA`).
-/
import Spike.Lib.AllocLo
import Spike.Lib.X64ConsumerA

namespace Spike.Test.B2LoFloor

open Scc.Sem (Range lrange)
open Spike.Lib.AllocRow (freeR)
open Spike.Lib.AllocLo (LoOf hsz'_of_loOf rt_of_loOf)

/-- The arena's base. -/
abbrev heap : Nat := 0
/-- The arena's cells. -/
abbrev cells : Nat := 16
/-- The call's elements. -/
abbrev n : Nat := 2
/-- The call's units: `n` words and the header's cell share. -/
abbrev u : Nat := 3
/-- The base's offset in the object (no trace words). -/
abbrev off : Nat := 8
/-- The header's address at the old count `o` (`Call.hdrAt`, no trace words). -/
abbrev hdrAt (o : Nat) : Nat := heap + 16 * o

/-- The label placed by the first allocation. -/
abbrev l1 : WeakMem.AllocLabel := 1

/-- **The placement after one allocation of one word** at cursor `0`. -/
def lbl1 : WeakMem.AllocLabel → Option Nat := fun l => if l = l1 then some 8 else none
/-- Its sizes. -/
def ls1 : WeakMem.AllocLabel → Nat := fun l => if l = l1 then 1 else 0

/-- **The size fact over every old count** (`AllocW2.hsz` before the floor),
at the arena and the call above. -/
def HszAll (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) : Prop :=
  ∀ l b old, lbl l = some b → b = heap + 16 * old + off → old + u ≤ cells → n ≤ lsize l

/-- **The size fact above the floor** (`AllocW2.hsz` with `ms.lo old`, `lo`
the arena's `LoOf`). -/
def HszLo (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) : Prop :=
  ∀ l b old, lbl l = some b → LoOf heap cells lbl lsize old → b = heap + 16 * old + off → old + u ≤ cells →
    n ≤ lsize l

/-- **The counterexample**: the size fact over every old count is false at
the placement after one allocation (the stale count `0` asks `2 ≤ 1`). -/
theorem hsz_unrestricted_false : ¬ HszAll lbl1 ls1 := fun h => by
  have := h l1 8 0 (by simp [lbl1]) (by decide) (by decide)
  simp [ls1, n] at this

/-- **The stale count is below the floor**: at the old count `0`, the free
range meets the placed label. -/
theorem not_loOf_stale : ¬ LoOf heap cells lbl1 ls1 0 := fun h => by
  have hd := (h l1 8 (by simp [lbl1])).1
  simp [Range.Disjoint, freeR, lrange, ls1, cells] at hd

/-- **The floor at the cursor past the allocation** (`3`): the placed label
lies below the free range, its base not past the cursor's first word. -/
theorem loOf_cursor : LoOf heap cells lbl1 ls1 u := by
  intro l b hl
  simp only [lbl1] at hl
  split at hl
  · cases hl
    subst l
    simp [Range.Disjoint, freeR, lrange, ls1, cells, u]
  · cases hl

/-- **The size fact above the floor holds** at that placement (from
`hsz'_of_loOf`, the arena's fit facts `8 ≤ off`, `off + 8 · n ≤ 16 · u`). -/
theorem hsz_floor : HszLo lbl1 ls1 :=
  fun _ _ _ hl hlo hb hle => hsz'_of_loOf hlo hl hb (by decide) (by decide) hle

/-- **The size fact above the floor, directly**: the only old count a
placed base answers is the stale `0`, below the floor. -/
example : HszLo lbl1 ls1 := by
  intro l b old hl hlo hb _
  simp only [lbl1] at hl
  split at hl
  · cases hl
    subst l
    have h0 : old = 0 := by omega
    subst h0
    exact absurd hlo not_loOf_stale
  · cases hl

/-- The placement with a two-word label at `8`. -/
def lbl2 : WeakMem.AllocLabel → Option Nat := lbl1
/-- Its sizes. -/
def ls2 : WeakMem.AllocLabel → Nat := fun l => if l = l1 then 2 else 0

/-- **Runtime memory at the arena's memory side**: no placed label's
address (`msOfA`'s `rt` at the heap). -/
def Rt (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (a : Nat) : Prop :=
  ¬ ∃ l b, lbl l = some b ∧ (lrange lsize l b).contains a

/-- **The header fact over every old count is false** with a two-word label
placed: the header address of the old count `1` is in it. -/
theorem hdr_unrestricted_false : ¬ ∀ o, o + u ≤ cells → Rt lbl2 ls2 (hdrAt o) := fun h =>
  h 1 (by decide) ⟨l1, 8, by simp [lbl2, lbl1], by simp [Range.contains, lrange, ls2]⟩

/-- The floor at the cursor `3` with the two-word label. -/
theorem loOf_cursor2 : LoOf heap cells lbl2 ls2 u := by
  intro l b hl
  simp only [lbl2, lbl1] at hl
  split at hl
  · cases hl
    subst l
    simp [Range.Disjoint, freeR, lrange, ls2, cells, u]
  · cases hl

/-- **The header fact above the floor holds** (`Call.OK.hdr` with
`ms.lo o`): the header of an old count above the floor is in the free range
at it, so no placed label's (`rt_of_loOf`). -/
theorem hdr_floor : ∀ o, LoOf heap cells lbl2 ls2 o → o + u ≤ cells → Rt lbl2 ls2 (hdrAt o) :=
  fun _ hlo hle => rt_of_loOf hlo (by simp only [Range.contains, freeR, hdrAt, heap, cells, u] at hle ⊢; omega)

/-- **The cursor past the allocation is above the floor**, and the
counterexample's old count `1` is not. -/
example : LoOf heap cells lbl2 ls2 u ∧ ¬ LoOf heap cells lbl2 ls2 1 :=
  ⟨loOf_cursor2, fun h => by simpa [Range.Disjoint, freeR, lrange, ls2, cells] using (h l1 8 rfl).1⟩

/-- **The x86-64 arena memory side's floor is `LoOf`** (`msOfA`'s `lo`):
the facts above are the ones `Call.OK.hdr` and `AllocW2`'s size field ask
there. -/
example {Λ μ rd G own ar I fs} :
    (Spike.Lib.X64ConsumerA.msOfA Λ μ rd G own ar I lbl1 ls1 fs).lo = LoOf ar.heap ar.cells lbl1 ls1 :=
  rfl

end Spike.Test.B2LoFloor

-- No axioms beyond Lean's.

/-- info: 'Spike.Test.B2LoFloor.hsz_unrestricted_false' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Test.B2LoFloor.hsz_unrestricted_false

/-- info: 'Spike.Test.B2LoFloor.hsz_floor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.B2LoFloor.hsz_floor

/-- info: 'Spike.Test.B2LoFloor.hdr_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.B2LoFloor.hdr_floor
