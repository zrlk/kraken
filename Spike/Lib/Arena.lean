/-
**The allocator's arena** (ISA-neutral; the allocation-capable consumers
`Spike/Lib/A64ConsumerA.lean` and `Spike/Lib/X64ConsumerA.lean` take it):
the arena at `heap` of `cells` 16-byte cells, the heap counter word `ctr`,
the allocator's `units` and base offsets `off`.

- `Arena`, `Arena.OK`: the arena's parameters and their facts.
- `Arena.ofWords`, `Arena.ofWords_ok`: a concrete arena meeting `Arena.OK`.
- `Arena.ofWords_units_fit`: its units within the cells are the object's.
- `Arena.ctrLoc`: the counter word's location.
-/
import WeakCore.TermRun
import Kraken.Promising.Basic

namespace Spike.Lib

open CoreLang CoreTerm
open Kraken.Promising

/-- **The allocator's arena**: at `heap`, of `cells` 16-byte cells, the
heap counter word at `ctr`, an object of `k` elements of type `τ` taking
`units k τ` cells with its base at `off k τ` in it; box allocations
admitted where `newOk` holds. -/
structure Arena where
  heap : Nat
  cells : Nat
  ctr : Nat
  units : Nat → Ty → Nat
  off : Nat → Ty → Nat
  /-- Whether the consumer's rows admit box allocations (`MemSide.newOk`
  of the memory side with the arena). The default (none) is the strong
  direction: only buffer allocations. -/
  newOk : Prop := False
  /-- Whether the consumer's rows admit the source's publication at a fence
  (`MemSide.pub` of the memory side with the arena, `FenceRun.pub`). The
  default (none) is the strong direction: fence rows take local runs only. -/
  pub : Prop := False

/-- **The arena's facts**: the counter word off the arena; an object of `k`
elements of a type of words `us` that fits the arena (`k · nWords us + 1 ≤
cells`) takes its `k · nWords us` words and the header's cell share
(`units k τ = k · nWords us + 1`), its base a word boundary past the header
word from the object's start with the buffer's words within the object's
cells (`8 ≤ off k τ`, `off k τ + 8 · (k · nWords us) ≤ 16 · units k τ`; the
allocator's `Call.OK.off` puts it at `8 · (k · m) + 8`, `m` the header's
trace words, at most `nWords us`); the units and the cells below `2^63` (the
counter's add does not wrap); the counter an address. The fit premise keeps
the laws satisfiable together with `units_lt` (an object of `2^63` words has
no units below `2^63`); only a landing object (`AllocLand`) uses them, and it
fits. -/
structure Arena.OK (ar : Arena) : Prop where
  ctr_out : ¬ (ar.heap ≤ ar.ctr ∧ ar.ctr < ar.heap + 16 * ar.cells)
  units : ∀ k τ us, TermRun.accs (TermRun.close [] τ) = some us → k * TermRun.nWords us + 1 ≤ ar.cells →
    ar.units k τ = k * TermRun.nWords us + 1
  off : ∀ k τ us, TermRun.accs (TermRun.close [] τ) = some us → k * TermRun.nWords us + 1 ≤ ar.cells →
    ar.off k τ % 8 = 0 ∧ 8 ≤ ar.off k τ ∧ ar.off k τ + 8 * (k * TermRun.nWords us) ≤ 16 * ar.units k τ
  units_lt : ∀ k τ, ar.units k τ < 2 ^ 63
  cells_lt : ar.cells < 2 ^ 63
  ctr_lt : ar.ctr < 2 ^ 64

/-- **The arena of a placement**: at `heap`, of `cells` cells, the counter at
`ctr`, an object's units and base offset by its type's words `us` and trace
words `m τ` (`k · nWords us + 1`, saturating at `2^63 - 1`, and
`8 · (k · m τ) + 8`), none for a type without words. Saturating (not
wrapping) keeps an object too large for the cells from having units within
them (`Arena.ofWords_units_fit`). -/
def Arena.ofWords (heap cells ctr : Nat) (m : Ty → Nat) : Arena where
  heap := heap
  cells := cells
  ctr := ctr
  units k τ := match TermRun.accs (TermRun.close [] τ) with
    | some us => if k * TermRun.nWords us + 1 < 2 ^ 63 then k * TermRun.nWords us + 1 else 2 ^ 63 - 1
    | none => 0
  off k τ := match TermRun.accs (TermRun.close [] τ) with
    | some _ => 8 * (k * m τ) + 8
    | none => 0

/-- **`Arena.OK` is satisfiable**: the arena of a placement with the counter off
the arena, the cells below `2^63`, the counter an address and at most a
type's words as its trace words meets it. -/
theorem Arena.ofWords_ok {heap cells ctr : Nat} {m : Ty → Nat} (hout : ¬ (heap ≤ ctr ∧ ctr < heap + 16 * cells))
    (hc : cells < 2 ^ 63) (hctr : ctr < 2 ^ 64)
    (hm : ∀ τ us, TermRun.accs (TermRun.close [] τ) = some us → m τ ≤ TermRun.nWords us) :
    (Arena.ofWords heap cells ctr m).OK where
  ctr_out := hout
  units k τ us hus hfit := by
    simp only [Arena.ofWords, hus] at hfit ⊢; split <;> omega
  off k τ us hus hfit := by
    have hkm : k * m τ ≤ k * TermRun.nWords us := Nat.mul_le_mul_left k (hm τ us hus)
    simp only [Arena.ofWords, hus] at hfit ⊢
    split <;> omega
  units_lt k τ := by
    simp only [Arena.ofWords]; split
    · split <;> omega
    · decide
  cells_lt := hc
  ctr_lt := hctr

/-- **An arena of a placement's units within its cells are the object's**
(`k · nWords us + 1`): an object too large saturates at `2^63 - 1`, past
cells below it. -/
theorem Arena.ofWords_units_fit {heap cells ctr : Nat} {m : Ty → Nat} (hc : cells < 2 ^ 63 - 1) {k : Nat}
    {τ : Ty}
    {us : List TermRun.Acc} (hus : TermRun.accs (TermRun.close [] τ) = some us)
    (h : (Arena.ofWords heap cells ctr m).units k τ ≤ cells) :
    (Arena.ofWords heap cells ctr m).units k τ = k * TermRun.nWords us + 1 := by
  simp only [Arena.ofWords, hus] at h ⊢
  split at h <;> split <;> omega

/-- The counter word's location. -/
def Arena.ctrLoc (ar : Arena) : Loc := ⟨BitVec.ofNat 64 ar.ctr, 8⟩

end Spike.Lib

/-- info: 'Spike.Lib.Arena.ofWords_units_fit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Arena.ofWords_units_fit
