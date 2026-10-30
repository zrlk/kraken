/-
**The counter floor of the arena's placement** (ISA-generic): at the
counter's cursor `o`, every placed label lies off the free range and its
base is not past the cursor's first word (`LoOf`), the value a `MemSide`'s
`lo` channel takes at the arena's memory side.

- `LoOf`: the floor at cursor `o`;
- `loOf_of_arenaOK`: the floor at the arena contract's cursor (`ArenaOK.disj`
  and `ArenaOK.base`);
- `rt_of_loOf`: an address of the free range is in no placed label's range;
- `hsz'_of_loOf`: an object returned at the cursor (base
  `heap + 16 · o + off`, `8 ≤ off`, fitting `u` cells) has at most the words
  of any label placed at its base.
-/
import Spike.Lib.AllocRow

namespace Spike.Lib.AllocLo

open Scc.Sem (Range lrange)
open Spike.Lib.AllocRow (freeR ArenaOK)

/-- **The counter floor at cursor `o`**: every placed label lies off the free
range at `o`, and its base is not in it past the cursor's first word (a
0-word label's empty range is disjoint from everything; its base may sit at
the cursor, where an object's header is, but not past it). -/
def LoOf (heap cells : Nat) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (o : Nat) : Prop :=
  ∀ l b, lbl l = some b →
    (freeR heap cells o).Disjoint (lrange lsize l b) ∧ ¬ (heap + 16 * o + 8 ≤ b ∧ b < heap + 16 * cells)

/-- **The floor at the arena contract's cursor** (`ArenaOK.disj`,
`ArenaOK.base`). -/
theorem loOf_of_arenaOK {I : Kraken.Promising.ISA} {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {t : Kraken.Promising.Thread I} {tm : Kraken.Promising.Memory}
    {heap cells hu : Nat} {ex : Nat → Prop} (ha : ArenaOK Λ lbl lsize t tm heap cells hu ex) :
    LoOf heap cells lbl lsize hu :=
  fun l b hl => ⟨ha.disj l b hl, ha.base l b hl⟩

/-- **The free range is no placed label's**: under the floor at `o`, an
address of the free range at `o` is in no placed label's range. -/
theorem rt_of_loOf {heap cells : Nat} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {o a : Nat} (h : LoOf heap cells lbl lsize o)
    (ha : (freeR heap cells o).contains a) : ¬ ∃ l b, lbl l = some b ∧ (lrange lsize l b).contains a := by
  rintro ⟨l, b, hl, hc⟩
  have hd := (h l b hl).1
  simp only [Range.Disjoint, Range.contains, freeR, lrange] at hd ha hc
  omega

/-- **An object at the cursor has at most a placed label's words at its
base**: under the floor at `o`, an object of `n` words returned at
`heap + 16 · o + off` (`8 ≤ off`, `off + 8 · n ≤ 16 · u`, `o + u ≤ cells`)
whose base a label `l` is placed at has `n ≤ lsize l` (vacuously: a base
past the cursor's first word is no placed label's). -/
theorem hsz'_of_loOf {heap cells : Nat} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {o off u n : Nat} {l : WeakMem.AllocLabel} {b : Nat}
    (h : LoOf heap cells lbl lsize o) (hl : lbl l = some b) (hb : b = heap + 16 * o + off) (h8 : 8 ≤ off)
    (hfit : off + 8 * n ≤ 16 * u) (hle : o + u ≤ cells) : n ≤ lsize l := by
  refine Nat.le_of_not_lt fun hn => (h l b hl).2 ⟨by omega, by omega⟩

end Spike.Lib.AllocLo

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.AllocLo.loOf_of_arenaOK' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.AllocLo.loOf_of_arenaOK

/-- info: 'Spike.Lib.AllocLo.rt_of_loOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.AllocLo.rt_of_loOf

/-- info: 'Spike.Lib.AllocLo.hsz'_of_loOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.AllocLo.hsz'_of_loOf
