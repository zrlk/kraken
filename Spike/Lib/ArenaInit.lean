/-
**The arena and the counter at load** (`correctKA`'s `hz0` and `hc0` from a
check of the load's initial words).

The arena (`scc_rt_heap`, the link's heap region) and the counter word
(`scc_rt_heap_use`) are `.bss`: the load writes nothing there, so every
initial value there is `0`. `arenaInitOk` checks by evaluation, fail-closed,
that no initial word of a load (`Memory.init`, e.g. the canonical load's
`Rt.A64.initOf`: the image's nonzero words and the `.rodata` words) is at an
address of the arena or at the counter's word; `initVal_arena` and
`initVal_ctr` turn it into the zero values `correctKA` takes.

Contents:

- `arenaInitOk`: the check.
- `initVal_arena`: every word of the free range at cursor `0` starts at `0`
  (the arena below `2^64`).
- `initVal_ctr`: the counter word starts at `0`.
-/
import Spike.Lib.AllocRow

namespace Spike.Lib.ArenaInit

open Kraken.Promising
open Scc.Sem (wordLoc Range)

/-- **No initial word in the arena or at the counter**: every entry of
`init` is at an address off `[heap, heap + 16 · cells)` and at a location
other than the counter's word. -/
def arenaInitOk (init : List (Loc × Val)) (heap cells ctr : Nat) : Bool :=
  init.all fun e => !(decide (heap ≤ e.1.addr.toNat) && decide (e.1.addr.toNat < heap + 16 * cells)) &&
    e.1 != wordLoc ctr

/-- **The arena starts zero**: with no initial word in the arena, every word
of the free range at cursor `0` starts at `0` (the arena below `2^64`). -/
theorem initVal_arena {m : Memory} {heap cells ctr : Nat} (h : arenaInitOk m.init heap cells ctr = true)
    (hb : heap + 16 * cells ≤ 2 ^ 64) {a : Nat} (ha : (AllocRow.freeR heap cells 0).contains a) :
    m.initVal (wordLoc a) = 0 := by
  have ha' : heap ≤ a ∧ a < heap + 16 * cells := by
    simpa [AllocRow.freeR, Range.contains] using ha
  have hfind : m.init.find? (·.1 == wordLoc a) = none := by
    rw [List.find?_eq_none]
    intro e he heq
    have hl : e.1 = wordLoc a := by simpa using heq
    have he' := List.all_eq_true.mp h e he
    rw [hl] at he'
    have hat : (wordLoc a).addr.toNat = a := by
      simp only [wordLoc, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    simp only [hat, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.and_eq_false_iff,
      decide_eq_false_iff_not] at he'
    omega
  unfold Memory.initVal
  rw [hfind]
  rfl

/-- **The counter starts at `0`**: with no initial word at the counter's
word, its initial value is `0`. -/
theorem initVal_ctr {m : Memory} {heap cells ctr : Nat} (h : arenaInitOk m.init heap cells ctr = true) :
    m.initVal (wordLoc ctr) = 0 := by
  have hfind : m.init.find? (·.1 == wordLoc ctr) = none := by
    rw [List.find?_eq_none]
    intro e he heq
    have hl : e.1 = wordLoc ctr := by simpa using heq
    have he' := List.all_eq_true.mp h e he
    rw [hl] at he'
    simp at he'
  unfold Memory.initVal
  rw [hfind]
  rfl

end Spike.Lib.ArenaInit
