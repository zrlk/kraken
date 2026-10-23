/-
**The heap counter's invariant, one thread** (`Scc/DESIGN.md` §7.3,
item 5, *Heap, settled shape*).

The runtime's `scc_rt_alloc(h, k, u)` (`Scc/Lower/Runtime.lean`,
`allocF`) counts the arena in 16-byte cells. The counter
`scc_rt_heap_use` is the cursor. Its blocks (labels
`.L2_scc_rt_alloc.<i>_<b>` on AArch64, `.Lscc_rt_alloc.<b>` on x64):

- `entry`: `k ≥ 2^lenBits` goes to `full`, else to `cnt`;
- `cnt`: `old ← rmw add [scc_rt_heap_use] u` (`ldaddal`, `lock xadd`), then
  `old + u > cells` goes to `slow`, else to `ok`;
- `slow`: `old > cells` goes to `spin`, else to `full`;
- `spin`: loops; `full`: the `heap` abort;
- `ok`: the object takes the cells `[old, old + u)`, from
  `s = scc_rt_heap + 16 · old`; the header is stored and the base
  `s + 8 · k · m + 8` returned.

The source `newBuf` step (`heapUse` grows by `u`, `heapUse_newBuf`) is
simulated at the `rmw` when `old + u ≤ cells` (the label is placed there in
advance, `alloc_placed`). Otherwise it is simulated at `full`'s exit, the
abort step, which it justifies (`AbortJustified.heap_of_crossing`). Between
the `rmw` and that exit the allocation is **pending**: the counter has
`u` that the source has not.

**The invariant** (`HeapCtr1 cells ctr hu pend`, one thread, promises never
mirrored, so the counter's value is the thread's last write to it, or `0`):
the counter is the source heap use plus the pending `u`, the heap use is
within `cells`, and a pending allocation is past `cells`. The thread's
phase picks `pend`: `none` before `cnt`'s `rmw` and from `ok` on, `some u`
after the `rmw` on the way to `slow`, and in `slow` and `full`.

- `HeapCtr1.init`: the loaded program (counter `0` in `.bss`, empty
  source heap).
- `HeapCtr1.rmw_ok`, `HeapCtr1.rmw_slow`: the `rmw` from an idle phase,
  with the source step when `old + u ≤ cells` and pending otherwise.
- `HeapCtr1.ok_of_le`, `HeapCtr1.full_of_pending`: the branches. The `rmw`
  returned the heap use, so `cnt` goes to `ok` exactly when the source step
  stays within the budget. A pending allocation's `old` is within `cells`,
  so `slow` goes to `full` and one thread never reaches `spin`.
- `HeapCtr1.crossing`: at `full` the source step crosses `cells`, the
  premises of `AbortJustified.heap_of_crossing`; `HeapCtr1.abort_justified`
  states it with them.
- `HeapCtr1.bound`: the counter is below `2^64` when
  `cells + umax < 2^64`.
- `slot_sub_arena`, `slot_disjoint`: the cells of an `ok` allocation lie
  in the arena (`16 · cells` bytes) and hold the object
  (`8 · (1 + k · (n + m)) ≤ 16 · u`, the lowering's `n + m ≤ 2 · words`
  check). Two allocations' cells are disjoint because the counter only
  grows.

Several threads (M2, a DESIGN note for now): the pending allocations form
a list. The oldest one's `old` is the heap use, and each newer one's `old`
is at least the previous one's `old + u`. So only the oldest can have
`old ≤ cells` (the crossing thread, which goes to `full`), every other one
spins, and the counter stays below `cells + (threads + 1) · umax`.
-/
import Scc.Sem.Budget

namespace Scc.Sem

/-- **The heap counter's invariant, one thread**: the counter `ctr` is the
source heap use `hu` plus the pending allocation's units, `hu` is within
`cells`, and a pending allocation crosses `cells`. -/
structure HeapCtr1 (cells ctr hu : Nat) (pend : Option Nat) : Prop where
  /-- The counter is the heap use plus the pending units. -/
  sum : ctr = hu + pend.getD 0
  /-- The heap use is within the budget (no abort has happened). -/
  within : hu ≤ cells
  /-- A pending allocation is past the budget. -/
  past : ∀ u, pend = some u → cells < hu + u

namespace HeapCtr1

variable {cells ctr hu : Nat}

/-- **The loaded program**: counter `0`, empty source heap, idle. -/
theorem init (cells : Nat) : HeapCtr1 cells 0 0 none :=
  ⟨rfl, Nat.zero_le _, fun _ h => by cases h⟩

/-- **The `rmw`, within the budget**: from an idle phase, `old = ctr` and
`old + u ≤ cells`. The source's `newBuf` step (heap use `hu + u`) is
simulated here, and the thread is idle again. -/
theorem rmw_ok (h : HeapCtr1 cells ctr hu none) {u : Nat} (hle : ctr + u ≤ cells) :
    HeapCtr1 cells (ctr + u) (hu + u) none := by
  have := h.sum; simp only [Option.getD_none] at this
  exact ⟨by simp only [Option.getD_none]; omega, by omega, fun _ h => by cases h⟩

/-- **The `rmw`, past the budget**: from an idle phase with
`cells < old + u`, the allocation is pending; no source step. -/
theorem rmw_slow (h : HeapCtr1 cells ctr hu none) {u : Nat} (hlt : cells < ctr + u) :
    HeapCtr1 cells (ctr + u) hu (some u) := by
  have := h.sum; simp only [Option.getD_none] at this
  exact ⟨by simp only [Option.getD_some]; omega, h.within, fun u' he => by cases he; omega⟩

/-- **`cnt`'s branch is the source budget**: from an idle phase, the value
the `rmw` returns is the heap use, so `old + u ≤ cells` (to `ok`) exactly
when the source step stays within `cells`. -/
theorem ok_of_le (h : HeapCtr1 cells ctr hu none) {u : Nat} : ctr + u ≤ cells ↔ hu + u ≤ cells := by
  have := h.sum; simp only [Option.getD_none] at this; omega

/-- **`slow` goes to `full`**: a pending allocation's `old` (the counter
before its `rmw`, `ctr - u`) is the heap use, within `cells`; with one thread
`spin` is unreachable. -/
theorem full_of_pending {u : Nat} (h : HeapCtr1 cells ctr hu (some u)) : ctr - u ≤ cells := by
  have := h.sum; have := h.within; simp only [Option.getD_some] at *; omega

/-- **At `full` the source step crosses the budget**: the heap use is
within `cells` and the step's `u` takes it past. -/
theorem crossing {u : Nat} (h : HeapCtr1 cells ctr hu (some u)) : hu ≤ cells ∧ cells < hu + u :=
  ⟨h.within, h.past u rfl⟩

/-- **The heap abort at `full` is justified**: the source step of the
thread's `newBuf` (heap use `hu + u`) from a configuration with heap use
`hu` crosses `B.cells`. -/
theorem abort_justified {B : Budget} {S : SrcSem} {tr : List Ev} {s s' : S.Cfg} {i : Nat} {es : List Ev}
    {u : Nat} (h : HeapCtr1 B.cells ctr (heapUse (S.core s)) (some u)) (hstep : S.step i s es s')
    (hu : heapUse (S.core s') = heapUse (S.core s) + u) : AbortJustified B S tr s i .heap :=
  AbortJustified.heap_of_crossing hstep hu h.crossing.1 h.crossing.2

/-- **The counter does not wrap**: it is at most `cells + umax`. -/
theorem bound {pend : Option Nat} (h : HeapCtr1 cells ctr hu pend) {umax : Nat}
    (hu : ∀ u, pend = some u → u ≤ umax) : ctr ≤ cells + umax := by
  have hs := h.sum; have hw := h.within
  cases pend with
  | none => simp only [Option.getD_none] at hs; omega
  | some u => have := hu u rfl; simp only [Option.getD_some] at hs; omega

end HeapCtr1

/-! ## The cells of an allocation -/

/-- **An `ok` allocation's object lies in its cells, and they lie in the
arena**: the object's `8 · (1 + k · (n + m))` bytes from
`heap + 16 · old` fit `u` cells, and `old + u ≤ cells` with
`16 · cells` the arena's bytes. -/
theorem slot_sub_arena {heap cells old u bytes : Nat} (hfit : bytes ≤ 16 * u) (hle : old + u ≤ cells) :
    heap + 16 * old + bytes ≤ heap + 16 * cells := by
  omega

/-- **Two allocations' cells are disjoint**: the later one's `old` is at
least the earlier one's `old + u` (the counter only grows). -/
theorem slot_disjoint {heap old u old' bytes : Nat} (hfit : bytes ≤ 16 * u) (hgrow : old + u ≤ old') :
    heap + 16 * old + bytes ≤ heap + 16 * old' := by
  omega

/-! ## Tests -/

/-- One thread, `cells = 4`: an allocation of 3 units is simulated at the
`rmw`; the next of 2 is pending, and its abort is a crossing (`3 ≤ 4 < 5`). -/
example : HeapCtr1 4 5 3 (some 2) :=
  ((HeapCtr1.init 4).rmw_ok (u := 3) (by decide)).rmw_slow (u := 2) (by decide)

/-- **Rejected: a pending allocation within the budget.** `rmw_slow`
needs `cells < old + u`: an allocation that fits is never pending. -/
example : ¬ HeapCtr1 4 3 1 (some 2) := fun h => by have := h.past 2 rfl; omega

end Scc.Sem
