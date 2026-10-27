/-
**The heap obligations of an alloc-capable consumer**, ISA-free: the shapes
the multi-frame consumers (`A64ConsumerS`, `X64ConsumerS`) take for the heap
abort and the heap counter, with the allocation invariant that discharges
them.

- `AtNewBuf c`: the control is at a buffer allocation.
- `HeapAbortObl cells ctr c`: the heap disjunct of the abort path's sites
  (after `k = .heap`): every count `old` the control allows at a `newBuf`
  (within `cells`, the held counter word, if any, `old`) makes it
  `HeapReady` (`Spike/Lib/HeapAbort.lean`).
- `HeapCtr cells ctr hu c`: the relation's heap clause at the source's heap
  use `hu` (`heapUse s`): at a `newBuf`, `hu` within `cells` and a held
  counter word `hu`. `HeapAbortObl.at_heapCtr`: the two meet at `old := hu`,
  the premise of `abortJustified_heap_source`.
- `AllocInvAt … hu c`: `AllocInv` (`Spike/Lib/AllocInv.lean`) with its counts
  fixed to `hu`; `AllocInvAt.allocInv`, `AllocInvAt.heapCtr`.
-/
import Spike.Lib.HeapAbort
import Spike.Lib.AllocInv

namespace Spike.Lib

open CoreLang CoreTerm
open Kraken Kraken.Promising

/-- **The control is at a buffer allocation.** -/
def AtNewBuf (c : Ctl) : Prop := ∃ x a τ e, c.term = .let_ x (.newBuf a τ) e

/-- **The heap disjunct of an abort site** (after `k = .heap`): for every
count `old` that the control allows at a `newBuf` (within the cells, the
held counter word, if any, `old`), the control is `HeapReady`. -/
def HeapAbortObl (cells ctr : Nat) (c : Ctl) : Prop :=
  ∀ old, (AtNewBuf c → old ≤ cells ∧ ∀ w, c.hold = some (ctr, w) → w = TermRun.cst (.num old)) →
    HeapReady cells old c

/-- **The relation's heap clause** at the source's heap use `hu`: at a
`newBuf`, `hu` within the cells and the held counter word, if any, `hu`. -/
def HeapCtr (cells ctr hu : Nat) (c : Ctl) : Prop :=
  AtNewBuf c → hu ≤ cells ∧ ∀ w, c.hold = some (ctr, w) → w = TermRun.cst (.num hu)

/-- **The two meet at the source's heap use**: the abort site's obligation
at `old := hu`, given the relation's clause at `hu`. -/
theorem HeapAbortObl.at_heapCtr {cells ctr hu : Nat} {c : Ctl} (hab : HeapAbortObl cells ctr c)
    (hctr : HeapCtr cells ctr hu c) : HeapReady cells hu c :=
  hab hu hctr

open Spike.Lib.AllocInv (CtrAt Pending AllocInv)
open Spike.Lib.AllocRow (ArenaOK)

/-- **The allocation invariant at heap use `hu`** (`AllocInv` with its
counts fixed): pending from `hu`, the held counter word `hu`'s, the contract
at `hu`; or idle, the counter at `hu`, the contract at `hu` with no
exception. -/
def AllocInvAt {I : ISA} (Λ : Scc.Sem.Layout) (lbl : WeakMem.AllocLabel → Option Nat)
    (lsize : WeakMem.AllocLabel → Nat) (t : Thread I) (tm : Memory) (heap cells ctr : Nat)
    (units off : Nat → Ty → Nat) (hu : Nat) (c : Ctl) : Prop :=
  (c.hold = some (ctr, TermRun.cst (.num hu)) ∧ ∃ ex, Pending units off tm t.prom heap ctr hu ex c ∧
      ArenaOK Λ lbl lsize t tm heap cells hu ex) ∨
    ((∀ w, c.hold ≠ some (ctr, w)) ∧ CtrAt tm t.prom ctr hu ∧
      ArenaOK Λ lbl lsize t tm heap cells hu (fun _ => False))

variable {I : ISA} {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat}
  {lsize : WeakMem.AllocLabel → Nat} {t : Thread I} {tm : Memory} {heap cells ctr : Nat}
  {units off : Nat → Ty → Nat} {hu : Nat} {c : Ctl}

/-- `AllocInvAt` is an `AllocInv`. -/
theorem AllocInvAt.allocInv (h : AllocInvAt Λ lbl lsize t tm heap cells ctr units off hu c) :
    AllocInv Λ lbl lsize t tm heap cells ctr units off c := by
  rcases h with ⟨hh, ex, hp, ha⟩ | ⟨hn, hc, ha⟩
  · exact .inl ⟨_, hh, hu, ex, rfl, hp, ha⟩
  · exact .inr ⟨hn, hu, hc, ha⟩

/-- **`AllocInvAt` gives the heap clause**: the cursor is within the cells
(`ArenaOK.hu_le`), and a held counter word is `hu`'s. -/
theorem AllocInvAt.heapCtr (h : AllocInvAt Λ lbl lsize t tm heap cells ctr units off hu c) :
    HeapCtr cells ctr hu c := by
  intro _
  rcases h with ⟨hh, ex, -, ha⟩ | ⟨hn, -, ha⟩
  · refine ⟨ha.hu_le, fun w hw => ?_⟩
    rw [hh] at hw
    cases hw
    rfl
  · exact ⟨ha.hu_le, fun w hw => absurd hw (hn w)⟩

end Spike.Lib
