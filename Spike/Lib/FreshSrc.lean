/-
**The source's next allocation label is fresh**, from the memory relation:
every source message's label is placed (`MemRel.lbl_mem`), and the
thread's labels from its allocation count on are not
(`AllocInv.FreshInv`), so no source message has the next one
(`Scc.Sem.Fresh`, the premise of `abortJustified_heap_source`).

- `fresh_of_placed`: from placement alone (`lbl_mem`'s shape) and an
  unplaced label.
- `fresh_of_memRel`: from `MemRel` and `FreshInv` at the thread's count.

(A source-only proof over all reachable configurations does not exist in
this form: TermRun's promise steps are unrestricted, so a thread may
promise a store at its own next label, certified by allocating it, before
the allocation. The relation rules that out for a consumer's pairs.)
-/
import Scc.Sem.MemRel
import Spike.Lib.AllocInv

namespace Spike.Lib

open Scc.Sem (Fresh MemRel)
open Spike.Lib.AllocInv (FreshInv)

/-- **An unplaced label is fresh** in a source configuration whose every
message's label is placed. -/
theorem fresh_of_placed {lbl : WeakMem.AllocLabel → Option Nat} {s : TermRun.Cfg}
    (hm : ∀ m ∈ s.mem.toList, ∃ b, lbl m.loc.label = some b) {l : WeakMem.AllocLabel} (hl : lbl l = none) :
    Fresh s l := by
  intro m hmem he
  obtain ⟨b, hb⟩ := hm m hmem
  rw [he, hl] at hb
  cases hb

/-- **The thread's next label is fresh** in the source memory of a memory
relation whose placement leaves the thread's labels from its count `na`
on unplaced. -/
theorem fresh_of_memRel {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {tm : Kraken.Promising.Memory} {pairs : List Nat}
    {s : TermRun.Cfg} (hm : MemRel Λ lbl lsize ts tm s.mem pairs) {base n i na : Nat}
    (hf : FreshInv lbl base n i na) : Fresh s (TermRun.freshLabel base n i na) :=
  fresh_of_placed (fun m hmem => (hm.lbl_mem m hmem).imp fun _ h => h.1) hf.fresh

end Spike.Lib
