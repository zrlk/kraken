/-
**The memory side of a store**, for the consumers of the judgement: the
Kraken half of `Out.store` and `Out.rtStore`, and the runtime store against
the memory relation of `Scc/Sem/MemRel.lean`.

A plain store's Kraken step has two shapes (`writeSuccs`), kept apart here
so that a consumer with promises uses both and one without uses the first:

- **append** (promise now): the message is appended at `last + 1`, which
  is promised and fulfilled at once;
- **fulfil**: an outstanding promise of the same message is fulfilled;
  memory is unchanged.

`k_store_out` gives the two cases for any non-exclusive store tree (no
hypothesis on the thread's promises). `k_store_append` is the case with no
outstanding promise, the shape `MemRel.store` and `MemRel.runtime_write`
take.

For a runtime store (`Out.rtStore`, an address outside every placed label:
`MemSide.ofLabels`), `rtStore_memRel` keeps `MemRel` in both cases: the
append by `MemRel.runtime_write`, the fulfil trivially (memory unchanged; the
promised message was already related when it was promised). The source
stutters, so source memory, `ts` and the pair list are unchanged.
-/
import Spike.Lib.Seg
import Spike.Bridge.Progress
import Scc.Sem.MemRel

namespace Spike.Lib

open Kraken.Promising Kraken.Promising.Lower Kraken.Promising.Live.TicketStep
open Scc.Sem (MemRel lrange)

/-- **The memory side of `MemRel`** over the label placement `lbl` and sizes
`lsize`, with read side `rd`: the runtime owns every address outside every
placed label's range (the condition of `MemRel.runtime_write`). The
kernel model `K` of the system calls is passed through (default: none), and
so are the runtime memory's value invariant `G` (default: every value) and
the allocator's arena base, heap counter address, units and base offset
(`MemSide.heap`, `ctr`, `units`, `off`; defaults `0`, `0`, one unit, one
header word) and the arena's cells (`MemSide.cells`, default `0`), and the
owned words, the mapped locations, the abort sites, the placed pairs, the
allocation fragment, the output's byte step and the counter floor
(`MemSide.own`, `mp`, `abortAt`, `pl`, `xa`, `bo`, `lo`; defaults as
`MemSide`'s). -/
def MemSide.ofLabels {I : ISA} (rd : TermRun.Word → Prop) (lbl : WeakMem.AllocLabel → Option Nat)
    (lsize : WeakMem.AllocLabel → Nat) (K : Option (Scc.Sem.Kernel.Abi I) := none)
    (G : Loc → Val → Prop := fun _ _ => True) (heap ctr : Nat := 0) (units : Nat → CoreLang.Ty → Nat := fun _ _ => 1)
    (off : Nat → CoreLang.Ty → Nat := fun _ _ => 8) (cells : Nat := 0)
    (own : I.State → List (Loc × Val) := fun _ => []) (mp : Loc → Bool → Prop := fun _ _ => False)
    (abortAt : I.State → Prop := fun _ => False) (pl : I.State → Ctl → Prop := fun _ _ => False)
    (xa : WeakMem.AllocLabel → Nat → Nat → Frag I := fun _ _ _ _ _ => False)
    (bo : I.State → Nat → Ctl → (Ctl → Prop) → Prop := fun _ _ _ _ => False)
    (lo : Nat → Prop := fun _ => True) : MemSide I :=
  { rd, rt := fun a => ¬ ∃ l b, lbl l = some b ∧ (lrange lsize l b).contains a, K, G, heap, ctr, units,
    off, cells, own, mp, abortAt, pl, xa, bo, lo }

section KStore

variable {I : ISA} (A : Arch)

/-- **A plain store, Kraken side**: the thread lands at the tree's state,
and either appends the message (promising its timestamp and fulfilling it
at once) or fulfils an outstanding promise of the same message, leaving
memory unchanged. -/
theorem k_store_out {tid : Nat} {t : Thread I} {mem : Memory} {q : Thread I × Memory} {kr : Kraken.StoreKind}
    {L : Loc} {V : Val} {s' : I.State} (hex : I.exec t.st = some (.store kr false L V fun _ => .done s'))
    (h : ThreadStep A tid (t, mem) q) :
    q.1.st = s' ∧
      ((q.2 = (mem.append ⟨L, V, tid⟩).1 ∧ q.1.prom = (t.prom ++ [mem.last + 1]).erase (mem.last + 1)) ∨
       (∃ ts ∈ t.prom, mem.get? ts = some ⟨L, V, tid⟩ ∧ q.2 = mem ∧ q.1.prom = t.prom.erase ts)) := by
  obtain ⟨outs, o, hs, ho, rfl⟩ := h
  obtain ⟨st, c', hrun, hth, hm⟩ := (stepOne_ok_iff A tid hex).mp ⟨outs, o, hs, ho, rfl, rfl⟩
  rw [run_store_iff] at hrun
  obtain ⟨rfl, hw⟩ := hrun
  refine ⟨finishInstr_st hth, ?_⟩
  have hp := (finishInstr_relKey hth).1
  rcases (mem_writeSuccs_iff A tid _).mp hw with ⟨ts, hts, hg, -, rfl⟩ | ⟨-, rfl⟩
  · exact .inr ⟨ts, hts, hg, hm, hp⟩
  · exact .inl ⟨hm, hp⟩

/-- **A plain store with no outstanding promise** appends the message and
keeps no promise. -/
theorem k_store_append {tid : Nat} {t : Thread I} {mem : Memory} {q : Thread I × Memory} {kr : Kraken.StoreKind}
    {L : Loc} {V : Val} {s' : I.State} (hex : I.exec t.st = some (.store kr false L V fun _ => .done s'))
    (h : ThreadStep A tid (t, mem) q) (hp : t.prom = []) :
    q.1.st = s' ∧ q.2 = (mem.append ⟨L, V, tid⟩).1 ∧ q.1.prom = [] := by
  obtain ⟨hst, ⟨hm, hq⟩ | ⟨ts, hts, -⟩⟩ := k_store_out A hex h
  · rw [hp] at hq
    exact ⟨hst, hm, by simpa using hq⟩
  · rw [hp] at hts; cases hts

/-- **A plain store has no faulting outcome.** -/
theorem k_store_no_error {t : Thread I} {tid : Nat} {mem : Memory} {kr : Kraken.StoreKind} {L : Loc} {V : Val}
    {s' : I.State} (hex : I.exec t.st = some (.store kr false L V fun _ => .done s'))
    {outs : List (Except String (Outcome I))} (hs : stepOne A t tid mem = some outs) (m : String) :
    (.error m : Except String (Outcome I)) ∉ outs :=
  Spike.Bridge.stepOne_no_error A hex (Spike.Bridge.runTree_store_ok A _ _ _ _ _ _ _) hs m

end KStore

/-- **A runtime store keeps the memory relation**, the source stuttering:
in the append case by `MemRel.runtime_write`, in the fulfil case because
memory is unchanged. -/
theorem rtStore_memRel {I : ISA} (A : Arch) {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {sm : WeakMem.Memory} {pairs : List Nat}
    {rd : TermRun.Word → Prop} {tid : Nat} {t : Thread I} {mem : Memory} {q : Thread I × Memory}
    {kr : Kraken.StoreKind} {L : Loc} {V : Val} {s' : I.State}
    (hex : I.exec t.st = some (.store kr false L V fun _ => .done s'))
    (hrt : (MemSide.ofLabels (I := I) rd lbl lsize).rt L.addr.toNat)
    (h : ThreadStep A tid (t, mem) q) (hm : MemRel Λ lbl lsize ts mem sm pairs) :
    MemRel Λ lbl lsize ts q.2 sm pairs := by
  obtain ⟨-, ⟨hq, -⟩ | ⟨-, -, -, hq, -⟩⟩ := k_store_out A hex h
  · rw [hq]; exact hm.runtime_write hrt
  · rw [hq]; exact hm

end Spike.Lib
