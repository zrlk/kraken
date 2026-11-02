/-
**The two TCB self words at main's clone** (x86-64 only): the owned-word facts the start row's
`X64WakeOwnX.post_startOXW` needs of main's own list `own₀` at the clone, `hT0`/`hW0` and `hown`. After the
spawn, main's park and the worker's tail read their TCB's self word through `%fs:0`, so each thread's memory side
owns it (`X64HelloOwnLift.msHX`/`msWHX`): main's `⟨T, 8⟩ ↦ T`, the worker's `⟨W, 8⟩ ↦ W`. Main hands both over at
the clone, so at the clone each self word's latest write not promised must hold its address (`OwnVal`).

- `SelfWordsAtClone mem prom T W`: the two `OwnVal` facts; nothing in it is hello-specific.
- `selfPairs T W`: the two owned words; `selfPairs_T`, `selfPairs_W`: both are in `own₀ ++ selfPairs T W`
  (`hT0`, `hW0`).
- `ownOk_append`: `OwnOk` of two lists is `OwnOk` of their concatenation; `SelfWordsAtClone.ownOk`: the two
  facts as `OwnOk (selfPairs T W)`, so `hown` at `own₀ ++ selfPairs T W` is `ownOk_append hown h.ownOk`.
- `SelfWordsAtClone.of_ownOk`: the facts from an `OwnOk` list holding both words (the producer's route: main's
  pre-spawn own map with the self words appended, whose `OwnOk` the consumer maintains along the run).

**Why the value invariant cannot give these facts.** Extending hello's `G` (`X64HelloGOf2H.GOf2H`) with the self
words as fixed words (`FixG` entries `(T, T)`, `(W, W)`) only gives that every message to `⟨T, 8⟩` holds `T` or
its initial value `0`: `MemInv G` must hold of the initial values, so `G` cannot exclude a later message equal to
the initial value, and it carries no order of messages. The per-site fact that main's stores miss both words must
instead feed an order-aware invariant: the consumer's `OwnOk` of main's own map, the self words appended from
their stores on (`scc_rt_thread_init`'s self store) to the clone.

## Differences from the AArch64 version

AArch64 has no counterpart: its park and worker tail take the thread pointer from a register, so no thread owns a
TCB word and its start row's own list needs no self word.
-/
import Spike.Lib.ExtRows

namespace Spike.Lib.X64HelloSelfWords

open Kraken.Promising Scc.Sem
open Spike.Lib.ExtRows (OwnOk)

/-- **The two self words at the clone** (see the module doc): the latest write not promised of `T`'s word holds
`T`, and of `W`'s word `W`. -/
structure SelfWordsAtClone (mem : Memory) (prom : List Time) (T W : BitVec 64) : Prop where
  selfT : OwnVal mem prom T.toNat (T.setWidth 128)
  selfW : OwnVal mem prom W.toNat (W.setWidth 128)

/-- The two self words, each holding its address. -/
abbrev selfPairs (T W : BitVec 64) : List (Loc × Val) :=
  [(⟨T, 8⟩, T.setWidth 128), (⟨W, 8⟩, W.setWidth 128)]

variable {mem : Memory} {prom : List Time} {T W : BitVec 64}

/-- `T`'s word is in `own₀ ++ selfPairs T W` (`post_startOXW`'s `hT0`). -/
theorem selfPairs_T (own₀ : List (Loc × Val)) : ((⟨T, 8⟩ : Loc), T.setWidth 128) ∈ own₀ ++ selfPairs T W := by
  simp

/-- `W`'s word is in `own₀ ++ selfPairs T W` (`post_startOXW`'s `hW0`). -/
theorem selfPairs_W (own₀ : List (Loc × Val)) : ((⟨W, 8⟩ : Loc), W.setWidth 128) ∈ own₀ ++ selfPairs T W := by
  simp

/-- **`OwnOk` of a concatenation.** -/
theorem ownOk_append {o₁ o₂ : List (Loc × Val)} (h₁ : OwnOk o₁ mem prom) (h₂ : OwnOk o₂ mem prom) :
    OwnOk (o₁ ++ o₂) mem prom := by
  intro L v hm
  rcases List.mem_append.mp hm with h | h
  · exact h₁ L v h
  · exact h₂ L v h

/-- **The two facts as `OwnOk` of the two words.** -/
theorem SelfWordsAtClone.ownOk (h : SelfWordsAtClone mem prom T W) : OwnOk (selfPairs T W) mem prom := by
  intro L v hm
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨rfl, h.selfT⟩
  · exact ⟨rfl, h.selfW⟩

/-- **The two facts from an `OwnOk` list holding both words.** -/
theorem SelfWordsAtClone.of_ownOk {own : List (Loc × Val)} (h : OwnOk own mem prom)
    (hT : ((⟨T, 8⟩ : Loc), T.setWidth 128) ∈ own) (hW : ((⟨W, 8⟩ : Loc), W.setWidth 128) ∈ own) :
    SelfWordsAtClone mem prom T W :=
  ⟨(h _ _ hT).2, (h _ _ hW).2⟩

/-- **`hown` at `own₀ ++ selfPairs T W`.** -/
theorem ownOk_selfPairs {own₀ : List (Loc × Val)} (h : OwnOk own₀ mem prom) (hs : SelfWordsAtClone mem prom T W) :
    OwnOk (own₀ ++ selfPairs T W) mem prom :=
  ownOk_append h hs.ownOk

/-- **Not vacuous**: an `OwnOk` list holding both words gives the facts, which give `hown` back at the
concatenation. -/
example {own₀ : List (Loc × Val)} (h : OwnOk (own₀ ++ selfPairs T W) mem prom) :
    OwnOk (own₀ ++ selfPairs T W) mem prom :=
  ownOk_selfPairs (fun L v hm => h L v (List.mem_append_left _ hm))
    (SelfWordsAtClone.of_ownOk h (selfPairs_T own₀) (selfPairs_W own₀))

end Spike.Lib.X64HelloSelfWords

/-- info: 'Spike.Lib.X64HelloSelfWords.ownOk_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSelfWords.ownOk_append

/-- info: 'Spike.Lib.X64HelloSelfWords.SelfWordsAtClone.ownOk' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSelfWords.SelfWordsAtClone.ownOk

/-- info: 'Spike.Lib.X64HelloSelfWords.SelfWordsAtClone.of_ownOk' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSelfWords.SelfWordsAtClone.of_ownOk

/-- info: 'Spike.Lib.X64HelloSelfWords.ownOk_selfPairs' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSelfWords.ownOk_selfPairs

/-- info: 'Spike.Lib.X64HelloSelfWords.selfPairs_T' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSelfWords.selfPairs_T
