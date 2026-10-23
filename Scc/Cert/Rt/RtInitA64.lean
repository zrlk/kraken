import Scc.Cert.Rt.RtWordsA64

/-!
# The runtime's words at load (AArch64; A8's `rtInitOk`)

The runtime writes its data words (`rtWords`: the counters, the first TCB's
header and fields) and reads them after its own writes; a value invariant
on them (the consumer's `G`, e.g. `FixG` on the limit word) holds at load
when their initial values are known. The canonical load's initial memory
(`initOf`, `loadParsed_of_loadOk`) is the image's words and the `.rodata`
words; `rtInitOk` checks by evaluation, fail-closed, that no runtime word
has an entry there, so each starts at `0` (`initVal_rt_of_rtInitOk`).
`rtOffOk` checks that the first TCB's words (in the pinned region) are
clear of `.data` and the heap (`clear_of_rtOffOk`), so no placed data and
no allocation shares one. The four counters (`scc_rt_pinned_next`,
`scc_rt_stack_next`, `scc_rt_stack_lock`, `scc_rt_stack_free_n`) are `.bss`
words in `.data`, not checked here: the heap is disjoint from `.data`
(`Link.wfB`, A1), and no label is placed in the static link (`static _ :=
none`), so the user's memory side covers none of them (`RtFree` with
`lbl = fun _ => none`, `rtFree_ofPlaceOK`).
-/

namespace Scc.Cert.Rt.A64

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.Link.A64

/-- **The canonical load's initial words**: the image, then `.rodata`
(`loadParsed_of_loadOk`). -/
def initOf (Λ : Scc.Sem.Layout) (prog : Program) (secs : DataSecs) : List (Loc × Val) :=
  imageMem Λ ++ wordsMem (rodataWords Λ secs.rodata (quadCode Λ prog))

/-- **The runtime's words start at `0`**: none of them has an initial
word in the load (`initOf`). -/
def rtInitOk (Λ : Scc.Sem.Layout) (prog : Program) (secs : DataSecs) : Bool :=
  (rtWords (rtA Λ prog secs "scc_rt_pinned") (rtA Λ prog secs "scc_rt_pinned_next")
      (rtA Λ prog secs "scc_rt_stack_next") (rtA Λ prog secs "scc_rt_stack_lock")
      (rtA Λ prog secs "scc_rt_stack_free_n")).all fun a =>
    ((initOf Λ prog secs).find? (·.1 == ⟨a, 8⟩)).isNone

/-- **A runtime word's initial value is `0`** in any memory with the load's
initial words. -/
theorem initVal_rt_of_rtInitOk {Λ : Scc.Sem.Layout} {prog : Program} {secs : DataSecs}
    (h : rtInitOk Λ prog secs = true) {m : Memory} (hm : m.init = initOf Λ prog secs) {a : BitVec 64}
    (ha : a ∈ rtWords (rtA Λ prog secs "scc_rt_pinned") (rtA Λ prog secs "scc_rt_pinned_next")
      (rtA Λ prog secs "scc_rt_stack_next") (rtA Λ prog secs "scc_rt_stack_lock")
      (rtA Λ prog secs "scc_rt_stack_free_n")) :
    m.initVal ⟨a, 8⟩ = 0 := by
  have := List.all_eq_true.mp h a ha
  unfold Memory.initVal
  rw [hm, Option.isNone_iff_eq_none.mp this]
  rfl

/-- **The first TCB's words are off `.data` and the heap**: the header at
`scc_rt_pinned` and its six fields (`scc_rt_pinned + 8 j`, `j < 7`), each
word's 8 bytes clear of both (`clearB`), so no placed data label and no
heap allocation covers one. The counters are `.bss` words in `.data`, not
checked. -/
def rtOffOk (Λ : Scc.Sem.Layout) (prog : Program) (secs : DataSecs) : Bool :=
  (List.range 7).all fun j =>
    clearB Λ.data (rtA Λ prog secs "scc_rt_pinned" + BitVec.ofNat 64 (8 * j)) &&
      clearB Λ.heap (rtA Λ prog secs "scc_rt_pinned" + BitVec.ofNat 64 (8 * j))

/-- **A word of the first TCB is clear of `.data` and the heap.** -/
theorem clear_of_rtOffOk {Λ : Scc.Sem.Layout} {prog : Program} {secs : DataSecs}
    (h : rtOffOk Λ prog secs = true) {j : Nat} (hj : j < 7) :
    clearB Λ.data (rtA Λ prog secs "scc_rt_pinned" + BitVec.ofNat 64 (8 * j)) = true ∧
      clearB Λ.heap (rtA Λ prog secs "scc_rt_pinned" + BitVec.ofNat 64 (8 * j)) = true := by
  have := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  simpa only [Bool.and_eq_true] using this

end Scc.Cert.Rt.A64
