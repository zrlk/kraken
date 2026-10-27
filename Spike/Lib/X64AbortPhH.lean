/-
**The heap abort path's phase check** (x86-64): `abortPhHeapOk`, the heap
twin of `abortPhOk` (`Spike/Lib/X64AbortPh.lean`) and the x86-64 twin of
`Spike/Lib/A64AbortPhH.lean`: each block of the dispatcher at code 2 (`d0`,
`t1`, `j1`, `t2`, `g2`) and of the heap stub `blkPh` without dead targets,
each single instruction off the sites and its next pc in its phase
(`phOne`), the exit call's next pc in its phase.

- `abortPhHeapOk`: the check at any `okPc`, `ph` and labels (for the heap
  stub's `SFactsA` facts, `Spike/Lib/X64StubHA.lean`);
- `abortHeapLabs`: the labels it reads; `abortPhHeapOk_congr`: two label
  maps agreeing on them give the same check.

Like `X64AbortPh`, this file stays free of the segment proofs.
-/
import Spike.Lib.X64AbortPh

namespace Spike.Lib.X64.StubW

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64
open Spike.Lib.X64Consumer (blkPh)
open Spike.Lib.LowerX64 (blkLabs blkPh_congr)

/-- **The heap abort path's phase check**: the dispatcher's blocks at code
2 and the heap stub's blocks (`blkPh` without dead targets), the stub's
single instructions (`phOne`: the `leaq` and the `write` call), and the
exit call's next pc in its phase (the exit call is an abort site, so not
off the sites). -/
def abortPhHeapOk (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) : Bool :=
  blkPh okPc ph (fun _ => false) lab (lab "scc_rt_abort" + Int64.ofNat 0) 0 Abort.Disp.d0 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_abort.entry" + Int64.ofNat 0) 0 Abort.Disp.t1 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_abort.entry" + Int64.ofNat 16) 0 Abort.Disp.j1 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_abort.next1" + Int64.ofNat 0) 0 Abort.Disp.t2 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_abort.is2" + Int64.ofNat 0) 0 Abort.Disp.g2 &&
  blkPh okPc ph (fun _ => false) lab (lab Abort.heap.fn + Int64.ofNat 0) 0 Abort.x0 &&
  phOne okPc ph (lab Abort.heap.entry + Int64.ofNat 0) 7 &&
  blkPh okPc ph (fun _ => false) lab (lab Abort.heap.entry + Int64.ofNat 7) 0 Abort.x1Heap &&
  phOne okPc ph (lab Abort.heap.entry + Int64.ofNat 34) 2 &&
  blkPh okPc ph (fun _ => false) lab (lab Abort.heap.entry + Int64.ofNat 36) 0 Abort.x2 &&
  ph (lab Abort.heap.exit + Int64.ofNat 2).toBitVec.toNat == ph (lab Abort.heap.exit).toBitVec.toNat

/-- The path's own labels `abortPhHeapOk` reads. -/
def abortHeapOwnLabs : List String :=
  ["scc_rt_abort", ".Lscc_rt_abort.entry", ".Lscc_rt_abort.next1", ".Lscc_rt_abort.is2", Abort.heap.fn,
    Abort.heap.entry, Abort.heap.exit]

/-- **The labels `abortPhHeapOk` reads**: the path's own and its blocks'
branch targets. -/
def abortHeapLabs : List String :=
  abortHeapOwnLabs ++ blkLabs Abort.Disp.d0 ++ blkLabs Abort.Disp.t1 ++ blkLabs Abort.Disp.j1 ++
    blkLabs Abort.Disp.t2 ++ blkLabs Abort.Disp.g2 ++ blkLabs Abort.x0 ++ blkLabs Abort.x1Heap ++ blkLabs Abort.x2

/-- **`abortPhHeapOk` reads the labels of `abortHeapLabs` only.** -/
theorem abortPhHeapOk_congr {okPc : Nat → Bool} {ph : Nat → Nat} {lab lab' : Label → Int64}
    (h : ∀ l ∈ abortHeapLabs, lab l = lab' l) : abortPhHeapOk okPc ph lab = abortPhHeapOk okPc ph lab' := by
  have ho : ∀ l ∈ abortHeapOwnLabs, lab l = lab' l := fun l hl => h l (by simp only [abortHeapLabs]; simp [hl])
  have hb : ∀ blk, blkLabs blk ⊆ abortHeapLabs → ∀ l ∈ blkLabs blk, lab l = lab' l :=
    fun _ hs l hl => h l (hs hl)
  unfold abortPhHeapOk
  rw [ho "scc_rt_abort" (by simp [abortHeapOwnLabs]), ho ".Lscc_rt_abort.entry" (by simp [abortHeapOwnLabs]),
    ho ".Lscc_rt_abort.next1" (by simp [abortHeapOwnLabs]), ho ".Lscc_rt_abort.is2" (by simp [abortHeapOwnLabs]),
    ho Abort.heap.fn (by simp [abortHeapOwnLabs]), ho Abort.heap.entry (by simp [abortHeapOwnLabs]),
    ho Abort.heap.exit (by simp [abortHeapOwnLabs]),
    blkPh_congr (hb Abort.Disp.d0 fun l hl => by simp only [abortHeapLabs]; simp [hl]),
    blkPh_congr (hb Abort.Disp.t1 fun l hl => by simp only [abortHeapLabs]; simp [hl]),
    blkPh_congr (hb Abort.Disp.j1 fun l hl => by simp only [abortHeapLabs]; simp [hl]),
    blkPh_congr (hb Abort.Disp.t2 fun l hl => by simp only [abortHeapLabs]; simp [hl]),
    blkPh_congr (hb Abort.Disp.g2 fun l hl => by simp only [abortHeapLabs]; simp [hl]),
    blkPh_congr (hb Abort.x0 fun l hl => by simp only [abortHeapLabs]; simp [hl]),
    blkPh_congr (hb Abort.x1Heap fun l hl => by simp only [abortHeapLabs]; simp [hl]),
    blkPh_congr (hb Abort.x2 fun l hl => by simp only [abortHeapLabs]; simp [hl])]

end Spike.Lib.X64.StubW
