/-
**The threads abort path's phase check** (x86-64): `abortPhThreadsOk`, the
threads twin of `abortPhWriteOk` (`Spike/Lib/X64AbortPhW.lean`) and the x86-64
twin of `Spike/Lib/A64AbortPhT.lean`: each block of the dispatcher at code 5
(`d0`, `t1`, `j1`, `t2`, `j2`, `t3`, `j3`, `t4`, `j4`, `t5`, `g5`) and of the
threads stub `blkPh` without dead targets, each single instruction off the
sites and its next pc in its phase (`phOne`), the exit call's next pc in its
phase.

- `abortPhThreadsOk`: the check at any `okPc`, `ph` and labels (for the
  threads stub's abort-phase facts);
- `abortThreadsLabs`: the labels it reads; `abortPhThreadsOk_congr`: two
  label maps agreeing on them give the same check.

Like `X64AbortPh`, this file stays free of the segment proofs.
-/
import Spike.Lib.X64AbortPhW

namespace Spike.Lib.X64.StubW

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64
open Spike.Lib.X64Consumer (blkPh)
open Spike.Lib.LowerX64 (blkLabs blkPh_congr)

/-- **The threads abort path's phase check**: the dispatcher's blocks at code
5 and the threads stub's blocks (`blkPh` without dead targets), the stub's
single instructions (`phOne`: the `leaq` and the `write` call), and the
exit call's next pc in its phase (the exit call is an abort site, so not
off the sites). -/
def abortPhThreadsOk (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) : Bool :=
  blkPh okPc ph (fun _ => false) lab (lab "scc_rt_abort" + Int64.ofNat 0) 0 Abort.Disp.d0 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_abort.entry" + Int64.ofNat 0) 0 Abort.Disp.t1 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_abort.entry" + Int64.ofNat 16) 0 Abort.Disp.j1 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_abort.next1" + Int64.ofNat 0) 0 Abort.Disp.t2 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_abort.next1" + Int64.ofNat 16) 0 Abort.Disp.j2 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_abort.next3" + Int64.ofNat 0) 0 Abort.Disp.t3 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_abort.next3" + Int64.ofNat 16) 0 Abort.Disp.j3 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_abort.next5" + Int64.ofNat 0) 0 Abort.Disp.t4 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_abort.next5" + Int64.ofNat 16) 0 Abort.Disp.j4 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_abort.next7" + Int64.ofNat 0) 0 Abort.Disp.t5 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_abort.is8" + Int64.ofNat 0) 0 Abort.Disp.g5 &&
  blkPh okPc ph (fun _ => false) lab (lab Abort.threads.fn + Int64.ofNat 0) 0 Abort.x0 &&
  phOne okPc ph (lab Abort.threads.entry + Int64.ofNat 0) 7 &&
  blkPh okPc ph (fun _ => false) lab (lab Abort.threads.entry + Int64.ofNat 7) 0 Abort.x1Threads &&
  phOne okPc ph (lab Abort.threads.entry + Int64.ofNat 34) 2 &&
  blkPh okPc ph (fun _ => false) lab (lab Abort.threads.entry + Int64.ofNat 36) 0 Abort.x2 &&
  ph (lab Abort.threads.exit + Int64.ofNat 2).toBitVec.toNat == ph (lab Abort.threads.exit).toBitVec.toNat

/-- The path's own labels `abortPhThreadsOk` reads. -/
def abortThreadsOwnLabs : List String :=
  ["scc_rt_abort", ".Lscc_rt_abort.entry", ".Lscc_rt_abort.next1", ".Lscc_rt_abort.next3",
    ".Lscc_rt_abort.next5", ".Lscc_rt_abort.next7", ".Lscc_rt_abort.is8", Abort.threads.fn,
    Abort.threads.entry, Abort.threads.exit]

/-- **The labels `abortPhThreadsOk` reads**: the path's own and its blocks'
branch targets. -/
def abortThreadsLabs : List String :=
  abortThreadsOwnLabs ++ blkLabs Abort.Disp.d0 ++ blkLabs Abort.Disp.t1 ++ blkLabs Abort.Disp.j1 ++
    blkLabs Abort.Disp.t2 ++ blkLabs Abort.Disp.j2 ++ blkLabs Abort.Disp.t3 ++ blkLabs Abort.Disp.j3 ++
    blkLabs Abort.Disp.t4 ++ blkLabs Abort.Disp.j4 ++ blkLabs Abort.Disp.t5 ++ blkLabs Abort.Disp.g5 ++
    blkLabs Abort.x0 ++ blkLabs Abort.x1Threads ++
    blkLabs Abort.x2

/-- **`abortPhThreadsOk` reads the labels of `abortThreadsLabs` only.** -/
theorem abortPhThreadsOk_congr {okPc : Nat → Bool} {ph : Nat → Nat} {lab lab' : Label → Int64}
    (h : ∀ l ∈ abortThreadsLabs, lab l = lab' l) : abortPhThreadsOk okPc ph lab = abortPhThreadsOk okPc ph lab' := by
  have ho : ∀ l ∈ abortThreadsOwnLabs, lab l = lab' l := fun l hl => h l (by simp only [abortThreadsLabs]; simp [hl])
  have hb : ∀ blk, blkLabs blk ⊆ abortThreadsLabs → ∀ l ∈ blkLabs blk, lab l = lab' l :=
    fun _ hs l hl => h l (hs hl)
  unfold abortPhThreadsOk
  rw [ho "scc_rt_abort" (by simp [abortThreadsOwnLabs]), ho ".Lscc_rt_abort.entry" (by simp [abortThreadsOwnLabs]),
    ho ".Lscc_rt_abort.next1" (by simp [abortThreadsOwnLabs]),
    ho ".Lscc_rt_abort.next3" (by simp [abortThreadsOwnLabs]),
    ho ".Lscc_rt_abort.next5" (by simp [abortThreadsOwnLabs]),
    ho ".Lscc_rt_abort.next7" (by simp [abortThreadsOwnLabs]),
    ho ".Lscc_rt_abort.is8" (by simp [abortThreadsOwnLabs]),
    ho Abort.threads.fn (by simp [abortThreadsOwnLabs]), ho Abort.threads.entry (by simp [abortThreadsOwnLabs]),
    ho Abort.threads.exit (by simp [abortThreadsOwnLabs]),
    blkPh_congr (hb Abort.Disp.d0 fun l hl => by simp only [abortThreadsLabs]; simp [hl]),
    blkPh_congr (hb Abort.Disp.t1 fun l hl => by simp only [abortThreadsLabs]; simp [hl]),
    blkPh_congr (hb Abort.Disp.j1 fun l hl => by simp only [abortThreadsLabs]; simp [hl]),
    blkPh_congr (hb Abort.Disp.t2 fun l hl => by simp only [abortThreadsLabs]; simp [hl]),
    blkPh_congr (hb Abort.Disp.j2 fun l hl => by simp only [abortThreadsLabs]; simp [hl]),
    blkPh_congr (hb Abort.Disp.t3 fun l hl => by simp only [abortThreadsLabs]; simp [hl]),
    blkPh_congr (hb Abort.Disp.j3 fun l hl => by simp only [abortThreadsLabs]; simp [hl]),
    blkPh_congr (hb Abort.Disp.t4 fun l hl => by simp only [abortThreadsLabs]; simp [hl]),
    blkPh_congr (hb Abort.Disp.j4 fun l hl => by simp only [abortThreadsLabs]; simp [hl]),
    blkPh_congr (hb Abort.Disp.t5 fun l hl => by simp only [abortThreadsLabs]; simp [hl]),
    blkPh_congr (hb Abort.Disp.g5 fun l hl => by simp only [abortThreadsLabs]; simp [hl]),
    blkPh_congr (hb Abort.x0 fun l hl => by simp only [abortThreadsLabs]; simp [hl]),
    blkPh_congr (hb Abort.x1Threads fun l hl => by simp only [abortThreadsLabs]; simp [hl]),
    blkPh_congr (hb Abort.x2 fun l hl => by simp only [abortThreadsLabs]; simp [hl])]

end Spike.Lib.X64.StubW

/-- info: 'Spike.Lib.X64.StubW.abortPhThreadsOk_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.StubW.abortPhThreadsOk_congr
