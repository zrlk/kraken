/-
**The threads abort path's phase check** (AArch64): `abortPhThreadsOk`, the
threads twin of `abortPhThreadsOk` (`Spike/Lib/A64AbortPhW.lean`): each block
of the dispatcher at code 5 (`d0`, `t1`, `j1`, `t2`, `j2`, `t3`, `j3`, `t4`,
`j4`, `t5`, `g5`) and of the threads stub `blkPh` without dead targets, each single
instruction off the sites and its next pc in its phase (`phOne`), the exit
call's next pc in its phase.

- `abortPhThreadsOk`: the check at any `okPc`, `ph` and labels (for the
  threads stub's abort-phase facts);
- `abortThreadsLabs`: the labels it reads; `abortPhThreadsOk_congr`: two
  label maps agreeing on them give the same check.

Like `A64AbortPh`, this file stays free of the segment proofs.
-/
import Spike.Lib.A64AbortPhW

namespace Spike.Lib.A64.StubW

open Kraken Kraken.AArch64.Parser
open Spike.Lib.A64Consumer (blkPh)
open Spike.Lib.LowerA64 (blkLabs blkPh_congr)

/-- **The threads abort path's phase check**: the dispatcher's blocks at code
5 and the threads stub's blocks (`blkPh` without dead targets), the stub's
single instructions (`phOne`), and the exit call's next pc in its phase
(the exit call is an abort site, so not off the sites). -/
def abortPhThreadsOk (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) : Bool :=
  blkPh okPc ph (fun _ => false) lab (lab "scc_rt_abort" + Int64.ofNat (4 * 0)) 0 Abort.Disp.d0 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L12_scc_rt_abort.0_entry" + Int64.ofNat (4 * 0)) 0 Abort.Disp.t1 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L12_scc_rt_abort.0_entry" + Int64.ofNat (4 * 4)) 0 Abort.Disp.j1 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L12_scc_rt_abort.2_next1" + Int64.ofNat (4 * 0)) 0 Abort.Disp.t2 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L12_scc_rt_abort.2_next1" + Int64.ofNat (4 * 4)) 0 Abort.Disp.j2 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L12_scc_rt_abort.4_next3" + Int64.ofNat (4 * 0)) 0 Abort.Disp.t3 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L12_scc_rt_abort.4_next3" + Int64.ofNat (4 * 4)) 0 Abort.Disp.j3 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L12_scc_rt_abort.6_next5" + Int64.ofNat (4 * 0)) 0 Abort.Disp.t4 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L12_scc_rt_abort.6_next5" + Int64.ofNat (4 * 4)) 0 Abort.Disp.j4 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L12_scc_rt_abort.8_next7" + Int64.ofNat (4 * 0)) 0 Abort.Disp.t5 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L12_scc_rt_abort.9_is8" + Int64.ofNat (4 * 0)) 0 Abort.Disp.g5 &&
  blkPh okPc ph (fun _ => false) lab (lab Abort.threads.fn + Int64.ofNat (4 * 0)) 0 Abort.b0 &&
  phOne okPc ph (lab Abort.threads.entry + Int64.ofNat (4 * 0)) &&
  phOne okPc ph (lab Abort.threads.entry + Int64.ofNat (4 * 1)) &&
  blkPh okPc ph (fun _ => false) lab (lab Abort.threads.entry + Int64.ofNat (4 * 2)) 0 Abort.b1Threads &&
  phOne okPc ph (lab Abort.threads.entry + Int64.ofNat (4 * 7)) &&
  blkPh okPc ph (fun _ => false) lab (lab Abort.threads.entry + Int64.ofNat (4 * 8)) 0 Abort.b2 &&
  ph (lab Abort.threads.exit + Int64.ofNat 4).toBitVec.toNat == ph (lab Abort.threads.exit).toBitVec.toNat

/-- The path's own labels `abortPhThreadsOk` reads. -/
def abortThreadsOwnLabs : List String :=
  ["scc_rt_abort", ".L12_scc_rt_abort.0_entry", ".L12_scc_rt_abort.2_next1", ".L12_scc_rt_abort.4_next3",
    ".L12_scc_rt_abort.6_next5", ".L12_scc_rt_abort.8_next7", ".L12_scc_rt_abort.9_is8", Abort.threads.fn, Abort.threads.entry, Abort.threads.exit]

/-- **The labels `abortPhThreadsOk` reads**: the path's own and its blocks'
branch targets. -/
def abortThreadsLabs : List String :=
  abortThreadsOwnLabs ++ blkLabs Abort.Disp.d0 ++ blkLabs Abort.Disp.t1 ++ blkLabs Abort.Disp.j1 ++
    blkLabs Abort.Disp.t2 ++ blkLabs Abort.Disp.j2 ++ blkLabs Abort.Disp.t3 ++ blkLabs Abort.Disp.j3 ++
    blkLabs Abort.Disp.t4 ++ blkLabs Abort.Disp.j4 ++ blkLabs Abort.Disp.t5 ++ blkLabs Abort.Disp.g5 ++ blkLabs Abort.b0 ++ blkLabs Abort.b1Threads ++
    blkLabs Abort.b2

/-- **`abortPhThreadsOk` reads the labels of `abortThreadsLabs` only.** -/
theorem abortPhThreadsOk_congr {okPc : Nat → Bool} {ph : Nat → Nat} {lab lab' : Label → Int64}
    (h : ∀ l ∈ abortThreadsLabs, lab l = lab' l) : abortPhThreadsOk okPc ph lab = abortPhThreadsOk okPc ph lab' := by
  have ho : ∀ l ∈ abortThreadsOwnLabs, lab l = lab' l := fun l hl => h l (by simp only [abortThreadsLabs]; simp [hl])
  have hb : ∀ blk, blkLabs blk ⊆ abortThreadsLabs → ∀ l ∈ blkLabs blk, lab l = lab' l :=
    fun _ hs l hl => h l (hs hl)
  unfold abortPhThreadsOk
  rw [ho "scc_rt_abort" (by simp [abortThreadsOwnLabs]), ho ".L12_scc_rt_abort.0_entry" (by simp [abortThreadsOwnLabs]),
    ho ".L12_scc_rt_abort.2_next1" (by simp [abortThreadsOwnLabs]),
    ho ".L12_scc_rt_abort.4_next3" (by simp [abortThreadsOwnLabs]),
    ho ".L12_scc_rt_abort.6_next5" (by simp [abortThreadsOwnLabs]),
    ho ".L12_scc_rt_abort.8_next7" (by simp [abortThreadsOwnLabs]),
    ho ".L12_scc_rt_abort.9_is8" (by simp [abortThreadsOwnLabs]), ho Abort.threads.fn (by simp [abortThreadsOwnLabs]),
    ho Abort.threads.entry (by simp [abortThreadsOwnLabs]), ho Abort.threads.exit (by simp [abortThreadsOwnLabs]),
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
    blkPh_congr (hb Abort.b0 fun l hl => by simp only [abortThreadsLabs]; simp [hl]),
    blkPh_congr (hb Abort.b1Threads fun l hl => by simp only [abortThreadsLabs]; simp [hl]),
    blkPh_congr (hb Abort.b2 fun l hl => by simp only [abortThreadsLabs]; simp [hl])]

end Spike.Lib.A64.StubW
