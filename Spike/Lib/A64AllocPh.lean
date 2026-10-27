/-
**`scc_rt_alloc`'s phase check** (AArch64; read by A7's `tailOffC`):
`allocPhOk` (each block of `Flow.allocIn` `blkPh` without dead targets,
each single instruction off the sites and its next pc in its phase, the
`ret` off the sites and in the phase of the function's entry), at any
`okPc`, `ph` and labels:

- `allocPhOk`: the check (read by `Spike/Lib/A64AllocG.lean`'s `allocPc`,
  `allocSt`, `allocAb`). The `ret`'s target is its caller's return address,
  not checked here: a call site gives the return address in the phase of
  `scc_rt_alloc`'s entry (its `bl`'s target), and the check gives the
  `ret`'s pc in that phase, so the two meet without a walk along the
  function's edges.
- `allocLabs`: the labels it reads (the function's labels and every branch
  target of its blocks); `allocPhOk_congr`: two label maps agreeing on them
  give the same check.

This file stays free of the segment proofs so that `PlaceOK` (A7) reads it.
-/
import Spike.Lib.A64AbortPh

namespace Spike.Lib.A64.AllocG

open Kraken Kraken.AArch64.Parser
open Spike.Lib.A64Consumer (blkPh)
open Spike.Lib.LowerA64 (blkLabs blkPh_congr)
open Spike.Lib.A64.StubW (phOne)
open Spike.Lib.A64.Alloc

/-- **`scc_rt_alloc`'s phase check**: its blocks (`blkPh` without dead
targets), its single instructions (`phOne`), and its `ret` off the sites
and in the phase of the function's entry. -/
def allocPhOk (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) : Bool :=
  blkPh okPc ph (fun _ => false) lab (lab "scc_rt_alloc" + Int64.ofNat (4 * 0)) 0 b0 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L2_scc_rt_alloc.0_entry" + Int64.ofNat (4 * 0)) 0 b1 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L2_scc_rt_alloc.0_entry" + Int64.ofNat (4 * 4)) 0 b2 &&
  phOne okPc ph (lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 0)) &&
  phOne okPc ph (lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 1)) &&
  blkPh okPc ph (fun _ => false) lab (lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 2)) 0 b3 &&
  phOne okPc ph (lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 5)) &&
  blkPh okPc ph (fun _ => false) lab (lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 6)) 0 b4 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 15)) 0 b5 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L2_scc_rt_alloc.2_slow" + Int64.ofNat (4 * 0)) 0 b6 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L2_scc_rt_alloc.2_slow" + Int64.ofNat (4 * 4)) 0 b7 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L2_scc_rt_alloc.4_full" + Int64.ofNat (4 * 0)) 0 b9 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 0)) 0 b11 &&
  phOne okPc ph (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 8)) &&
  phOne okPc ph (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 9)) &&
  blkPh okPc ph (fun _ => false) lab (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 10)) 0 b12 &&
  phOne okPc ph (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 41)) &&
  blkPh okPc ph (fun _ => false) lab (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 42)) 0 b13 &&
  okPc (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 54)).toBitVec.toNat &&
  ph (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 54)).toBitVec.toNat == ph (lab "scc_rt_alloc").toBitVec.toNat

/-- The function's own labels `allocPhOk` reads. -/
def allocOwnLabs : List String :=
  ["scc_rt_alloc", ".L2_scc_rt_alloc.0_entry", ".L2_scc_rt_alloc.1_cnt", ".L2_scc_rt_alloc.2_slow",
    ".L2_scc_rt_alloc.4_full", ".L2_scc_rt_alloc.5_ok"]

/-- **The labels `allocPhOk` reads**: the function's own and its blocks'
branch targets. -/
def allocLabs : List String :=
  allocOwnLabs ++ blkLabs b0 ++ blkLabs b1 ++ blkLabs b2 ++ blkLabs b3 ++ blkLabs b4 ++ blkLabs b5 ++
    blkLabs b6 ++ blkLabs b7 ++ blkLabs b9 ++ blkLabs b11 ++ blkLabs b12 ++ blkLabs b13

/-- **`allocPhOk` reads the labels of `allocLabs` only.** -/
theorem allocPhOk_congr {okPc : Nat → Bool} {ph : Nat → Nat} {lab lab' : Label → Int64}
    (h : ∀ l ∈ allocLabs, lab l = lab' l) : allocPhOk okPc ph lab = allocPhOk okPc ph lab' := by
  have ho : ∀ l ∈ allocOwnLabs, lab l = lab' l := fun l hl => h l (by simp only [allocLabs]; simp [hl])
  have hb : ∀ blk, blkLabs blk ⊆ allocLabs → ∀ l ∈ blkLabs blk, lab l = lab' l :=
    fun _ hs l hl => h l (hs hl)
  unfold allocPhOk
  rw [ho "scc_rt_alloc" (by simp [allocOwnLabs]), ho ".L2_scc_rt_alloc.0_entry" (by simp [allocOwnLabs]),
    ho ".L2_scc_rt_alloc.1_cnt" (by simp [allocOwnLabs]), ho ".L2_scc_rt_alloc.2_slow" (by simp [allocOwnLabs]),
    ho ".L2_scc_rt_alloc.4_full" (by simp [allocOwnLabs]), ho ".L2_scc_rt_alloc.5_ok" (by simp [allocOwnLabs]),
    blkPh_congr (hb b0 fun l hl => by simp only [allocLabs]; simp [hl]),
    blkPh_congr (hb b1 fun l hl => by simp only [allocLabs]; simp [hl]),
    blkPh_congr (hb b2 fun l hl => by simp only [allocLabs]; simp [hl]),
    blkPh_congr (hb b3 fun l hl => by simp only [allocLabs]; simp [hl]),
    blkPh_congr (hb b4 fun l hl => by simp only [allocLabs]; simp [hl]),
    blkPh_congr (hb b5 fun l hl => by simp only [allocLabs]; simp [hl]),
    blkPh_congr (hb b6 fun l hl => by simp only [allocLabs]; simp [hl]),
    blkPh_congr (hb b7 fun l hl => by simp only [allocLabs]; simp [hl]),
    blkPh_congr (hb b9 fun l hl => by simp only [allocLabs]; simp [hl]),
    blkPh_congr (hb b11 fun l hl => by simp only [allocLabs]; simp [hl]),
    blkPh_congr (hb b12 fun l hl => by simp only [allocLabs]; simp [hl]),
    blkPh_congr (hb b13 fun l hl => by simp only [allocLabs]; simp [hl])]

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64.AllocG.allocPhOk_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocPhOk_congr

end Spike.Lib.A64.AllocG
