/-
**The write abort path's phase check** (x86-64): `abortPhWriteOk`, the
write twin of `abortPhHeapOk` (`Spike/Lib/X64AbortPhH.lean`) and the x86-64
twin of `Spike/Lib/A64AbortPhW.lean`: each block of the dispatcher at code 4
(`d0`, `t1`, `j1`, `t2`, `j2`, `t3`, `j3`, `t4`, `g4`) and of the write stub
`blkPh` without dead targets, each single instruction off the sites and its
next pc in its phase (`phOne`), the exit call's next pc in its phase.

- `abortPhWriteOk`: the check at any `okPc`, `ph` and labels (for the write
  stub's `SFactsA` facts, `Spike/Lib/X64StubWA.lean`);
- `abortWriteLabs`: the labels it reads; `abortPhWriteOk_congr`: two label
  maps agreeing on them give the same check.

Like `X64AbortPh`, this file stays free of the segment proofs.
-/
import Spike.Lib.X64AbortPh

namespace Spike.Lib.X64.StubW

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64
open Spike.Lib.X64Consumer (blkPh)
open Spike.Lib.LowerX64 (blkLabs blkPh_congr)

/-- **The write abort path's phase check**: the dispatcher's blocks at code
4 and the write stub's blocks (`blkPh` without dead targets), the stub's
single instructions (`phOne`: the `leaq` and the `write` call), and the
exit call's next pc in its phase (the exit call is an abort site, so not
off the sites). -/
def abortPhWriteOk (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) : Bool :=
  blkPh okPc ph (fun _ => false) lab (lab "scc_rt_abort" + Int64.ofNat 0) 0 Abort.Disp.d0 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_abort.entry" + Int64.ofNat 0) 0 Abort.Disp.t1 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_abort.entry" + Int64.ofNat 16) 0 Abort.Disp.j1 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_abort.next1" + Int64.ofNat 0) 0 Abort.Disp.t2 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_abort.next1" + Int64.ofNat 16) 0 Abort.Disp.j2 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_abort.next3" + Int64.ofNat 0) 0 Abort.Disp.t3 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_abort.next3" + Int64.ofNat 16) 0 Abort.Disp.j3 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_abort.next5" + Int64.ofNat 0) 0 Abort.Disp.t4 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_abort.is6" + Int64.ofNat 0) 0 Abort.Disp.g4 &&
  blkPh okPc ph (fun _ => false) lab (lab Abort.write.fn + Int64.ofNat 0) 0 Abort.x0 &&
  phOne okPc ph (lab Abort.write.entry + Int64.ofNat 0) 7 &&
  blkPh okPc ph (fun _ => false) lab (lab Abort.write.entry + Int64.ofNat 7) 0 Abort.x1Write &&
  phOne okPc ph (lab Abort.write.entry + Int64.ofNat 34) 2 &&
  blkPh okPc ph (fun _ => false) lab (lab Abort.write.entry + Int64.ofNat 36) 0 Abort.x2 &&
  ph (lab Abort.write.exit + Int64.ofNat 2).toBitVec.toNat == ph (lab Abort.write.exit).toBitVec.toNat

/-- The path's own labels `abortPhWriteOk` reads. -/
def abortWriteOwnLabs : List String :=
  ["scc_rt_abort", ".Lscc_rt_abort.entry", ".Lscc_rt_abort.next1", ".Lscc_rt_abort.next3",
    ".Lscc_rt_abort.next5", ".Lscc_rt_abort.is6", Abort.write.fn, Abort.write.entry, Abort.write.exit]

/-- **The labels `abortPhWriteOk` reads**: the path's own and its blocks'
branch targets. -/
def abortWriteLabs : List String :=
  abortWriteOwnLabs ++ blkLabs Abort.Disp.d0 ++ blkLabs Abort.Disp.t1 ++ blkLabs Abort.Disp.j1 ++
    blkLabs Abort.Disp.t2 ++ blkLabs Abort.Disp.j2 ++ blkLabs Abort.Disp.t3 ++ blkLabs Abort.Disp.j3 ++
    blkLabs Abort.Disp.t4 ++ blkLabs Abort.Disp.g4 ++ blkLabs Abort.x0 ++ blkLabs Abort.x1Write ++
    blkLabs Abort.x2

/-- **`abortPhWriteOk` reads the labels of `abortWriteLabs` only.** -/
theorem abortPhWriteOk_congr {okPc : Nat → Bool} {ph : Nat → Nat} {lab lab' : Label → Int64}
    (h : ∀ l ∈ abortWriteLabs, lab l = lab' l) : abortPhWriteOk okPc ph lab = abortPhWriteOk okPc ph lab' := by
  have ho : ∀ l ∈ abortWriteOwnLabs, lab l = lab' l := fun l hl => h l (by simp only [abortWriteLabs]; simp [hl])
  have hb : ∀ blk, blkLabs blk ⊆ abortWriteLabs → ∀ l ∈ blkLabs blk, lab l = lab' l :=
    fun _ hs l hl => h l (hs hl)
  unfold abortPhWriteOk
  rw [ho "scc_rt_abort" (by simp [abortWriteOwnLabs]), ho ".Lscc_rt_abort.entry" (by simp [abortWriteOwnLabs]),
    ho ".Lscc_rt_abort.next1" (by simp [abortWriteOwnLabs]), ho ".Lscc_rt_abort.next3" (by simp [abortWriteOwnLabs]),
    ho ".Lscc_rt_abort.next5" (by simp [abortWriteOwnLabs]), ho ".Lscc_rt_abort.is6" (by simp [abortWriteOwnLabs]),
    ho Abort.write.fn (by simp [abortWriteOwnLabs]), ho Abort.write.entry (by simp [abortWriteOwnLabs]),
    ho Abort.write.exit (by simp [abortWriteOwnLabs]),
    blkPh_congr (hb Abort.Disp.d0 fun l hl => by simp only [abortWriteLabs]; simp [hl]),
    blkPh_congr (hb Abort.Disp.t1 fun l hl => by simp only [abortWriteLabs]; simp [hl]),
    blkPh_congr (hb Abort.Disp.j1 fun l hl => by simp only [abortWriteLabs]; simp [hl]),
    blkPh_congr (hb Abort.Disp.t2 fun l hl => by simp only [abortWriteLabs]; simp [hl]),
    blkPh_congr (hb Abort.Disp.j2 fun l hl => by simp only [abortWriteLabs]; simp [hl]),
    blkPh_congr (hb Abort.Disp.t3 fun l hl => by simp only [abortWriteLabs]; simp [hl]),
    blkPh_congr (hb Abort.Disp.j3 fun l hl => by simp only [abortWriteLabs]; simp [hl]),
    blkPh_congr (hb Abort.Disp.t4 fun l hl => by simp only [abortWriteLabs]; simp [hl]),
    blkPh_congr (hb Abort.Disp.g4 fun l hl => by simp only [abortWriteLabs]; simp [hl]),
    blkPh_congr (hb Abort.x0 fun l hl => by simp only [abortWriteLabs]; simp [hl]),
    blkPh_congr (hb Abort.x1Write fun l hl => by simp only [abortWriteLabs]; simp [hl]),
    blkPh_congr (hb Abort.x2 fun l hl => by simp only [abortWriteLabs]; simp [hl])]

end Spike.Lib.X64.StubW
