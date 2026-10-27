/-
**`scc_rt_print`'s phase check** (x86-64), the twin of
`Spike/Lib/A64TailPh.lean`'s `printPhOk`: each block of `Print.printIn`
`blkPh` without dead targets (the epilogue `x13` without its `ret`), the
`write` system call off the sites and its next pc in its phase (`phOne`),
and the `ret`'s pc off the sites, at any `okPc`, `ph` and labels:

- `printPhOk`: the check. The `ret`'s target is its caller's return
  address, not a label, so not checked here: `printSt`
  (`Spike/Lib/X64PrintG.lean`) takes it in the epilogue's phase.
- `printLabs`: the labels it reads (the function's labels and every branch
  and call target of its blocks); `printPhOk_congr`: two label maps
  agreeing on them give the same check.

This file stays free of the segment proofs (as `Spike/Lib/X64AllocPh.lean`).
-/
import Spike.Lib.X64AllocPh
import Spike.Lib.X64Print

namespace Spike.Lib.X64.PrintG

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64Consumer (blkPh)
open Spike.Lib.LowerX64 (blkLabs blkPh_congr)
open Spike.Lib.X64.StubW (phOne)
open Spike.Lib.X64.AllocG (aBlk)
open Spike.Lib.X64.Print (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)

/-- **`scc_rt_print`'s phase check**: its blocks (`blkPh` without dead
targets; the epilogue `x13` without its `ret`), the `write` call
(`phOne`), and the `ret`'s pc off the sites (its target, the caller's
return address, is not a label). -/
def printPhOk (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) : Bool :=
  aBlk okPc ph lab "scc_rt_print" 0 x0 && aBlk okPc ph lab ".Lscc_rt_print.entry" 0 x1 &&
  aBlk okPc ph lab ".Lscc_rt_print.loop" 0 x2 && aBlk okPc ph lab ".Lscc_rt_print.loop" 20 x3 &&
  aBlk okPc ph lab ".Lscc_rt_print.write" 0 x4 &&
  phOne okPc ph (lab ".Lscc_rt_print.write" + Int64.ofNat 20) 2 &&
  aBlk okPc ph lab ".Lscc_rt_print.write" 22 x5 && aBlk okPc ph lab ".Lscc_rt_print.write" 42 x6 &&
  aBlk okPc ph lab ".Lscc_rt_print.chk2" 0 x7 && aBlk okPc ph lab ".Lscc_rt_print.chk2" 16 x8 &&
  aBlk okPc ph lab ".Lscc_rt_print.chk3" 0 x9 && aBlk okPc ph lab ".Lscc_rt_print.chk3" 16 x10 &&
  aBlk okPc ph lab ".Lscc_rt_print.adv" 0 x11 && aBlk okPc ph lab ".Lscc_rt_print.fail" 0 x12 &&
  aBlk okPc ph lab ".Lscc_rt_print.done" 0 (x13.take 2) &&
  okPc (lab ".Lscc_rt_print.done" + Int64.ofNat 4).toBitVec.toNat

/-- The function's own labels `printPhOk` reads. -/
def printOwnLabs : List String :=
  ["scc_rt_print", ".Lscc_rt_print.entry", ".Lscc_rt_print.loop", ".Lscc_rt_print.write", ".Lscc_rt_print.chk2",
    ".Lscc_rt_print.chk3", ".Lscc_rt_print.adv", ".Lscc_rt_print.fail", ".Lscc_rt_print.done"]

/-- **The labels `printPhOk` reads**: the function's own and its blocks'
branch and call targets. -/
def printLabs : List String :=
  printOwnLabs ++ blkLabs x0 ++ blkLabs x1 ++ blkLabs x2 ++ blkLabs x3 ++ blkLabs x4 ++ blkLabs x5 ++
    blkLabs x6 ++ blkLabs x7 ++ blkLabs x8 ++ blkLabs x9 ++ blkLabs x10 ++ blkLabs x11 ++ blkLabs x12 ++
    blkLabs (x13.take 2)

/-- **`printPhOk` reads the labels of `printLabs` only.** -/
theorem printPhOk_congr {okPc : Nat → Bool} {ph : Nat → Nat} {lab lab' : Label → Int64}
    (h : ∀ l ∈ printLabs, lab l = lab' l) : printPhOk okPc ph lab = printPhOk okPc ph lab' := by
  have ho : ∀ l ∈ printOwnLabs, lab l = lab' l := fun l hl => h l (by simp only [printLabs]; simp [hl])
  have hb : ∀ blk, blkLabs blk ⊆ printLabs → ∀ l ∈ blkLabs blk, lab l = lab' l :=
    fun _ hs l hl => h l (hs hl)
  unfold printPhOk aBlk
  rw [ho "scc_rt_print" (by simp [printOwnLabs]), ho ".Lscc_rt_print.entry" (by simp [printOwnLabs]),
    ho ".Lscc_rt_print.loop" (by simp [printOwnLabs]), ho ".Lscc_rt_print.write" (by simp [printOwnLabs]),
    ho ".Lscc_rt_print.chk2" (by simp [printOwnLabs]), ho ".Lscc_rt_print.chk3" (by simp [printOwnLabs]),
    ho ".Lscc_rt_print.adv" (by simp [printOwnLabs]), ho ".Lscc_rt_print.fail" (by simp [printOwnLabs]),
    ho ".Lscc_rt_print.done" (by simp [printOwnLabs]),
    blkPh_congr (hb x0 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb x1 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb x2 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb x3 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb x4 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb x5 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb x6 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb x7 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb x8 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb x9 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb x10 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb x11 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb x12 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb (x13.take 2) fun l hl => by simp only [printLabs]; simp [hl])]

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64.PrintG.printPhOk_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printPhOk_congr

end Spike.Lib.X64.PrintG
