/-
**`scc_rt_alloc`'s targets off the write abort's pcs** (AArch64; for A7's
`tailOffC`): `allocAbOk` (every block's targets off `WriteAb.abPcs`, as
`A64ConsumerA.blkAb`; every single instruction's next pc off them; the heap
abort's call target off every pc of `WriteAb.Ab` but the dispatcher's
prologue, which `Ab` holds only at `x0 = 4`), at any labels.

Not derivable from `placeOKAt`'s A7 alone: `b6`'s `b.hi .L2_scc_rt_alloc.3_spin`
targets a label the runtime pass (`rtIn`) does not place, so a layout may
put it just before `.L9_scc_rt_print.6_fail` (a pc of `Ab`).

- `blkAbC`: `A64ConsumerA.blkAb` without the segment proofs (the same
  definition; `Spike/Lib/A64AllocGAb.lean` bridges them by `rfl`).
- `abNoDispE`, `allocAbOk`: the check (read by `allocAb`).
- `abLabs`, `allocAbLabs`: the labels it reads; `allocAbOk_congr`: two label
  maps agreeing on them give the same check.

This file stays free of the segment proofs so that `PlaceOK` (A7) reads it.
-/
import Spike.Lib.A64AllocPh
import Spike.Lib.A64WriteAb

namespace Spike.Lib.A64.AllocG

open Kraken Kraken.AArch64.Parser
open Spike.Lib.A64Consumer (aiTgts)
open Spike.Lib.LowerA64 (blkLabs aiLab aiTgts_congr)
open Spike.Lib.A64.Alloc
open Spike.Lib.A64.WriteAb (abPcs pcRet tailPcs failPcs dispEPcs dispTPcs g4Pcs stubPcs)

/-- **A block's targets off the write abort's pcs** (`A64ConsumerA.blkAb`). -/
def blkAbC (lab : Label → Int64) (pc ra : Int64) (blk : List Directive) : Bool :=
  (List.range blk.length).all fun k =>
    match blk[k]? with
    | some d => match Spike.Lib.A64.Flow.classify d with
      | some a => (aiTgts lab (pc + Int64.ofNat (4 * k) + Int64.ofNat 4) ra a).all fun t =>
          !(abPcs lab).contains t
      | none => false
    | none => false

/-- Every pc of `Ab` but the dispatcher's prologue (`dispEPcs`, in `Ab`
only at `x0 = 4`). -/
def abNoDispE (lab : Label → Int64) : List Int64 :=
  pcRet lab :: tailPcs lab ++ failPcs lab ++ dispTPcs lab ++ g4Pcs lab ++ stubPcs lab

/-- **`scc_rt_alloc`'s targets off the write abort's pcs**: every block's
but the heap abort's (`blkAbC`), every single instruction's next pc, the
heap abort's `movz`'s next pc, and its call's target off `abNoDispE` (the
call enters the dispatcher with `x0 = 2`). The `ret`'s target is the
caller's (`allocAb`'s `hraAb`). -/
def allocAbOk (lab : Label → Int64) : Bool :=
  blkAbC lab (lab "scc_rt_alloc" + Int64.ofNat (4 * 0)) 0 b0 &&
  blkAbC lab (lab ".L2_scc_rt_alloc.0_entry" + Int64.ofNat (4 * 0)) 0 b1 &&
  blkAbC lab (lab ".L2_scc_rt_alloc.0_entry" + Int64.ofNat (4 * 4)) 0 b2 &&
  !(abPcs lab).contains (lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 0) + Int64.ofNat 4) &&
  !(abPcs lab).contains (lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 1) + Int64.ofNat 4) &&
  blkAbC lab (lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 2)) 0 b3 &&
  !(abPcs lab).contains (lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 5) + Int64.ofNat 4) &&
  blkAbC lab (lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 6)) 0 b4 &&
  blkAbC lab (lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 15)) 0 b5 &&
  blkAbC lab (lab ".L2_scc_rt_alloc.2_slow" + Int64.ofNat (4 * 0)) 0 b6 &&
  blkAbC lab (lab ".L2_scc_rt_alloc.2_slow" + Int64.ofNat (4 * 4)) 0 b7 &&
  !(abPcs lab).contains (lab ".L2_scc_rt_alloc.4_full" + Int64.ofNat (4 * 0) + Int64.ofNat 4) &&
  !(abNoDispE lab).contains (lab "scc_rt_abort") &&
  blkAbC lab (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 0)) 0 b11 &&
  !(abPcs lab).contains (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 8) + Int64.ofNat 4) &&
  !(abPcs lab).contains (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 9) + Int64.ofNat 4) &&
  blkAbC lab (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 10)) 0 b12 &&
  !(abPcs lab).contains (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 41) + Int64.ofNat 4) &&
  blkAbC lab (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 42)) 0 b13

/-! ## The labels it reads -/

/-- **The labels `abPcs` reads**: `print`'s, `scc_rt_abort`'s and the write
stub's. -/
def abLabs : List String :=
  [".L9_scc_rt_print.2_write", ".L9_scc_rt_print.3_chk2", ".L9_scc_rt_print.4_chk3",
    ".L9_scc_rt_print.6_fail", "scc_rt_abort", ".L12_scc_rt_abort.0_entry", ".L12_scc_rt_abort.2_next1",
    ".L12_scc_rt_abort.4_next3", ".L12_scc_rt_abort.6_next5", ".L12_scc_rt_abort.7_is6",
    Spike.Lib.A64.Abort.write.fn, Spike.Lib.A64.Abort.write.entry, Spike.Lib.A64.Abort.write.exit]

/-- **`abPcs` reads the labels of `abLabs` only.** -/
theorem abPcs_congr {lab lab' : Label → Int64} (h : ∀ l ∈ abLabs, lab l = lab' l) :
    abPcs lab = abPcs lab' := by
  simp (disch := decide) only [abPcs, pcRet, Spike.Lib.A64.Print.pcSvc, tailPcs, failPcs, dispEPcs,
    dispTPcs, g4Pcs, stubPcs, h]

/-- **`abNoDispE` reads the labels of `abLabs` only.** -/
theorem abNoDispE_congr {lab lab' : Label → Int64} (h : ∀ l ∈ abLabs, lab l = lab' l) :
    abNoDispE lab = abNoDispE lab' := by
  simp (disch := decide) only [abNoDispE, pcRet, Spike.Lib.A64.Print.pcSvc, tailPcs, failPcs,
    dispTPcs, g4Pcs, stubPcs, h]

/-- **`blkAbC` reads the labels at the block's targets and `abLabs` only.** -/
theorem blkAbC_congr {lab lab' : Label → Int64} {pc ra : Int64} {blk : List Directive}
    (h : ∀ L ∈ blkLabs blk, lab L = lab' L) (ha : ∀ l ∈ abLabs, lab l = lab' l) :
    blkAbC lab pc ra blk = blkAbC lab' pc ra blk := by
  unfold blkAbC
  rw [abPcs_congr ha]
  congr 1
  funext k
  cases hk : blk[k]? with
  | none => rfl
  | some d =>
    simp only
    cases hc : Spike.Lib.A64.Flow.classify d with
    | none => rfl
    | some a =>
      simp only
      rw [aiTgts_congr fun L hL => h L ?_]
      exact List.mem_filterMap.mpr ⟨d, List.mem_of_getElem? hk, by rw [hc]; exact hL⟩

/-- **The labels `allocAbOk` reads**: `allocPhOk`'s and `abPcs`'. -/
def allocAbLabs : List String := allocLabs ++ abLabs

/-- **`allocAbOk` reads the labels of `allocAbLabs` only.** -/
theorem allocAbOk_congr {lab lab' : Label → Int64} (h : ∀ l ∈ allocAbLabs, lab l = lab' l) :
    allocAbOk lab = allocAbOk lab' := by
  have hl : ∀ l ∈ allocLabs, lab l = lab' l := fun l hl => h l (by simp [allocAbLabs, hl])
  have ha : ∀ l ∈ abLabs, lab l = lab' l := fun l hl => h l (by simp [allocAbLabs, hl])
  have ho : ∀ l ∈ allocOwnLabs, lab l = lab' l := fun l hl' => hl l (by simp only [allocLabs]; simp [hl'])
  have hb : ∀ blk, blkLabs blk ⊆ allocLabs → ∀ l ∈ blkLabs blk, lab l = lab' l :=
    fun _ hs l hl' => hl l (hs hl')
  unfold allocAbOk
  rw [abPcs_congr ha, abNoDispE_congr ha, ha "scc_rt_abort" (by simp [abLabs]),
    ho "scc_rt_alloc" (by simp [allocOwnLabs]), ho ".L2_scc_rt_alloc.0_entry" (by simp [allocOwnLabs]),
    ho ".L2_scc_rt_alloc.1_cnt" (by simp [allocOwnLabs]), ho ".L2_scc_rt_alloc.2_slow" (by simp [allocOwnLabs]),
    ho ".L2_scc_rt_alloc.4_full" (by simp [allocOwnLabs]), ho ".L2_scc_rt_alloc.5_ok" (by simp [allocOwnLabs]),
    blkAbC_congr (hb b0 fun l hl => by simp only [allocLabs]; simp [hl]) ha,
    blkAbC_congr (hb b1 fun l hl => by simp only [allocLabs]; simp [hl]) ha,
    blkAbC_congr (hb b2 fun l hl => by simp only [allocLabs]; simp [hl]) ha,
    blkAbC_congr (hb b3 fun l hl => by simp only [allocLabs]; simp [hl]) ha,
    blkAbC_congr (hb b4 fun l hl => by simp only [allocLabs]; simp [hl]) ha,
    blkAbC_congr (hb b5 fun l hl => by simp only [allocLabs]; simp [hl]) ha,
    blkAbC_congr (hb b6 fun l hl => by simp only [allocLabs]; simp [hl]) ha,
    blkAbC_congr (hb b7 fun l hl => by simp only [allocLabs]; simp [hl]) ha,
    blkAbC_congr (hb b11 fun l hl => by simp only [allocLabs]; simp [hl]) ha,
    blkAbC_congr (hb b12 fun l hl => by simp only [allocLabs]; simp [hl]) ha,
    blkAbC_congr (hb b13 fun l hl => by simp only [allocLabs]; simp [hl]) ha]

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64.AllocG.allocAbOk_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocAbOk_congr

end Spike.Lib.A64.AllocG
