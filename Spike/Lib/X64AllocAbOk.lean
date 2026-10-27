/-
**`scc_rt_alloc`'s targets off the write abort's pcs** (x86-64; for A7's
`tailOffC`), the twin of `Spike/Lib/A64AllocAbOk.lean`: `allocAbOk` (every
block's targets off `WriteAb.abPcs`, as `X64ConsumerA.blkAb`; every single
instruction's next pc off them; the heap abort's `movq $2, %rdi`'s next pc
off them and its call's target off every pc of `WriteAb.Ab` but the
dispatcher's prologue, which `Ab` holds only at `%rdi = 4`), at any labels.

Not derivable from `placeOKAt`'s A7 alone: `bSlow`'s `ja .Lscc_rt_alloc.spin`
targets a label the runtime pass does not place, so a layout may put it at a
pc of `Ab`.

- `blkAbC`: `X64ConsumerA.blkAb` without the segment proofs (the same
  definition; `Spike/Lib/X64AllocGAb.lean` bridges them by `rfl`).
- `abNoDispE`, `allocAbOk`: the check (read by `allocAb`).
- `abLabs`, `allocAbLabs`: the labels it reads; `abPcs_congr`,
  `abNoDispE_congr`, `blkAbC_congr`, `allocAbOk_congr`: two label maps
  agreeing on them give the same check.

This file stays free of the segment proofs so that `PlaceOK` (A7) reads it.
-/
import Spike.Lib.X64AllocPh
import Spike.Lib.X64WriteAb

namespace Spike.Lib.X64.AllocG

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64 (cellOff classify)
open Spike.Lib.X64Consumer (aiTgts)
open Spike.Lib.LowerX64 (blkLabs aiLab aiTgts_congr)
open Spike.Lib.X64.Alloc
open Spike.Lib.X64.WriteAb (abPcs pcRet tailPcs failPcs dispEPcs dispTPcs g4Pcs stubPcs)

/-- **A block's targets off the write abort's pcs** (`X64ConsumerA.blkAb`). -/
def blkAbC (lab : Label → Int64) (pc ra : Int64) (blk : List (Directive × Nat)) : Bool :=
  (List.range blk.length).all fun k =>
    match blk[k]? with
    | some dz => match classify dz.1 with
      | some a => (aiTgts lab (pc + Int64.ofNat (cellOff blk k) + Int64.ofNat dz.2) ra a).all fun t =>
          !(abPcs lab).contains t
      | none => false
    | none => false

/-- Every pc of `Ab` but the dispatcher's prologue (`dispEPcs`, in `Ab`
only at `%rdi = 4`). -/
def abNoDispE (lab : Label → Int64) : List Int64 :=
  pcRet lab :: tailPcs lab ++ failPcs lab ++ dispTPcs lab ++ g4Pcs lab ++ stubPcs lab

/-- A pc off the write abort's pcs. -/
abbrev offAb (lab : Label → Int64) (p : Int64) : Bool := !(abPcs lab).contains p

/-- **`scc_rt_alloc`'s targets off the write abort's pcs**: every block's
but the heap abort's (`blkAbC`), every single instruction's next pc, the
heap abort's `movq $2, %rdi`'s next pc, and its call's target off
`abNoDispE` (the call enters the dispatcher with `%rdi = 2`). The `ret`'s
target is the caller's (`allocAb`'s `hraAb`). -/
def allocAbOk (lab : Label → Int64) : Bool :=
  blkAbC lab (lab fnL + Int64.ofNat 0) 0 bPro && blkAbC lab (lab entryL + Int64.ofNat 0) 0 bChk &&
  blkAbC lab (lab entryL + Int64.ofNat 16) 0 bJ1 && offAb lab (lab cntL + Int64.ofNat 0 + Int64.ofNat 7) &&
  blkAbC lab (lab cntL + Int64.ofNat 7) 0 bC1 && offAb lab (lab cntL + Int64.ofNat 19 + Int64.ofNat 5) &&
  blkAbC lab (lab cntL + Int64.ofNat 24) 0 bC2 && blkAbC lab (lab cntL + Int64.ofNat 59) 0 bJ2 &&
  blkAbC lab (lab slowL + Int64.ofNat 0) 0 bSlow && blkAbC lab (lab slowL + Int64.ofNat 16) 0 bJ3 &&
  offAb lab (lab fullL + Int64.ofNat 0 + Int64.ofNat 7) && !(abNoDispE lab).contains (lab "scc_rt_abort") &&
  blkAbC lab (lab okL + Int64.ofNat 0) 0 bO0 && offAb lab (lab okL + Int64.ofNat 11 + Int64.ofNat 3) &&
  blkAbC lab (lab okL + Int64.ofNat 14) 0 bO1 && offAb lab (lab okL + Int64.ofNat 29 + Int64.ofNat 3) &&
  blkAbC lab (lab okL + Int64.ofNat 32) 0 bO2 && offAb lab (lab okL + Int64.ofNat 36 + Int64.ofNat 7) &&
  blkAbC lab (lab okL + Int64.ofNat 43) 0 bO3 && offAb lab (lab okL + Int64.ofNat 58 + Int64.ofNat 3) &&
  blkAbC lab (lab okL + Int64.ofNat 61) 0 bO4 && offAb lab (lab okL + Int64.ofNat 88 + Int64.ofNat 4) &&
  blkAbC lab (lab okL + Int64.ofNat 92) 0 bO5 && offAb lab (lab okL + Int64.ofNat 107 + Int64.ofNat 3) &&
  blkAbC lab (lab okL + Int64.ofNat 110) 0 bO6 && offAb lab (lab okL + Int64.ofNat 125 + Int64.ofNat 3) &&
  blkAbC lab (lab okL + Int64.ofNat 128) 0 bO7 && offAb lab (lab okL + Int64.ofNat 140 + Int64.ofNat 3) &&
  blkAbC lab (lab okL + Int64.ofNat 143) 0 bO8 && offAb lab (lab okL + Int64.ofNat 170 + Int64.ofNat 3) &&
  blkAbC lab (lab okL + Int64.ofNat 173) 0 bO9

/-! ## The labels it reads -/

/-- **The labels `abPcs` reads**: `print`'s, `scc_rt_abort`'s and the write
stub's. -/
def abLabs : List String :=
  [".Lscc_rt_print.write", ".Lscc_rt_print.chk2", ".Lscc_rt_print.chk3", ".Lscc_rt_print.fail",
    "scc_rt_abort", ".Lscc_rt_abort.entry", ".Lscc_rt_abort.next1", ".Lscc_rt_abort.next3",
    ".Lscc_rt_abort.next5", ".Lscc_rt_abort.is6", Spike.Lib.X64.Abort.write.fn,
    Spike.Lib.X64.Abort.write.entry, Spike.Lib.X64.Abort.write.exit]

/-- **`abPcs` reads the labels of `abLabs` only.** -/
theorem abPcs_congr {lab lab' : Label → Int64} (h : ∀ l ∈ abLabs, lab l = lab' l) :
    abPcs lab = abPcs lab' := by
  simp (disch := decide) only [abPcs, pcRet, tailPcs, failPcs, dispEPcs, dispTPcs, g4Pcs, stubPcs, h]

/-- **`abNoDispE` reads the labels of `abLabs` only.** -/
theorem abNoDispE_congr {lab lab' : Label → Int64} (h : ∀ l ∈ abLabs, lab l = lab' l) :
    abNoDispE lab = abNoDispE lab' := by
  simp (disch := decide) only [abNoDispE, pcRet, tailPcs, failPcs, dispTPcs, g4Pcs, stubPcs, h]

/-- **`blkAbC` reads the labels at the block's targets and `abLabs` only.** -/
theorem blkAbC_congr {lab lab' : Label → Int64} {pc ra : Int64} {blk : List (Directive × Nat)}
    (h : ∀ L ∈ blkLabs blk, lab L = lab' L) (ha : ∀ l ∈ abLabs, lab l = lab' l) :
    blkAbC lab pc ra blk = blkAbC lab' pc ra blk := by
  unfold blkAbC
  rw [abPcs_congr ha]
  congr 1
  funext k
  cases hk : blk[k]? with
  | none => rfl
  | some dz =>
    simp only
    cases hc : classify dz.1 with
    | none => rfl
    | some a =>
      simp only
      rw [aiTgts_congr fun L hL => h L ?_]
      exact List.mem_filterMap.mpr ⟨dz, List.mem_of_getElem? hk, by rw [hc]; exact hL⟩

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
  unfold allocAbOk offAb
  rw [abPcs_congr ha, abNoDispE_congr ha, ha "scc_rt_abort" (by simp [abLabs]),
    ho fnL (by simp [allocOwnLabs]), ho entryL (by simp [allocOwnLabs]), ho cntL (by simp [allocOwnLabs]),
    ho slowL (by simp [allocOwnLabs]), ho fullL (by simp [allocOwnLabs]), ho okL (by simp [allocOwnLabs]),
    blkAbC_congr (hb bPro fun l hl => by simp only [allocLabs]; simp [hl]) ha,
    blkAbC_congr (hb bChk fun l hl => by simp only [allocLabs]; simp [hl]) ha,
    blkAbC_congr (hb bJ1 fun l hl => by simp only [allocLabs]; simp [hl]) ha,
    blkAbC_congr (hb bC1 fun l hl => by simp only [allocLabs]; simp [hl]) ha,
    blkAbC_congr (hb bC2 fun l hl => by simp only [allocLabs]; simp [hl]) ha,
    blkAbC_congr (hb bJ2 fun l hl => by simp only [allocLabs]; simp [hl]) ha,
    blkAbC_congr (hb bSlow fun l hl => by simp only [allocLabs]; simp [hl]) ha,
    blkAbC_congr (hb bJ3 fun l hl => by simp only [allocLabs]; simp [hl]) ha,
    blkAbC_congr (hb bO0 fun l hl => by simp only [allocLabs]; simp [hl]) ha,
    blkAbC_congr (hb bO1 fun l hl => by simp only [allocLabs]; simp [hl]) ha,
    blkAbC_congr (hb bO2 fun l hl => by simp only [allocLabs]; simp [hl]) ha,
    blkAbC_congr (hb bO3 fun l hl => by simp only [allocLabs]; simp [hl]) ha,
    blkAbC_congr (hb bO4 fun l hl => by simp only [allocLabs]; simp [hl]) ha,
    blkAbC_congr (hb bO5 fun l hl => by simp only [allocLabs]; simp [hl]) ha,
    blkAbC_congr (hb bO6 fun l hl => by simp only [allocLabs]; simp [hl]) ha,
    blkAbC_congr (hb bO7 fun l hl => by simp only [allocLabs]; simp [hl]) ha,
    blkAbC_congr (hb bO8 fun l hl => by simp only [allocLabs]; simp [hl]) ha,
    blkAbC_congr (hb bO9 fun l hl => by simp only [allocLabs]; simp [hl]) ha]

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64.AllocG.allocAbOk_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocAbOk_congr

end Spike.Lib.X64.AllocG
