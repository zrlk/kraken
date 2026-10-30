/-
**A7's `scc_rt_alloc` target check is the one approved with the barrier**
(AArch64): `AllocG.allocAbOk`, the function `StubW.tailPhOk` reads (at
`fenceLab`), equals the text it had when `scc_rt_print`'s write block gained
its barrier `dmb ish`, copied here verbatim under the suffix `201`: the
check over the write abort's pcs `abPcs201`, whose write-block pcs count
from `pcSvc201` (the write block's label `+ 16`).

Since then the write abort's pcs (`WriteAb.abPcs`) count from the
executable's labels past the barrier (`PrintD.pcSvc`, the label `+ 20`), the
check over them is `allocAbOkR`, and `allocAbOk` is `allocAbOkR` at
`unfenceLab` (the write block's label one instruction back): `allocAbOk_pin`
checks that the two texts give the same function.
-/
import Spike.Lib.A64AllocAbOk

namespace Spike.Test.A64AllocAbOkPin

open Kraken Kraken.AArch64.Parser
open Spike.Lib.A64Consumer (aiTgts)
open Spike.Lib.LowerA64 (blkLabs aiTgts_congr)
open Spike.Lib.A64.Alloc
open Spike.Lib.A64.WriteAb (failPcs dispEPcs dispTPcs g4Pcs stubPcs)

/-! ## The approved text -/

section Approved

variable (lab : Label → Int64)

/-- `Print.pcSvc`, as approved. -/
abbrev pcSvc201 : Int64 := lab ".L9_scc_rt_print.2_write" + 4 + 4 + 4 + 4

/-- `WriteAb.pcRet`, as approved. -/
abbrev pcRet201 : Int64 := pcSvc201 lab + 4

/-- `WriteAb.tailPcs`, as approved. -/
def tailPcs201 : List Int64 :=
  [pcSvc201 lab + 8, pcSvc201 lab + 12, pcSvc201 lab + 16, pcSvc201 lab + 20,
   pcSvc201 lab + 24, pcSvc201 lab + 28, pcSvc201 lab + 32, pcSvc201 lab + 36,
   lab ".L9_scc_rt_print.3_chk2", lab ".L9_scc_rt_print.3_chk2" + 4, lab ".L9_scc_rt_print.3_chk2" + 8,
   lab ".L9_scc_rt_print.3_chk2" + 12, lab ".L9_scc_rt_print.3_chk2" + 16,
   lab ".L9_scc_rt_print.3_chk2" + 20, lab ".L9_scc_rt_print.3_chk2" + 24,
   lab ".L9_scc_rt_print.3_chk2" + 28,
   lab ".L9_scc_rt_print.4_chk3", lab ".L9_scc_rt_print.4_chk3" + 4, lab ".L9_scc_rt_print.4_chk3" + 8,
   lab ".L9_scc_rt_print.4_chk3" + 12]

/-- `WriteAb.abPcs`, as approved. -/
def abPcs201 : List Int64 :=
  pcRet201 lab :: tailPcs201 lab ++ failPcs lab ++ dispEPcs lab ++ dispTPcs lab ++ g4Pcs lab ++ stubPcs lab

end Approved

/-- `AllocG.blkAbC`, as approved. -/
def blkAbC201 (lab : Label → Int64) (pc ra : Int64) (blk : List Directive) : Bool :=
  (List.range blk.length).all fun k =>
    match blk[k]? with
    | some d => match Spike.Lib.A64.Flow.classify d with
      | some a => (aiTgts lab (pc + Int64.ofNat (4 * k) + Int64.ofNat 4) ra a).all fun t =>
          !(abPcs201 lab).contains t
      | none => false
    | none => false

/-- `AllocG.abNoDispE`, as approved. -/
def abNoDispE201 (lab : Label → Int64) : List Int64 :=
  pcRet201 lab :: tailPcs201 lab ++ failPcs lab ++ dispTPcs lab ++ g4Pcs lab ++ stubPcs lab

/-- `AllocG.allocAbOk`, as approved. -/
def allocAbOk201 (lab : Label → Int64) : Bool :=
  blkAbC201 lab (lab "scc_rt_alloc" + Int64.ofNat (4 * 0)) 0 b0 &&
  blkAbC201 lab (lab ".L2_scc_rt_alloc.0_entry" + Int64.ofNat (4 * 0)) 0 b1 &&
  blkAbC201 lab (lab ".L2_scc_rt_alloc.0_entry" + Int64.ofNat (4 * 4)) 0 b2 &&
  !(abPcs201 lab).contains (lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 0) + Int64.ofNat 4) &&
  !(abPcs201 lab).contains (lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 1) + Int64.ofNat 4) &&
  blkAbC201 lab (lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 2)) 0 b3 &&
  !(abPcs201 lab).contains (lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 5) + Int64.ofNat 4) &&
  blkAbC201 lab (lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 6)) 0 b4 &&
  blkAbC201 lab (lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 15)) 0 b5 &&
  blkAbC201 lab (lab ".L2_scc_rt_alloc.2_slow" + Int64.ofNat (4 * 0)) 0 b6 &&
  blkAbC201 lab (lab ".L2_scc_rt_alloc.2_slow" + Int64.ofNat (4 * 4)) 0 b7 &&
  !(abPcs201 lab).contains (lab ".L2_scc_rt_alloc.4_full" + Int64.ofNat (4 * 0) + Int64.ofNat 4) &&
  !(abNoDispE201 lab).contains (lab "scc_rt_abort") &&
  blkAbC201 lab (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 0)) 0 b11 &&
  !(abPcs201 lab).contains (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 8) + Int64.ofNat 4) &&
  !(abPcs201 lab).contains (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 9) + Int64.ofNat 4) &&
  blkAbC201 lab (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 10)) 0 b12 &&
  !(abPcs201 lab).contains (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 41) + Int64.ofNat 4) &&
  blkAbC201 lab (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 42)) 0 b13

/-! ## The current text gives the same function -/

open Spike.Lib.A64.AllocG (unfenceLab blkAbC abNoDispE allocAbOk allocAbOkR)

variable {lab : Label → Int64}

/-- The write block's label one back, then the call's pc past the barrier:
the approved call's pc. -/
theorem pcSvc_unfence : Spike.Lib.A64.PrintD.pcSvc (unfenceLab lab) = pcSvc201 lab := by
  simp only [Spike.Lib.A64.PrintD.pcSvc, pcSvc201, unfenceLab, ↓reduceIte]
  apply Int64.toBitVec_inj.mp
  simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
  bv_omega

/-- `unfenceLab` moves the write block's label only. -/
theorem unfence_ne {l : Label} (h : l ≠ ".L9_scc_rt_print.2_write") : unfenceLab lab l = lab l := by
  simp [unfenceLab, h]

/-- **The write abort's pcs at `unfenceLab` are the approved ones.** -/
theorem abPcs_unfence : Spike.Lib.A64.WriteAb.abPcs (unfenceLab lab) = abPcs201 lab := by
  simp (disch := decide) only [Spike.Lib.A64.WriteAb.abPcs, abPcs201, Spike.Lib.A64.WriteAb.pcRet, pcRet201,
    Spike.Lib.A64.WriteAb.tailPcs, tailPcs201, failPcs, dispEPcs, dispTPcs, g4Pcs, stubPcs, pcSvc_unfence,
    unfence_ne]

/-- **`abNoDispE` at `unfenceLab` is the approved one.** -/
theorem abNoDispE_unfence : abNoDispE (unfenceLab lab) = abNoDispE201 lab := by
  simp (disch := decide) only [abNoDispE, abNoDispE201, Spike.Lib.A64.WriteAb.pcRet, pcRet201,
    Spike.Lib.A64.WriteAb.tailPcs, tailPcs201, failPcs, dispTPcs, g4Pcs, stubPcs, pcSvc_unfence, unfence_ne]

/-- **A block not naming the write block checks the same** at `unfenceLab`. -/
theorem blkAbC_unfence {pc ra : Int64} {blk : List Directive}
    (h : ∀ L ∈ blkLabs blk, L ≠ ".L9_scc_rt_print.2_write") :
    blkAbC (unfenceLab lab) pc ra blk = blkAbC201 lab pc ra blk := by
  unfold blkAbC blkAbC201
  rw [abPcs_unfence]
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
      rw [aiTgts_congr fun L hL => unfence_ne (h L ?_)]
      exact List.mem_filterMap.mpr ⟨d, List.mem_of_getElem? hk, by rw [hc]; exact hL⟩

/-- **The pin**: A7's `scc_rt_alloc` target check is the approved text's. -/
theorem allocAbOk_pin : allocAbOk = allocAbOk201 := by
  funext lab
  unfold allocAbOk allocAbOkR allocAbOk201
  rw [blkAbC_unfence (blk := b0) (by decide), blkAbC_unfence (blk := b1) (by decide),
    blkAbC_unfence (blk := b2) (by decide), blkAbC_unfence (blk := b3) (by decide),
    blkAbC_unfence (blk := b4) (by decide), blkAbC_unfence (blk := b5) (by decide),
    blkAbC_unfence (blk := b6) (by decide), blkAbC_unfence (blk := b7) (by decide),
    blkAbC_unfence (blk := b11) (by decide), blkAbC_unfence (blk := b12) (by decide),
    blkAbC_unfence (blk := b13) (by decide), abPcs_unfence, abNoDispE_unfence]
  simp (disch := decide) only [unfence_ne]

-- No axioms beyond Lean's.

/-- info: 'Spike.Test.A64AllocAbOkPin.allocAbOk_pin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocAbOk_pin

end Spike.Test.A64AllocAbOkPin
