import Spike.Lib.A64PhasesOfPlaceOK
import Spike.Lib.A64Ret0I
import Spike.Lib.A64Hello1I
import Spike.Test.A64Ret0PlaceOK
import Spike.Lib.Rt.A64LayoutOfPlaceOK

/-!
# The phases of `ret0.w` and `hello1.w` from `PlaceOK` (A6)

The program's phases and sites (`Rt.A64.phOf`, `Rt.A64.okPcOf`, resolved by
labels) are the hand ones (`Spike/Lib/A64Ret0I.lean`, `A64Hello1I.lean`),
and the hand proofs' phase checks of the blocks (`blkPh`) follow from
`ret0_placeOK` (`blkPh_of_rowAt_placeOK`), their crossings in their dead
sets. A table with a row over a site fails A6.
-/

namespace Scc.Cert.PlaceOK.A64.Test

open Kraken Kraken.Promising.AArch64 Scc.Cert.Rt.A64 Scc.Cert.Link.A64 SccCode
open Spike.Lib.A64.Flow Spike.Lib.A64 Spike.Lib.A64Consumer Spike.Lib.A64.Phases

/-! ## The tables -/

theorem ret0_phTab : phTabOf 4194304 ret0Prog = some
    ⟨[(4194304, 4194376), (4194964, 4195160)], [(4195896, 4196076)],
      [(4194304, 4194388), (4194964, 4195384), (4195496, 4195524), (4195652, 4196100)],
      [(4194304, 4194388), (4194964, 4195384), (4195496, 4195524), (4195652, 4196196)]⟩ := by
  decide +kernel

/-- **`ret0.w`'s phases are the hand ones.** -/
theorem ret0_phOf : phOf 4194304 ret0Prog = Ret0.Inst.ph := by
  funext pc
  simp only [phOf, ret0_phTab, PhTab.ph, inRs, List.any_cons, List.any_nil, Bool.or_false, Ret0.Inst.ph,
    Ret0.Inst.bP, Ret0.Inst.bL, Ret0.Inst.bN, Ret0.Inst.bT, Ret0.Inst.inN, Bool.or_assoc]

theorem ret0_sites : sitesOf 4194304 ret0Prog ret0Λ =
    some [4196192, 4196248, 4198508, 4198580, 4198652, 4198724, 4198796] := by
  decide +kernel

/-- **`ret0.w`'s sites are the hand ones.** -/
theorem ret0_okPcOf : okPcOf 4194304 ret0Prog ret0Λ = Ret0.Inst.okPc := by
  funext pc
  simp only [okPcOf, ret0_sites, Ret0.Inst.okPc]

theorem hello1_phTab : phTabOf 4194304 hello1Prog = some
    ⟨[(4194304, 4194376), (4195004, 4195200)], [(4195936, 4196116)],
      [(4194304, 4194388), (4195004, 4195424), (4195536, 4195564), (4195692, 4196140)],
      [(4194304, 4194388), (4195004, 4195424), (4195536, 4195564), (4195692, 4196236)]⟩ := by
  decide +kernel

/-- **`hello1.w`'s phases are the hand ones.** -/
theorem hello1_phOf : phOf 4194304 hello1Prog = Hello1.Inst.ph := by
  funext pc
  simp only [phOf, hello1_phTab, PhTab.ph, inRs, List.any_cons, List.any_nil, Bool.or_false, Hello1.Inst.ph,
    Hello1.Inst.bP, Hello1.Inst.bL, Hello1.Inst.bN, Hello1.Inst.bT, Ret0.Inst.inN, Bool.or_assoc]

theorem hello1_sites : sitesOf 4194304 hello1Prog hello1Λ =
    some [4196232, 4196288, 4198548, 4198620, 4198692, 4198764, 4198836] := by
  decide +kernel

/-- **`hello1.w`'s sites are the hand ones.** -/
theorem hello1_okPcOf : okPcOf 4194304 hello1Prog hello1Λ = Hello1.Inst.okPc := by
  funext pc
  simp only [okPcOf, hello1_sites, Hello1.Inst.okPc]

/-! ## The blocks' phase checks

The hand checks of `tcbW` (`scc_rt_alloc_tcb`'s entry row, its crossing
to `.2_full` dead; its `ret` row, returning to `.sp2`) and of the take's
`ret` row, from `ret0_placeOK`. -/

open Ret0.Inst (labT ret0_labT)

theorem codeLo_canonical (o : Out) : (tablesOf Config.canonical o).Λ.code.lo = 4194304 := rfl

theorem ret0_sites' : sitesOf 4194304 ret0Prog (tablesOf Config.canonical ⟨ret0Prog, ret0Secs, [], ret0Place⟩).Λ =
    some [4196192, 4196248, 4198508, 4198580, 4198652, 4198724, 4198796] := by
  decide +kernel

theorem ret0_okPcOf' :
    okPcOf 4194304 ret0Prog (tablesOf Config.canonical ⟨ret0Prog, ret0Secs, [], ret0Place⟩).Λ = Ret0.Inst.okPc := by
  funext pc
  simp only [okPcOf, ret0_sites', Ret0.Inst.okPc]

example : blkPh Ret0.Inst.okPc Ret0.Inst.ph (fun t => t == 4195200) labT
    (labT Ret0.AllocTcb.entryL + Int64.ofNat (4 * 0)) 0 Ret0.AllocTcb.atChk = true := by
  have h := blkPh_of_rowAt_placeOK (k := 0) (blk := Ret0.AllocTcb.atChk)
    (l := Ret0.AllocTcb.entryL) (dead := fun t => t == 4195200) (ra := 0) (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK)
        (by decide +kernel)
    ret0_labT (by decide +kernel) (by decide +kernel)
  simp only [codeLo_canonical] at h
  rw [ret0_phOf, ret0_okPcOf'] at h
  exact h

example : blkPh Ret0.Inst.okPc Ret0.Inst.ph (fun _ => false) labT
    (labT Ret0.AllocTcb.okL + Int64.ofNat (4 * 30)) (labT ".L0_scc_rt_start.sp2") Ret0.AllocTcb.atRet = true := by
  have h := blkPh_of_rowAt_placeOK (k := 30) (blk := Ret0.AllocTcb.atRet)
    (l := Ret0.AllocTcb.okL) (dead := fun _ => false) (ra := labT ".L0_scc_rt_start.sp2")
        (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK)
    (by decide +kernel) ret0_labT (by decide +kernel) (by decide +kernel)
  simp only [codeLo_canonical] at h
  rw [ret0_phOf, ret0_okPcOf'] at h
  exact h

example : blkPh Ret0.Inst.okPc Ret0.Inst.ph (fun _ => false) labT
    (labT Ret0.StackTake.siteL + Int64.ofNat (4 * 1)) (labT ".L5_scc_rt_thread_init.sp0") Ret0.StackTake.stRet
      = true := by
  have h := blkPh_of_rowAt_placeOK (k := 1) (blk := Ret0.StackTake.stRet)
    (l := Ret0.StackTake.siteL) (dead := fun _ => false) (ra := labT ".L5_scc_rt_thread_init.sp0")
        (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK)
    (by decide +kernel) ret0_labT (by decide +kernel) (by decide +kernel)
  simp only [codeLo_canonical] at h
  rw [ret0_phOf, ret0_okPcOf'] at h
  exact h

/-! ## A negative test

A row starting at the take site (a mark) fails A6, and so `PlaceOK`. -/

/-- `ret0.w`'s placement data with a row at `scc_rt_take_site`. -/
def ret0PlaceSite : PlaceData :=
  { ret0Place with
    blocks := ret0Place.blocks ++ [⟨"scc_rt_take_site", [⟨0, (-208), 0, SO.entry, Ret0.StackTake.stRet⟩], []⟩] }

example : placeOK Config.canonical ⟨ret0Prog, ret0Secs, [], ret0PlaceSite⟩ = false :=
  placeOK_eq_false_of_a6 (by decide +kernel)

/-! ## The marks and the pins

`_start`'s phase from `PlaceOK` (`pin_of_placeOK`), at the hand phases;
the marks' check fails on a repeated site, and on a pin out of its phase
(`_start` resolved at the take site's pc, phase `8`, not `13`). -/

/-- `_start` (at `4194304`) is in the initial phase. -/
example : Ret0.Inst.ph 4194304 = 13 := by
  have ⟨a, ha, hp⟩ := pin_of_placeOK (cfg := Config.canonical) (o := ⟨ret0Prog, ret0Secs, [], ret0Place⟩)
    ret0_placeOK (l := "_start") (k := 0) (v := 13) (by decide)
  simp only [codeLo_canonical] at ha hp
  rw [ret0_phOf] at hp
  have e : codeOf 4194304 ret0Prog "_start" = some 4194304 := by decide +kernel
  rw [e] at ha; cases ha
  simpa using hp

example : ∃ T, phTabOf 4194304 ret0Prog = some T ∧
    marksOkT (codeOf 4194304 ret0Prog) T [4196192, 4196192] = false :=
  ⟨_, ret0_phTab, by decide +kernel⟩

example : ∃ T, phTabOf 4194304 ret0Prog = some T ∧
    marksOkT (fun l => codeOf 4194304 ret0Prog (if l = "_start" then "scc_rt_take_site" else l)) T
      [4196192, 4196248, 4198508, 4198580, 4198652, 4198724, 4198796] = false :=
  ⟨_, ret0_phTab, by decide +kernel⟩

/-! ## The words disjoint

A8 fails when two of the runtime's words overlap: `ret0.w`'s words with
`scc_rt_stack_next` at `scc_rt_pinned_next`'s address. -/

example : wordsOk ret0Λ (rtA ret0Λ ret0Prog ret0Secs "scc_rt_pinned") (rtA ret0Λ ret0Prog ret0Secs "scc_rt_pinned_next")
    (rtA ret0Λ ret0Prog ret0Secs "scc_rt_stacks") (rtA ret0Λ ret0Prog ret0Secs "scc_rt_pinned_next")
    (rtA ret0Λ ret0Prog ret0Secs "scc_rt_stack_lock") (rtA ret0Λ ret0Prog ret0Secs "scc_rt_stack_free_n") = false := by
  decide +kernel

end Scc.Cert.PlaceOK.A64.Test
