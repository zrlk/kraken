import Spike.Lib.X64PhasesOfPlaceOK
import Spike.Lib.X64Ret0I
import Spike.Lib.X64Hello1I
import Spike.Test.X64Ret0PlaceOK

/-!
# The phases of `ret0.w` and `hello1.w` from `PlaceOK` on x86-64 (A6)

The x86-64 twin of `Spike/Test/A64Ret0PhasesPlaceOK.lean`. The program's
phases and sites (`Rt.X64.phOf`, `Rt.X64.okPcOf`, resolved by labels) are
the hand ones (`Spike/Lib/X64Ret0I.lean`, `X64Hello1I.lean`), and the hand
proofs' phase checks of the blocks (`blkPh`) follow from `ret0_placeOK`
(`blkPh_of_rowAt_placeOK`), their crossings in their dead sets. A table
with a row over a site, other than the site's `nop`, fails A6.
-/

namespace Scc.Cert.PlaceOK.X64.Test

open Scc.Cert.PlaceOK.X64 (atTables)

open Kraken Kraken.Promising.X64 Scc.Cert.Rt.X64 Scc.Cert.Link.X64 SccCode
open Spike.Lib.X64 Spike.Lib.X64Consumer Spike.Lib.X64.Phases
open Spike.Lib.X64.Flow

/-! ## The tables -/

theorem ret0_phTab : phTabOf 4194304 ret0Cells = some
    ⟨[(4194304, 4194391), (4194892, 4195096)], [(4195839, 4196033)],
      [(4194304, 4194404), (4194892, 4195347), (4195445, 4195469), (4195595, 4196063)],
      [(4194304, 4194404), (4194892, 4195347), (4195445, 4195469), (4195595, 4196178)]⟩ := by
  decide +kernel

/-- **`ret0.w`'s phases are the hand ones.** -/
theorem ret0_phOf : phOf 4194304 ret0Cells = Ret0.Inst.ph := by
  funext pc
  simp only [phOf, ret0_phTab, PhTab.ph, inRs, List.any_cons, List.any_nil, Bool.or_false, Ret0.Inst.ph,
    Ret0.Inst.bP, Ret0.Inst.bL, Ret0.Inst.bN, Ret0.Inst.bT, Ret0.Inst.inN, Bool.or_assoc]

theorem ret0_sites : sitesOf 4194304 ret0Cells ret0Λ =
    some [4196177, 4196217, 4198555, 4198623, 4198691, 4198759, 4198827] := by
  decide +kernel

/-- **`ret0.w`'s sites are the hand ones.** -/
theorem ret0_okPcOf : okPcOf 4194304 ret0Cells ret0Λ = Ret0.Inst.okPc := by
  funext pc
  simp only [okPcOf, ret0_sites, Ret0.Inst.okPc]

theorem hello1_phTab : phTabOf 4194304 hello1Cells = some
    ⟨[(4194304, 4194391), (4194933, 4195137)], [(4195880, 4196074)],
      [(4194304, 4194404), (4194933, 4195388), (4195486, 4195510), (4195636, 4196104)],
      [(4194304, 4194404), (4194933, 4195388), (4195486, 4195510), (4195636, 4196219)]⟩ := by
  decide +kernel

/-- **`hello1.w`'s phases are the hand ones.** -/
theorem hello1_phOf : phOf 4194304 hello1Cells = Hello1.Inst.ph := by
  funext pc
  simp only [phOf, hello1_phTab, PhTab.ph, inRs, List.any_cons, List.any_nil, Bool.or_false, Hello1.Inst.ph,
    Hello1.Inst.bP, Hello1.Inst.bL, Hello1.Inst.bN, Hello1.Inst.bT, Ret0.Inst.inN, Bool.or_assoc]

theorem hello1_sites : sitesOf 4194304 hello1Cells hello1Λ =
    some [4196218, 4196258, 4198596, 4198664, 4198732, 4198800, 4198868] := by
  decide +kernel

/-- **`hello1.w`'s sites are the hand ones.** -/
theorem hello1_okPcOf : okPcOf 4194304 hello1Cells hello1Λ = Hello1.Inst.okPc := by
  funext pc
  simp only [okPcOf, hello1_sites, Hello1.Inst.okPc]

/-! ## The blocks' phase checks

The hand checks of `tcbW` (`scc_rt_alloc_tcb`'s entry row, its crossing
to `.full` dead; its `ret` row, returning to `.Lscc_rt_start.x0`) and of
the take's `ret` row, from `ret0_placeOK`. -/

open Ret0.Inst (labT ret0_labT)

theorem codeLo_canonical (o : Out) : (tablesOf Config.canonical o).Λ.code.lo = 4194304 := rfl

theorem ret0_sites' : sitesOf 4194304 ret0Cells
    (tablesOf Config.canonical ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩).Λ =
    some [4196177, 4196217, 4198555, 4198623, 4198691, 4198759, 4198827] := by
  decide +kernel

theorem ret0_okPcOf' :
    okPcOf 4194304 ret0Cells (tablesOf Config.canonical ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩).Λ =
      Ret0.Inst.okPc := by
  funext pc
  simp only [okPcOf, ret0_sites', Ret0.Inst.okPc]

/-- The loaded thread does not read the link's immediate table. -/
theorem threadAt_withImms (E : Scc.Sem.Entry) (Λ : Scc.Sem.Layout) (i) (cells : List (Directive × Nat))
    (r : List Kraken.DataImage.Item) :
    Scc.Sem.X64.threadAt E { Λ with imms := i }.code.lo cells (Scc.Sem.loadSyms { Λ with imms := i } r) =
      Scc.Sem.X64.threadAt E Λ.code.lo cells (Scc.Sem.loadSyms Λ r) := rfl

/-- **`ret0_labT` at the placement check's tables.** -/
theorem ret0_labT' : (_root_.Executable.labels (Scc.Sem.X64.threadAt Scc.Sem.Entry.linux
    (tablesOf Config.canonical ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩).Λ.code.lo ret0Cells
    (Scc.Sem.loadSyms (tablesOf Config.canonical ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩).Λ
      ret0Secs.rodata)).exe).label = labT := by
  rw [tablesOf_canonical, ← threadAt_withImms Scc.Sem.Entry.linux (linkOf ret0Cells ret0Secs) ret0Imms]
  exact ret0_labT

example : blkPh Ret0.Inst.okPc Ret0.Inst.ph (fun t => t == 4195133) labT
    (labT Ret0.AllocTcb.entryL + Int64.ofNat 0) 0 Ret0.AllocTcb.atChk = true := by
  have h := blkPh_of_rowAt_placeOK (off := 0) (blk := Ret0.AllocTcb.atChk)
    (l := Ret0.AllocTcb.entryL) (dead := fun t => t == 4195133) (ra := 0) (atTables ret0_placeOK) (by decide +kernel)
    (by decide +kernel) ret0_labT' (by decide +kernel)
  simp only [codeLo_canonical] at h
  rw [ret0_phOf, ret0_okPcOf'] at h
  exact h

example : blkPh Ret0.Inst.okPc Ret0.Inst.ph (fun _ => false) labT
    (labT Ret0.AllocTcb.okL + Int64.ofNat 143) (labT ".Lscc_rt_start.x0") Ret0.AllocTcb.atRet = true := by
  have h := blkPh_of_rowAt_placeOK (off := 143) (blk := Ret0.AllocTcb.atRet)
    (l := Ret0.AllocTcb.okL) (dead := fun _ => false) (ra := labT ".Lscc_rt_start.x0") (atTables ret0_placeOK)
    (by decide +kernel) (by decide +kernel) ret0_labT' (by decide +kernel)
  simp only [codeLo_canonical] at h
  rw [ret0_phOf, ret0_okPcOf'] at h
  exact h

example : blkPh Ret0.Inst.okPc Ret0.Inst.ph (fun _ => false) labT
    (labT Ret0.StackTake.siteL + Int64.ofNat 1) (labT ".Lscc_rt_thread_init.x7") Ret0.StackTake.stRet
      = true := by
  have h := blkPh_of_rowAt_placeOK (off := 1) (blk := Ret0.StackTake.stRet)
    (l := Ret0.StackTake.siteL) (dead := fun _ => false) (ra := labT ".Lscc_rt_thread_init.x7") (atTables ret0_placeOK)
    (by decide +kernel) (by decide +kernel) ret0_labT' (by decide +kernel)
  simp only [codeLo_canonical] at h
  rw [ret0_phOf, ret0_okPcOf'] at h
  exact h

/-! ## A negative test

A row starting at the take site other than its `nop` (here the take's
`ret` row) fails A6, and so `PlaceOK`. -/

/-- `ret0.w`'s placement data with the take's `ret` row at
`scc_rt_take_site`. -/
def ret0PlaceSite : PlaceData :=
  { ret0Place with
    blocks := ret0Place.blocks ++ [⟨"scc_rt_take_site", [⟨0, 0, -192, 0, SO.entry, Ret0.StackTake.stRet⟩], []⟩] }

example : placeOK Config.canonical ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0PlaceSite⟩ = false :=
  placeOK_eq_false_of_a6 (by decide +kernel)

/-! ## The words disjoint

A8 fails when two of the runtime's words overlap: `ret0.w`'s words with
`scc_rt_stack_next` at `scc_rt_pinned_next`'s address. With the real
address they pass. -/

example : wordsOk ret0Λ (rtA ret0Λ ret0Cells ret0Secs "scc_rt_pinned")
    (rtA ret0Λ ret0Cells ret0Secs "scc_rt_pinned_next")
    (rtA ret0Λ ret0Cells ret0Secs "scc_rt_stacks") (rtA ret0Λ ret0Cells ret0Secs "scc_rt_pinned_next")
    (rtA ret0Λ ret0Cells ret0Secs "scc_rt_stack_lock")
        (rtA ret0Λ ret0Cells ret0Secs "scc_rt_stack_free_n") = false := by
  decide +kernel

example : wordsOk ret0Λ (rtA ret0Λ ret0Cells ret0Secs "scc_rt_pinned")
    (rtA ret0Λ ret0Cells ret0Secs "scc_rt_pinned_next")
    (rtA ret0Λ ret0Cells ret0Secs "scc_rt_stacks") (rtA ret0Λ ret0Cells ret0Secs "scc_rt_stack_next")
    (rtA ret0Λ ret0Cells ret0Secs "scc_rt_stack_lock") (rtA ret0Λ ret0Cells ret0Secs "scc_rt_stack_free_n") = true := by
  decide +kernel

end Scc.Cert.PlaceOK.X64.Test
