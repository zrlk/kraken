/-
**The phase record at `ret0.x`'s layout** (`Spike/Lib/X64PhRec.lean`): the
record's phases, sites, owned words and marks at `ret0L` are the hand ones
of `Spike/Lib/X64Ret0I.lean`, and its instance's facts hold. The twin of
`Spike/Test/A64PhRec.lean`.
-/
import Spike.Lib.X64PhRec
import Spike.Lib.Rt.X64LayoutRet0
import Spike.Test.X64Ret0PlaceOK

namespace Spike.Lib.X64.PhRec.Test

open Scc.Cert.PlaceOK.X64 (atTables)

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Spike.Lib.X64.PhRec
open Spike.Lib.X64.Rt.Ret0L (ret0L)
open SccCode (ret0Λ ret0Cells ret0Asm)

/-- `ret0.x`'s resolved phase table: the hand ranges. -/
theorem ret0_phTab : Scc.Cert.Rt.X64.phTabOf ret0Λ.code.lo ret0Cells = some
    ⟨[(4194304, 4194391), (4194892, 4195096)], [(4195839, 4196033)],
      [(4194304, 4194404), (4194892, 4195347), (4195445, 4195469), (4195595, 4196063)],
      [(4194304, 4194404), (4194892, 4195347), (4195445, 4195469), (4195595, 4196178)]⟩ := by
  decide +kernel

/-- **The record's phases are the hand ones.** -/
theorem ret0_ph : ph ret0L = Spike.Lib.X64.Flow.Ret0.Inst.ph := by
  funext pc
  show Scc.Cert.Rt.X64.phOf ret0Λ.code.lo ret0Cells pc = _
  unfold Scc.Cert.Rt.X64.phOf
  rw [ret0_phTab]
  simp only [Scc.Cert.Rt.X64.PhTab.ph, Scc.Cert.Rt.X64.inRs, List.any_cons, List.any_nil, Bool.or_false,
    Spike.Lib.X64.Flow.Ret0.Inst.ph, Spike.Lib.X64.Flow.Ret0.Inst.bP, Spike.Lib.X64.Flow.Ret0.Inst.bL,
    Spike.Lib.X64.Flow.Ret0.Inst.bN, Spike.Lib.X64.Flow.Ret0.Inst.bT, Spike.Lib.X64.Flow.Ret0.Inst.inN,
    Bool.or_assoc]

/-- `ret0.x`'s sites: the hand ones. -/
theorem ret0_sites : Scc.Cert.Rt.X64.sitesOf ret0Λ.code.lo ret0Cells ret0Λ =
    some [4196177, 4196217, 4198555, 4198623, 4198691, 4198759, 4198827] := by
  decide +kernel

/-- **The record's off-site pcs are the hand ones.** -/
theorem ret0_okPc : okPc ret0L = Spike.Lib.X64.Flow.Ret0.Inst.okPc := by
  funext pc
  show Scc.Cert.Rt.X64.okPcOf ret0Λ.code.lo ret0Cells ret0Λ pc = _
  unfold Scc.Cert.Rt.X64.okPcOf
  rw [ret0_sites]
  rfl

/-- **The record's owned words are the hand ones.** -/
theorem ret0_ownOf : ownOf ret0L = Spike.Lib.X64.Flow.Ret0.Inst.ownOf := rfl

/-- **The record's marks are the hand ones**, given the loader's parse. -/
theorem ret0_μ (hpa : Scc.Sem.X64.cellsOf ret0Asm = some ret0Cells) : μ ret0L = Spike.Lib.X64.Flow.Ret0.Inst.μ0 :=
  (marks_eq ret0L hpa).symm.trans (Spike.Lib.X64.Flow.Ret0.Inst.ret0_marks hpa)

/-- The take site at its label in `ret0.x`'s loaded thread. -/
theorem ret0_site :
    (μ ret0L).site .take = some (ret0L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
  show _ = some ((_root_.Executable.labels Spike.Lib.X64.Flow.Ret0.Mem.ret0Exe).label _).toBitVec.toNat
  rw [Spike.Lib.X64.Flow.Ret0.Inst.ret0_labT]
  decide +kernel

/-- **The record's instance's facts at `ret0.x`.** -/
theorem ret0_instOk {rS : Range} :
    Spike.Lib.X64.Rt.InstOk ret0L.exe ret0L.endPc ret0L.prog ret0L.lab (μ ret0L) (own ret0L) (Tk ret0L)
      (K ret0L rS) (okPc ret0L) (ph ret0L) :=
  instOk ret0L ret0_site

/-- The frame condition's words: satisfiable (the entry stack's memory). -/
example {m : MachineData} (h : m.dmem = Scc.Sem.Entry.linux.stackMem) :
    Mem.loadInt m.dmem ret0L.pnA 8 = none ∧ Mem.loadInt m.dmem (ret0L.pinA + 0#64) 8 = none :=
  ⟨rtF_pn (Spike.Lib.X64.Rt.rtF_stackMem ret0L Spike.Lib.X64.Rt.Ret0L.ret0L_ok h), rtF_hdr0
      (Spike.Lib.X64.Rt.rtF_stackMem ret0L Spike.Lib.X64.Rt.Ret0L.ret0L_ok h)⟩

/-- `ret0.x`'s first TCB is off its counters. -/
theorem ret0_tcbSep : TcbSep ret0L := by unfold TcbSep; decide

/-- `ret0.x`'s TCB words: owned at no phase, mapped, unmapped at the entry. -/
example {m : MachineData} (h : m.dmem = Scc.Sem.Entry.linux.stackMem) :
    ∀ j < 7, (∀ i w, (⟨ret0L.pinA + BitVec.ofNat 64 (8 * j), 8⟩, w) ∉ ownOf ret0L i) ∧
      Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 ret0L.Λ) true ⟨ret0L.pinA + BitVec.ofNat 64 (8 * j), 8⟩ ∧
      Mem.loadInt m.dmem (ret0L.pinA + BitVec.ofNat 64 (8 * j)) 8 = none := fun j hj =>
  ⟨tcb_not_own ret0_tcbSep ⟨j, hj, rfl⟩, mapped_tcb ⟨j, hj, rfl⟩,
    rtF_tcb (Spike.Lib.X64.Rt.rtF_stackMem ret0L Spike.Lib.X64.Rt.Ret0L.ret0L_ok h) ⟨j, hj, rfl⟩⟩

/-- **The instance's facts from `ret0.x`'s placement check**: the generic
discharge of the take site's label (`site_ofPlaceOK`) at `ret0.x`. -/
example {rS : Range} := instOk_ofPlaceOK (atTables Scc.Cert.PlaceOK.X64.Test.ret0_placeOK) SccCode.ret0Imms (rS := rS)

/-- At `ret0.x`'s placement check the record's layout is `ret0L` in the
fields the phases read. -/
example : Spike.Lib.X64.Rt.ret0P.prog =
    ret0L.prog := rfl

end Spike.Lib.X64.PhRec.Test
