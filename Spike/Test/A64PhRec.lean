/-
**The phase record at `ret0`'s layout** (`Spike/Lib/A64PhRec.lean`): the
record's phases, sites, owned words and marks at `ret0L` are the hand ones
of `Spike/Lib/A64Ret0I.lean`, and its instance's facts hold.
-/
import Spike.Lib.A64PhRec
import Spike.Lib.Rt.A64LayoutRet0

namespace Spike.Lib.A64.PhRec.Test

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Range)
open Spike.Lib.A64.PhRec
open Spike.Lib.A64.Rt.Ret0L (ret0L)
open SccCode (ret0Λ ret0Prog ret0Asm)

/-- `ret0`'s resolved phase table: the hand ranges. -/
theorem ret0_phTab : Scc.Cert.Rt.A64.phTabOf ret0Λ.code.lo ret0Prog = some
    ⟨[(4194304, 4194376), (4194964, 4195160)], [(4195896, 4196076)],
      [(4194304, 4194388), (4194964, 4195384), (4195496, 4195524), (4195652, 4196100)],
      [(4194304, 4194388), (4194964, 4195384), (4195496, 4195524), (4195652, 4196196)]⟩ := by
  decide +kernel

/-- **The record's phases are the hand ones.** -/
theorem ret0_ph : ph ret0L = Spike.Lib.A64.Flow.Ret0.Inst.ph := by
  funext pc
  show Scc.Cert.Rt.A64.phOf ret0Λ.code.lo ret0Prog pc = _
  unfold Scc.Cert.Rt.A64.phOf
  rw [ret0_phTab]
  simp only [Scc.Cert.Rt.A64.PhTab.ph, Scc.Cert.Rt.A64.inRs, List.any_cons, List.any_nil, Bool.or_false,
    Spike.Lib.A64.Flow.Ret0.Inst.ph, Spike.Lib.A64.Flow.Ret0.Inst.bP, Spike.Lib.A64.Flow.Ret0.Inst.bL,
    Spike.Lib.A64.Flow.Ret0.Inst.bN, Spike.Lib.A64.Flow.Ret0.Inst.bT, Spike.Lib.A64.Flow.Ret0.Inst.inN,
    Bool.or_assoc]

/-- `ret0`'s sites: the hand ones. -/
theorem ret0_sites : Scc.Cert.Rt.A64.sitesOf ret0Λ.code.lo ret0Prog ret0Λ =
    some [4196192, 4196248, 4198508, 4198580, 4198652, 4198724, 4198796] := by
  decide +kernel

/-- **The record's off-site pcs are the hand ones.** -/
theorem ret0_okPc : okPc ret0L = Spike.Lib.A64.Flow.Ret0.Inst.okPc := by
  funext pc
  show Scc.Cert.Rt.A64.okPcOf ret0Λ.code.lo ret0Prog ret0Λ pc = _
  unfold Scc.Cert.Rt.A64.okPcOf
  rw [ret0_sites]
  rfl

/-- **The record's owned words are the hand ones.** -/
theorem ret0_ownOf : ownOf ret0L = Spike.Lib.A64.Flow.Ret0.Inst.ownOf := rfl

/-- **The record's marks are the hand ones**, given the loader's parse. -/
theorem ret0_μ (hpa : Scc.Sem.A64.textProgram ret0Asm = .ok ret0Prog) : μ ret0L = Spike.Lib.A64.Flow.Ret0.Inst.μ0 :=
  (marks_eq ret0L hpa).symm.trans (Spike.Lib.A64.Flow.Ret0.Inst.ret0_marks hpa)

/-- The take site at its label in `ret0`'s loaded thread. -/
theorem ret0_site :
    (μ ret0L).site .take = some (ret0L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
  show _ = some ((_root_.Executable.labels Spike.Lib.A64.Flow.Ret0.Mem.ret0Exe).label _).toBitVec.toNat
  rw [Spike.Lib.A64.Flow.Ret0.Inst.ret0_labT]
  decide +kernel

/-- **The record's instance's facts at `ret0`.** -/
theorem ret0_instOk {rS : Range} :
    Spike.Lib.A64.Rt.InstOk ret0L.exe ret0L.endPc ret0L.prog ret0L.lab (μ ret0L) (own ret0L) (Tk ret0L)
      (K ret0L rS) (okPc ret0L) (ph ret0L) :=
  instOk ret0L ret0_site

/-- The frame condition's words: satisfiable (the entry stack's memory). -/
example {m : MachineData} (h : m.dmem = Scc.Sem.Entry.linux.stackMem) :
    Mem.loadInt m.dmem ret0L.pnA 8 = none ∧ Mem.loadInt m.dmem (ret0L.pinA + 0#64) 8 = none :=
  ⟨rtF_pn (Spike.Lib.A64.Rt.rtF_stackMem ret0L Spike.Lib.A64.Rt.Ret0L.ret0L_ok h), rtF_hdr0
      (Spike.Lib.A64.Rt.rtF_stackMem ret0L Spike.Lib.A64.Rt.Ret0L.ret0L_ok h)⟩

/-- `ret0`'s first TCB is off its counters. -/
theorem ret0_tcbSep : TcbSep ret0L := by unfold TcbSep; decide

/-- `ret0`'s TCB words: owned at no phase, mapped, unmapped at the entry. -/
example {m : MachineData} (h : m.dmem = Scc.Sem.Entry.linux.stackMem) :
    ∀ j < 7, (∀ i w, (⟨ret0L.pinA + BitVec.ofNat 64 (8 * j), 8⟩, w) ∉ ownOf ret0L i) ∧
      Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 ret0L.Λ) true ⟨ret0L.pinA + BitVec.ofNat 64 (8 * j), 8⟩ ∧
      Mem.loadInt m.dmem (ret0L.pinA + BitVec.ofNat 64 (8 * j)) 8 = none := fun j hj =>
  ⟨tcb_not_own ret0_tcbSep ⟨j, hj, rfl⟩, mapped_tcb ⟨j, hj, rfl⟩,
    rtF_tcb (Spike.Lib.A64.Rt.rtF_stackMem ret0L Spike.Lib.A64.Rt.Ret0L.ret0L_ok h) ⟨j, hj, rfl⟩⟩

/-- **The instance's facts from `ret0`'s placement check**: the generic
discharge of the take site's label (`site_ofPlaceOK`) at `ret0`. -/
example {rS : Range} := instOk_ofPlaceOK
    (Scc.Cert.PlaceOK.A64.atTables Scc.Cert.PlaceOK.A64.Test.ret0_placeOK) SccCode.ret0Imms (rS := rS)

/-- At `ret0`'s placement check the record's layout is `ret0L` in the
fields the phases read. -/
example : (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK
    (Scc.Cert.PlaceOK.A64.atTables Scc.Cert.PlaceOK.A64.Test.ret0_placeOK) SccCode.ret0Imms).prog =
    ret0L.prog := rfl

end Spike.Lib.A64.PhRec.Test
