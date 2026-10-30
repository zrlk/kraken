/-
**wake.w's heap abort path keeps both abort phases** (`Wf`'s `AbSt`/`AcSt`,
AArch64): every obligation of `Abort.Disp.HPathW` (the dispatcher at the
heap code `2` with a return address `ra`, then `scc_rt_abort_heap`) at
`AbSt μ (WriteAb.Ab lab) ∧ AcSt μ Cl (ThreadsAb.Ac lab pfxM)`, for an
executable with `InstOk`, its program holding the runtime's abort code
(`abortIn`) and passing the path's phase check (`abortPhHeapOk`), its labels
wake's code labels where they resolve (`hlab`), `ra` not the threads
abort's return address (`hra`).

The dispatcher's prologue and first tests are at pcs of both phases: the
code `2` (in `x0`, then at `[sp]`) keeps the write abort out, `x30 = ra`
the threads abort (`blkW_dispPh`). Every other block and instruction of
the path reaches neither phase's pcs (`blkW_phSt`, `nodeW_phSt`); the exit
call resumes in no state.

- `d0_x30'`, `tj_x30`: `x30` kept through the prologue and the tests.
- `blkW_phI`, `blkW_dispI`, `nodeW_siI`, `nodeW_svcI`, `nodeW_exitI`: the
  WfPh lemmas at a block or instruction of the program.
- `hpathW_ph`.
-/
import Spike.Lib.A64WakeWfAb
import Spike.Lib.A64WakeWfG
import Spike.Lib.A64AbortHeapRW
import Spike.Lib.A64AbortPhH

namespace Spike.Lib.A64.WakeWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (NodeW BlkW ND At)
open Spike.Lib.A64.Rt (InstOk)
open Scc.Cert.Rt.A64 (blockAt label_labelGap)
open Scc.Cert.Rt.A64.Print (add4 add0)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.StubW (abortPhHeapOk phOne)

/-! ## `x30` through the dispatcher -/

section Run

set_option linter.unusedSimpArgs false

/-- The abstract run's simp set over the dispatcher's blocks. -/
local macro "arun_simp" : tactic =>
  `(tactic| simp [Spike.Lib.A64.Flow.arun, Spike.Lib.A64.Flow.dstep, Spike.Lib.A64.Flow.classify,
    Spike.Lib.A64.Flow.RegOnly, Spike.Lib.A64.Flow.AI.so, Spike.Lib.A64.Flow.AI.step,
    Spike.Lib.A64.Flow.AI.tgt, Spike.Lib.A64.Flow.soReg, Spike.Lib.A64.Flow.regDst, Spike.Lib.A64.Flow.zrB,
    Spike.Lib.A64.Flow.regRes, Operation.interp, MachineData.setRegOrZr, MachineData.setRegOrSp,
    Reg64s.setRegOrZr, Reg64s.getRegOrZr, Reg64s.setRegOrZr64, Reg64s.getRegOrZr64, Reg64s.setRegOrSp,
    Reg64s.getRegOrSp, Reg64s.setRegOrSp64, Reg64s.getRegOrSp64, Reg64s.setXReg, Reg64s.getXReg,
    ShiftRegExpr.interp, ExtOrImmReg.interp, ConstExpr.interp, RegOrZr.base, RegOrSp.base,
    Spike.Lib.A64.Flow.SO.get, Spike.Lib.A64.Flow.SO.set, Spike.Lib.A64.Flow.SO.kill,
    Spike.Lib.A64.Flow.SO.write, Spike.Lib.A64.Flow.SO.killZ, Spike.Lib.lk, Spike.Lib.rm, Spike.Lib.upd_apply])

/-- The dispatcher's prologue keeps `x30` through its end. -/
theorem d0_x30' (lab : Label → Int64) (pc : Int64) (σ : Spike.Lib.A64.Flow.AS) {k : Nat}
    (hk : k ≤ Abort.Disp.d0.length) :
    (Spike.Lib.A64.Flow.arun lab (Abort.Disp.d0.take k) ⟨pc, Abort.oE, σ⟩).σ.regs.X30 = σ.regs.X30 := by
  simp only [Abort.Disp.d0] at hk ⊢
  simp only [List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|_|_|_|k <;> (try omega) <;> arun_simp

/-- The dispatcher's tests against `1`, `2` and the jump keep `x30`
through their end. -/
theorem tj_x30 (lab : Label → Int64) {blk : List Directive}
    (hb : blk = Abort.Disp.t1 ∨ blk = Abort.Disp.t2 ∨ blk = Abort.Disp.j1) (pc : Int64) (σ : Spike.Lib.A64.Flow.AS)
    {j : Nat} (hj : j ≤ blk.length) :
    (Spike.Lib.A64.Flow.arun lab (blk.take j) ⟨pc, Abort.Disp.oD, σ⟩).σ.regs.X30 = σ.regs.X30 := by
  rcases hb with rfl | rfl | rfl <;>
    simp only [Abort.Disp.t1, Abort.Disp.t2, Abort.Disp.j1] at hj ⊢ <;>
    simp only [List.length_cons, List.length_nil] at hj <;>
    rcases j with _|_|_|_|_|j <;> (try omega) <;> arun_simp

end Run

/-! ## At the program's blocks -/

section Prog

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop} {okPc : Nat → Bool}
  {ph : Nat → Nat} {kp : Nat} {Cl : State → Prop} {R : Region} {F : MachineData → Prop} {pfx : String}

omit [Kraken.Executable.ValidLayout exe] in
/-- A covered block's pcs off the marks' sites from its phase check. -/
theorem hpcOf (hI : InstOk exe endPc prog (_root_.Executable.labels exe).label μ own Tk K okPc ph kp) {n : ND}
    {blk : List Directive} {lo hi : Int} (hok : Spike.Lib.A64.Flow.okBlk lo hi n.o blk = true)
    (hph : blkPh okPc ph (fun _ => false) (_root_.Executable.labels exe).label n.pc 0 blk = true)
    (hnr : noRetBlk blk = true) :
    ∀ j < blk.length, ∀ s : State, s.exe = exe → s.endPc = endPc → s.st.2 = n.pc + Int64.ofNat (4 * j) →
      PcOff μ s := fun j hj s h1 h2 h3 =>
  ((blkPh_sound (μ := μ) (endPc := endPc) hI.same hI.off hok hph
    (fun _ _ _ k hk r hr => (noRet_false hnr k hk r hr).elim) (fun _ _ _ => rfl)).1 j hj s h1 h2 h3).1

/-- **`blkW_phSt` at a block of the program** without a `ret`. -/
theorem blkW_phI (hI : InstOk exe endPc prog (_root_.Executable.labels exe).label μ own Tk K okPc ph kp)
    {n : ND} {blk : List Directive} {lo hi : Int} {l : Label} {k : Nat} (hb : blockAt prog l k blk = true)
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk lo hi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hph : blkPh okPc ph (fun _ => false) (_root_.Executable.labels exe).label
      ((_root_.Executable.labels exe).label l + Int64.ofNat (4 * k)) 0 blk = true)
    (hnr : noRetBlk blk = true) (h : phOff (_root_.Executable.labels exe).label pfx l k l blk = true) :
    BlkW (fun s _ => AbSt μ (Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (Spike.Lib.A64.ThreadsAb.Ac (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n blk := by
  rw [he] at hph
  exact blkW_phSt (Spike.Lib.A64.Flow.code_of hI.lays hI.endOk hb he) hok hR hal hlo hhi (hpcOf hI hok hph hnr)
    he h fun _ _ _ j hj r hr => (noRet_false hnr j hj r hr).elim

/-- **`blkW_dispPh` at a block of the program.** -/
theorem blkW_dispI (hI : InstOk exe endPc prog (_root_.Executable.labels exe).label μ own Tk K okPc ph kp)
    {n : ND} {blk : List Directive} {lo hi : Int} {l : Label} {k : Nat} {E T : List Nat}
    (hb : blockAt prog l k blk = true) (he : (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk lo hi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hoff : R.Off (-32))
    (hph : blkPh okPc ph (fun _ => false) (_root_.Executable.labels exe).label
      ((_root_.Executable.labels exe).label l + Int64.ofNat (4 * k)) 0 blk = true)
    (hnr : noRetBlk blk = true)
    (h : dChk (_root_.Executable.labels exe).label pfx ((_root_.Executable.labels exe).label l + Int64.ofNat (4 * k))
      E T blk = true)
    (hE : ∀ σ c, n.J σ c → ∀ k, k < blk.length → k ∈ E →
      (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ.regs.X0
        ≠ 4)
    (hT : ∀ σ c, n.J σ c → ∀ k, k < blk.length → k ∈ T →
      (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so.sp
        = -32 ∧
      (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ.slot
        (-32) ≠ 4#64)
    (hX : ∀ σ c, n.J σ c → ∀ k, k < blk.length →
      (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1))
        ⟨n.pc, n.o, σ⟩).σ.regs.X30.toBitVec ≠ ThreadsAb.raT (_root_.Executable.labels exe).label pfx) :
    BlkW (fun s _ => AbSt μ (Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (Spike.Lib.A64.ThreadsAb.Ac (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n blk := by
  rw [he] at hph h
  exact blkW_dispPh (Spike.Lib.A64.Flow.code_of hI.lays hI.endOk hb he) hok hR hal hlo hhi hoff
    (hpcOf hI hok hph hnr) hnr h hE hT hX

/-- **`nodeW_phSt` at a single instruction of the program**, its pc off
the sites (`hok`). -/
theorem nodeW_siI (hI : InstOk exe endPc prog (_root_.Executable.labels exe).label μ own Tk K okPc ph kp)
    {n : ND} {si : Spike.Lib.A64.Flow.SI} {l : Label} {k : Nat} (hb : blockAt prog l k [si.toDir] = true)
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) = n.pc)
    (hok : okPc ((_root_.Executable.labels exe).label l + Int64.ofNat (4 * k)).toBitVec.toNat = true)
    (h : siOff (_root_.Executable.labels exe).label pfx l k = true) :
    NodeW (fun s _ => AbSt μ (Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (Spike.Lib.A64.ThreadsAb.Ac (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n := by
  intro s c hA
  obtain ⟨-, -, -, hpc, -⟩ := id hA
  have hP := (hI.off s (by unfold pcOf; rw [hpc, ← he]; exact hok)).1
  exact nodeW_phSt he h (fun a ha heq => hP.noTake a ha (by unfold pcOf; rw [hpc]; exact heq))
    (si_step hI hb he) s c hA

/-- **An `svc` of the program resuming off both phases' pcs** (`h`), its
pc off the sites (`hok`). -/
theorem nodeW_svcI (hI : InstOk exe endPc prog (_root_.Executable.labels exe).label μ own Tk K okPc ph kp)
    {n : ND} {l : Label} {k : Nat} (hb : blockAt prog l k [Spike.Lib.A64.Flow.svcDir] = true)
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) = n.pc)
    (hok : okPc ((_root_.Executable.labels exe).label l + Int64.ofNat (4 * k)).toBitVec.toNat = true)
    (h : siOff (_root_.Executable.labels exe).label pfx l k = true) :
    NodeW (fun s _ => AbSt μ (Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (Spike.Lib.A64.ThreadsAb.Ac (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n := by
  have hc := Spike.Lib.A64.Flow.code_of hI.lays hI.endOk hb he
  simp only [siOff, he, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at h
  intro s c hA
  obtain ⟨-, -, -, hpc, -⟩ := id hA
  have hP := (hI.off s (by unfold pcOf; rw [hpc, ← he]; exact hok)).1
  have htk : ∀ a, μ.site .take = some a → n.pc.toBitVec.toNat ≠ a :=
    fun a ha heq => hP.noTake a ha (by unfold pcOf; rw [hpc]; exact heq)
  refine NodeW.and (nodeW_abSt_svc hc htk fun s' c' hA' r => ?_)
    (nodeW_acSt_svc hc htk fun s' c' hA' => .inr fun r => ?_) s c hA
  · obtain ⟨-, -, -, hpc', -⟩ := hA'
    exact Spike.Lib.A64.WriteAb.not_ab_of_pc (by show s'.st.2 + Int64.ofNat 4 ∉ _; rw [hpc']; exact h.1)
  · obtain ⟨-, -, -, hpc', -⟩ := hA'
    exact Spike.Lib.A64.ThreadsAb.not_ac_of_pc (by show s'.st.2 + Int64.ofNat 4 ∉ _; rw [hpc']; exact h.2)

/-- **An exit call keeps both phases**: at `x8 = 94` (`hx`) the call is
`exit_group`, which resumes in no state; its pc off the take site (`htk`). -/
theorem nodeW_exitI (hI : InstOk exe endPc prog (_root_.Executable.labels exe).label μ own Tk K okPc ph kp)
    {n : ND} {l : Label} {k : Nat} {p : Int64} (hb : blockAt prog l k [Spike.Lib.A64.Flow.svcDir] = true)
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (htk : ∀ a, μ.site .take = some a → p.toBitVec.toNat ≠ a) (hx : ∀ σ c, n.J σ c → σ.regs.X8 = 94) :
    NodeW (fun s _ => AbSt μ (Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (Spike.Lib.A64.ThreadsAb.Ac (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n := by
  refine NodeW.and (Spike.Lib.LowerA64.nodeW_ab_exit hI hb he hp htk hx) ?_
  rintro s c ⟨hs, hn, -, hpc, σ, hA, -, hJ⟩
  rw [hp] at hpc
  have hc := Spike.Lib.A64.Rt.cellOf hI hb he hs hn hpc
  refine ⟨⟨fun _ h => absurd h (by rw [show abi.atSys s = true from atSvc_of_cellAt (imm := 0) hc]; decide),
    fun _ _ _ call hd s' hs' _ => ?_,
    fun _ a ha hpc' => (htk a ha (by rw [← hpc']; unfold pcOf; rw [hpc])).elim⟩, fun _ h => h⟩
  have hd' : Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) =
      some (.exitGroup s.st.1.regs.X0.toNat) := by
    rw [← Spike.Lib.A64.Flow.svcCall_exitGroup (r := s.st.1.regs) (by rw [hA.regs, hx σ c hJ]; rfl)]; rfl
  obtain rfl := Option.some.inj (hd'.symm.trans hd)
  rw [Spike.Lib.A64.Flow.certSuccs_exitGroup] at hs'
  cases hs'

end Prog

end Spike.Lib.A64.WakeWf

/-- info: 'Spike.Lib.A64.WakeWf.tj_x30' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeWf.tj_x30

/-- info: 'Spike.Lib.A64.WakeWf.blkW_dispI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeWf.blkW_dispI

/-- info: 'Spike.Lib.A64.WakeWf.nodeW_svcI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeWf.nodeW_svcI

/-- info: 'Spike.Lib.A64.WakeWf.nodeW_exitI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeWf.nodeW_exitI
