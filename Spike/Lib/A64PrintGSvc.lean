/-
**`scc_rt_print`'s system call at any instance** (AArch64): the state's
facts (`SFactsSt`) and the write abort's phase (`AbSt` at `WriteAb.Ab`) at
`PrintA.N … .svc`, the `write` of `print`'s loop, for any executable with
`InstOk`, its program holding the routine's code (`printIn`) passing the
phase check `printPhOkF`: the system-call twins of `printSt`
(`Spike/Lib/A64PrintG.lean`) and `printAb` (`Spike/Lib/A64PrintGAb.lean`),
the place-independent parts of `PrintW`'s system-call obligation at `W2`
(`Spike/Lib/LowerA64/PrintCallC2.lean`).

- `decode_print`: `x0 = 1`, `x8 = 64` decode to a `write` to the standard
  output of `x2` bytes at `x1`.
- `pcRet_nmem`: the pc after the call is no other pc of the phase.
- `ret_ab`: a kernel return from the call in the phase refuses the stored
  length (`[sp + 8]`).
- `printSvcSt`: the call's states carry `SFactsSt`, the write tail `Dt`
  given at the node (`hDt`), the range owned from the frame condition
  (`hFO`).
- `printSvcStP`: `printSvcSt` in `print`'s region at a call, under a frame
  condition inside `print`'s (`pF`, `PrintW`'s system-call clause).
- `printSvcAb`: the call's states keep the write abort's phase: off it, a
  return lands in it only as a refusal of the length passed (`x2`, the
  frame's cell `-40`).
- `printSvcWe`: every refused result of the call lands in the phase (`WeAb`).
-/
import Spike.Lib.A64PrintGAb
import Spike.Lib.A64PrintCall

namespace Spike.Lib.A64.PrintG

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow (NodeW ND svcDir)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.A64.Rt (InstOk)
open Scc.Cert.Rt.A64 (blockAt InRun pc_ne_of_inRun Lays)
open Spike.Lib.A64ConsumerA (SFactsSt AbSt)
open Spike.Lib.A64.WriteAb (Ab abPcs spLoad pcRet tailPcs failPcs dispEPcs dispTPcs g4Pcs stubPcs)
open Spike.Lib.LowerA64 (abPos abPcs_eq abPos_inRun)
open Spike.Lib.A64.StubW (printPhOk)
open Spike.Lib.A64.AllocG (phOne_spec)
open Spike.Lib.A64.PrintA (N)
open Kraken.Promising.Lower.A64 (CellAt after)

/-! ## The call and its return -/

/-- **`x0 = 1`, `x8 = 64` decode to a `write`** to the standard output of
`x2` bytes at `x1`. -/
theorem decode_print {s : State} (h0 : s.st.1.regs.X0 = 1) (h8 : s.st.1.regs.X8 = 64) :
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) =
      some (.write 1 s.st.1.regs.X1.toNat s.st.1.regs.X2.toNat) := by
  simp [abi, Kernel.decode, Kernel.Nrs.a64, h0, h8, xRegs]

section Ret

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive} {kp : Nat}

/-- **The pc after the call is no other pc of the phase**: `pcRet` is
`abPos`'s first position, its others told apart from it by
`pc_ne_of_inRun`. -/
theorem pcRet_nmem (hp : Lays exe prog kp) (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true) :
    pcRet (_root_.Executable.labels exe).label ∉
      tailPcs (_root_.Executable.labels exe).label ++ failPcs (_root_.Executable.labels exe).label ++
        dispEPcs (_root_.Executable.labels exe).label ++ dispTPcs (_root_.Executable.labels exe).label ++
        g4Pcs (_root_.Executable.labels exe).label ++ stubPcs (_root_.Executable.labels exe).label := by
  have hpos : abPos = (".L9_scc_rt_print.2_write", 6) :: abPos.tail := by decide
  have hnin : (".L9_scc_rt_print.2_write", 6) ∉ abPos.tail := by decide
  have h := abPcs_eq (_root_.Executable.labels exe).label
  rw [hpos, List.map_cons] at h
  simp only [abPcs, List.cons_append] at h
  obtain ⟨he0, h⟩ := List.cons.inj h
  rw [h, List.mem_map]
  rintro ⟨q, hq, he⟩
  have hq' : q ∈ abPos := by rw [hpos]; exact List.mem_cons_of_mem _ hq
  have h5 : (".L9_scc_rt_print.2_write", 6) ∈ abPos := by rw [hpos]; exact List.mem_cons_self
  refine pc_ne_of_inRun hp (abPos_inRun hpr hab q hq') (abPos_inRun hpr hab _ h5) ?_ (he.trans he0)
  intro hq5
  exact hnin (hq5 ▸ hq)

/-- **A kernel return from the call in the phase refuses the stored
length**: at the pc after the call, `Ab` is its first case. -/
theorem ret_ab (hp : Lays exe prog kp) (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true) {s : State}
    (hs : s.st.2 = pcRet (_root_.Executable.labels exe).label) (h : Ab (_root_.Executable.labels exe).label s) :
    ∃ l, spLoad s 8 = some l ∧ Refusal l.toNat s.st.1.regs.X0.toBitVec := by
  have hn := pcRet_nmem hp hpr hab
  rw [← hs] at hn
  rcases h with ⟨-, h⟩ | ⟨h, -⟩ | h | ⟨h, -⟩ | ⟨h, -⟩ | h | h
  · exact h
  all_goals exact (hn (by simp [h])).elim

end Ret

/-! ## The call's states -/

section Svc

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region} {F : MachineData → Prop}
  {x29 ra buf0 : BitVec 64} {len0 : Nat} {P Q : Nat → Ctl → Prop}

/-- The call's pc at its label and offset. -/
theorem pcSvc_eq (lab : Label → Int64) :
    Spike.Lib.A64.PrintD.pcSvc lab = lab ".L9_scc_rt_print.2_write" + Int64.ofNat (4 * 5) := by
  simp only [Spike.Lib.A64.PrintD.pcSvc, Int64.add_assoc]; rfl

/-- The call's facts at a state of its node: off the marks' sites, no
outside move, at the `svc` cell, its next pc in its phase. -/
theorem svc_cell (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hin : Scc.Cert.Rt.A64.Print.printIn prog = true) (hph : printPhOkF okPc ph lab = true) {s : State}
    (hs : s.exe = exe) (hn : s.endPc = endPc)
    (hpc : s.st.2 = Spike.Lib.A64.PrintD.pcSvc (_root_.Executable.labels exe).label) :
    (PcOff μ s ∧ ∀ s', ¬ K s s') ∧ CellAt s svcDir 4 ∧
      ∀ m, own (after s 4 m) = own s ∧ (Tk (after s 4 m) ↔ Tk s) := by
  obtain ⟨-, -, -, -, -, -, h5, -⟩ := printIn_spec hin
  obtain ⟨-, -, -, -, -, -, p5, -⟩ := printPhOk_spec hph
  obtain ⟨hok, hph5⟩ := phOne_spec p5
  rw [hI.labOk, pcSvc_eq] at hpc
  exact ⟨hI.off s (by unfold pcOf; rw [hpc]; exact hok), Spike.Lib.A64.Rt.cellOf hI h5 rfl hs hn hpc,
    Spike.Lib.A64.Rt.next_same hI hpc hph5⟩

/-- **`scc_rt_print`'s system call carries the state's facts**, none moved
by `K`, its code in the program (`hin`) passing the phase check (`hph`), in
a region whose frame condition gives the stack range off it (`hFO`), the
write tail `Dt` given at the node (`hDt`). -/
theorem printSvcSt (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hin : Scc.Cert.Rt.A64.Print.printIn prog = true) (hph : printPhOkF okPc ph lab = true)
    {Λ : Scc.Sem.Layout} {rS : Range} {Dt : State → Prop}
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (hDt : ∀ s c, Spike.Lib.A64.Flow.At exe endPc R F
      (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc) s c → Dt s) :
    NodeW (fun s _ => SFactsSt Λ μ own rS Tk s Dt) K exe endPc R F
      (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc) := by
  intro s c hAt
  obtain ⟨hs, hn, -, hpc, σ, hA, hD, -⟩ := id hAt
  obtain ⟨⟨hP, hK⟩, hc, hnext⟩ := svc_cell hI hin hph hs hn hpc
  have hO : Tk s → Owned Λ rS s := fun _ =>
    Spike.Lib.A64.Rt.owned_off hR hR8 hl hh hsub (hFO _ hD) fun k hk => by
      obtain ⟨j, hj, -⟩ := hA.slot k hk
      rw [hj]; rfl
  have hsy : abi.atSys s = true := atSvc_of_cellAt hc
  have hsucc : ∀ call, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call →
      ∀ s' ∈ Kernel.certSuccs abi s call, own s' = own s ∧ (Tk s' ↔ Tk s) := by
    intro call hd s' hs'
    obtain ⟨r, -, rfl⟩ := (mem_certSuccs_svc hc hd).1 hs'
    exact hnext _
  refine ⟨⟨hP.noSite, fun h => ?_, fun _ => ⟨0, 4, hc⟩, fun h => ?_,
    fun _ call hd s' hs' => (hsucc call hd s' hs').1, fun a ha hpc => (hP.noTake a ha hpc).elim,
    fun a ha hpc => (hP.noTake a ha hpc).elim, fun a ha hpc => (hP.noTake a ha hpc).elim, fun _ h => ?_,
    fun _ call hd s' hs' => (hsucc call hd s' hs').2, hO, fun _ _ _ _ _ => hDt s c hAt⟩, hK⟩
  all_goals (rw [hsy] at h; cases h)

/-- **`scc_rt_print`'s system call keeps the write abort's phase**: off
the phase (its pc is), a kernel return lands in it only as a refusal of the
length passed (`x2`, the frame's cell `-40`, read back at `[sp + 8]`); its
and the abort's code in the program (`hpr`, `hab`) passing the phase check
(`hph`), in a region of the routine's frame. -/
theorem printSvcAb (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hph : printPhOkF okPc ph lab = true) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) :
    NodeW (fun s _ => AbSt μ (Ab (_root_.Executable.labels exe).label) s) (fun _ _ => False) exe endPc R F
      (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc) := by
  intro s c hAt
  obtain ⟨hs, hn, -, hpc, σ, hA, -, hJ⟩ := hAt
  obtain ⟨⟨hP, -⟩, hc, -⟩ := svc_cell hI hpr hph hs hn hpc
  obtain ⟨-, h0, h8, -, h2⟩ := hJ
  have hsy : abi.atSys s = true := atSvc_of_cellAt hc
  have hd := decode_print (s := s) (by rw [hA.regs]; exact h0) (by rw [hA.regs]; exact h8)
  refine ⟨⟨fun _ h => (by rw [hsy] at h; cases h), fun _ _ call hd' s' hs' hab' => ?_,
    fun _ a ha hpc => (hP.noTake a ha hpc).elim⟩, fun _ h => h⟩
  rw [hd] at hd'
  cases hd'
  refine ⟨_, _, _, rfl, fun r hr => ?_⟩
  subst hr
  have hret : (abi.ret s r).st.2 = pcRet (_root_.Executable.labels exe).label := by
    show nextPc s = _
    rw [nextPc_of_cellAt hc, hpc]; rfl
  obtain ⟨l, hl, hrf⟩ := ret_ab hI.lays hpr hab hret hab'
  obtain ⟨e8, -⟩ := spLoad_of_abs hA rfl hlo hhi
  have hl' : spLoad (abi.ret s r) 8 = spLoad s 8 := rfl
  rw [hl', e8, Option.some_inj] at hl
  have hx : (abi.ret s r).st.1.regs.X0.toBitVec = r := by simp [abi]
  rw [hx, ← hl, ← h2, ← hA.regs] at hrf
  exact hrf

/-- **`printSvcSt` in `print`'s region at a call** (`PrintCall.pR kc R`),
under any frame condition `F'` inside `print`'s (`hFF`, as `PrintW`'s system
call clause gives it): the stack range off the callee's region from the
caller's frame condition (`hFO`) and the caller's cells outside it
(`stackOff_callee`). -/
theorem printSvcStP (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hin : Scc.Cert.Rt.A64.Print.printIn prog = true) (hph : printPhOkF okPc ph lab = true)
    {Λ : Scc.Sem.Layout} {rS : Range} {Dt : State → Prop} {kc : Int} {F' : MachineData → Prop}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hlo : R.lo ≤ kc + -48) (hkc : kc < R.hi) (hk16 : kc % 16 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (hFF : ∀ m, F' m → Spike.Lib.A64.Flow.PrintCall.pF kc R F m)
    (hDt : ∀ s c, Spike.Lib.A64.Flow.At exe endPc (Spike.Lib.A64.Flow.PrintCall.pR kc R) F'
      (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc) s c → Dt s) :
    NodeW (fun s _ => SFactsSt Λ μ own rS Tk s Dt) K exe endPc (Spike.Lib.A64.Flow.PrintCall.pR kc R) F'
      (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc) := by
  obtain ⟨hR', hal'⟩ := Spike.Lib.A64.Flow.Ret0.Inst.callee_facts hR hal hlo (by decide) hkc hk16
  refine printSvcSt hI hin hph hR' (by show (R.callee kc (-48) 0).base.toNat % 8 = 0; omega)
    (by simp [Region.callee]) (by simp [Region.callee]) hsub (fun m hm => ?_) hDt
  obtain ⟨hF, hcc⟩ := hFF m hm
  exact Spike.Lib.A64.Flow.Ret0.Inst.stackOff_callee hR (by omega) hl hh hlo (by decide) hkc (by omega)
    (hFO m hF) hcc

/-- **Every refused result of `scc_rt_print`'s call lands in the write
abort's phase** (`WeAb`'s obligation): the return is at the pc after the
call, the stored length (`[sp + 8]`, the frame's cell `-40`) at most the
length `len0 < 2^63` (`hlen`), so a refusal of it (`refusal_of_refused`). -/
theorem printSvcWe (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hin : Scc.Cert.Rt.A64.Print.printIn prog = true) (hph : printPhOkF okPc ph lab = true)
    (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (hlen : len0 < 2 ^ 63) {s : State} {c : Ctl}
    (hAt : Spike.Lib.A64.Flow.At exe endPc R F (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc)
      s c) :
    ∀ r, Kernel.writeRefused r = true → Ab (_root_.Executable.labels exe).label (abi.ret s r) := by
  intro r hr
  obtain ⟨hs, hn, -, hpc, σ, hA, -, ⟨k, ⟨-, -, -, h40, hk⟩, -, -⟩, -⟩ := hAt
  obtain ⟨-, hc, -⟩ := svc_cell hI hin hph hs hn hpc
  have hret : (abi.ret s r).st.2 = pcRet (_root_.Executable.labels exe).label := by
    show nextPc s = _
    rw [nextPc_of_cellAt hc, hpc]; rfl
  obtain ⟨e8, -⟩ := Spike.Lib.A64.PrintG.spLoad_of_abs hA rfl hlo hhi
  have hl : spLoad (abi.ret s r) 8 = some (σ.slot (-40)) := e8
  have hx : (abi.ret s r).st.1.regs.X0.toBitVec = r := by simp [abi]
  refine .inl ⟨hret, σ.slot (-40), hl, ?_⟩
  rw [hx]
  refine Spike.Lib.A64.PrintAb.refusal_of_refused ?_ hr
  rw [h40, BitVec.toNat_ofNat]
  omega

end Svc

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64.PrintG.printSvcSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printSvcSt

/-- info: 'Spike.Lib.A64.PrintG.printSvcStP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printSvcStP

/-- info: 'Spike.Lib.A64.PrintG.printSvcAb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printSvcAb

/-- info: 'Spike.Lib.A64.PrintG.printSvcWe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printSvcWe

end Spike.Lib.A64.PrintG
