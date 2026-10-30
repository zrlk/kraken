/-
**main's post-spawn system calls are `futex` or `exit_group`** (AArch64): the node obligations of main's post-spawn segments at
`W := fun s _ => WakeInst.MainSys s`: a covered block's internal states and
a load or exchange are at no `svc`, the park's `svc` has `x8 = 98`, the exit
tail's `x8 = 94` (`WCompat0.noWrite0` through `WakeInst.noWrite0_I`).

- `mainSys_cell`: a state at a cell other than an `svc`; `blkW_sys`,
  `nodeW_sysCell`, `nodeW_sysNr`.
- `loopW_sys`, `parkGW_sys`, `parentW_sys`, `exitW0_sys`, `exitW1_sys`,
  `tlsW_sys`.
- `tlsW_mainR`: the limit load inside `WakeInst.mainWR` (`seg_waitTlsW`'s
  `hW`), its `FlagW` conjunct `A64WakeMainF.tlsW_flag`.
-/
import Spike.Lib.A64WakeMainF

namespace Spike.Lib.A64WakeMainS

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64WakeMainSegW (ParentW exitNP)
open Spike.Lib.WakeInst (MainSys)
open Spike.Lib.A64 (CodeAt)

variable {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **A state at a cell other than an `svc` is at no system call.** -/
theorem mainSys_cell {s : State} {d : Directive} {sz : Nat} (hc : CellAt s d sz)
    (hd : ∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) : MainSys s := by
  intro ha
  obtain ⟨imm, sz', rest, hsv⟩ := Spike.Lib.A64.SvcFault.svc_codeAt ha
  obtain ⟨rest', hc'⟩ := hc.code
  rw [hsv] at hc'
  simp only [List.cons.injEq, Prod.mk.injEq] at hc'
  exact absurd hc'.1.1.symm (hd imm)

/-- **A covered block's internal states are at no system call**: they run
to `.done` (`blk_exec_done`), an `svc` faults (`exec_atSvc`). -/
theorem blkW_sys {n : ND} {lo hi : Int} {blk : List Directive} (hok : okBlk lo hi n.o blk = true) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk) :
    BlkW (fun s _ => MainSys s) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c he hn _ _ _ _ _ k hk m hA _
  subst he
  refine ⟨fun ha => ?_, fun _ h => h⟩
  obtain ⟨s', hx⟩ := blk_exec_done hok hR hal hlo hhi (hcode s rfl hn) hk hA
  have hv : Kraken.Executable.ValidLayout s.exe := (hcode s rfl hn k _ (List.getElem?_eq_getElem hk)).valid
  obtain ⟨_, hf⟩ := Spike.Lib.A64.SvcFault.exec_atSvc (s := { s with st := (m, n.pc + Int64.ofNat (4 * k)) })
    hv ha hx
  cases hf

/-- **A one-instruction node other than an `svc` is at no system call.** -/
theorem nodeW_sysCell {n : ND} {d : Directive}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [d])
    (hd : ∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) :
    NodeW (fun s _ => MainSys s) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨he, hn, -, hpc, -⟩
  exact ⟨mainSys_cell ((hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)) hd, fun _ h => h⟩

/-- **A node whose `x8` is `98` or `94`** satisfies `MainSys`. -/
theorem nodeW_sysNr {n : ND}
    (h : ∀ σ c, n.J σ c → σ.regs.X8.toNat = 98 ∨ σ.regs.X8.toNat = 94) :
    NodeW (fun s _ => MainSys s) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨-, -, -, -, σ, hA, -, hJ⟩
  refine ⟨fun _ => ?_, fun _ h => h⟩
  rw [hA.regs]
  exact h σ c hJ

section Loop

open Spike.Lib.A64.WaitLoop

variable {pfx : String} {c0 : Ctl} {x : String} {e : Expr} {ty : Ty} {Rd : TermRun.Word → Prop}
  {A x29 ra tp : BitVec 64}

/-- **`wc_waitLoop`'s states are at no system call.** -/
theorem loopW_sys (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    (hcode : Code pfx c0 x e ty Rd A x29 ra tp exe endPc) :
    LoopW (fun s _ => MainSys s) exe endPc R F pfx c0 x e ty Rd A x29 ra tp where
  top := blkW_sys b0_ok hR hal hlo hhi hcode.top
  n1 := blkW_sys b1_ok hR hal hlo hhi hcode.n1
  n2 := blkW_sys b2_ok hR hal hlo hhi hcode.n2
  entry := blkW_sys b3_ok hR hal hlo hhi hcode.entry
  ld := nodeW_sysCell hcode.ld fun _ h => by cases h
  n4 := blkW_sys b4_ok hR hal hlo hhi hcode.n4
  n5 := blkW_sys b5_ok hR hal hlo hhi hcode.n5
  then1 := blkW_sys b6_ok hR hal hlo hhi hcode.then1
  else2 := blkW_sys b7_ok hR hal hlo hhi hcode.else2
  sp3 := blkW_sys b8_ok hR hal hlo hhi hcode.sp3

end Loop

section Park

open Spike.Lib.A64.Flow.Park

/-- **`scc_rt_park`'s states**: its `svc` is `futex` (`x8 = 98`), its other
states at no system call. -/
theorem parkGW_sys {c0 : Ctl} {x29 ra tp : BitVec 64} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -64) (hhi : 0 ≤ R.hi) (hcode : Code c0 x29 ra tp exe endPc) :
    ParkGW (fun s _ => MainSys s) exe endPc R F c0 x29 ra tp where
  e := blkW_sys b0_ok hR hal hlo hhi hcode.e
  n1 := blkW_sys b1_ok hR hal hlo hhi hcode.n1
  swp1 := nodeW_sysCell hcode.swp1 fun _ h => by cases h
  n2 := blkW_sys b2_ok hR hal hlo hhi hcode.n2
  n3 := blkW_sys b3_ok hR hal hlo hhi hcode.n3
  wait := blkW_sys b4_ok hR hal hlo hhi hcode.wait
  svc := nodeW_sysNr fun σ _ hJ => by
    obtain ⟨-, -, -, -, h8⟩ := hJ
    exact .inl (by rw [h8]; rfl)
  n5 := blkW_sys b5_ok hR hal hlo hhi hcode.n5
  swp2 := nodeW_sysCell hcode.swp2 fun _ h => by cases h
  n6 := blkW_sys b6_ok hR hal hlo hhi hcode.n6
  done := blkW_sys b7_ok hR hal hlo hhi hcode.done

end Park

/-- **The parent's states are at no system call**, in any valid layout of
`wakeProg`. -/
theorem parentW_sys [Kraken.Executable.ValidLayout exe] {kp : Nat} {cP : Ctl} {A x29 ra tp : BitVec 64}
    (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi) :
    ParentW (fun s _ => MainSys s) exe endPc R F cP A x29 ra tp := by
  have hin := Spike.Lib.A64.Flow.Worker.Wake.Parent.wake_parentIn
  simp only [Spike.Lib.A64.Flow.Worker.Wake.Parent.parentIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨hcb, -⟩, hcl⟩, hbs⟩, hsp⟩ := hin
  open Spike.Lib.A64.Flow.Worker.Wake.Parent in
  exact {
    wcb := blkW_sys cbP_ok hR hal hlo hhi (code_of hp hend hcb (by simp only [pN, ofNat4_succ, ofNat4_zero]))
    wcl := blkW_sys cl_ok hR hal hlo hhi (code_of hp hend hcl (ofNat4_zero _))
    wbs := blkW_sys bs_ok hR hal hlo hhi (code_of hp hend hbs rfl)
    wsp := blkW_sys spB_ok hR hal hlo hhi (code_of hp hend hsp (ofNat4_zero _)) }

section Exit

variable {c0 : Ctl} {x : String} {e : Expr} {ty : Ty} {Rd : TermRun.Word → Prop} {A x29 ra tp : BitVec 64}
  [Kraken.Executable.ValidLayout exe] {kp : Nat}

/-- **The exit tail's block is at no system call.** -/
theorem exitW0_sys (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ 0) (hhi : 16 ≤ R.hi)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label Spike.Lib.A64.Flow.Worker.Wake.MainPost.mainSp0) :
    BlkW (fun s _ => MainSys s) (fun _ _ => False) exe endPc R F
      (Spike.Lib.A64.WaitLoop.E c0 x e ty Rd A x29 ra tp .ret) (exitTail 8) := by
  have hin := Spike.Lib.A64.Flow.Worker.Wake.MainPost.wake_exitIn
  simp only [exitIn, Bool.and_eq_true] at hin
  exact blkW_sys (exitTail_ok (lo := 0) (hi := 16) rfl rfl) hR hal hlo hhi
    (code_of hp hend hin.1 (by show _ = Int64.ofBitVec ra; rw [hra, ofNat4_zero]))

omit [Kraken.Executable.ValidLayout exe] in
/-- **The exit tail's `svc` is `exit_group`** (`x8 = 94`). -/
theorem exitW1_sys :
    NodeW (fun s _ => MainSys s) (fun _ _ => False) exe endPc R F
      (exitNP (Spike.Lib.A64.WaitLoop.E c0 x e ty Rd A x29 ra tp .ret)) :=
  nodeW_sysNr fun _ _ hJ => .inr hJ.1

end Exit

/-- **The limit load is at no system call** (a plain `ldr`). -/
theorem tlsW_sys [Kraken.Executable.ValidLayout exe] {kp : Nat} (hp : Lays exe wakeProg kp)
    (hend : endPc = endOf exe wakeProg kp) {n : ND}
    (hpc : n.pc = (_root_.Executable.labels exe).label (Spike.Lib.A64.WakeLabels.pfx ++ ".stack_check") +
      Int64.ofNat (4 * 2)) :
    NodeW (fun s _ => MainSys s) (fun _ _ => False) exe endPc R F n :=
  nodeW_sysCell (code_of hp hend Spike.Lib.A64.Flow.Worker.Wake.AbOffAt.wait_tlsCode hpc.symm) fun _ h => by
    cases h

/-- **`wc_waitLoop`'s limit load inside `mainWR`** (`seg_waitTlsW`'s `hW`
at the instance): `A64WakeMainW.tlsW_main`, `A64WakeMainR.tlsW_relW` and
`A64WakeMainL.tlsW_ctl` at `LabMapped` (`hm0`, e.g. `labMapped_c0`),
`tlsW_sys` and `A64WakeMainF.tlsW_flag` (the loop's control at `wlBody`,
`hwb`; its flag word inside its label, `hin`; `tp + 8` outside every placed
label, `hrt8`; `hflag`). -/
theorem tlsW_mainR [Kraken.Executable.ValidLayout exe] {kp : Nat} {Λ : Scc.Sem.Layout}
    {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {ms : MemSide isaLSE2}
    {c0 : Ctl} {x cv : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {w : TermRun.Word}
    {A x29 ra tp : BitVec 64}
    (hp : Scc.Cert.Rt.A64.Lays exe Spike.Lib.A64.WakeLabels.wakeProg kp)
    (hend : endPc = Scc.Cert.Rt.A64.endOf exe Spike.Lib.A64.WakeLabels.wakeProg kp)
    (hpc : (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels exe).label Spike.Lib.A64.WakeLabels.pfx c0 x e ty
        (fun w' => ms.rd w' ∧ Scc.Sem.ValRep lbl w'.val 1) A x29 ra tp .tls).pc =
      (_root_.Executable.labels exe).label (Spike.Lib.A64.WakeLabels.pfx ++ ".stack_check") + Int64.ofNat (4 * 2))
    (hruns : Spike.Lib.A64WakeOff.RunsOffA (_root_.Executable.labels exe).label
      (Spike.Lib.A64WakeMainW.waitRuns Spike.Lib.A64.WakeLabels.pfx))
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → Spike.Lib.A64.WideKeep.WideX exe s)
    (hc0 : c0.term ≠ WakeMLive.wlRet) (hfv0 : ∀ y ∈ Scc.Sem.exprFv c0.term, y = cv)
    (hl : TermRun.lookupE c0.env cv = some (ty, [w])) (hloc : Scc.Sem.LocRep lbl w.val A.toNat 0)
    (hm0 : Spike.Lib.WakeMappedRow.LabMapped lbl (Spike.Lib.A64Consumer.K0 Λ) c0)
    (hflag : Spike.Lib.A64WakeOff.RunsNe (_root_.Executable.labels exe).label
      ((_root_.Executable.labels exe).label (Spike.Lib.A64.WakeLabels.pfx ++ ".0_entry") + 4 + 4)
      (Spike.Lib.A64WakeMainF.flagRuns Spike.Lib.A64.WakeLabels.pfx))
    (hrt8 : ¬ ∃ l b, lbl l = some b ∧ (Scc.Sem.lrange lsize l b).contains (tp + 8#64).toNat)
    (hwb : c0.term = Spike.Lib.WakeM0.wlBody) (hterm : c0.term = .let_ x (.load true a) e)
    (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label) :
    NodeW (Spike.Lib.WakeInst.mainWR (_root_.Executable.labels exe).label exe Λ lbl lsize) (fun _ _ => False) exe endPc
      R F (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels exe).label Spike.Lib.A64.WakeLabels.pfx c0 x e ty
        (fun w' => ms.rd w' ∧ Scc.Sem.ValRep lbl w'.val 1) A x29 ra tp .tls) :=
  (Spike.Lib.A64WakeMainW.tlsW_main hruns hwide hc0 hfv0 hl hloc).and
    ((Spike.Lib.A64WakeMainR.tlsW_relW hp hend hpc).and
      ((Spike.Lib.A64WakeMainL.tlsW_ctl hm0).and ((tlsW_sys hp hend hpc).and
        (Spike.Lib.A64WakeMainF.tlsW_flag hp hend hpc hflag (Spike.Lib.A64WakeMainF.tp8_ne hrt8 hloc hin)
          (Spike.Lib.A64WakeMainF.flag0_of hwb hterm hev hloc hin)))))

/-- info: 'Spike.Lib.A64WakeMainS.tlsW_mainR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tlsW_mainR

/-- info: 'Spike.Lib.A64WakeMainS.loopW_sys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loopW_sys
/-- info: 'Spike.Lib.A64WakeMainS.parkGW_sys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parkGW_sys
/-- info: 'Spike.Lib.A64WakeMainS.parentW_sys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parentW_sys
/-- info: 'Spike.Lib.A64WakeMainS.exitW0_sys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exitW0_sys
/-- info: 'Spike.Lib.A64WakeMainS.tlsW_sys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tlsW_sys

end Spike.Lib.A64WakeMainS
