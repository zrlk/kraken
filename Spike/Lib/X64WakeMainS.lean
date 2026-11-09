/-
**main's post-spawn system calls are `futex` or `exit_group`** (x86-64): the x64 twin of
`Spike/Lib/A64WakeMainS.lean`. The node
obligations of main's post-spawn segments (`WaitLoop.LoopW`, `Park.ParkGW`,
`X64WakeMainSegW.ParentW`, the `exit_group` tail's) at
`W := fun s _ => MainSys s`: a covered block's internal states and a load,
exchange or test are at no `syscall`, the park's `syscall` has `%rax = 202`
(`futex`), the exit tail's `%rax = 231` (`exit_group`).

- `MainSys`: at a system call of the x86-64 kernel model
  (`Scc.Sem.X64.abi.atSys`), `%rax` is `202` or `231` (the x86-64 analog of
  `WakeInst.MainSys`'s `x8 = 98 ∨ x8 = 94`; `Kernel.Nrs.x64`).
- `mainSys_cell`: a state at a cell other than a `syscall`; `blkW_sys`,
  `nodeW_sysCell`, `nodeW_sysNr`.
- `xProW_sys`, `loopW_sys`, `parkGW_sys`, `parentW_sys`, `exitW0_sys`,
  `exitW1_sys`.

**Deviations from the A64 file.** `MainSys` is defined here (A64's lives in
`WakeInst`; there is no x86-64 `WakeInst` yet) and tests `%rax`, the
x86-64 number register (`abi.nr`). The code comes from the listing checks
(`prologueIn`, `waitIn`, `parentIn`, `exitIn`) as in `X64WakeMainR`; no
alignment premise (x86-64's `blk_exec_done` needs none). There is no
`tlsW_sys`: x86-64's limit load is the prologue's `w2` node, covered by
`xProW_sys`; `tlsW_mainR` moves to the x86-64 `mainWR` file.
-/
import Spike.Lib.X64WakeMainL
import Spike.Lib.X64SvcFault

namespace Spike.Lib.X64WakeMainS

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib (Region)
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.Rt.X64 (Lays endOf blockAt blockAtB codeAt_blockAt_lays code_field label_labelGapB)
open Spike.Lib.X64.WakePh.MainPost (mainX2)
open Spike.Lib.X64WakeMainSegW (ParentW exitN exitNP)

/-- **main's system calls are `futex` or `exit_group`**: at a system call
of the x86-64 kernel model, `%rax` (`abi.nr`) is `202` or `231`. -/
def MainSys (s : State) : Prop :=
  Scc.Sem.X64.abi.atSys s = true → s.st.1.regs.rax.toNat = 202 ∨ s.st.1.regs.rax.toNat = 231

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **A state at a cell other than a `syscall` is at no system call.** -/
theorem mainSys_cell {s : State} {d : Directive} {z : Nat} (hc : CellAt s d z)
    (hd : ∀ w w', d ≠ .instr (.regular w w' .syscall)) : MainSys s := by
  intro ha
  have h : Scc.Sem.X64.atSyscall s = false := Scc.Sem.X64.atSyscall_false_of_cellAt hc hd
  change Scc.Sem.X64.atSyscall s = true at ha
  rw [h] at ha
  cases ha

/-- **A covered block's internal states are at no system call**: they run
to `.done` (`blk_exec_done`), a `syscall` faults (`exec_atSyscall`). -/
theorem blkW_sys {n : ND} {lo hi : Int} {blk : List (Directive × Nat)} (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk) :
    BlkW (fun s _ => MainSys s) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c he hn _ _ _ _ _ k hk m hA _
  subst he
  refine ⟨fun ha => ?_, fun _ h => h⟩
  obtain ⟨s', hx⟩ := blk_exec_done hok hR hlo hhi (hcode s rfl hn) hk hA
  have hv : Kraken.Executable.ValidLayout s.exe :=
    (hcode s rfl hn k blk[k].1 blk[k].2 (by simp [hk])).valid
  obtain ⟨_, hf⟩ := Spike.Lib.X64.SvcFault.exec_atSyscall
    (s := { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) }) hv ha hx
  cases hf

/-- **A one-instruction node other than a `syscall` is at no system
call.** -/
theorem nodeW_sysCell {n : ND} {d : Directive} {z : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(d, z)])
    (hd : ∀ w w', d ≠ .instr (.regular w w' .syscall)) :
    NodeW (fun s _ => MainSys s) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨he, hn, -, hpc, -⟩
  exact ⟨mainSys_cell ((hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp [cellOff])) hd,
    fun _ h => h⟩

/-- **A node whose `%rax` is `202` or `231`** satisfies `MainSys`. -/
theorem nodeW_sysNr {n : ND}
    (h : ∀ σ c, n.J σ c → σ.regs.rax.toNat = 202 ∨ σ.regs.rax.toNat = 231) :
    NodeW (fun s _ => MainSys s) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨-, -, -, -, σ, hA, -, hJ⟩
  refine ⟨fun _ => ?_, fun _ h => h⟩
  rw [hA.regs]
  exact h σ c hJ

/-! ## The prologue -/

section Pro

variable {ms : MemSide isa} {Z lim : Int64} {L : String} {zl zf z1 z2 zs : Nat}
  {ps : List (Reg64 × Int64 × Nat)} {J : AS → Ctl → Prop}

/-- **A stack-checked prologue's states are at no system call** (from
`prologueIn`; the limit's load `w2` a `movq %fs:…`). -/
theorem xProW_sys [Executable.ValidLayout exe] {cells : List (Directive × Nat)} {kp : Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) {fn sc entry : Label}
    (hin : prologueIn cells fn sc entry Z lim L zl zf z1 z2 zs ps = true)
    (hR : R.OK) (hlo : R.lo ≤ -8 - Z.toInt) (hhi : 0 ≤ R.hi) (hZ : 0 ≤ Z.toInt)
    (hps : ∀ q ∈ ps, offOk (-8 - Z.toInt) 0 (-8 + q.2.1.toInt) = true) :
    XProW (fun s _ => MainSys s) (fun _ _ => False) exe endPc R F ms ((_root_.Executable.labels exe).label fn) Z
      lim L zl zf z1 z2 zs ps J := by
  simp only [prologueIn, Bool.and_eq_true, and_assoc] at hin
  obtain ⟨g0, b0, b1, b2, b3, b4, -⟩ := hin
  have e0 := label_labelGapB hp g0
  have h4 : (_root_.Executable.labels exe).label fn + 1 + 3 = (_root_.Executable.labels exe).label sc := by
    rw [e0, Int64.add_assoc]; rfl
  exact {
    w0 := blkW_sys (xHead_ok (lo := -8 - Z.toInt) (hi := 0) (by omega) (Int.le_refl _)) hR hlo hhi
      (code_field hp hend b0 (ofNat_zero' _))
    w1 := blkW_sys (xLea_ok (lo := -8 - Z.toInt) (hi := 0) Z zl) hR hlo hhi
      (code_field hp hend b1 (by show _ = _ + 1 + 3; rw [h4, ofNat_zero']))
    w2 := nodeW_sysCell (code_field hp hend b2 (by show _ = _ + 1 + 3 + _; rw [h4])) fun _ _ h => by
      cases h
    w3 := blkW_sys (xCmp_ok (lo := -8 - Z.toInt) (hi := 0) _ L z1 z2) hR hlo hhi
      (code_field hp hend b3 (by show _ = _ + 1 + 3 + _ + _; rw [h4, ofNat_add']))
    w4 := blkW_sys (xFr_ok (lo := -8 - Z.toInt) (hi := 0) Z zs ps hps) hR hlo hhi
      (code_field hp hend b4 (by
        show _ = _ + 1 + 3 + _ + _ + _ + _; rw [h4, ofNat_add', ofNat_add', ofNat_add'])) }

end Pro

/-! ## `wc_waitLoop` -/

section Loop

open Spike.Lib.X64.WaitLoop

variable {ms : MemSide isa} {c0 : Ctl} {x : String} {e : Expr} {ty : Ty} {Rd : TermRun.Word → Prop}
  {A fp ra tp sp : BitVec 64}

/-- **`wc_waitLoop`'s states are at no system call** (at
`seg_waitLoopW`'s region bounds). -/
theorem loopW_sys [Executable.ValidLayout exe] {cells : List (Directive × Nat)} {kp : Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hin : waitIn cells = true)
    (hR : R.OK) (hlo : R.lo ≤ -88) (hhi : 8 ≤ R.hi) :
    LoopW (fun s _ => MainSys s) ms exe endPc R F c0 x e ty Rd A fp ra tp sp := by
  have hin' := hin
  simp only [waitIn, Bool.and_eq_true, and_assoc] at hin'
  obtain ⟨hpro, h4, hld, h5, h6, h7, h8, h9, -⟩ := hin'
  exact {
    pro := xProW_sys hp hend hpro hR (by have : (16 : Int64).toInt = 16 := by decide
                                         omega) (by omega) (by decide) (by decide)
    entry := blkW_sys b4_ok hR hlo hhi (code_field hp hend h4 (ofNat_zero' _))
    ld := nodeW_sysCell (code_field hp hend hld rfl) fun _ _ h => by cases h
    n5 := blkW_sys b5_ok hR hlo hhi (code_field hp hend h5 rfl)
    n6 := blkW_sys b6_ok hR hlo hhi (code_field hp hend h6 rfl)
    then1 := blkW_sys b7_ok hR hlo hhi
      (Spike.Lib.X64.code_field_blockAcrossB hp hend h7 (List.take_append_drop _ _) (ofNat_zero' _))
    else2 := blkW_sys b8_ok hR hlo hhi (code_field hp hend h8 (ofNat_zero' _))
    x16 := blkW_sys b9_ok hR hlo hhi (code_field hp hend h9 (ofNat_zero' _)) }

end Loop

/-! ## `scc_rt_park` -/

section Park

open Spike.Lib.X64.Flow.Park (ParkGW)

variable {c0 : Ctl} {rbp0 ra tp : BitVec 64}

/-- **`scc_rt_park`'s states**: its `syscall` is `futex` (`%rax = 202`),
its other states at no system call. -/
theorem parkGW_sys (hR : R.OK) (hlo : R.lo ≤ -56) (hhi : 8 ≤ R.hi)
    (hcode : Spike.Lib.X64.Flow.Park.Code c0 rbp0 ra tp exe endPc) :
    ParkGW (fun s _ => MainSys s) exe endPc R F c0 rbp0 ra tp where
  e := blkW_sys Spike.Lib.X64.Flow.Park.b0_ok hR hlo hhi hcode.e
  fsl := nodeW_sysCell hcode.fsl fun _ _ h => by cases h
  n1 := blkW_sys Spike.Lib.X64.Flow.Park.b1_ok hR hlo hhi hcode.n1
  xchg1 := nodeW_sysCell hcode.xchg1 fun _ _ h => by cases h
  n2 := blkW_sys Spike.Lib.X64.Flow.Park.b2_ok hR hlo hhi hcode.n2
  n3 := blkW_sys Spike.Lib.X64.Flow.Park.b3_ok hR hlo hhi hcode.n3
  wait := blkW_sys Spike.Lib.X64.Flow.Park.b4_ok hR hlo hhi hcode.wait
  sys := nodeW_sysNr fun σ _ hJ => by
    obtain ⟨-, -, -, -, h8⟩ := hJ
    have := congrArg BitVec.toNat h8
    exact .inl (by simpa [Reg64s.get64] using this)
  n5 := blkW_sys Spike.Lib.X64.Flow.Park.b5_ok hR hlo hhi hcode.n5
  xchg2 := nodeW_sysCell hcode.xchg2 fun _ _ h => by cases h
  n6 := blkW_sys Spike.Lib.X64.Flow.Park.b6_ok hR hlo hhi hcode.n6
  done := blkW_sys Spike.Lib.X64.Flow.Park.b7_ok hR hlo hhi hcode.done

end Park

/-! ## The parent -/

section Parent

open Spike.Lib.X64.WakePh.Parent

variable {cP : Ctl} {A fp ra tp : BitVec 64}

/-- **The parent's states are at no system call**, in any valid layout of
cells with `parentIn`. -/
theorem parentW_sys [Executable.ValidLayout exe] {cells : List (Directive × Nat)} {kp : Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hin : parentIn cells = true)
    (hR : R.OK) (hlo : R.lo ≤ -64) (hhi : 16 ≤ R.hi) :
    ParentW (fun s _ => MainSys s) exe endPc R F cP A fp ra tp := by
  simp only [parentIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨bts, bje⟩, -⟩, b22⟩, bbs⟩, bsp⟩ := hin
  have code : ∀ {l : Label} {k off : Nat} {b : List (Directive × Nat)}, blockAt cells l k off b = true →
      ∀ s : State, s.exe = exe → s.endPc = endPc →
        CodeAt s ((_root_.Executable.labels exe).label l + Int64.ofNat off) b :=
    fun h s he hn => codeAt_blockAt_lays hp he (hn.trans hend) h
  have code0 : ∀ {l : Label} {k : Nat} {b : List (Directive × Nat)}, blockAt cells l k 0 b = true →
      ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s ((_root_.Executable.labels exe).label l) b :=
    fun h s he hn => by simpa using code h s he hn
  exact {
    wts := nodeW_sysCell (fun s he hn => code bts s he hn) fun _ _ h => by cases h
    wje := blkW_sys jeB_ok hR hlo hhi (fun s he hn => code bje s he hn)
    wx22 := blkW_sys x22B_ok hR hlo hhi (fun s he hn => code0 b22 s he hn)
    wbs := blkW_sys bsB_ok hR hlo hhi (fun s he hn => code bbs s he hn)
    wsp := blkW_sys spB_ok hR hlo hhi (fun s he hn => code0 bsp s he hn) }

end Parent

/-! ## The `exit_group` tail -/

section Exit

variable {c0 : Ctl} {x : String} {e : Expr} {ty : Ty} {Rd : TermRun.Word → Prop} {A fp ra tp sp : BitVec 64}

/-- **The tail block's states are at no system call** (`%rbp` at offset
`40`, the spill cell `24`). -/
theorem exitW0_sys [Executable.ValidLayout exe] {cells : List (Directive × Nat)} {kp : Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hin : exitIn cells mainX2 (-16) 4 4 5 = true) (hR : R.OK) (hlo : R.lo ≤ 0) (hhi : 32 ≤ R.hi)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainX2) :
    BlkW (fun s _ => MainSys s) (fun _ _ => False) exe endPc R F (exitN c0 x e ty Rd A fp ra tp sp)
      (xExit (-16) 4 4 5) := by
  rw [exitIn, Bool.and_eq_true] at hin
  exact blkW_sys (xExit_ok (lo := 0) (hi := 32) (-16) 4 4 5 (by decide)) hR hlo hhi
    (code_field hp hend hin.1 (by show _ = Int64.ofBitVec ra; rw [hra, ofNat_zero']))

/-- **The tail's `syscall` is `exit_group`** (`%rax = 231`). -/
theorem exitW1_sys :
    NodeW (fun s _ => MainSys s) (fun _ _ => False) exe endPc R F (exitNP (exitN c0 x e ty Rd A fp ra tp sp)) :=
  nodeW_sysNr fun _ _ hJ => .inr hJ.1

end Exit

end Spike.Lib.X64WakeMainS

/-- info: 'Spike.Lib.X64WakeMainS.blkW_sys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainS.blkW_sys
/-- info: 'Spike.Lib.X64WakeMainS.loopW_sys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainS.loopW_sys
/-- info: 'Spike.Lib.X64WakeMainS.parkGW_sys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainS.parkGW_sys
/-- info: 'Spike.Lib.X64WakeMainS.parentW_sys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainS.parentW_sys
/-- info: 'Spike.Lib.X64WakeMainS.exitW0_sys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainS.exitW0_sys
/-- info: 'Spike.Lib.X64WakeMainS.exitW1_sys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainS.exitW1_sys
