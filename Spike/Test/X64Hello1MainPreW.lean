/-
**`scc_rt_main`'s own nodes up to the call of `wc_rodata` at `hello1.w`'s
instance** (x86-64): `MainPreW`'s `pro` (the stack-checked prologue of
frame 64 saving `%rdi`) and `call` (`call wc_rodata`,
`Spike/Lib/X64Hello1Main.lean`) inside the state's facts (`SFactsSt`) at
any control, from `Wr` at the source start's control (`dumN`,
`XProW.mapC`, `BlkW.st`), and inside the write abort's phase
(`AbSt μ0 (WriteAb.Ab labT)`), none moved. The twin of
`Spike/Test/A64Hello1MainPreW.lean`.

- `mainPh_hd`, `mainPh_lea`, `mainPh_ld`, `mainPh_cmp`, `mainPh_fr`,
  `mainPh_call`: the phase checks of `scc_rt_main`'s blocks at `labT`
  (`labT_eq_labX`).
- `mainProWr`, `mainProSt`: the prologue inside `Wr` at the source start's
  control, and inside `SFactsSt` at any control of `J`, the thread pointer
  `tp` fixed by `J` (`htp`) with its limit word mapped (`hmr`) and unmapped in
  private memory (`hun`).
- `mainCallWr`, `mainCallSt`: the call block, likewise.
- `nodeW_ab_fsld`: a thread-pointer load of a word unmapped in private
  memory keeps the write abort's phase (as `nodeW_ab_st`).
- `mainProAb`, `mainCallAb`: the prologue and the call block keep the write
  abort's phase.
-/
import Spike.Test.X64Hello1AllocAb
import Spike.Lib.Rt.X64RtMainU
import Spike.Lib.LowerX64.UserW

namespace Spike.Test.X64Hello1W0

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (MemSide Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer
open Spike.Lib.X64 (NodeW BlkW ND AS fsDir arun classify okBlk)
open Spike.Lib.X64.Flow (XProW xProN1 xProN2 xProN3 xProN4 xHead xLea xCmp xFr xHead_ok xLea_ok xCmp_ok xFr_ok
  xS2 xS1 hdRegs prologueIn ofNat_zero' ofNat_add' h1MainPro hello1_mainPro)
open Spike.Lib.X64.Rt (InstOk cellOf blkW_postO nodeW_fsld_postO)
open Spike.Lib.X64.Rt.MainU (xHead_noRet xLea_noRet xCmp_noRet xFr_noRet callB_noRet)
open Spike.Lib.X64.Flow.Ret0 (StackOff limA)
open Scc.Cert.Rt.X64 (blockAtB label_labelGapB)
open Kraken.Promising.Lower.X64 (CellAt after exec_movfs_load_agrees fsAddr eaddr)
open Spike.Lib.X64ConsumerA (AbSt AbSt.ofLeaves SFactsSt blkAb)
open Spike.Lib.X64.WriteAb (Ab abPcs not_ab_of_pc)
open Spike.Lib.X64.Flow.Hello1 (mO mN0 mB0 mB0_ok hello1_mainIn mainIn)
open Spike.Lib.X64.Flow.Ret0.Inst (cfacts_c0)
open Spike.Test.X64Hello1RtW (hello1_instOk labT_eq_labX)
open Spike.Lib.X64.Flow.Hello1.Mem (hello1Exe hello1End)
open Spike.Lib.X64.Flow.Hello1.Inst
open SccCode (hello1Λ hello1Cells)

/-! ## A thread-pointer load off the write abort's pcs -/

section Gen

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {R : Region} {F : MachineData → Prop}

/-- **A node at a thread-pointer load** `movq %fs:k, %d` of a word `a`
(`ha`) unmapped in private memory (`hun`) keeps the write abort's phase, as
`nodeW_ab_st`. -/
theorem nodeW_ab_fsld {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND} {d : Reg64}
    {k : Int64} {z : Nat} {l : Label} {off : Nat} {p : Int64} {a : BitVec 64}
    (hb : blockAtB cells l off [(fsDir d k, z)] = true) (he : lab l + Int64.ofNat off = p) (hp : n.pc = p)
    (hok : okPc p.toBitVec.toNat = true) (hnx : p + Int64.ofNat z ∉ abPcs lab)
    (ha : ∀ σ c, n.J σ c → σ.regs.fsBase.toBitVec + k.toBitVec = a)
    (hun : ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    NodeW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  rw [hp] at hpc
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc := cellOf hI hb he hs hn hpc
  have ha' : fsAddr s z { base := none, idx := none, disp := .int64 k } = a := by
    rw [← ha σ c hJ]
    simp [fsAddr, eaddr, AddrExpr.interp, ConstExpr.interp, hA.regs]
  have hex := exec_movfs_load_agrees hc ha' (hun _ hD) (Spike.Lib.X64.agrees_of_decls hdc _ _)
  refine ⟨AbSt.ofLeaves hP.noTake (atSyscall_false_of_cellAt hc (by intro w w' h; cases h)) fun t ht => ?_,
    fun _ h => h⟩
  rw [hex] at ht
  cases ht
  exact fun _ _ => not_ab_after hpc hnx

end Gen

/-! ## `scc_rt_main`'s phase checks -/

theorem mainPh_hd : blkPh okPc ph (fun _ => false) labT (labT "scc_rt_main" + Int64.ofNat 0) 0 xHead = true := by
  rw [labT_eq_labX]; decide +kernel

theorem mainPh_lea : blkPh okPc ph (fun _ => false) labT (labT ".Lscc_rt_main.chk" + Int64.ofNat 0) 0
    (xLea 64 5) = true := by rw [labT_eq_labX]; decide +kernel

theorem mainPh_ld : okPc (labT ".Lscc_rt_main.chk" + Int64.ofNat 5).toBitVec.toNat = true ∧
    ph (labT ".Lscc_rt_main.chk" + Int64.ofNat 5 + Int64.ofNat 9).toBitVec.toNat =
      ph (labT ".Lscc_rt_main.chk" + Int64.ofNat 5).toBitVec.toNat := by
  rw [labT_eq_labX]; exact ⟨by decide +kernel, by decide +kernel⟩

theorem mainPh_cmp : blkPh okPc ph (fun _ => false) labT (labT ".Lscc_rt_main.chk" + Int64.ofNat (5 + 9)) 0
    (xCmp ".Lscc_rt_main.stk" 3 2) = true := by rw [labT_eq_labX]; decide +kernel

theorem mainPh_fr : blkPh okPc ph (fun _ => false) labT (labT ".Lscc_rt_main.chk" + Int64.ofNat (5 + 9 + 3 + 2)) 0
    (xFr 64 4 [(.rdi, -8, 4)]) = true := by rw [labT_eq_labX]; decide +kernel

theorem mainPh_call : blkPh okPc ph (fun _ => false) labT (labT ".Lscc_rt_main.entry" + Int64.ofNat 0) 0
    mB0 = true := by rw [labT_eq_labX]; decide +kernel

/-- No `ret` in a block: `hret` of `blkW_postO`, for any return address. -/
private theorem hnr {lab : Label → Int64} {blk : List (Directive × Nat)} (hb : noRetBlk blk = true) {n : ND}
    {ra' : Int64} :
    ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp)
        = ra' :=
  fun _ _ _ k hk hr => (noRet_false hb k hk hr).elim

/-- The call block fits a frame of 64 with the pushed return address. -/
theorem mB0_ok80 : okBlk (-80) 0 mO mB0 = true := by decide

/-! ## `scc_rt_main`'s prologue and call -/

section Main

variable {rS : Range} {R : Region} {F : MachineData → Prop} {ms : MemSide isa} {J : AS → Spike.Lib.Ctl → Prop}
  {tp : UInt64}

/-- The thread pointer after the prologue's head and the check's address. -/
private theorem xS2_fsBase (σ : AS) : (xS2 64 σ).regs.fsBase = σ.regs.fsBase := by
  simp [xS2, xS1, hdRegs, Reg64s.set64]

/-- **`scc_rt_main`'s prologue inside `Wr`** at the source start's control,
for the abstract states of `J`, none moved by the take: its thread pointer
`tp` (`htp`), the limit word mapped (`hmr`) and unmapped in private memory
(`hun`), in an 8-aligned region holding the frame of 64 under the saved
`%rbp` with 8-aligned bounds whose frame condition gives the stack range
off it (`hFO`). -/
theorem mainProWr (htp : ∀ σ c, J σ c → σ.regs.fsBase = tp)
    (hmr : Kernel.mapped (K0 hello1Λ) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -72) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub hello1Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) :
    XProW (Wr rS) (Kr rS) hello1Exe hello1End R F ms (labT "scc_rt_main") 64 8 ".Lscc_rt_main.stk" 5 9 3 2 4
      [(.rdi, -8, 4)] (fun σ c' => c' = Spike.Lib.X64Consumer.c0 ∧ ∃ c, J σ c) := by
  have hI := hello1_instOk (rS := rS)
  have h := hello1_mainPro
  simp only [h1MainPro, prologueIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hgap, bHd⟩, bLea⟩, bLd⟩, bCmp⟩, bFr⟩, -⟩ := h
  have esc := label_labelGapB hI.lays hgap
  rw [hI.labOk] at esc
  have h4 : labT "scc_rt_main" + 1 + 3 = labT ".Lscc_rt_main.chk" := by rw [esc, Int64.add_assoc]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact blkW_postO hI bHd (ofNat_zero' _) (xHead_ok (lo := -72) (hi := 0) (by omega) (Int.le_refl _))
      hR hlo hhi hR8 hl hh (fun _ _ hJ => hJ.1 ▸ cfacts_c0) mainPh_hd (hnr xHead_noRet) (fun _ _ _ => rfl) hsub hfit
      hFO
  · exact blkW_postO hI bLea (by show _ = _ + 1 + 3; rw [h4, ofNat_zero'])
      (xLea_ok (lo := -72) (hi := 0) _ _) hR hlo hhi hR8 hl hh
      (fun _ _ ⟨_, hJ, _⟩ => hJ.1 ▸ cfacts_c0) mainPh_lea (hnr (xLea_noRet _ _)) (fun _ _ _ => rfl) hsub hfit hFO
  · exact nodeW_fsld_postO (p := labT ".Lscc_rt_main.chk" + Int64.ofNat 5) hI bLd rfl
      (by show _ + 1 + 3 + _ = _; rw [h4]) (fun _ _ ⟨_, hJ, _⟩ => hJ.1 ▸ cfacts_c0) mainPh_ld.1 mainPh_ld.2
      (fun _ _ ⟨σ0, ⟨_, c, hJ⟩, he⟩ => by rw [he, xS2_fsBase, htp _ _ hJ]; rfl)
      hmr hun hR hR8 hl hh hsub hFO
  · exact blkW_postO hI bCmp (by show _ = _ + 1 + 3 + _ + _; rw [h4, ofNat_add'])
      (xCmp_ok (lo := -72) (hi := 0) _ _ _ _) hR hlo hhi hR8 hl hh
      (fun _ _ ⟨_, _, hJ, _⟩ => hJ.1 ▸ cfacts_c0) mainPh_cmp (hnr (xCmp_noRet _ _ _)) (fun _ _ _ => rfl) hsub hfit
      hFO
  · exact blkW_postO hI bFr (by show _ = _ + 1 + 3 + _ + _ + _ + _; rw [h4, ofNat_add', ofNat_add', ofNat_add'])
      (xFr_ok (lo := -72) (hi := 0) _ _ _ (by decide)) hR hlo hhi hR8 hl hh
      (fun _ _ ⟨_, _, hJ, _⟩ => hJ.1 ▸ cfacts_c0) mainPh_fr (hnr (xFr_noRet _ _ _)) (fun _ _ _ => rfl) hsub hfit
      hFO

/-- **`scc_rt_main`'s prologue carries the state's facts** at any control
of `J` (`mainProWr`, `XProW.mapC`): `MainPreW`'s `pro`. -/
theorem mainProSt (htp : ∀ σ c, J σ c → σ.regs.fsBase = tp)
    (hmr : Kernel.mapped (K0 hello1Λ) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -72) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub hello1Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) :
    XProW (fun s _ => SFactsSt hello1Λ μ0 own rS Tk s) (Kr rS) hello1Exe hello1End R F ms
      ((_root_.Executable.labels hello1Exe).label "scc_rt_main") 64 8 ".Lscc_rt_main.stk" 5 9 3 2 4
      [(.rdi, -8, 4)] J := by
  rw [hello1_labT]
  exact Spike.Lib.LowerX64.XProW.mapC (mainProWr htp hmr hun hR hR8 hlo hhi hl hh hsub hfit hFO)
    fun σ c hJ => ⟨_, ⟨rfl, c, hJ⟩, fun _ h => h.toSt⟩

/-- **`scc_rt_main`'s call of `wc_rodata` inside `Wr`** at the source
start's control, none moved by the take, the region holding the frame and
the pushed return address. -/
theorem mainCallWr (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub hello1Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) :
    BlkW (Wr rS) (Kr rS) hello1Exe hello1End R F (dumN (mN0 labT R J)) mB0 := by
  have hin := hello1_mainIn
  simp only [mainIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨h0, -⟩, -⟩, -⟩ := hin
  exact blkW_postO (hello1_instOk (rS := rS)) (l := ".Lscc_rt_main.entry") (off := 0) (ra := 0) h0
    (ofNat_zero' _) mB0_ok80 hR hlo hhi hR8 hl hh (fun _ _ hJ => hJ.1 ▸ cfacts_c0) mainPh_call (hnr (by decide))
    (fun _ _ _ => rfl) hsub hfit hFO

/-- **`scc_rt_main`'s call of `wc_rodata` carries the state's facts** at any
control of `J` (`mainCallWr`, `BlkW.st`): `MainPreW`'s `call`. -/
theorem mainCallSt (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub hello1Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) :
    BlkW (fun s _ => SFactsSt hello1Λ μ0 own rS Tk s) (Kr rS) hello1Exe hello1End R F
      (mN0 (_root_.Executable.labels hello1Exe).label R J) mB0 := by
  rw [hello1_labT]
  exact BlkW.st (mainCallWr hR hR8 hlo hhi hl hh hsub hfit hFO)

/-- **`scc_rt_main`'s prologue keeps the write abort's phase**, none moved,
its limit word unmapped in private memory (`hun`). -/
theorem mainProAb (htp : ∀ σ c, J σ c → σ.regs.fsBase = tp)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hR : R.OK) (hlo : R.lo ≤ -72) (hhi : 0 ≤ R.hi) :
    XProW (fun s _ => AbSt μ0 (Ab labT) s) (fun _ _ => False) hello1Exe hello1End R F ms
      ((_root_.Executable.labels hello1Exe).label "scc_rt_main") 64 8 ".Lscc_rt_main.stk" 5 9 3 2 4
      [(.rdi, -8, 4)] J := by
  have hI := hello1_instOk (rS := ⟨0, 0⟩)
  have h := hello1_mainPro
  simp only [h1MainPro, prologueIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hgap, bHd⟩, bLea⟩, bLd⟩, bCmp⟩, bFr⟩, -⟩ := h
  have esc := label_labelGapB hI.lays hgap
  rw [hI.labOk] at esc
  have h4 : labT "scc_rt_main" + 1 + 3 = labT ".Lscc_rt_main.chk" := by rw [esc, Int64.add_assoc]; rfl
  rw [hello1_labT]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact blkW_ab hI bHd (ofNat_zero' _) (xHead_ok (lo := -72) (hi := 0) (by omega) (Int.le_refl _))
      hR hlo hhi mainPh_hd (hnr xHead_noRet) (fun _ _ _ => rfl) (by rw [labT_eq_labY]; decide +kernel)
  · exact blkW_ab hI bLea (by show _ = _ + 1 + 3; rw [h4, ofNat_zero'])
      (xLea_ok (lo := -72) (hi := 0) _ _) hR hlo hhi mainPh_lea (hnr (xLea_noRet _ _)) (fun _ _ _ => rfl)
      (by rw [labT_eq_labY]; decide +kernel)
  · exact nodeW_ab_fsld (p := labT ".Lscc_rt_main.chk" + Int64.ofNat 5) hI bLd rfl
      (by show _ + 1 + 3 + _ = _; rw [h4]) mainPh_ld.1 (by rw [labT_eq_labY]; decide +kernel)
      (fun _ _ ⟨σ0, hJ, he⟩ => by rw [he, xS2_fsBase, htp _ _ hJ]; rfl) hun
  · exact blkW_ab hI bCmp (by show _ = _ + 1 + 3 + _ + _; rw [h4, ofNat_add'])
      (xCmp_ok (lo := -72) (hi := 0) _ _ _ _) hR hlo hhi mainPh_cmp (hnr (xCmp_noRet _ _ _)) (fun _ _ _ => rfl)
      (by rw [labT_eq_labY]; decide +kernel)
  · exact blkW_ab hI bFr (by show _ = _ + 1 + 3 + _ + _ + _ + _; rw [h4, ofNat_add', ofNat_add', ofNat_add'])
      (xFr_ok (lo := -72) (hi := 0) _ _ _ (by decide)) hR hlo hhi mainPh_fr (hnr (xFr_noRet _ _ _))
      (fun _ _ _ => rfl) (by rw [labT_eq_labY]; decide +kernel)

/-- **`scc_rt_main`'s call of `wc_rodata` keeps the write abort's phase**,
none moved. -/
theorem mainCallAb (hR : R.OK) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi) :
    BlkW (fun s _ => AbSt μ0 (Ab labT) s) (fun _ _ => False) hello1Exe hello1End R F
      (mN0 (_root_.Executable.labels hello1Exe).label R J) mB0 := by
  have hin := hello1_mainIn
  simp only [mainIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨h0, -⟩, -⟩, -⟩ := hin
  rw [hello1_labT]
  exact blkW_ab (hello1_instOk (rS := ⟨0, 0⟩)) (l := ".Lscc_rt_main.entry") (off := 0) (ra := 0) h0
    (ofNat_zero' _) mB0_ok80 hR hlo hhi mainPh_call (hnr (by decide)) (fun _ _ _ => rfl)
    (by rw [labT_eq_labY]; decide +kernel)

end Main

-- No axioms beyond Lean's.

/-- info: 'Spike.Test.X64Hello1W0.nodeW_ab_fsld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_ab_fsld

/-- info: 'Spike.Test.X64Hello1W0.mainProSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainProSt

/-- info: 'Spike.Test.X64Hello1W0.mainCallSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainCallSt

/-- info: 'Spike.Test.X64Hello1W0.mainProAb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainProAb

/-- info: 'Spike.Test.X64Hello1W0.mainCallAb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainCallAb

end Spike.Test.X64Hello1W0
