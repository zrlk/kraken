/-
**`scc_rt_alloc`'s states keep the write abort's phase at `hello1.x`'s
instance** (x86-64): the allocator's node obligations (`AllocW`,
`Spike/Lib/X64Alloc.lean`) inside `AbSt μ0 (WriteAb.Ab labT)`
(`Spike/Lib/X64AbSt.lean`), none moved. The twin of
`Spike/Test/A64Hello1AllocAb.lean`.

- `blkW_ab`: a covered block whose targets are off the write abort's pcs
  (`blkAb`), its pcs off the sites (`blkPh`); `blkW_abG` with `blkW_abSt`'s
  target obligation instead of the check.
- `nodeW_ab_si`, `nodeW_ab_fi`, `nodeW_ab_st`, `nodeW_ab_xadd`: a single
  instruction without an event, one with undefined flags, a store and a
  `lock xadd` of a word unmapped in private memory, at an off-site pc whose
  next pc is off the write abort's pcs (AArch64 has no `nodeW_ab_fi`, and its
  RMW is `nodeW_ab_ldop`).
- `labY`, `labT_eq_labY`: `labX` extended by the write abort's labels off
  its tables (`abTabX`), so the kernel reduces `abPcs`.
- `allocAb_ret`: the `ret` to `wc_rodata`'s `.x13`.
- `allocAb`: every node of `scc_rt_alloc`; its heap abort's call
  (`movq $2, %rdi; call scc_rt_abort`) enters the dispatcher with `%rdi = 2`,
  not the write abort's `4`.
-/
import Spike.Test.X64Hello1AllocW
import Spike.Lib.X64AbSt

namespace Spike.Test.X64Hello1W0

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (MemSide Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer
open Spike.Lib.X64 (NodeW BlkW ND SI FI bAddr xaddDir stDir mB eaddr_mB cellOff arun)
open Spike.Lib.X64.Rt (InstOk cellOf codeOf)
open Scc.Cert.Rt.X64 (blockAtB)
open Kraken.Promising.Lower.X64 (CellAt after exec_store_agrees exec_xaddG_agrees eaddr)
open Spike.Lib.X64ConsumerA (AbSt AbSt.ofLeaves blkW_abSt blkAb blkAb_sound)
open Spike.Lib.X64.WriteAb (Ab abPcs not_ab_of_pc)

/-! ## Generic nodes off the write abort's pcs -/

section Gen

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {R : Region} {F : MachineData → Prop}

/-- **A covered block keeps the write abort's phase**: its pcs off the
sites (`hph`, as `blkW_postO`'s), every target of every instruction off
the write abort's pcs (`hab`). -/
theorem blkW_ab {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {blk : List (Directive × Nat)} {lo hi : Int} {dead : Nat → Bool} {ra : Int64} {l : Label} {off : Nat}
    (hb : blockAtB cells l off blk = true) (he : lab l + Int64.ofNat off = n.pc)
    (hok : Spike.Lib.X64.okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hph : blkPh okPc ph dead lab (lab l + Int64.ofNat off) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), Spike.Lib.X64.classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp)
        = ra)
    (hdead : ∀ σ c, n.J σ c → dead (arun lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hab : blkAb lab (lab l + Int64.ofNat off) ra blk = true) :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  rw [he] at hph hab
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → Spike.Lib.X64.CodeAt s n.pc blk := fun s hs hn =>
    he ▸ codeOf hI hb hs hn
  rw [← hI.labOk] at hph hret hdead hab ⊢
  obtain ⟨hpc, -, -⟩ := blkPh_sound (μ := μ) (endPc := endPc) hI.same hI.off hok hph hret hdead
  exact blkW_abSt hcode hok hR hlo hhi (fun k hk s h1 h2 h3 => (hpc k hk s h1 h2 h3).1) (blkAb_sound hab hret)

/-- **A covered block keeps the write abort's phase**, as `blkW_ab`, every
instruction's next state, at the abstract run's next pc and registers, out
of `Ab` (`htgt`, `blkW_abSt`'s at the labels `lab`). -/
theorem blkW_abG {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {blk : List (Directive × Nat)} {lo hi : Int} {dead : Nat → Bool} {ra : Int64} {l : Label} {off : Nat}
    (hb : blockAtB cells l off blk = true) (he : lab l + Int64.ofNat off = n.pc)
    (hok : Spike.Lib.X64.okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hph : blkPh okPc ph dead lab (lab l + Int64.ofNat off) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), Spike.Lib.X64.classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp)
        = ra)
    (hdead : ∀ σ c, n.J σ c → dead (arun lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (htgt : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), ∀ a, Spike.Lib.X64.classify blk[k].1 = some a →
      ∀ s' : State, s'.exe = exe → s'.endPc = endPc →
      s'.st.2 = a.tgt lab (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so
        (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2) (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      Spike.Lib.X64.Abs R (a.so (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so) s'.st.1
        (a.step (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
          (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ) →
      ¬ Ab lab s') :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  rw [he] at hph
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → Spike.Lib.X64.CodeAt s n.pc blk := fun s hs hn =>
    he ▸ codeOf hI hb hs hn
  rw [← hI.labOk] at hph hret hdead htgt ⊢
  obtain ⟨hpc, -, -⟩ := blkPh_sound (μ := μ) (endPc := endPc) hI.same hI.off hok hph hret hdead
  exact blkW_abSt hcode hok hR hlo hhi (fun k hk s h1 h2 h3 => (hpc k hk s h1 h2 h3).1) htgt

omit [Kraken.Executable.ValidLayout exe] in
/-- The next state's pc off the write abort's pcs. -/
theorem not_ab_after {s : State} {p : Int64} {z : Nat} {m : MachineData} (hpc : s.st.2 = p)
    (hnx : p + Int64.ofNat z ∉ abPcs lab) : ¬ Ab lab (after s z m) :=
  not_ab_of_pc (by show s.st.2 + Int64.ofNat z ∉ _; rw [hpc]; exact hnx)

/-- **A node at a single instruction without an event** (`SI`) keeps the
write abort's phase: its pc off the sites, its next pc off the write
abort's pcs. -/
theorem nodeW_ab_si {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {si : SI} {z : Nat} {l : Label} {off : Nat} {p : Int64} (hb : blockAtB cells l off [(si.toDir, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hnx : p + Int64.ofNat z ∉ abPcs lab) :
    NodeW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, -, hpc, -⟩
  rw [hp] at hpc
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc := cellOf hI hb he hs hn hpc
  refine ⟨AbSt.ofLeaves hP.noTake (atSyscall_false_of_cellAt hc ?_) fun t ht => ?_, fun _ h => h⟩
  · cases si <;> intro w w' h <;> cases h
  · rw [Spike.Lib.X64.exec_si hc] at ht
    cases ht
    exact not_ab_after hpc hnx

/-- **A node at an instruction with undefined flags** (`FI`) keeps the
write abort's phase, as `nodeW_ab_si`: every leaf is past it. -/
theorem nodeW_ab_fi {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {fi : FI} {z : Nat} {l : Label} {off : Nat} {p : Int64} (hb : blockAtB cells l off [(fi.toDir, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hnx : p + Int64.ofNat z ∉ abPcs lab) :
    NodeW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, -, hpc, -⟩
  rw [hp] at hpc
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc := cellOf hI hb he hs hn hpc
  obtain ⟨t0, hex, hst⟩ := Spike.Lib.X64.exec_fi hc
  refine ⟨AbSt.ofLeaves hP.noTake (atSyscall_false_of_cellAt hc ?_) fun t ht => ?_, fun _ h => h⟩
  · cases fi <;> intro w w' h <;> cases h
  · rw [hex] at ht
    cases ht
    exact (silent_facts (p := fun _ _ => True) (G := fun _ _ => True) (G' := fun _ _ => True)
      (fun _ ⟨_, h⟩ => h ▸ not_ab_after hpc hnx) hst).2.1

/-- **A node at a store** `movq %r, k(%b)` of a word unmapped in private
memory (`ha`) keeps the write abort's phase, as `nodeW_ab_si`. -/
theorem nodeW_ab_st {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND} {b r : Reg64}
    {k : Int64} {z : Nat} {l : Label} {off : Nat} {p : Int64} (hb : blockAtB cells l off [(stDir b k r, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hnx : p + Int64.ofNat z ∉ abPcs lab)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b k) 8 = none) :
    NodeW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  rw [hp] at hpc
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc := cellOf hI hb he hs hn hpc
  have ha' : eaddr s z (mB b k) = bAddr σ.regs b k := (eaddr_mB s z b k).trans (by rw [hA.regs]; rfl)
  have hex := exec_store_agrees hc ha' (ha σ c s.st.1 hJ hD) (Spike.Lib.X64.agrees_of_decls hdc _ _)
  refine ⟨AbSt.ofLeaves hP.noTake (atSyscall_false_of_cellAt hc (by intro w w' h; cases h)) fun t ht => ?_,
    fun _ h => h⟩
  rw [hex] at ht
  cases ht
  exact ⟨trivial, fun _ _ => not_ab_after hpc hnx⟩

/-- **A node at a `lock xaddq %r, k(%b)`** of a word unmapped in private
memory (`ha`) keeps the write abort's phase, as `nodeW_ab_si`. -/
theorem nodeW_ab_xadd {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND} {b r : Reg64}
    {k : Int64} {z : Nat} {l : Label} {off : Nat} {p : Int64} (hb : blockAtB cells l off [(xaddDir b k r, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hnx : p + Int64.ofNat z ∉ abPcs lab)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b k) 8 = none) :
    NodeW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  rw [hp] at hpc
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc := cellOf hI hb he hs hn hpc
  have ha' : eaddr s z (mB b k) = bAddr σ.regs b k := (eaddr_mB s z b k).trans (by rw [hA.regs]; rfl)
  have hex := exec_xaddG_agrees (w := .W64) hc ha' (ha σ c s.st.1 hJ hD) (Spike.Lib.X64.agrees_of_decls hdc _ _)
  refine ⟨AbSt.ofLeaves hP.noTake (atSyscall_false_of_cellAt hc (by intro w w' h; cases h)) fun t ht => ?_,
    fun _ h => h⟩
  rw [hex] at ht
  cases ht
  exact fun _ _ => ⟨fun _ _ => trivial, not_ab_after hpc hnx⟩

end Gen

/-! ## The write abort's labels -/

section Lab

open Spike.Lib.X64.Flow.Hello1.Inst
open Spike.Lib.X64.Flow.Hello1.Mem (hello1Exe hello1_lays)
open Spike.Test.X64Hello1RtW (labX labT_eq_labX tabChk)

/-- The labels of the write abort's pcs off `labX`'s tables: the
dispatcher's tests, its jump to the write stub and the stub's. -/
def abTabX : List (Label × Nat) :=
  [(".Lscc_rt_abort.entry", 4198402), (".Lscc_rt_abort.next1", 4198426),
   (".Lscc_rt_abort.next3", 4198453), (".Lscc_rt_abort.next5", 4198480),
   (".Lscc_rt_abort.is6", 4198498), ("scc_rt_abort_write", 4198740),
   (".Lscc_rt_abort_write.entry", 4198748), ("scc_rt_abort_write_exit", 4198800)]

theorem abTabX_ok : abTabX.all tabChk = true := by decide +kernel

/-- `labX` extended by `abTabX`, so the kernel reduces the write abort's
pcs (`abPcs`). -/
noncomputable def labY (l : Label) : Int64 :=
  match abTabX.lookup l with
  | some n => Int64.ofNat n
  | none => labX l

/-- `labT` is `labY`: `abTabX`'s entries are the loaded thread's labels. -/
theorem labT_eq_labY : labT = labY := by
  funext l
  unfold labY
  cases hn : abTabX.lookup l with
  | some n =>
    have h := List.all_eq_true.mp abTabX_ok _ (Spike.Lib.X64.Flow.Ret0.Inst.lookup_mem hn)
    simp only [tabChk, Bool.and_eq_true, beq_iff_eq] at h
    show _ = Int64.ofNat n
    rw [← h.2, ← hello1_labT]
    exact Spike.Lib.X64.OwnLimRt.label_labIn hello1_lays rfl h.1
  | none => exact congrFun labT_eq_labX l

end Lab

/-! ## `scc_rt_alloc`'s nodes -/

section Alloc

open Spike.Lib.X64.Alloc (Call AllocW N iCtr iHeap iRmw iHdr iRet fnL entryL cntL slowL fullL okL bPro bChk bJ1
  bC1 bC2 bJ2 bSlow bJ3 bFull bO0 bO1 bO2 bO3 bO4 bO5 bO6 bO7 bO8 bO9 bPro_ok bChk_ok bJ1_ok bC1_ok bC2_ok bJ2_ok
  bSlow_ok bJ3_ok bFull_ok bO0_ok bO1_ok bO2_ok bO3_ok bO4_ok bO5_ok bO6_ok bO7_ok bO8_ok bO9_ok)
open Spike.Test.X64Hello1RtW (hello1_instOk labT_eq_labX)
open Spike.Lib.X64.Flow.Hello1.Mem (hello1Exe hello1End)
open Spike.Lib.X64.Flow.Hello1.Inst

variable {R : Region} {F : MachineData → Prop} {ms : MemSide isa} {q : Call}

set_option hygiene false in
/-- A block of `scc_rt_alloc` with no `ret`, its targets off the write
abort's pcs. -/
local macro "bab " l:term:max k:term:max ok:term:max : tactic =>
  `(tactic| exact blkW_ab (hello1_instOk (rS := ⟨0, 0⟩)) (l := $l) (off := $k) (dead := fun _ => false) (ra := 0)
    (by decide +kernel) (by first | rfl | exact Spike.Lib.X64.Flow.ofNat_zero' _) $ok hR (by omega) (by omega)
    (by rw [labT_eq_labX]; decide +kernel) (fun _ _ _ k hk hr => (noRet_false (by decide) k hk hr).elim)
    (fun _ _ _ => rfl) (by rw [labT_eq_labY]; decide +kernel))

set_option hygiene false in
/-- A single instruction of `scc_rt_alloc` without an event. -/
local macro "bsi " si:term:max z:term:max l:term:max k:term:max : tactic =>
  `(tactic| exact nodeW_ab_si (hello1_instOk (rS := ⟨0, 0⟩)) (si := $si) (z := $z) (l := $l) (off := $k)
    (p := labT $l + Int64.ofNat $k) (by decide +kernel) rfl
    (by first | rfl | exact (Spike.Lib.X64.Flow.ofNat_zero' _).symm) (by decide +kernel)
    (by rw [labT_eq_labY]; decide +kernel))

set_option hygiene false in
/-- An instruction of `scc_rt_alloc` with undefined flags. -/
local macro "bfi " fi:term:max z:term:max l:term:max k:term:max : tactic =>
  `(tactic| exact nodeW_ab_fi (hello1_instOk (rS := ⟨0, 0⟩)) (fi := $fi) (z := $z) (l := $l) (off := $k)
    (p := labT $l + Int64.ofNat $k) (by decide +kernel) rfl rfl (by decide +kernel)
    (by rw [labT_eq_labY]; decide +kernel))

/-- `scc_rt_alloc`'s `ret` keeps the write abort's phase: it returns to
`wc_rodata`'s `.x13` (`hra`). -/
theorem allocAb_ret (hR : R.OK) (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hra : q.ra = (labT ".Lwc_rodata.x13").toBitVec) :
    NodeW (fun s _ => AbSt μ0 (Ab labT) s) (fun _ _ => False) hello1Exe hello1End R F
      (Spike.Lib.X64.Alloc.N labT ms q .ret) := by
  have hab : blkAb labT (labT okL + Int64.ofNat 226) (labT ".Lwc_rodata.x13") [(iRet.toDir, 1)] = true := by
    rw [labT_eq_labY]; decide +kernel
  have hph : blkPh okPc ph (fun _ => false) labT (labT okL + Int64.ofNat 226) (labT ".Lwc_rodata.x13")
      [(iRet.toDir, 1)] = true := by
    rw [labT_eq_labX]; decide +kernel
  have hok : Spike.Lib.X64.okBlk (-160) 8 (Spike.Lib.X64.Alloc.N labT ms q .ret).o [(iRet.toDir, 1)] = true :=
    show Spike.Lib.X64.okBlk (-160) 8 Spike.Lib.X64.Alloc.oE [(iRet.toDir, 1)] = true by decide
  have hret := hret_of_run (lab := labT) (ra := labT ".Lwc_rodata.x13") hok fun σ c hJ => by
    obtain ⟨o, -, -, -, -, -, h0⟩ := hJ
    show Int64.ofBitVec (σ.slot 0) = _
    rw [h0, hra]
    exact Int64.ofBitVec_toBitVec _
  exact BlkW.nodeW (blkW_ab (hello1_instOk (rS := ⟨0, 0⟩)) (l := okL) (off := 226) (dead := fun _ => false)
    (by decide +kernel) rfl hok hR (by omega) (by omega) hph hret (fun _ _ _ => rfl) hab) (List.cons_ne_nil _ _)

/-- **`scc_rt_alloc`'s states keep the write abort's phase**, none moved,
for a call `q` returning to `wc_rodata`'s `.x13` (`hra`), in a region of
the allocator's frame, the counter and every header the code may store
unmapped in private memory (`hmem`, `hq`). -/
theorem allocAb (hR : R.OK) (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hq : ∀ m, F m → q.OK ms (_root_.Executable.labels hello1Exe).label)
    (hra : q.ra = (labT ".Lwc_rodata.x13").toBitVec)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    AllocW ms q (fun s _ => AbSt μ0 (Ab labT) s) (fun _ _ => False) hello1Exe hello1End R F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hello1_labT]
  · bab fnL 0 bPro_ok
  · bab entryL 0 bChk_ok
  · bab entryL 16 bJ1_ok
  · bsi iCtr 7 cntL 0
  · bab cntL 7 bC1_ok
  · refine nodeW_ab_xadd (hello1_instOk (rS := ⟨0, 0⟩)) (b := .rcx) (k := 0) (r := .rax) (z := 5)
      (l := cntL) (off := 19) (p := labT cntL + Int64.ofNat 19) (by decide +kernel) rfl rfl (by decide +kernel)
      (by rw [labT_eq_labY]; decide +kernel) fun σ c m hJ hF => ?_
    obtain ⟨-, hcx, -⟩ := hJ
    have hq' := hq m hF
    rw [hello1_labT] at hq'
    have hb : bAddr σ.regs .rcx 0 = BitVec.ofNat 64 ms.ctr := by
      rw [← hq'.ctr, ← hcx]; simp [bAddr, Reg64s.get64]
    rw [hb]
    exact hmem _ (.inl rfl) m hF
  · bab cntL 24 bC2_ok
  · bab cntL 59 bJ2_ok
  · bab slowL 0 bSlow_ok
  · bab slowL 16 bJ3_ok
  · refine blkW_abG (hello1_instOk (rS := ⟨0, 0⟩)) (l := fullL) (off := 0) (dead := fun _ => false) (ra := 0)
      (by decide +kernel) (Spike.Lib.X64.Flow.ofNat_zero' _) bFull_ok hR (by omega) (by omega)
      (by rw [labT_eq_labX]; decide +kernel) (fun _ _ _ k hk hr => (noRet_false (by decide) k hk hr).elim)
      (fun _ _ _ => rfl) ?_
    intro σ c hJ k hk a ha s' _ _ hpc' hA'
    match k, hk with
    | 0, _ =>
      obtain ⟨a', ha', -, hterm⟩ := Spike.Lib.X64.okBlk_get labT (am := ⟨0, Spike.Lib.X64.Alloc.oI, σ⟩) bFull_ok
        (k := 0) (by decide)
      rw [ha] at ha'
      cases ha'
      rw [Spike.Lib.X64.AI.tgt_of_not_term (hterm (by decide))] at hpc'
      refine not_ab_of_pc ?_
      rw [hpc']
      dsimp only [Spike.Lib.X64.Alloc.N]
      rw [labT_eq_labY]
      change labY fullL + Int64.ofNat (cellOff bFull 0) + Int64.ofNat (bFull[0]'(by decide)).2 ∉ abPcs labY
      decide +kernel
    | 1, _ =>
      -- the heap abort's call: into the dispatcher with `%rdi = 2`, not the write abort's `4`
      have hc1 : Spike.Lib.X64.classify (bFull[1]'(by decide)).1 = some (.call "scc_rt_abort") := rfl
      rw [hc1] at ha
      cases ha
      have hx := hA'.regs
      rw [Spike.Lib.X64.BlockSpec.AI.step_call'] at hx
      have h2 := Spike.Lib.X64.Alloc.bFull_run labT (Spike.Lib.X64.Alloc.N labT ms q .full).pc σ
      have h3 := Spike.Lib.X64.arun_take_succ labT (blk := bFull) (k := 1) (by decide)
        ⟨(Spike.Lib.X64.Alloc.N labT ms q .full).pc, (Spike.Lib.X64.Alloc.N labT ms q .full).o, σ⟩
      rw [show bFull.take (1 + 1) = bFull from rfl] at h3
      have hrdi : (arun labT bFull ⟨(Spike.Lib.X64.Alloc.N labT ms q .full).pc,
          (Spike.Lib.X64.Alloc.N labT ms q .full).o, σ⟩).σ.regs.get64 .rdi = 2#64 := by
        rw [show (Spike.Lib.X64.Alloc.N labT ms q .full).o = Spike.Lib.X64.Alloc.oI from rfl, h2]
        simp [Reg64s.set64, Reg64s.get64]
      rw [h3] at hrdi
      generalize hb1 : bFull[1] = d1 at hrdi hc1
      obtain ⟨d1, z1⟩ := d1
      simp only [Spike.Lib.X64.dstep] at hrdi hc1
      simp only [hc1, Spike.Lib.X64.BlockSpec.AI.step_call'] at hrdi
      intro hab
      rcases hab with ⟨h1, -⟩ | ⟨h1, -⟩ | h1 | ⟨-, h4⟩ | ⟨h1, -⟩ | h1 | h1
      all_goals first
        | (rw [hpc'] at h1; revert h1; rw [Spike.Lib.X64.BlockSpec.AI.tgt_call', labT_eq_labY]; decide +kernel)
        | skip
      rw [hx] at h4
      simp only [Reg64s.set64, Reg64s.get64] at h4 hrdi
      rw [hrdi] at h4
      exact absurd h4 (by decide)
  · bab okL 0 bO0_ok
  · bfi (.shr_cl .rax) 3 okL 11
  · bab okL 14 bO1_ok
  · bfi (.and_rr .rax .rcx) 3 okL 29
  · bab okL 32 bO2_ok
  · bsi iHeap 7 okL 36
  · bab okL 43 bO3_ok
  · bfi (.shl_cl .rax) 3 okL 58
  · bab okL 61 bO4_ok
  · bfi (.imul_rr .rax .rcx) 4 okL 88
  · bab okL 92 bO5_ok
  · bfi (.shl_cl .rax) 3 okL 107
  · bab okL 110 bO6_ok
  · bfi (.shl_cl .rax) 3 okL 125
  · bab okL 128 bO7_ok
  · bfi (.or_rr .rax .rcx) 3 okL 140
  · bab okL 143 bO8_ok
  · refine nodeW_ab_st (hello1_instOk (rS := ⟨0, 0⟩)) (b := .rcx) (k := 0) (r := .rax) (z := 3)
      (l := okL) (off := 170) (p := labT okL + Int64.ofNat 170) (by decide +kernel) rfl rfl (by decide +kernel)
      (by rw [labT_eq_labY]; decide +kernel) fun σ c m hJ hF => ?_
    obtain ⟨o, ⟨-, hle, -, hn28, -⟩, -, -, hcx⟩ := hJ
    have hq' := hq m hF
    rw [hello1_labT] at hq'
    have hk := Spike.Lib.X64.Alloc.Call.k_toNat hq'.n_lt
    have hcl := hq'.cells
    have hra' : bAddr σ.regs .rcx 0 =
        Spike.Lib.X64.Alloc.H labT + o <<< 4 + (q.k * Spike.Lib.X64.Alloc.mOf q.h) <<< 3 := by
      rw [← hcx]; simp [bAddr, Reg64s.get64]
    have hAeq : (bAddr σ.regs .rcx 0).toNat = q.hdrAt ms o.toNat := by
      rw [hra', Spike.Lib.X64.Alloc.base_toNat (by omega) (by omega) (Spike.Lib.X64.Alloc.mOf_lt _)
        (by rw [hq'.heap]; exact hq'.room), hq'.heap, hk]
      rfl
    exact hmem _ (.inr ⟨o.toNat, hle, hAeq⟩) m hF
  · bab okL 173 bO9_ok
  · exact allocAb_ret hR hlo hhi hra

end Alloc

-- No axioms beyond Lean's.

/--
info: 'Spike.Test.X64Hello1W0.blkW_ab' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms blkW_ab

/--
info: 'Spike.Test.X64Hello1W0.blkW_abG' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms blkW_abG

/--
info: 'Spike.Test.X64Hello1W0.nodeW_ab_si' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nodeW_ab_si

/--
info: 'Spike.Test.X64Hello1W0.nodeW_ab_fi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nodeW_ab_fi

/--
info: 'Spike.Test.X64Hello1W0.nodeW_ab_st' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nodeW_ab_st

/--
info: 'Spike.Test.X64Hello1W0.nodeW_ab_xadd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nodeW_ab_xadd

/--
info: 'Spike.Test.X64Hello1W0.labT_eq_labY' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms labT_eq_labY

/--
info: 'Spike.Test.X64Hello1W0.allocAb_ret' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms allocAb_ret

/--
info: 'Spike.Test.X64Hello1W0.allocAb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms allocAb

end Spike.Test.X64Hello1W0
