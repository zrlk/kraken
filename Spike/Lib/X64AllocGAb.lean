/-
**`scc_rt_alloc`'s states keep the write abort's phase at any instance**
(x86-64): `AllocW` (`Spike/Lib/X64Alloc.lean`) inside
`AbSt μ (WriteAb.Ab lab)`, none moved, for any executable with `InstOk`,
its cells holding the allocator's code (`allocIn`), passing the phase check
(`allocPhOk`) and with its targets off the write abort's pcs (`allocAbOk`):
`hello1.x`'s `allocAb` (`Spike/Test/X64Hello1AllocAb.lean`) with the
kernel's decisions over `labY`'s numeric tables replaced by `allocAbOk` at
the labels `lab`. The twin of `Spike/Lib/A64AllocGAb.lean`, name for name.

- `blkW_ab`, `blkW_abG`, `not_ab_after`, `nodeW_ab_si`, `nodeW_ab_fi`,
  `nodeW_ab_st`, `nodeW_ab_xadd`: `hello1.x`'s generic lemmas.
- `blkAbC_eq`, `allocAbOk_spec`: the check `allocAbOk`
  (`Spike/Lib/X64AllocAbOk.lean`) node by node; `not_ab_abort`: the heap
  abort's call target out of `Ab` at `%rdi ≠ 4`; `blkAb_ret`: the `ret`'s
  target, the caller's return address.
- `allocAb`.
-/
import Spike.Lib.X64AllocGSt
import Spike.Lib.X64AllocAbOk
import Spike.Lib.X64AbSt

namespace Spike.Lib.X64.AllocG

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region MemSide)
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

/-! ## The check -/

section Chk

open Spike.Lib.X64.Alloc
open Spike.Lib.X64.WriteAb (pcRet tailPcs failPcs dispTPcs g4Pcs stubPcs)

variable {lab : Label → Int64}

/-- **`blkAbC` is `blkAb`.** -/
theorem blkAbC_eq {p ra : Int64} {blk : List (Directive × Nat)} : blkAbC lab p ra blk = blkAb lab p ra blk := rfl

/-- **`allocAbOk`'s facts**, one per node (the heap abort's two, the
`ret`'s none). -/
theorem allocAbOk_spec (h : allocAbOk lab = true) :
    blkAb lab (lab fnL + Int64.ofNat 0) 0 bPro = true ∧ blkAb lab (lab entryL + Int64.ofNat 0) 0 bChk = true ∧
    blkAb lab (lab entryL + Int64.ofNat 16) 0 bJ1 = true ∧
    lab cntL + Int64.ofNat 0 + Int64.ofNat 7 ∉ abPcs lab ∧
    blkAb lab (lab cntL + Int64.ofNat 7) 0 bC1 = true ∧
    lab cntL + Int64.ofNat 19 + Int64.ofNat 5 ∉ abPcs lab ∧
    blkAb lab (lab cntL + Int64.ofNat 24) 0 bC2 = true ∧ blkAb lab (lab cntL + Int64.ofNat 59) 0 bJ2 = true ∧
    blkAb lab (lab slowL + Int64.ofNat 0) 0 bSlow = true ∧ blkAb lab (lab slowL + Int64.ofNat 16) 0 bJ3 = true ∧
    lab fullL + Int64.ofNat 0 + Int64.ofNat 7 ∉ abPcs lab ∧ lab "scc_rt_abort" ∉ abNoDispE lab ∧
    blkAb lab (lab okL + Int64.ofNat 0) 0 bO0 = true ∧ lab okL + Int64.ofNat 11 + Int64.ofNat 3 ∉ abPcs lab ∧
    blkAb lab (lab okL + Int64.ofNat 14) 0 bO1 = true ∧ lab okL + Int64.ofNat 29 + Int64.ofNat 3 ∉ abPcs lab ∧
    blkAb lab (lab okL + Int64.ofNat 32) 0 bO2 = true ∧ lab okL + Int64.ofNat 36 + Int64.ofNat 7 ∉ abPcs lab ∧
    blkAb lab (lab okL + Int64.ofNat 43) 0 bO3 = true ∧ lab okL + Int64.ofNat 58 + Int64.ofNat 3 ∉ abPcs lab ∧
    blkAb lab (lab okL + Int64.ofNat 61) 0 bO4 = true ∧ lab okL + Int64.ofNat 88 + Int64.ofNat 4 ∉ abPcs lab ∧
    blkAb lab (lab okL + Int64.ofNat 92) 0 bO5 = true ∧ lab okL + Int64.ofNat 107 + Int64.ofNat 3 ∉ abPcs lab ∧
    blkAb lab (lab okL + Int64.ofNat 110) 0 bO6 = true ∧ lab okL + Int64.ofNat 125 + Int64.ofNat 3 ∉ abPcs lab ∧
    blkAb lab (lab okL + Int64.ofNat 128) 0 bO7 = true ∧ lab okL + Int64.ofNat 140 + Int64.ofNat 3 ∉ abPcs lab ∧
    blkAb lab (lab okL + Int64.ofNat 143) 0 bO8 = true ∧ lab okL + Int64.ofNat 170 + Int64.ofNat 3 ∉ abPcs lab ∧
    blkAb lab (lab okL + Int64.ofNat 173) 0 bO9 = true := by
  simp only [allocAbOk, offAb, blkAbC_eq, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true,
    List.contains_iff_mem] at h
  simpa only [and_assoc] using h

/-- **The heap abort's call target is out of `Ab`** at `%rdi ≠ 4`, off
every other pc of it. -/
theorem not_ab_abort {s : State} (hpc : s.st.2 = lab "scc_rt_abort") (hx : s.st.1.regs.get64 .rdi ≠ 4#64)
    (hn : lab "scc_rt_abort" ∉ abNoDispE lab) : ¬ Ab lab s := by
  rintro (⟨h, -⟩ | ⟨h, -⟩ | h | ⟨-, h4⟩ | ⟨h, -⟩ | h | h)
  all_goals first
    | exact hx h4
    | (rw [hpc] at h; exact hn (by simp [abNoDispE, h]))

/-- **The `ret`'s targets off the write abort's pcs**: its return address. -/
theorem blkAb_ret {p ra : Int64} (h : ra ∉ abPcs lab) : blkAb lab p ra [(iRet.toDir, 1)] = true := by
  have hc : Spike.Lib.X64.classify iRet.toDir = some iRet := rfl
  simp only [blkAb, List.length_singleton, List.range_one, List.all_cons, List.all_nil, Bool.and_true,
    List.getElem?_cons_zero, hc]
  simpa [iRet, aiTgts] using h

end Chk

/-! ## `scc_rt_alloc`'s nodes -/

section Alloc

open Spike.Lib.X64.Alloc (Call AllocW N iRet fullL bFull bPro_ok bChk_ok bJ1_ok bC1_ok bC2_ok bJ2_ok bSlow_ok
  bJ3_ok bFull_ok bO0_ok bO1_ok bO2_ok bO3_ok bO4_ok bO5_ok bO6_ok bO7_ok bO8_ok bO9_ok)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region}
  {F : MachineData → Prop} {ms : MemSide isa} {q : Call}

set_option hygiene false in
/-- A block of `scc_rt_alloc` with no `ret`, its targets off the write
abort's pcs. -/
local macro "bab " hb:term:max ok:term:max hp:term:max ha:term:max : tactic =>
  `(tactic| exact blkW_ab hI (dead := fun _ => false) (ra := 0) $hb (by pc_tac) $ok hR (by omega) (by omega)
    $hp (fun _ _ _ k hk hr => (noRet_false (by decide) k hk hr).elim) (fun _ _ _ => rfl) $ha)

set_option hygiene false in
/-- A single instruction of `scc_rt_alloc` without an event. -/
local macro "bsi " hb:term:max hp:term:max ha:term:max : tactic =>
  `(tactic| exact nodeW_ab_si hI $hb rfl (by pc_tac) (phOne_spec $hp).1 $ha)

set_option hygiene false in
/-- An instruction of `scc_rt_alloc` with undefined flags. -/
local macro "bfi " hb:term:max hp:term:max ha:term:max : tactic =>
  `(tactic| exact nodeW_ab_fi hI $hb rfl (by pc_tac) (phOne_spec $hp).1 $ha)

/-- **`scc_rt_alloc`'s states keep the write abort's phase**, none moved,
its code passing the phase check (`hph`) and its targets off the write
abort's pcs (`hab`), for a call `q` whose return address is off them
(`hraAb`) and in the entry's phase (`hra`), in a region of the allocator's
frame, the counter and every header the code may store unmapped in private
memory (`hmem`, `hq`). -/
theorem allocAb (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.X64.Alloc.allocIn cells = true) (hph : allocPhOk okPc ph lab = true)
    (hab : allocAbOk lab = true)
    (hR : R.OK) (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hq : ∀ m, F m → q.OK ms lab)
    (hra : ph (Int64.ofBitVec q.ra).toBitVec.toNat = ph (lab Spike.Lib.X64.Alloc.fnL).toBitVec.toNat)
    (hraAb : Int64.ofBitVec q.ra ∉ abPcs lab)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    AllocW ms q (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F := by
  obtain ⟨-, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28, h29, h30⟩ := allocIn_spec hA
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21,
    p22, p23, p24, p25, p26, p27, p28, p29, p30, p31⟩ := allocPhOk_spec hph
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a10', a11, a12, a13, a14, a15, a16, a17, a18, a19, a20,
    a21, a22, a23, a24, a25, a26, a27, a28, a29⟩ := allocAbOk_spec hab
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hI.labOk]
  · bab h0 bPro_ok p0 a0
  · bab h1 bChk_ok p1 a1
  · bab h2 bJ1_ok p2 a2
  · bsi h3 p3 a3
  · bab h4 bC1_ok p4 a4
  · refine nodeW_ab_xadd hI (b := .rcx) (k := 0) (r := .rax) h5 rfl rfl (phOne_spec p5).1 a5
      fun σ c m hJ hF => ?_
    obtain ⟨-, hcx, -⟩ := hJ
    rw [ctr_addr (hq m hF) hcx]
    exact hmem _ (.inl rfl) m hF
  · bab h6 bC2_ok p6 a6
  · bab h7 bJ2_ok p7 a7
  · bab h8 bSlow_ok p8 a8
  · bab h9 bJ3_ok p9 a9
  · refine blkW_abG hI (l := fullL) (off := 0) (dead := fun _ => false) (ra := 0) h10 (by pc_tac) bFull_ok hR
      (by omega) (by omega) p10 (fun _ _ _ k hk hr => (noRet_false (by decide) k hk hr).elim)
      (fun _ _ _ => rfl) ?_
    intro σ c hJ k hk a ha s' _ _ hpc' hA'
    match k, hk with
    | 0, _ =>
      obtain ⟨a', ha', -, hterm⟩ := Spike.Lib.X64.okBlk_get lab (am := ⟨0, Spike.Lib.X64.Alloc.oI, σ⟩) bFull_ok
        (k := 0) (by decide)
      rw [ha] at ha'
      cases ha'
      rw [Spike.Lib.X64.AI.tgt_of_not_term (hterm (by decide))] at hpc'
      refine not_ab_of_pc ?_
      rw [hpc']
      dsimp only [N]
      exact a10
    | 1, _ =>
      -- the heap abort's call: into the dispatcher with `%rdi = 2`, not the write abort's `4`
      have hc1 : Spike.Lib.X64.classify (bFull[1]'(by decide)).1 = some (.call "scc_rt_abort") := rfl
      rw [hc1] at ha
      cases ha
      refine not_ab_abort (by rw [hpc', Spike.Lib.X64.BlockSpec.AI.tgt_call']) ?_ a10'
      intro h4
      have hx := hA'.regs
      rw [Spike.Lib.X64.BlockSpec.AI.step_call'] at hx
      have h2 := Spike.Lib.X64.Alloc.bFull_run lab (N lab ms q .full).pc σ
      have h3 := Spike.Lib.X64.arun_take_succ lab (blk := bFull) (k := 1) (by decide)
        ⟨(N lab ms q .full).pc, (N lab ms q .full).o, σ⟩
      rw [show bFull.take (1 + 1) = bFull from rfl] at h3
      have hrdi : (arun lab bFull ⟨(N lab ms q .full).pc, (N lab ms q .full).o, σ⟩).σ.regs.get64 .rdi = 2#64 := by
        rw [show (N lab ms q .full).o = Spike.Lib.X64.Alloc.oI from rfl, h2]
        simp [Reg64s.set64, Reg64s.get64]
      rw [h3] at hrdi
      generalize hb1 : bFull[1] = d1 at hrdi hc1
      obtain ⟨d1, z1⟩ := d1
      simp only [Spike.Lib.X64.dstep] at hrdi hc1
      simp only [hc1, Spike.Lib.X64.BlockSpec.AI.step_call'] at hrdi
      rw [hx] at h4
      simp only [Reg64s.set64, Reg64s.get64] at h4 hrdi
      rw [hrdi] at h4
      exact absurd h4 (by decide)
  · bab h11 bO0_ok p11 a11
  · bfi h12 p12 a12
  · bab h13 bO1_ok p13 a13
  · bfi h14 p14 a14
  · bab h15 bO2_ok p15 a15
  · bsi h16 p16 a16
  · bab h17 bO3_ok p17 a17
  · bfi h18 p18 a18
  · bab h19 bO4_ok p19 a19
  · bfi h20 p20 a20
  · bab h21 bO5_ok p21 a21
  · bfi h22 p22 a22
  · bab h23 bO6_ok p23 a23
  · bfi h24 p24 a24
  · bab h25 bO7_ok p25 a25
  · bfi h26 p26 a26
  · bab h27 bO8_ok p27 a27
  · refine nodeW_ab_st hI (b := .rcx) (k := 0) (r := .rax) h28 rfl rfl (phOne_spec p28).1 a28
      fun σ c m hJ hF => ?_
    obtain ⟨o, ⟨-, hle, -, hn28, -⟩, -, -, hcx⟩ := hJ
    exact hmem _ (.inr ⟨o.toNat, hle, hdr_addr (hq m hF) hle hn28 hcx⟩) m hF
  · bab h29 bO9_ok p29 a29
  · refine Spike.Lib.LowerX64.BlkW.nodeW (blkW_ab hI (blk := [(iRet.toDir, 1)]) (lo := -160) (hi := 8)
      (dead := fun _ => false) (ra := Int64.ofBitVec q.ra) h30 rfl
      (show Spike.Lib.X64.okBlk (-160) 8 Spike.Lib.X64.Alloc.oE [(iRet.toDir, 1)] = true by decide) hR
      (by omega) (by omega) (blkPh_ret p30 (by rw [hra, p31]))
      (hret_of_run (lo := -160) (hi := 8) (by dsimp only [N]; decide) fun σ c hJ => ?_) (fun _ _ _ => rfl)
      (blkAb_ret hraAb)) (List.cons_ne_nil _ _)
    obtain ⟨o, -, -, -, -, -, h0⟩ := hJ
    have hc : Spike.Lib.X64.classify iRet.toDir = some iRet := rfl
    simp only [arun, List.foldl, Spike.Lib.X64.dstep, hc]
    simp only [iRet, Spike.Lib.X64.AI.tgt, N, Spike.Lib.X64.Alloc.oE]
    rw [h0]

end Alloc

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64.AllocG.allocAbOk_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocAbOk_spec

/-- info: 'Spike.Lib.X64.AllocG.allocAb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocAb

end Spike.Lib.X64.AllocG
