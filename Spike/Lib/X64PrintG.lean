/-
**`scc_rt_print`'s states off the sites, writing nothing and carrying the
state's facts at any instance** (x86-64): `PrintAW`
(`Spike/Lib/X64PrintA.lean`, the byte-by-byte specification) inside
`okPc`, no write off a system call, and the state's facts (`SFactsSt`), for
any executable with `InstOk`, its cells holding the routine's code
(`printIn`), passing the phase check `printPhOk`
(`Spike/Lib/X64PrintPh.lean`): the twin of `Spike/Lib/A64PrintG.lean`, name
for name, and of `Spike/Lib/X64AllocGSt.lean`'s `allocPc`, `allocSt` for
the output routine. None of these reads the source control: they are the
place-independent parts of `PrintW` at `W2`.

- `printIn_spec`, `printPhOk_spec`: the code's and the check's facts, one per
  block.
- `blkPh_x13`: the epilogue's phase check with its `ret` to a return
  address in the epilogue's phase.
- `blkW_noSysI`: a covered block of the cells is off a system call.
- `printPc`: the states off the marks' sites.
- `printNoWr`: the states write nothing and are off a system call.
- `printSt`: the states carry the state's facts (`SFactsSt`).
-/
import Spike.Lib.X64AllocGSt
import Spike.Lib.X64PrintA
import Spike.Lib.X64PrintPh
import Spike.Lib.LowerX64.W2Body

namespace Spike.Lib.X64.PrintG

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer
open Spike.Lib.X64 (NodeW BlkW ND AS cellOff okBlk)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.X64.Flow.Ret0.Inst (cfacts_c0)
open Spike.Lib.X64.Rt (InstOk codeOf)
open Scc.Cert.Rt.X64 (blockAtB labelGapB)
open Spike.Lib.X64ConsumerA (SFactsSt WrAt)
open Spike.Lib.X64.StubW (phOne)
open Spike.Lib.X64.AllocG (aBlk okPc_of_blkPh phOne_spec blkW_pc blkW_okPc dumN BlkW.st)
open Spike.Lib.X64.Print (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 oI oE
  x0_ok x1_ok x2_ok x3_ok x4_ok x5_ok x6_ok x7_ok x8_ok x9_ok x10_ok x11_ok x12_ok x13_ok x13_run)
open Spike.Lib.X64.PrintA (PrintAW N)

/-! ## The code's and the check's facts -/

section Spec

variable {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}

/-- **`printIn`'s facts**, one per block. -/
theorem printIn_spec {cells : List (Directive × Nat)} (h : Scc.Cert.Rt.X64.Print.printIn cells = true) :
    blockAtB cells "scc_rt_print" 0 x0 = true ∧
    blockAtB cells ".Lscc_rt_print.entry" 0 x1 = true ∧
    blockAtB cells ".Lscc_rt_print.loop" 0 x2 = true ∧
    blockAtB cells ".Lscc_rt_print.loop" 20 x3 = true ∧
    blockAtB cells ".Lscc_rt_print.write" 0 x4 = true ∧
    blockAtB cells ".Lscc_rt_print.write" 20 [(.instr (.regular .W64 .W64 .syscall), 2)] = true ∧
    blockAtB cells ".Lscc_rt_print.write" 22 x5 = true ∧
    blockAtB cells ".Lscc_rt_print.write" 42 x6 = true ∧
    blockAtB cells ".Lscc_rt_print.chk2" 0 x7 = true ∧
    blockAtB cells ".Lscc_rt_print.chk2" 16 x8 = true ∧
    blockAtB cells ".Lscc_rt_print.chk3" 0 x9 = true ∧
    blockAtB cells ".Lscc_rt_print.chk3" 16 x10 = true ∧
    blockAtB cells ".Lscc_rt_print.adv" 0 x11 = true ∧
    blockAtB cells ".Lscc_rt_print.fail" 0 x12 = true ∧
    blockAtB cells ".Lscc_rt_print.done" 0 x13 = true ∧
    labelGapB cells "scc_rt_print" ".Lscc_rt_print.entry" 16 = true := by
  simpa only [Scc.Cert.Rt.X64.Print.printIn, Bool.and_eq_true, and_assoc] using h

/-- **`printPhOk`'s facts**, one per block. -/
theorem printPhOk_spec (h : printPhOk okPc ph lab = true) :
    aBlk okPc ph lab "scc_rt_print" 0 x0 = true ∧ aBlk okPc ph lab ".Lscc_rt_print.entry" 0 x1 = true ∧
    aBlk okPc ph lab ".Lscc_rt_print.loop" 0 x2 = true ∧ aBlk okPc ph lab ".Lscc_rt_print.loop" 20 x3 = true ∧
    aBlk okPc ph lab ".Lscc_rt_print.write" 0 x4 = true ∧
    phOne okPc ph (lab ".Lscc_rt_print.write" + Int64.ofNat 20) 2 = true ∧
    aBlk okPc ph lab ".Lscc_rt_print.write" 22 x5 = true ∧ aBlk okPc ph lab ".Lscc_rt_print.write" 42 x6 = true ∧
    aBlk okPc ph lab ".Lscc_rt_print.chk2" 0 x7 = true ∧ aBlk okPc ph lab ".Lscc_rt_print.chk2" 16 x8 = true ∧
    aBlk okPc ph lab ".Lscc_rt_print.chk3" 0 x9 = true ∧ aBlk okPc ph lab ".Lscc_rt_print.chk3" 16 x10 = true ∧
    aBlk okPc ph lab ".Lscc_rt_print.adv" 0 x11 = true ∧ aBlk okPc ph lab ".Lscc_rt_print.fail" 0 x12 = true ∧
    aBlk okPc ph lab ".Lscc_rt_print.done" 0 (x13.take 2) = true ∧
    okPc (lab ".Lscc_rt_print.done" + Int64.ofNat 4).toBitVec.toNat = true := by
  simpa only [printPhOk, Bool.and_eq_true, and_assoc] using h

/-- **The epilogue's phase check with its `ret`**: the check of its first
two instructions (`printPhOk`), the `ret`'s pc off the sites, its return
address `ra` in the epilogue's phase. -/
theorem blkPh_x13 {pc ra : Int64} (h2 : blkPh okPc ph (fun _ => false) lab pc 0 (x13.take 2) = true)
    (hok : okPc (pc + Int64.ofNat 4).toBitVec.toNat = true)
    (hra : ph ra.toBitVec.toNat = ph pc.toBitVec.toNat) :
    blkPh okPc ph (fun _ => false) lab pc ra x13 = true := by
  unfold blkPh at h2 ⊢
  rw [List.all_eq_true] at h2 ⊢
  intro k hk
  have hk3 : k < 3 := by simpa [x13] using List.mem_range.mp hk
  have h0 := h2 0 (by simp [x13])
  have h1 := h2 1 (by simp [x13])
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  · simpa [x13, cellOff, aiTgts, Spike.Lib.X64.classify, Spike.Lib.X64.RegOnly] using h0
  · simpa [x13, cellOff, aiTgts, Spike.Lib.X64.classify, Spike.Lib.X64.RegOnly] using h1
  · simp [x13, cellOff, aiTgts, Spike.Lib.X64.classify] at h1 hok ⊢
    exact ⟨⟨hok, by simpa [Nat.add_assoc] using h1.2⟩, hra⟩

end Spec

/-! ## `scc_rt_print`'s states -/

section Print

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region}
  {F : MachineData → Prop} {rbp0 ra buf0 : BitVec 64} {len0 : Nat} {P Q : Nat → Ctl → Prop}

/-- **A covered block of the cells is off a system call** (`blkW_noSys'`
at its code from `InstOk`). -/
theorem blkW_noSysI (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {blk : List (Directive × Nat)} {lo hi : Int} {l : Label} {off : Nat}
    (hb : blockAtB cells l off blk = true) (he : lab l + Int64.ofNat off = n.pc) (hok : okBlk lo hi n.o blk = true) :
    BlkW (fun s _ => abi.atSys s = false) (fun _ _ => False) exe endPc R F n blk :=
  Spike.Lib.LowerX64.blkW_noSys' (fun _ hs hn => he ▸ codeOf hI hb hs hn) hok

omit [Kraken.Executable.ValidLayout exe] in
/-- **`scc_rt_print`'s states are off the marks' sites** (`okPc`), its code
passing the phase check (`hph`). -/
theorem printPc (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) (hph : printPhOk okPc ph lab = true) :
    PrintAW rbp0 ra buf0 len0 P Q (fun s _ => okPc (pcOf s) = true) (fun _ _ => False) exe endPc R F := by
  obtain ⟨p0, p1, p2, p3, p4, -, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14⟩ := printPhOk_spec hph
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hI.labOk]
  · exact blkW_okPc p0 (by pc_tac)
  · exact blkW_okPc p1 (by pc_tac)
  · exact blkW_okPc p2 (by pc_tac)
  · exact blkW_okPc p3 (by pc_tac)
  · exact blkW_okPc p4 (by pc_tac)
  · exact blkW_okPc p5 (by pc_tac)
  · exact blkW_okPc p6 (by pc_tac)
  · exact blkW_okPc p7 (by pc_tac)
  · exact blkW_okPc p8 (by pc_tac)
  · exact blkW_okPc p9 (by pc_tac)
  · exact blkW_okPc p10 (by pc_tac)
  · exact blkW_okPc p11 (by pc_tac)
  · exact blkW_okPc p12 (by pc_tac)
  · refine blkW_pc (P := fun p => okPc p = true) fun k hk => ?_
    have he : lab ".Lscc_rt_print.done" + Int64.ofNat 0 =
        (N lab rbp0 ra buf0 len0 P Q .done).pc := by pc_tac
    rw [← he]
    have hk3 : k < 3 := by simpa [x13] using hk
    rcases (by omega : k < 2 ∨ k = 2) with h2 | rfl
    · have hc : cellOff (x13.take 2) k = cellOff x13 k := by
        unfold cellOff; rw [List.take_take, Nat.min_eq_left (by omega)]
      exact hc ▸ okPc_of_blkPh p13 k (by simpa [x13] using h2)
    · simpa [cellOff, x13, Spike.Lib.X64.Flow.ofNat_zero'] using p14

/-- **`scc_rt_print`'s states write nothing and are off a system call**
(`blkW_noWr`, `blkW_noSysI`; the routine's block nodes leave out its
`write`), its code in the cells (`hin`), in a region holding its frame. -/
theorem printNoWr (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hin : Scc.Cert.Rt.X64.Print.printIn cells = true) (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 16 ≤ R.hi) :
    PrintAW rbp0 ra buf0 len0 P Q (fun s _ => (∀ L, ¬ WrAt s L) ∧ abi.atSys s = false) (fun _ _ => False)
      exe endPc R F := by
  obtain ⟨h0, h1, h2, h3, h4, -, h5, h6, h7, h8, h9, h10, h11, h12, h13, -⟩ := printIn_spec hin
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hI.labOk] <;>
    refine Spike.Lib.X64.AllocG.BlkW.imp (W1 := fun s _ => ∀ L, ¬ WrAt s L) (W2 := fun s _ => abi.atSys s = false)
      ?_ ?_ fun _ _ h1 h2 => ⟨h1, h2⟩
  · exact Spike.Lib.X64.AllocG.blkW_noWr hI h0 (by pc_tac) x0_ok hR hlo hhi
  · exact blkW_noSysI hI h0 (by pc_tac) x0_ok
  · exact Spike.Lib.X64.AllocG.blkW_noWr hI h1 (by pc_tac) x1_ok hR hlo hhi
  · exact blkW_noSysI hI h1 (by pc_tac) x1_ok
  · exact Spike.Lib.X64.AllocG.blkW_noWr hI h2 (by pc_tac) x2_ok hR hlo hhi
  · exact blkW_noSysI hI h2 (by pc_tac) x2_ok
  · exact Spike.Lib.X64.AllocG.blkW_noWr hI h3 (by pc_tac) x3_ok hR hlo hhi
  · exact blkW_noSysI hI h3 (by pc_tac) x3_ok
  · exact Spike.Lib.X64.AllocG.blkW_noWr hI h4 (by pc_tac) x4_ok hR hlo hhi
  · exact blkW_noSysI hI h4 (by pc_tac) x4_ok
  · exact Spike.Lib.X64.AllocG.blkW_noWr hI h5 (by pc_tac) x5_ok hR hlo hhi
  · exact blkW_noSysI hI h5 (by pc_tac) x5_ok
  · exact Spike.Lib.X64.AllocG.blkW_noWr hI h6 (by pc_tac) x6_ok hR hlo hhi
  · exact blkW_noSysI hI h6 (by pc_tac) x6_ok
  · exact Spike.Lib.X64.AllocG.blkW_noWr hI h7 (by pc_tac) x7_ok hR hlo hhi
  · exact blkW_noSysI hI h7 (by pc_tac) x7_ok
  · exact Spike.Lib.X64.AllocG.blkW_noWr hI h8 (by pc_tac) x8_ok hR hlo hhi
  · exact blkW_noSysI hI h8 (by pc_tac) x8_ok
  · exact Spike.Lib.X64.AllocG.blkW_noWr hI h9 (by pc_tac) x9_ok hR hlo hhi
  · exact blkW_noSysI hI h9 (by pc_tac) x9_ok
  · exact Spike.Lib.X64.AllocG.blkW_noWr hI h10 (by pc_tac) x10_ok hR hlo hhi
  · exact blkW_noSysI hI h10 (by pc_tac) x10_ok
  · exact Spike.Lib.X64.AllocG.blkW_noWr hI h11 (by pc_tac) x11_ok hR hlo hhi
  · exact blkW_noSysI hI h11 (by pc_tac) x11_ok
  · exact Spike.Lib.X64.AllocG.blkW_noWr hI h12 (by pc_tac) x12_ok hR hlo hhi
  · exact blkW_noSysI hI h12 (by pc_tac) x12_ok
  · exact Spike.Lib.X64.AllocG.blkW_noWr hI h13 (by pc_tac) x13_ok hR hlo hhi
  · exact blkW_noSysI hI h13 (by pc_tac) x13_ok

set_option hygiene false in
/-- A block of `scc_rt_print` without `ret`, no dead target, at the source
start's control. -/
local macro "pblk " hb:term:max ok:term:max hp:term:max : tactic =>
  `(tactic| exact BlkW.st (Spike.Lib.X64.Rt.blkW_postO hI (lbl := Λ.static) (dead := fun _ => false) (ra := 0) $hb
    (by pc_tac) $ok hR hlo hhi hR8 hl hh (fun _ _ hJ => hJ.1 ▸ cfacts_c0) $hp
    (fun _ _ _ k hk hr => (noRet_false (by decide) k hk hr).elim) (fun _ _ _ => rfl) hsub hfit hFO))

/-- **`scc_rt_print`'s states carry the state's facts** at any control,
none moved by `K`, its code in the cells (`hin`) passing the phase check
(`hph`), the return address `ra` in the epilogue's phase (`hra`), in a
region of the routine's frame (8-aligned) whose frame condition gives the
stack range off it (`hFO`). The system call is not a block node. -/
theorem printSt (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hin : Scc.Cert.Rt.X64.Print.printIn cells = true) (hph : printPhOk okPc ph lab = true)
    {Λ : Scc.Sem.Layout} {rS : Range}
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -40) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m)
    (hra : ph (Int64.ofBitVec ra).toBitVec.toNat = ph (lab ".Lscc_rt_print.done").toBitVec.toNat) :
    PrintAW rbp0 ra buf0 len0 P Q (fun s _ => SFactsSt Λ μ own rS Tk s) K exe endPc R F := by
  obtain ⟨h0, h1, h2, h3, h4, -, h5, h6, h7, h8, h9, h10, h11, h12, h13, -⟩ := printIn_spec hin
  obtain ⟨p0, p1, p2, p3, p4, -, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14⟩ := printPhOk_spec hph
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hI.labOk]
  · pblk h0 x0_ok p0
  · pblk h1 x1_ok p1
  · pblk h2 x2_ok p2
  · pblk h3 x3_ok p3
  · pblk h4 x4_ok p4
  · pblk h5 x5_ok p5
  · pblk h6 x6_ok p6
  · pblk h7 x7_ok p7
  · pblk h8 x8_ok p8
  · pblk h9 x9_ok p9
  · pblk h10 x10_ok p10
  · pblk h11 x11_ok p11
  · pblk h12 x12_ok p12
  · refine BlkW.st (Spike.Lib.X64.Rt.blkW_postO hI (lbl := Λ.static) (dead := fun _ => false)
      (ra := Int64.ofBitVec ra) h13 (by pc_tac) x13_ok hR hlo hhi hR8 hl hh (fun _ _ hJ => hJ.1 ▸ cfacts_c0)
      (blkPh_x13 p13 (by simpa [Spike.Lib.X64.Flow.ofNat_zero'] using p14)
        (by simpa [Spike.Lib.X64.Flow.ofNat_zero'] using hra))
      (hret_of_run x13_ok fun σ c hJ => ?_) (fun _ _ _ => rfl) hsub hfit hFO)
    obtain ⟨-, c, -, h8, -⟩ := hJ
    simp only [dumN, N]
    rw [x13_run, h8]

end Print

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64.PrintG.blkPh_x13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkPh_x13

/-- info: 'Spike.Lib.X64.PrintG.printPc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printPc

/-- info: 'Spike.Lib.X64.PrintG.printNoWr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printNoWr

/-- info: 'Spike.Lib.X64.PrintG.printSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printSt

end Spike.Lib.X64.PrintG
