/-
**`scc_rt_print`'s states off the sites, writing nothing and carrying the
state's facts at any instance** (AArch64): `PrintAW`
(`Spike/Lib/A64PrintA.lean`, the byte-by-byte specification) inside
`okPc`, no write off a system call, and the state's facts (`SFactsSt`), for
any executable with `InstOk`, its program holding the routine's code
(`printIn`), passing the phase check `printPhOk`
(`Spike/Lib/A64TailPh.lean`): the twin of `Spike/Lib/A64AllocGSt.lean`'s
`allocPc`, `allocSt` for the output routine. None of these reads the source
control: they are the place-independent parts of `PrintW` at `W2`
(`Spike/Lib/LowerA64/PrintCallC2.lean`).

- `printIn_spec`, `printPhOk_spec`: the code's and the check's facts, one per
  block.
- `blkPh_append`, `blkPh_b16`: the phase check of two blocks in a row; the
  epilogue's with its `ret` to a return address in the epilogue's phase.
- `printPc`: the states off the marks' sites.
- `printNoWr`: the states write nothing and are off a system call.
- `printSt`: the states carry the state's facts (`SFactsSt`).
-/
import Spike.Lib.A64AllocGSt
import Spike.Lib.A64PrintA
import Spike.Lib.A64TailPh
import Spike.Lib.LowerA64.W2Body

namespace Spike.Lib.A64.PrintG

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow (NodeW BlkW ND AS svcDir)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.A64.Flow.Ret0.Inst (cfacts_c0)
open Spike.Lib.A64.Rt (InstOk)
open Scc.Cert.Rt.A64 (blockAt labelGap)
open Spike.Lib.A64ConsumerA (SFactsSt WrAt)
open Spike.Lib.A64.StubW (phOne printPhOk)
open Spike.Lib.A64.AllocG (okPc_of_blkPh phOne_spec blkPh_ret blkW_pc blkW_okPc nodeW_okPc dumN)
open Spike.Lib.A64.Print (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b16 oI oE
  b0_ok b1_ok b2_ok b3_ok b4_ok b5_ok b6_ok b7_ok b8_ok b9_ok b10_ok b11_ok b12_ok b13_ok b14_ok b16_ok)
open Spike.Lib.A64.PrintA (PrintAW N)

/-! ## The code's and the check's facts -/

section Spec

variable {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}

/-- **`printIn`'s facts**, one per block. -/
theorem printIn_spec {prog : List Directive} (h : Scc.Cert.Rt.A64.Print.printIn prog = true) :
    blockAt prog "scc_rt_print" 0 b0 = true ∧
    blockAt prog ".L9_scc_rt_print.0_entry" 0 b1 = true ∧
    blockAt prog ".L9_scc_rt_print.1_loop" 0 b2 = true ∧
    blockAt prog ".L9_scc_rt_print.1_loop" 4 b3 = true ∧
    blockAt prog ".L9_scc_rt_print.2_write" 0 b4 = true ∧
    blockAt prog ".L9_scc_rt_print.2_write" 4 [svcDir] = true ∧
    blockAt prog ".L9_scc_rt_print.2_write" 5 b5 = true ∧
    blockAt prog ".L9_scc_rt_print.2_write" 12 b6 = true ∧
    blockAt prog ".L9_scc_rt_print.2_write" 13 b7 = true ∧
    blockAt prog ".L9_scc_rt_print.3_chk2" 0 b8 = true ∧
    blockAt prog ".L9_scc_rt_print.3_chk2" 6 b9 = true ∧
    blockAt prog ".L9_scc_rt_print.3_chk2" 7 b10 = true ∧
    blockAt prog ".L9_scc_rt_print.4_chk3" 0 b11 = true ∧
    blockAt prog ".L9_scc_rt_print.4_chk3" 4 b12 = true ∧
    blockAt prog ".L9_scc_rt_print.5_adv" 0 b13 = true ∧
    blockAt prog ".L9_scc_rt_print.6_fail" 0 b14 = true ∧
    blockAt prog ".L9_scc_rt_print.7_done" 0 b16 = true ∧
    labelGap prog "scc_rt_print" ".L9_scc_rt_print.0_entry" 6 = true := by
  simpa only [Scc.Cert.Rt.A64.Print.printIn, Bool.and_eq_true, and_assoc] using h

/-- **`printPhOk`'s facts**, one per block. -/
theorem printPhOk_spec (h : printPhOk okPc ph lab = true) :
    blkPh okPc ph (fun _ => false) lab (lab "scc_rt_print" + Int64.ofNat (4 * 0)) 0 b0 = true ∧
    blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.0_entry" + Int64.ofNat (4 * 0)) 0 b1 = true ∧
    blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.1_loop" + Int64.ofNat (4 * 0)) 0 b2 = true ∧
    blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.1_loop" + Int64.ofNat (4 * 4)) 0 b3 = true ∧
    blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.2_write" + Int64.ofNat (4 * 0)) 0 b4 = true ∧
    phOne okPc ph (lab ".L9_scc_rt_print.2_write" + Int64.ofNat (4 * 4)) = true ∧
    blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.2_write" + Int64.ofNat (4 * 5)) 0 b5 = true ∧
    blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.2_write" + Int64.ofNat (4 * 12)) 0 b6 = true ∧
    blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.2_write" + Int64.ofNat (4 * 13)) 0 b7 = true ∧
    blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.3_chk2" + Int64.ofNat (4 * 0)) 0 b8 = true ∧
    blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.3_chk2" + Int64.ofNat (4 * 6)) 0 b9 = true ∧
    blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.3_chk2" + Int64.ofNat (4 * 7)) 0 b10 = true ∧
    blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.4_chk3" + Int64.ofNat (4 * 0)) 0 b11 = true ∧
    blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.4_chk3" + Int64.ofNat (4 * 4)) 0 b12 = true ∧
    blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.5_adv" + Int64.ofNat (4 * 0)) 0 b13 = true ∧
    blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.6_fail" + Int64.ofNat (4 * 0)) 0 b14 = true ∧
    blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.7_done" + Int64.ofNat (4 * 0)) 0 (b16.take 3) =
      true ∧
    okPc (lab ".L9_scc_rt_print.7_done" + Int64.ofNat (4 * 3)).toBitVec.toNat = true := by
  simpa only [printPhOk, Bool.and_eq_true, and_assoc] using h

/-- **The phase check of two blocks in a row**, the second's start in the
first's phase. -/
theorem blkPh_append {dd : Nat → Bool} {pc ra : Int64} {a b : List Directive}
    (ha : blkPh okPc ph dd lab pc ra a = true)
    (hb : blkPh okPc ph dd lab (pc + Int64.ofNat (4 * a.length)) ra b = true)
    (he : ph (pc + Int64.ofNat (4 * a.length)).toBitVec.toNat = ph pc.toBitVec.toNat) :
    blkPh okPc ph dd lab pc ra (a ++ b) = true := by
  unfold blkPh at ha hb ⊢
  rw [List.all_eq_true] at ha hb ⊢
  intro k hk
  have hk' := List.mem_range.mp hk
  rw [List.length_append] at hk'
  rcases Nat.lt_or_ge k a.length with h' | h'
  · rw [List.getElem?_append_left h']
    exact ha k (List.mem_range.mpr h')
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h'
    have := hb j (List.mem_range.mpr (by omega))
    rw [he] at this
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, Nat.mul_add, Int64.ofNat_add,
      ← Int64.add_assoc]
    exact this

/-- **The epilogue's phase check with its `ret`**: the check of its first
three instructions (`printPhOk`), the `ret`'s pc off the sites, its return
address `ra` in the epilogue's phase. -/
theorem blkPh_b16 {pc ra : Int64} (h3 : blkPh okPc ph (fun _ => false) lab pc 0 (b16.take 3) = true)
    (hok : okPc (pc + Int64.ofNat (4 * 3)).toBitVec.toNat = true)
    (hra : ph ra.toBitVec.toNat = ph pc.toBitVec.toNat) :
    blkPh okPc ph (fun _ => false) lab pc ra b16 = true := by
  unfold blkPh at h3 ⊢
  rw [List.all_eq_true] at h3 ⊢
  intro k hk
  have hk4 : k < 4 := by simpa [b16] using List.mem_range.mp hk
  have h2 := h3 2 (by simp [b16])
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · simpa [b16, aiTgts, Spike.Lib.A64.Flow.classify, Spike.Lib.A64.Flow.RegOnly] using h3 0 (by simp [b16])
  · simpa [b16, aiTgts, Spike.Lib.A64.Flow.classify, Spike.Lib.A64.Flow.RegOnly] using h3 1 (by simp [b16])
  · simpa [b16, aiTgts, Spike.Lib.A64.Flow.classify, Spike.Lib.A64.Flow.RegOnly] using h2
  · simp [b16, aiTgts, Spike.Lib.A64.Flow.classify, Spike.Lib.A64.Flow.RegOnly] at h2 ⊢
    exact ⟨⟨by simpa using hok, by simpa [Nat.add_assoc] using h2.2⟩, hra⟩

end Spec

/-! ## The epilogue's run to its `ret` -/

open Kraken Kraken.AArch64.Parser in
/-- The epilogue but its `ret`: the saved pair reloaded, the frame popped. -/
def b16h : List Directive := parseAArch64("ldr x29, [sp, #32]
ldr x30, [sp, #40]
add sp, sp, #48")

theorem b16_take : b16.take 3 = b16h := by decide

block_spec b16h (-48) 0 oI b16h

/-- **The epilogue's `ret` returns to the saved return address**
(`blkW_postO`'s `hret`): from the frame's cell `-8`. -/
theorem b16_ret (lab : Label → Int64) (pc : Int64) (σ : Spike.Lib.A64.Flow.AS) {ra : BitVec 64} (h : σ.slot (-8) = ra) :
    ∀ k (hk : k < b16.length) r, Spike.Lib.A64.Flow.classify b16[k] = some (Spike.Lib.A64.Flow.AI.ret r) →
      Int64.ofInt ((Spike.Lib.A64.Flow.arun lab (b16.take k) ⟨pc, oI, σ⟩).σ.regs.getRegOrZr r).signed =
        Int64.ofBitVec ra := by
  intro k hk r hr
  have hk4 : k < 4 := by simpa [b16] using hk
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · simp [b16, Spike.Lib.A64.Flow.classify] at hr
  · simp [b16, Spike.Lib.A64.Flow.classify] at hr
  · simp [b16, Spike.Lib.A64.Flow.classify] at hr
  · simp [b16, Spike.Lib.A64.Flow.classify] at hr
    subst hr
    rw [b16_take, b16h_run]
    simp [h]

/-! ## `scc_rt_print`'s states -/

/-- **A node's pc at its label and offset**: `N`'s pcs are `lab l` plus
fours (also through `dumN`). -/
macro "ppc_tac" : tactic =>
  `(tactic| (dsimp only [dumN, N]; first | (simp only [Int64.add_assoc]; rfl) | simp))

section Print

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region} {F : MachineData → Prop}
  {x29 ra buf0 : BitVec 64} {len0 : Nat} {P Q : Nat → Ctl → Prop}

omit [Kraken.Executable.ValidLayout exe] in
/-- **`scc_rt_print`'s states are off the marks' sites** (`okPc`), its code
passing the phase check (`hph`). -/
theorem printPc (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) (hph : printPhOk okPc ph lab = true) :
    PrintAW x29 ra buf0 len0 P Q (fun s _ => okPc (pcOf s) = true) (fun _ _ => False) exe endPc R F := by
  obtain ⟨p0, p1, p2, p3, p4, -, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17⟩ :=
    printPhOk_spec hph
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hI.labOk]
  · exact blkW_okPc p0 (by ppc_tac)
  · exact blkW_okPc p1 (by ppc_tac)
  · exact blkW_okPc p2 (by ppc_tac)
  · exact blkW_okPc p3 (by ppc_tac)
  · exact blkW_okPc p4 (by ppc_tac)
  · exact blkW_okPc p6 (by ppc_tac)
  · exact blkW_okPc p7 (by ppc_tac)
  · exact blkW_okPc p8 (by ppc_tac)
  · exact blkW_okPc p9 (by ppc_tac)
  · exact blkW_okPc p10 (by ppc_tac)
  · exact blkW_okPc p11 (by ppc_tac)
  · exact blkW_okPc p12 (by ppc_tac)
  · exact blkW_okPc p13 (by ppc_tac)
  · exact blkW_okPc p14 (by ppc_tac)
  · exact blkW_okPc p15 (by ppc_tac)
  · refine blkW_pc (P := fun p => okPc p = true) fun k hk => ?_
    have he : lab ".L9_scc_rt_print.7_done" + Int64.ofNat (4 * 0) =
        (N lab x29 ra buf0 len0 P Q .done).pc := by ppc_tac
    rw [← he]
    have hk4 : k < 4 := by simpa [b16] using hk
    rcases (by omega : k < 3 ∨ k = 3) with h3 | rfl
    · exact okPc_of_blkPh p16 k (by simpa [b16] using h3)
    · simpa [Int64.add_zero, show Int64.ofNat (4 * 0) = 0 from rfl] using p17

/-- **`scc_rt_print`'s states write nothing and are off a system call**
(`blkW_noWr`, `blkW_noSys`; the routine's block nodes leave out its
`write`), its code in the program (`hin`), in a region holding its frame. -/
theorem printNoWr (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hin : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) :
    PrintAW x29 ra buf0 len0 P Q (fun s _ => (∀ L, ¬ WrAt s L) ∧ abi.atSys s = false) (fun _ _ => False)
      exe endPc R F := by
  obtain ⟨h0, h1, h2, h3, h4, -, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, -⟩ := printIn_spec hin
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hI.labOk] <;>
    refine Spike.Lib.A64.AllocG.BlkW.imp (W1 := fun s _ => ∀ L, ¬ WrAt s L) (W2 := fun s _ => abi.atSys s = false)
      ?_ ?_ fun _ _ h1 h2 => ⟨h1, h2⟩
  · exact Spike.Lib.A64.AllocG.blkW_noWr hI h0 (by ppc_tac) b0_ok hR hal hlo hhi
  · exact Spike.Lib.LowerA64.blkW_noSys hI h0 (by ppc_tac) b0_ok
  · exact Spike.Lib.A64.AllocG.blkW_noWr hI h1 (by ppc_tac) b1_ok hR hal hlo hhi
  · exact Spike.Lib.LowerA64.blkW_noSys hI h1 (by ppc_tac) b1_ok
  · exact Spike.Lib.A64.AllocG.blkW_noWr hI h2 (by ppc_tac) b2_ok hR hal hlo hhi
  · exact Spike.Lib.LowerA64.blkW_noSys hI h2 (by ppc_tac) b2_ok
  · exact Spike.Lib.A64.AllocG.blkW_noWr hI h3 (by ppc_tac) b3_ok hR hal hlo hhi
  · exact Spike.Lib.LowerA64.blkW_noSys hI h3 (by ppc_tac) b3_ok
  · exact Spike.Lib.A64.AllocG.blkW_noWr hI h4 (by ppc_tac) b4_ok hR hal hlo hhi
  · exact Spike.Lib.LowerA64.blkW_noSys hI h4 (by ppc_tac) b4_ok
  · exact Spike.Lib.A64.AllocG.blkW_noWr hI h6 (by ppc_tac) b5_ok hR hal hlo hhi
  · exact Spike.Lib.LowerA64.blkW_noSys hI h6 (by ppc_tac) b5_ok
  · exact Spike.Lib.A64.AllocG.blkW_noWr hI h7 (by ppc_tac) b6_ok hR hal hlo hhi
  · exact Spike.Lib.LowerA64.blkW_noSys hI h7 (by ppc_tac) b6_ok
  · exact Spike.Lib.A64.AllocG.blkW_noWr hI h8 (by ppc_tac) b7_ok hR hal hlo hhi
  · exact Spike.Lib.LowerA64.blkW_noSys hI h8 (by ppc_tac) b7_ok
  · exact Spike.Lib.A64.AllocG.blkW_noWr hI h9 (by ppc_tac) b8_ok hR hal hlo hhi
  · exact Spike.Lib.LowerA64.blkW_noSys hI h9 (by ppc_tac) b8_ok
  · exact Spike.Lib.A64.AllocG.blkW_noWr hI h10 (by ppc_tac) b9_ok hR hal hlo hhi
  · exact Spike.Lib.LowerA64.blkW_noSys hI h10 (by ppc_tac) b9_ok
  · exact Spike.Lib.A64.AllocG.blkW_noWr hI h11 (by ppc_tac) b10_ok hR hal hlo hhi
  · exact Spike.Lib.LowerA64.blkW_noSys hI h11 (by ppc_tac) b10_ok
  · exact Spike.Lib.A64.AllocG.blkW_noWr hI h12 (by ppc_tac) b11_ok hR hal hlo hhi
  · exact Spike.Lib.LowerA64.blkW_noSys hI h12 (by ppc_tac) b11_ok
  · exact Spike.Lib.A64.AllocG.blkW_noWr hI h13 (by ppc_tac) b12_ok hR hal hlo hhi
  · exact Spike.Lib.LowerA64.blkW_noSys hI h13 (by ppc_tac) b12_ok
  · exact Spike.Lib.A64.AllocG.blkW_noWr hI h14 (by ppc_tac) b13_ok hR hal hlo hhi
  · exact Spike.Lib.LowerA64.blkW_noSys hI h14 (by ppc_tac) b13_ok
  · exact Spike.Lib.A64.AllocG.blkW_noWr hI h15 (by ppc_tac) b14_ok hR hal hlo hhi
  · exact Spike.Lib.LowerA64.blkW_noSys hI h15 (by ppc_tac) b14_ok
  · exact Spike.Lib.A64.AllocG.blkW_noWr hI h16 (by ppc_tac) b16_ok hR hal hlo hhi
  · exact Spike.Lib.LowerA64.blkW_noSys hI h16 (by ppc_tac) b16_ok

set_option hygiene false in
/-- A block of `scc_rt_print` without `ret`, no dead target, at the source
start's control. -/
local macro "pblk " hb:term:max ok:term:max hp:term:max : tactic =>
  `(tactic| exact Spike.Lib.A64.AllocG.BlkW.st (Spike.Lib.A64.Rt.blkW_postO hI (lbl := Λ.static)
    (dead := fun _ => false) (ra := 0) $hb (by ppc_tac)
    $ok hR hal (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ cfacts_c0) $hp
    (fun _ _ _ k hk r hr => (Spike.Lib.A64Consumer.noRet_false (by decide) k hk r hr).elim) (fun _ _ _ => rfl)
    hl hh hsub hfit hFO))

/-- **`scc_rt_print`'s states carry the state's facts** at any control,
none moved by `K`, its code in the program (`hin`) passing the phase check
(`hph`), the return address `ra` in the epilogue's phase (`hra`), in a
region of the routine's frame (16-aligned) whose frame condition gives the
stack range off it (`hFO`). The system call is not a block node. -/
theorem printSt (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hin : Scc.Cert.Rt.A64.Print.printIn prog = true) (hph : printPhOk okPc ph lab = true)
    {Λ : Scc.Sem.Layout} {rS : Range}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m)
    (hra : ph (Int64.ofBitVec ra).toBitVec.toNat = ph (lab ".L9_scc_rt_print.7_done").toBitVec.toNat) :
    PrintAW x29 ra buf0 len0 P Q (fun s _ => SFactsSt Λ μ own rS Tk s) K exe endPc R F := by
  obtain ⟨h0, h1, h2, h3, h4, -, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, -⟩ := printIn_spec hin
  obtain ⟨p0, p1, p2, p3, p4, -, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17⟩ :=
    printPhOk_spec hph
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hI.labOk]
  · pblk h0 b0_ok p0
  · pblk h1 b1_ok p1
  · pblk h2 b2_ok p2
  · pblk h3 b3_ok p3
  · pblk h4 b4_ok p4
  · pblk h6 b5_ok p6
  · pblk h7 b6_ok p7
  · pblk h8 b7_ok p8
  · pblk h9 b8_ok p9
  · pblk h10 b9_ok p10
  · pblk h11 b10_ok p11
  · pblk h12 b11_ok p12
  · pblk h13 b12_ok p13
  · pblk h14 b13_ok p14
  · pblk h15 b14_ok p15
  · exact Spike.Lib.A64.AllocG.BlkW.st (Spike.Lib.A64.Rt.blkW_postO hI (lbl := Λ.static)
      (dead := fun _ => false) (ra := Int64.ofBitVec ra) h16 (by ppc_tac)
      b16_ok hR hal (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ cfacts_c0)
      (blkPh_b16 p16 (by simpa [show Int64.ofNat (4 * 0) = 0 from rfl] using p17) (by simpa using hra))
      (fun σ _ hJ => by obtain ⟨-, c, -, h8, -⟩ := hJ; exact b16_ret _ _ σ h8) (fun _ _ _ => rfl)
      hl hh hsub hfit hFO)

end Print

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64.PrintG.printPc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printPc

/-- info: 'Spike.Lib.A64.PrintG.printNoWr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printNoWr

/-- info: 'Spike.Lib.A64.PrintG.printSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printSt

end Spike.Lib.A64.PrintG
