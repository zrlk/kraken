/-
**`print`'s call-state facts from the program** (AArch64): the parts of
`printW2`'s premises at a call of `print` (`Spike/Lib/LowerA64/PrintW2.lean`)
that the caller's code and region give, independent of the frames' placement:
`print`'s region `pR (-frame) R` and frame condition `pF (-frame) R F`, the
count below `2 ^ 63`, the return address in the phase of `print`'s `done`
and off the write abort.

- `cell_kept`, `callerCells_stable`: a caller's cell outside a callee's
  region survives a write inside it (the twin of
  `Spike/Lib/Rt/X64Hello1RetDt.lean`'s);
- `pR_facts`: `print`'s region is `OK`, 16-aligned, its bounds `-48` and
  `0`, 8-aligned;
- `pF_stable`, `pF_off`: `print`'s frame condition is kept by writes inside
  its region and gives the words of `rS` off it;
- `x1_lt`: the count `printN n m` is below `2 ^ 63` when `8·m` is;
- `print_phDone`: `print`'s entry, `0_entry`, `1_loop` and `7_done` share a
  phase (`printPhOk`, `printIn`);
- `printRa_ph`, `printRa_notAb`: a `bl scc_rt_print` at `BlC2`'s return
  address in the phase of `7_done` and off the write abort;
- `callSt_x30`, `print_blC`: the call state's `x30` is the address after the
  `bl`, and the `bl` is at the code predicate `Bl` there;
- `printCall_ra`: `printRa_ph`, `printRa_notAb` at every call state
  (`callN`) of `printInsts`' code at the code predicate `BlC2`.
-/
import Spike.Lib.LowerA64.PrintArgW2
import Spike.Lib.LowerA64.AllocRa

namespace Spike.Lib.A64.Flow.Ret0

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-! ## Crossing a callee's region -/

section Cross

variable {R : Region} {kc lo' hi' : Int}

/-- **A caller's cell outside the callee's region survives a write inside
it.** -/
theorem cell_kept {k : Int} {m m' : MachineData} (hR : R.OK) (hlo : R.lo ≤ kc + lo') (hlo0 : lo' ≤ 0)
    (hkc : kc < R.hi) (hk8 : kc % 8 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0) (hk : R.Off k)
    (hn : ¬ (R.callee kc lo' hi').Off (k - kc)) (hd : DFrame (R.callee kc lo' hi') m m') :
    Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt m.dmem (R.addr k) 8 :=
  hd _ (R.addr_fit hR hk) (Region.callee_sep hR hlo hlo0 hkc hk8 hl8 hh8 hk hn)

/-- **The caller's cells outside the callee's region hold values** under
every write inside it. -/
theorem callerCells_stable (hR : R.OK) (hlo : R.lo ≤ kc + lo') (hlo0 : lo' ≤ 0) (hkc : kc < R.hi)
    (hk8 : kc % 8 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0) :
    FStable (R.callee kc lo' hi') (CallerCells R kc lo' hi') := fun _ _ hm hd k hk hn => by
  rw [cell_kept hR hlo hlo0 hkc hk8 hl8 hh8 hk hn hd]; exact hm k hk hn

end Cross

end Spike.Lib.A64.Flow.Ret0

namespace Spike.Lib.LowerA64

open CoreLang
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib (Region)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (StackOff CallerCells callerCells_stable)
open Spike.Lib.A64.Flow.PrintCall (pR pF)
open Spike.Lib.A64.StubW (printPhOk)
open Spike.Lib.PrintSrc (printN)
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.Rt.A64 (Lays label_labelGap)
open Spike.Lib.LowerShape (printInsts)

/-! ## `print`'s region and frame condition -/

section Region

variable {R : Region} {F : MachineData → Prop} {fr : Nat}

/-- **`print`'s region at a caller's frame** of `fr` bytes (16-aligned, at
least 16) inside the caller's 16-aligned region `R` holding `print`'s 48
bytes below the frame: `OK`, 16-aligned, its bounds `-48` and `0`,
8-aligned. -/
theorem pR_facts (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(fr : Int) - 48) (hhi : 0 ≤ R.hi)
    (hf16 : 16 ≤ fr) (h16 : fr % 16 = 0) :
    (pR (-(fr : Int)) R).OK ∧ (pR (-(fr : Int)) R).base.toNat % 16 = 0 ∧ (pR (-(fr : Int)) R).lo ≤ -48 ∧
      0 ≤ (pR (-(fr : Int)) R).hi ∧ (pR (-(fr : Int)) R).lo % 8 = 0 ∧ (pR (-(fr : Int)) R).hi % 8 = 0 := by
  have hb := Region.callee_base (R := R) (kc := -(fr : Int)) (lo' := -48) (hi' := 0) hR (by omega) (by decide)
    (by omega)
  refine ⟨Region.callee_ok hR (by omega) (by decide) (by omega) (by omega), ?_, by simp [Region.callee],
    by simp [Region.callee], by simp [Region.callee], by simp [Region.callee]⟩
  have : (((pR (-(fr : Int)) R).base.toNat : Int)) % 16 = 0 := by rw [hb]; omega
  omega

/-- **`print`'s frame condition is kept by writes inside its region**: the
caller's (`FStable.callee`) and the caller's cells outside it
(`callerCells_stable`). -/
theorem pF_stable (hR : R.OK) (hlo : R.lo ≤ -(fr : Int) - 48) (hhi : 0 ≤ R.hi) (hf16 : 16 ≤ fr) (h16 : fr % 16 = 0)
    (hF : FStable R F) : FStable (pR (-(fr : Int)) R) (pF (-(fr : Int)) R F) := fun m m' hm hd =>
  ⟨FStable.callee hR (by omega) (by decide) (by omega) (by omega) hF m m' hm.1 hd,
    callerCells_stable hR (by omega) (by decide) (by omega) (by omega) (by decide) (by decide) m m' hm.2 hd⟩

/-- **`print`'s frame condition gives the words of `rS` off its region**:
off the caller's (`hFO`) or a caller's cell outside `print`'s
(`stackOff_callee`). -/
theorem pF_off {rS : Scc.Sem.Range} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hlo : R.lo ≤ -(fr : Int) - 48) (hhi : 0 ≤ R.hi) (hf16 : 16 ≤ fr) (h16 : fr % 16 = 0)
    (hFO : ∀ m, F m → StackOff rS R m) :
    ∀ m, pF (-(fr : Int)) R F m → StackOff rS (pR (-(fr : Int)) R) m := fun m hm =>
  Spike.Lib.A64.Flow.Ret0.Inst.stackOff_callee hR (by omega) hl hh (by omega) (by decide) (by omega) (by omega)
    (hFO m hm.1) hm.2

end Region

/-- **The count is below `2 ^ 63`** when it is `printN n m` and `8·m` is. -/
theorem x1_lt {x : Nat} {n m : Nat} (h : x = printN n m) (hm : 8 * m < 2 ^ 63) : x < 2 ^ 63 := by
  subst h; unfold printN; omega

/-! ## The return address -/

section Ra

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive} {kp : Nat}
  {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}

/-- **`print`'s entry is in the phase of its `done`**: the prologue falls
through to `0_entry` (`labelGap`), which branches to `1_loop`, whose
`b.eq` targets `7_done`, each target in its block's phase (`printPhOk`). -/
theorem print_phDone (hp : Lays exe prog kp) (hlab : (_root_.Executable.labels exe).label = lab)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hph : printPhOk okPc ph lab = true) :
    ph (lab ".L9_scc_rt_print.7_done").toBitVec.toNat = ph (lab "scc_rt_print").toBitVec.toNat := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hgap⟩ := Spike.Lib.A64.PrintG.printIn_spec hpr
  obtain ⟨p0, p1, p2, -⟩ := Spike.Lib.A64.PrintG.printPhOk_spec hph
  have he : lab ".L9_scc_rt_print.0_entry" = lab "scc_rt_print" + Int64.ofNat (4 * 6) := by
    rw [← hlab]; exact label_labelGap hp hgap
  rw [ofNat4_zero] at p0 p1 p2
  unfold Spike.Lib.A64Consumer.blkPh at p0 p1 p2
  rw [List.all_eq_true] at p0 p1 p2
  have h0 := p0 5 (by simp [Spike.Lib.A64.Print.b0])
  simp [Spike.Lib.A64.Print.b0, Spike.Lib.A64Consumer.aiTgts, Spike.Lib.A64.Flow.classify] at h0
  have h1 := p1 0 (by simp [Spike.Lib.A64.Print.b1])
  simp [Spike.Lib.A64.Print.b1, Spike.Lib.A64Consumer.aiTgts, Spike.Lib.A64.Flow.classify] at h1
  have h2 := p2 3 (by simp [Spike.Lib.A64.Print.b2])
  simp [Spike.Lib.A64.Print.b2, Spike.Lib.A64Consumer.aiTgts, Spike.Lib.A64.Flow.classify] at h2
  have e6 : (lab "scc_rt_print" + Int64.ofNat (4 * 6)).toBitVec.toNat =
      ((lab "scc_rt_print").toBitVec.toNat + 20 + 4) % 18446744073709551616 := by
    simp [Int64.toBitVec_add, BitVec.toNat_add]
  rw [h2.2.1, h1.2, he, e6, h0.2]

/-- **A `bl scc_rt_print`'s return address is in the phase of `print`'s
`done`**: `print`'s entry in the return address's (`blC2_hra`) and
`print_phDone`. -/
theorem printRa_ph (hp : Lays exe prog kp) (hlab : (_root_.Executable.labels exe).label = lab)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hph : printPhOk okPc ph lab = true)
    {cx : FnCtx} {ra pc : Int64} {k : Nat} (h : BlC2 prog okPc ph lab cx ra pc Scc.Lower.Names.print k) :
    ph (pc + 4).toBitVec.toNat = ph (lab ".L9_scc_rt_print.7_done").toBitVec.toNat := by
  rw [print_phDone hp hlab hpr hph, ← blC2_hra h]; rfl

/-- **A `bl scc_rt_print`'s return address is off the write abort**
(`blC2_notAb`), for a caller other than the runtime's. -/
theorem printRa_notAb (hp : Lays exe prog kp) (hlab : (_root_.Executable.labels exe).label = lab)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {cx : FnCtx} (hfi : cx.fi ≠ 9 ∧ cx.fi ≠ 12 ∧ cx.fi ≠ 16) {ra pc : Int64} {k : Nat}
    (h : BlC2 prog okPc ph lab cx ra pc Scc.Lower.Names.print k) :
    pc + 4 ∉ Spike.Lib.A64.WriteAb.abPcs lab := by
  subst hlab; exact blC2_notAb hp hpr hab hfi h

end Ra

/-! ## At the call states -/

section Call

variable {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)

include hf h1 h16 in
/-- **The call state's `x30` is the address after the `bl`**, `4·|L| + 4`
past the block's pc. -/
theorem callSt_x30 {n : Nat} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand} {L : List Item}
    (hL : PrintCode cx n b o m cw L) (lab : Label → Int64) (pc : Int64) (σ0 : AS) :
    (callSt lab cx pc L σ0).regs.X30.toBitVec = (pc + Int64.ofNat (4 * (directives L).length) + 4).toBitVec := by
  have hok := printCode_okBlk hf h1 h16 hL
  have hpc := arun_pc lab (am := ⟨pc, oF cx, σ0⟩) hok (k := (directives L).length) (by simp [blPrintD_eq])
  rw [List.take_left' rfl] at hpc
  simp only at hpc
  rw [callSt, arun_append, ← hpc]
  generalize arun lab (directives L) ⟨pc, oF cx, σ0⟩ = a
  obtain ⟨pc', so, σ⟩ := a
  simp [blPrintD_eq, arun, A64.Flow.dstep, A64.Flow.classify, AI.step, AI.tgt, AI.so, SO.kill,
    Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Reg64s.setXReg]
  rw [Ret0.ofInt_bmod, BitVec.ofInt_add, int64_ofInt_toInt]; rfl

/-- **The `bl` of `printInsts`' code is at the code predicate `Bl`**, `4·|L|`
past the block's pc. -/
theorem print_blC {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    {kk n : Nat} {pc pc' : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    (hi : InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc') {L : List Item}
    (hL : PrintCode cx n b o m cw L) :
    ∃ k, Bl (pc + Int64.ofNat (4 * (directives L).length)) Scc.Lower.Names.print k := by
  obtain ⟨l1, l2, l3, l4, l5, hPC, -, -, -, -, -, k, hb⟩ := print_chunks hi
  obtain rfl := printCode_unique hL hPC
  refine ⟨k, ?_⟩
  simpa only [directives_append, List.length_append, pc_add4] using hb

include hf h1 h16 in
/-- **At every call state, the return address in the phase of `print`'s
`done` and off the write abort**: the `bl` at `BlC2` (`hBl`), for a caller
other than the runtime's. -/
theorem printCall_ra {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive}
    {kp : Nat} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
    (hp : Lays exe prog kp) (hlab : (_root_.Executable.labels exe).label = lab)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hph : printPhOk okPc ph lab = true) (hfi : cx.fi ≠ 9 ∧ cx.fi ≠ 12 ∧ cx.fi ≠ 16) {ra : Int64}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hBl : ∀ pc g k, Bl pc g k → BlC2 prog okPc ph lab cx ra pc g k)
    {kk n : Nat} {pc pc' : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    (hi : InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc') {L : List Item}
    (hL : PrintCode cx n b o m cw L) {Jn : AS → Ctl → Prop} :
    ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L Jn).J σC c →
      ph (Int64.ofBitVec σC.regs.X30.toBitVec).toBitVec.toNat = ph (lab ".L9_scc_rt_print.7_done").toBitVec.toNat ∧
      Int64.ofBitVec σC.regs.X30.toBitVec ∉ Spike.Lib.A64.WriteAb.abPcs lab := by
  rintro σC c ⟨σ0, -, rfl⟩
  obtain ⟨k, hb⟩ := print_blC hi hL
  rw [callSt_x30 hf h1 h16 hL, int64_ofBitVec_toBitVec]
  exact ⟨printRa_ph hp hlab hpr hph (hBl _ _ _ hb), printRa_notAb hp hlab hpr hab hfi (hBl _ _ _ hb)⟩

end Call

end Spike.Lib.LowerA64

/-- info: 'Spike.Lib.A64.Flow.Ret0.callerCells_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Ret0.callerCells_stable

/-- info: 'Spike.Lib.LowerA64.pR_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.pR_facts

/-- info: 'Spike.Lib.LowerA64.pF_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.pF_stable

/-- info: 'Spike.Lib.LowerA64.pF_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.pF_off

/-- info: 'Spike.Lib.LowerA64.printCall_ra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printCall_ra
