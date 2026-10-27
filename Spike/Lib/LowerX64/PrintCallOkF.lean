/-
**`print`'s call-state facts from the program** (x86-64): the twin of
`Spike/Lib/LowerA64/PrintCallOkF.lean`. The parts of `printW2`'s premises at
a call of `print` (`Spike/Lib/LowerX64/PrintW2.lean`) that the caller's code
and region give, independent of the frames' placement: `print`'s region
`pR kb R` and frame condition `pF kb R F` (`kb` the call node's `%rsp` less
the 8 bytes `print` pushes), the count below `2 ^ 63`, the return address in
the phase of `print`'s `done` and off the write abort.

- `pR_facts`: `print`'s region is `OK`, 8-aligned, its bounds `-40` and
  `16`, 8-aligned;
- `pF_stable`, `pF_off`: `print`'s frame condition is kept by writes inside
  its region and gives the words of `rS` off it;
- `x1_lt`: the count `printN n m` is below `2 ^ 63` when `8·m` is;
- `print_phDone`: `print`'s entry, `.entry`, `.loop` and `.done` share a
  phase (`printPhOk`, `printIn`);
- `printRa_ph`, `printRa_notAb`: a `call scc_rt_print` at `BlC2`'s return
  address in the phase of `.done` and off the write abort;
- `stC_ra`, `printCodeC_bl`: the call state's return-address cell holds the
  address after the `call`, and the `call` is at the code predicate `Bl`
  there;
- `printCall_ra`: `printRa_ph`, `printRa_notAb` at every call state
  (`PBlk.nC`) of `PrintCodeC`'s block at the code predicate `BlC2`.
-/
import Spike.Lib.LowerX64.PrintArgW2
import Spike.Lib.LowerX64.AllocRa

namespace Spike.Lib.LowerX64

open CoreLang
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib (Region)
open Spike.Lib.X64 (AS FStable DFrame cellOff)
open Spike.Lib.X64.Flow.Ret0 (StackOff CallerCells)
open Spike.Lib.X64.PrintCall (pR pF)
open Spike.Lib.X64.PrintG (printPhOk)
open Spike.Lib.PrintSrc (printN)
open Scc.Cert.Rt.X64 (Lays label_labelGapB)

/-! ## `print`'s region and frame condition -/

section Region

variable {R : Region} {F : MachineData → Prop} {z : Nat}

/-- **`print`'s region at a caller's frame** of `z` bytes (16-aligned)
inside the caller's 16-aligned region `R` holding `print`'s 40 bytes below
and 16 above its entry, `16` below the frame: `OK`, 8-aligned, its bounds
`-40` and `16`, 8-aligned. -/
theorem pR_facts (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(z : Int) - 56) (hhi : 16 ≤ R.hi)
    (h16 : z % 16 = 0) :
    (pR (-(z : Int) - 8 - 8) R).OK ∧ (pR (-(z : Int) - 8 - 8) R).base.toNat % 8 = 0 ∧
      (pR (-(z : Int) - 8 - 8) R).lo ≤ -40 ∧ 16 ≤ (pR (-(z : Int) - 8 - 8) R).hi ∧
      (pR (-(z : Int) - 8 - 8) R).lo % 8 = 0 ∧ (pR (-(z : Int) - 8 - 8) R).hi % 8 = 0 := by
  have hb := Region.callee_base (R := R) (kc := -(z : Int) - 8 - 8) (lo' := -40) (hi' := 16) hR (by omega)
    (by decide) (by omega)
  refine ⟨Region.callee_ok hR (by omega) (by decide) (by omega) (by omega), ?_, by simp [Region.callee],
    by simp [Region.callee], by simp [Region.callee], by simp [Region.callee]⟩
  have : (((pR (-(z : Int) - 8 - 8) R).base.toNat : Int)) % 8 = 0 := by rw [hb]; omega
  omega

/-- **The caller's cells outside `print`'s region hold values** under every
write inside it (`Region.callee_sep`). -/
theorem pCells_stable (hR : R.OK) (hlo : R.lo ≤ -(z : Int) - 56) (hhi : 16 ≤ R.hi) (h16 : z % 16 = 0) :
    FStable (pR (-(z : Int) - 8 - 8) R) (CallerCells R (-(z : Int) - 8 - 8) (-40) 16) :=
  fun m m' hm hd k hk hn => by
    rw [hd _ (R.addr_fit hR hk) (Region.callee_sep hR (by omega) (by decide) (by omega) (by omega) (by decide)
      (by decide) hk hn)]
    exact hm k hk hn

/-- **`print`'s frame condition is kept by writes inside its region**: the
caller's (`FStable.callee`) and the caller's cells outside it
(`pCells_stable`). -/
theorem pF_stable (hR : R.OK) (hlo : R.lo ≤ -(z : Int) - 56) (hhi : 16 ≤ R.hi) (h16 : z % 16 = 0)
    (hF : FStable R F) : FStable (pR (-(z : Int) - 8 - 8) R) (pF (-(z : Int) - 8 - 8) R F) := fun m m' hm hd =>
  ⟨FStable.callee hR (by omega) (by decide) (by omega) (by omega) hF m m' hm.1 hd,
    pCells_stable hR hlo hhi h16 m m' hm.2 hd⟩

/-- **`print`'s frame condition gives the words of `rS` off its region**:
off the caller's (`hFO`) or a caller's cell outside `print`'s
(`stackOff_callee`). -/
theorem pF_off {rS : Scc.Sem.Range} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hlo : R.lo ≤ -(z : Int) - 56) (hhi : 16 ≤ R.hi) (h16 : z % 16 = 0)
    (hFO : ∀ m, F m → StackOff rS R m) :
    ∀ m, pF (-(z : Int) - 8 - 8) R F m → StackOff rS (pR (-(z : Int) - 8 - 8) R) m := fun m hm =>
  Spike.Lib.X64.Rt.stackOff_callee hR (by omega) hl hh (by omega) (by decide) (by omega) (by omega)
    (hFO m hm.1) hm.2

end Region

/-- **The count is below `2 ^ 63`** when it is `printN n m` and `8·m` is. -/
theorem x1_lt {x : Nat} {n m : Nat} (h : x = printN n m) (hm : 8 * m < 2 ^ 63) : x < 2 ^ 63 := by
  subst h; unfold printN; omega

/-! ## The return address -/

section Ra

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)}
  {kp : Nat} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}

/-- **`print`'s entry is in the phase of its `done`**: the prologue falls
through to `.entry` (`labelGapB`), which jumps to `.loop`, whose `je`
targets `.done`, each target in its block's phase (`printPhOk`). -/
theorem print_phDone (hp : Lays exe cells kp) (hlab : (_root_.Executable.labels exe).label = lab)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hph : printPhOk okPc ph lab = true) :
    ph (lab ".Lscc_rt_print.done").toBitVec.toNat = ph (lab "scc_rt_print").toBitVec.toNat := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hgap⟩ := Spike.Lib.X64.PrintG.printIn_spec hpr
  obtain ⟨p0, p1, p2, -⟩ := Spike.Lib.X64.PrintG.printPhOk_spec hph
  have he : lab ".Lscc_rt_print.entry" = lab "scc_rt_print" + Int64.ofNat 16 := by
    rw [← hlab]; exact label_labelGapB hp hgap
  unfold Spike.Lib.X64.AllocG.aBlk Spike.Lib.X64Consumer.blkPh at p0 p1 p2
  rw [Spike.Lib.X64.Flow.ofNat_zero'] at p0 p1 p2
  rw [List.all_eq_true] at p0 p1 p2
  have h0 := p0 4 (by simp [Spike.Lib.X64.Print.x0])
  simp [Spike.Lib.X64.Print.x0, Spike.Lib.X64Consumer.aiTgts, Spike.Lib.X64.classify, cellOff] at h0
  have h1 := p1 0 (by simp [Spike.Lib.X64.Print.x1])
  simp [Spike.Lib.X64.Print.x1, Spike.Lib.X64Consumer.aiTgts, Spike.Lib.X64.classify, cellOff] at h1
  have h2 := p2 3 (by simp [Spike.Lib.X64.Print.x2])
  simp [Spike.Lib.X64.Print.x2, Spike.Lib.X64Consumer.aiTgts, Spike.Lib.X64.classify, cellOff] at h2
  have e16 : (lab "scc_rt_print" + Int64.ofNat 16).toBitVec.toNat =
      ((lab "scc_rt_print").toBitVec.toNat + 12 + 4) % 18446744073709551616 := by
    simp [Int64.toBitVec_add, BitVec.toNat_add]
  rw [h2.2.1, h1.2, he, e16, h0.2]

/-- **A `call scc_rt_print`'s return address is in the phase of `print`'s
`done`**: `print`'s entry in the return address's (`blC2_hra`) and
`print_phDone`. -/
theorem printRa_ph (hp : Lays exe cells kp) (hlab : (_root_.Executable.labels exe).label = lab)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hph : printPhOk okPc ph lab = true)
    {fr : Scc.Emit.X64.Frame} {ra pc : Int64} {zc k : Nat}
    (h : BlC2 cells okPc ph lab fr ra pc zc Scc.Lower.Names.print k) :
    ph (pc + Int64.ofNat zc).toBitVec.toNat = ph (lab ".Lscc_rt_print.done").toBitVec.toNat := by
  rw [print_phDone hp hlab hpr hph, ← blC2_hra h]; rfl

/-- **A `call scc_rt_print`'s return address is off the write abort**
(`blC2_notAb`). -/
theorem printRa_notAb (hp : Lays exe cells kp) (hlab : (_root_.Executable.labels exe).label = lab)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {fr : Scc.Emit.X64.Frame} {ra pc : Int64} {zc k : Nat}
    (h : BlC2 cells okPc ph lab fr ra pc zc Scc.Lower.Names.print k) :
    pc + Int64.ofNat zc ∉ Spike.Lib.X64.WriteAb.abPcs lab := by
  subst hlab; exact blC2_notAb hp hpr hab h

end Ra

/-! ## At the call states -/

section Call

/-- **The call state's return-address cell holds the address after the
`call`**: `%rsp` at `-fr.size` before it (`oB`), the `call` pushing
`pc3 + zc` (`arun_callD`). -/
theorem stC_ra (lab : String → Int64) (fr : Scc.Emit.X64.Frame) (B : PBlk) (σ0 : AS) (fl : StatusFlags) :
    (B.stC lab fr σ0 fl).slot (-(fr.size : Int) - 8) = (B.pc3 + Int64.ofNat B.zc).toBitVec := by
  simp only [PBlk.stC, arun_callD, oB, Spike.Lib.upd_apply]; simp

/-- **`PrintCodeC`'s `call` is at the code predicate `Bl`** at the block's
`pc3`, of its `zc` bytes. -/
theorem printCodeC_bl {fr : Scc.Emit.X64.Frame} {Cd : Int64 → List (Directive × Nat) → Prop}
    {Bl : Int64 → Nat → Label → Nat → Prop} {kk : Nat} {pc : Int64} {n : Nat} {b : Scc.IR.Operand}
    {o : Scc.IR.Reg} {m c : Scc.IR.Operand} {B : PBlk} (hB : PrintCodeC fr Cd Bl kk pc n b o m c B) :
    Bl B.pc3 B.zc Scc.Lower.Names.print kk := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    a1, a2, a3, b1, b2, b3, b4, c1, c2, c3, c4, e1, e2, e3, e4, e5, e6, e7, e8, g1, g2, zc,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hb, rfl⟩ := hB
  simpa only [pblk, List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add, Int64.add_assoc] using hb

/-- **At every call state, the return address in the phase of `print`'s
`done` and off the write abort**: the `call` at `BlC2` (`hBl`). -/
theorem printCall_ra {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe]
    {cells : List (Directive × Nat)} {kp : Nat} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
    (hp : Lays exe cells kp) (hlab : (_root_.Executable.labels exe).label = lab)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : printPhOk okPc ph lab = true) {fr : Scc.Emit.X64.Frame} {ra : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hBl : ∀ pc z g k, Bl pc z g k → BlC2 cells okPc ph lab fr ra pc z g k)
    {kk n : Nat} {pc : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand} {B : PBlk}
    (hB : PrintCodeC fr Cd Bl kk pc n b o m cw B) {Jn : AS → Ctl → Prop} :
    ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr Jn).J σC c →
      ph (Int64.ofBitVec (σC.slot (-(fr.size : Int) - 8))).toBitVec.toNat =
        ph (lab ".Lscc_rt_print.done").toBitVec.toNat ∧
      Int64.ofBitVec (σC.slot (-(fr.size : Int) - 8)) ∉ Spike.Lib.X64.WriteAb.abPcs lab := by
  rintro σC c ⟨σ0, fl, -, rfl⟩
  have hb := hBl _ _ _ _ (printCodeC_bl hB)
  rw [stC_ra]
  simp only [Int64.ofBitVec_toBitVec]
  exact ⟨printRa_ph hp hlab hpr hph hb, printRa_notAb hp hlab hpr hab hb⟩

end Call

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.pR_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.pR_facts

/-- info: 'Spike.Lib.LowerX64.pF_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.pF_stable

/-- info: 'Spike.Lib.LowerX64.pF_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.pF_off

/-- info: 'Spike.Lib.LowerX64.printCall_ra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printCall_ra
