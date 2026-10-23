/-
**Per-construct lowering lemmas** (AArch64), symbolic in the frame, the
IR register's slot and the pc.

- `rsOf`, `okBlk_getOp`, `arun_getOp`: an operand's load (`ldr` of its
  slot or the constant's `movImm`) is covered and puts its `opdVal` in the
  temporary;
- `directives_ret_slot`: `ret r` for an IR register `r` in slot `off` emits
  `retBlk F [.slot off]` (`F` the frame), the block `A64Ret` covers.
-/
import Spike.Lib.LowerA64.MovImm
import Scc.Lower.InvA64
import Spike.Lib.Form

namespace Spike.Lib.LowerA64

open Kraken Kraken.AArch64.Parser Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.Form (opdVal)

set_option linter.unusedSimpArgs false

/-! ## `ret` -/

theorem ofInt_sub_lit (F : Int) (k : Nat) :
    Int64.ofInt (F - k) = Int64.ofInt F - Int64.ofNat k := by
  apply Int64.toBitVec_inj.mp
  simp [Int64.toBitVec_ofInt, Int64.toBitVec_sub, Int64.toBitVec_ofNat]

theorem addImm_small (F : Int) (h0 : 0 ≤ F) (h1 : F ≤ 4095) :
    addImm spW64 spW64 F = [ins (.ADD_e spW64 spW64 (.imm ⟨i64 F, .S0⟩))] := by
  simp [addImm, arithImm?, h0, h1]

/-- **`ret` of a slot register**: the emitted code is `retBlk`. -/
theorem directives_ret_slot {c : FnCtx} (hf : FrameOk c) (h1 : c.frame ≤ 4095)
    {r : Scc.IR.Reg} {off : Int} (h : c.slotOff r = .ok off) {l : List Item}
    (hl : c.getOp .X0 (.reg r) = .ok l) :
    directives (l ++ c.leave ++ [ret]) =
      retBlk (Int64.ofInt c.frame) [.slot (Int64.ofInt off)] := by
  have hs : c.frame ≤ 32768 := by omega
  have hg := getReg_eq hf hs h .X0
  simp only [FnCtx.getOp] at hl
  rw [hl] at hg; cases hg
  have h0 : (0:Int) ≤ c.frame := by omega
  have h1' : (c.frame:Int) ≤ 4095 := by omega
  rw [leave_eq hf hs, addImm_small _ h0 h1']
  simp [directives, retBlk, wordDirs, epi,
    retRegs, RW.dir, AI.toDir, i64, ins, ret, rz, spW64,
    ofInt_sub_lit]


/-! ## Operands -/

/-- **The slot map of a frame**: an IR register's cell, relative to the
frame's base (`sp` at `-frame`). -/
def rsOf (c : FnCtx) (r : Scc.IR.Reg) : Option Int :=
  match c.slotOff r with
  | .ok off => some (off - c.frame)
  | .error _ => none

theorem toInt_ofInt_small {k : Int} (h0 : -(2 ^ 62) ≤ k) (h1 : k ≤ 2 ^ 62) : (Int64.ofInt k).toInt = k := by
  have hs : Int64.size = 18446744073709551616 := rfl
  rw [Int64.toInt_ofInt, hs]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- An operand's load: the directive list and its register effect. -/
theorem getOp_cases {c : FnCtx} (hf : FrameOk c) (h1 : c.frame ≤ 4095) {t : XReg} {a : Scc.IR.Operand}
    {l : List Item} (ha : c.getOp t a = .ok l) :
    (∃ r off, a = .reg r ∧ c.slotOff r = .ok off ∧ directives l = [RW.dir t (.slot (Int64.ofInt off))]) ∨
    (∃ v, a = .imm v ∧ l = movImm t v.toNat) := by
  cases a with
  | reg r =>
    left
    cases hs : c.slotOff r with
    | error e => simp [FnCtx.getOp, FnCtx.getReg, hs, bind, Except.bind] at ha
    | ok off =>
      refine ⟨r, off, rfl, hs, ?_⟩
      have hg := getReg_eq hf (by omega) hs t
      simp only [FnCtx.getOp] at ha
      rw [ha] at hg; cases hg
      simp [directives, RW.dir, AI.toDir, ins, rz, spW64, i64]
  | imm v =>
    right
    exact ⟨v, rfl, by simp [FnCtx.getOp] at ha; exact ha.symm⟩

/-- **An operand's load is covered** in the frame `[-frame, 0)`. -/
theorem okBlk_getOp {c : FnCtx} (hf : FrameOk c) (h1 : c.frame ≤ 4095) (h16 : c.frame % 16 = 0) {t : XReg}
    {a : Scc.IR.Operand} {l : List Item} (ha : c.getOp t a = .ok l) (ds : List Directive) :
    okBlk (-(c.frame : Int)) 0 ⟨-(c.frame : Int), []⟩ (directives l ++ ds) =
      okBlk (-(c.frame : Int)) 0 ⟨-(c.frame : Int), []⟩ ds := by
  rcases getOp_cases hf h1 ha with ⟨r, off, rfl, hs, hl⟩ | ⟨v, rfl, rfl⟩
  · obtain ⟨h0, h8, hle⟩ := slotOff_bounds hf hs
    rw [hl, List.singleton_append, okBlk_rw]
    have ho : (Int64.ofInt off).toInt = off := toInt_ofInt_small (by omega) (by omega)
    simp only [ho, offOk]
    have : (-(c.frame : Int)) % 16 = 0 := by omega
    simp [this]
    omega
  · rw [okBlk_movImm]; rfl

/-- **An operand's load runs** to `t := ` its value (`opdVal` at `rsOf`). -/
theorem arun_getOp {c : FnCtx} (hf : FrameOk c) (h1 : c.frame ≤ 4095) {t : XReg} {a : Scc.IR.Operand}
    {l : List Item} (ha : c.getOp t a = .ok l) (lab : Label → Int64) (pc : Int64) (σ : AS) :
    ∃ v : BitVec 64, opdVal (rsOf c) σ.slot a = some v.toNat ∧
      arun lab (directives l) ⟨pc, ⟨-(c.frame : Int), []⟩, σ⟩ =
        ⟨pc + Int64.ofNat (4 * (directives l).length), ⟨-(c.frame : Int), []⟩,
          { σ with regs := σ.regs.setXReg t v }⟩ := by
  rcases getOp_cases hf h1 ha with ⟨r, off, rfl, hs, hl⟩ | ⟨v, rfl, rfl⟩
  · obtain ⟨h0, h8, hle⟩ := slotOff_bounds hf hs
    have ho : (Int64.ofInt off).toInt = off := toInt_ofInt_small (by omega) (by omega)
    refine ⟨σ.slot (off - c.frame), ?_, ?_⟩
    · simp [opdVal, rsOf, hs]
    · rw [hl]
      simp only [arun, List.foldl, dstep_rw, RW.val, ho, List.length_singleton]
      rw [show -(c.frame : Int) + off = off - c.frame by omega]
  · refine ⟨BitVec.ofInt 64 (v.toNat : Int), ?_, ?_⟩
    · simp only [opdVal, Option.some.injEq]
      have := UInt64.toNat_lt v
      rw [BitVec.toNat_ofInt]; omega
    · rw [arun_movImm]; rfl


/-! ## Checked `+` -/

theorem directives_append (l l' : List Item) : directives (l ++ l') = directives l ++ directives l' := by
  simp [directives, List.filterMap_append]

theorem directives_addChecked (L : Label) :
    directives (addChecked .X9 .X9 .X10 L) =
      [.instr ⟨.W64, .ADDS_s (xz .X9) (xz .X9) ⟨xz .X10, 0, .LSL⟩⟩, .instr ⟨.W64, .B_cond .CS (.label L)⟩] := rfl

theorem okBlk_addChecked {lo hi sp : Int} (L : Label) :
    okBlk lo hi ⟨sp, []⟩ (directives (addChecked .X9 .X9 .X10 L)) = true := by
  simp [directives_addChecked, xz, okBlk, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg, regDst, zrB,
    SO.write, SO.kill, SO.killZ, rm]

/-- **The checked add's run**: `x9 := x9 + x10`; the branch is taken
exactly when the sum overflows 64 bits; the slots are unchanged. -/
theorem arun_addChecked (lab : Label → Int64) (pc : Int64) (sp : Int) (σ : AS) (L : Label) :
    (arun lab (directives (addChecked .X9 .X9 .X10 L)) ⟨pc, ⟨sp, []⟩, σ⟩).pc =
        (if σ.regs.X9.toNat + σ.regs.X10.toNat < 2 ^ 64 then pc + 4 + 4 else lab L) ∧
      (arun lab (directives (addChecked .X9 .X9 .X10 L)) ⟨pc, ⟨sp, []⟩, σ⟩).so = ⟨sp, []⟩ ∧
      (arun lab (directives (addChecked .X9 .X9 .X10 L)) ⟨pc, ⟨sp, []⟩, σ⟩).σ.regs =
        σ.regs.setXReg .X9 (σ.regs.X9.toBitVec + σ.regs.X10.toBitVec) ∧
      (arun lab (directives (addChecked .X9 .X9 .X10 L)) ⟨pc, ⟨sp, []⟩, σ⟩).σ.slot = σ.slot := by
  have hlt : ∀ a b : UInt64, ((a.toNat : Int) + b.toNat) % 18446744073709551616 = (a.toNat : Int) + b.toNat ↔
      a.toNat + b.toNat < 2 ^ 64 := by
    intro a b; have := UInt64.toNat_lt a; have := UInt64.toNat_lt b
    constructor
    · intro h; omega
    · intro h; exact Int.emod_eq_of_lt (by omega) (by omega)
  simp only [directives_addChecked, xz, arun, List.foldl, A64.Flow.dstep, classify, RegOnly, AI.so, AI.step, AI.tgt,
    soReg, regDst, regRes, zrB, SO.write, SO.kill, SO.killZ, rm]
  simp [Operation.interp, MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64, ConstExpr.interp,
    Reg64s.getRegOrZr_X, CondCode.interp, StatusFlags.adds, StatusFlags.from_result, BitVec.unsigned, hlt]
  refine ⟨?_, rfl⟩
  by_cases h : σ.regs.X9.toNat + σ.regs.X10.toNat < 18446744073709551616
  · simp [h, show ¬ 18446744073709551616 ≤ σ.regs.X9.toNat + σ.regs.X10.toNat by omega]
  · simp [h, show 18446744073709551616 ≤ σ.regs.X9.toNat + σ.regs.X10.toNat by omega]


theorem arun_append (lab : Label → Int64) (a b : List Directive) (am : AM) :
    arun lab (a ++ b) am = arun lab b (arun lab a am) := by
  simp [arun, List.foldl_append]

theorem pc_add3 (pc : Int64) (a b : Nat) :
    pc + Int64.ofNat (4 * a) + Int64.ofNat (4 * b) + 4 + 4 = pc + Int64.ofNat (4 * (a + b + 2)) := by
  rw [show 4 * (a + b + 2) = 4 * a + 4 * b + 4 + 4 by omega, Int64.ofNat_add, Int64.ofNat_add, Int64.ofNat_add]
  simp only [Int64.add_assoc]; rfl

/-- **The checked add's block** `la ++ lb ++ adds; b.cs L` (the operand
loads into `x9`, `x10`): covered in the frame; it computes the operands'
values `va`, `vb` (`opdVal` at `rsOf`), falls through past the block exactly
when `va + vb < 2^64` (else branches to `L`), leaves `x9 = va + vb`, the
static offsets and the slots. -/
theorem add_block {c : FnCtx} (hf : FrameOk c) (h1 : c.frame ≤ 4095) (h16 : c.frame % 16 = 0)
    {a b : Scc.IR.Operand} {la lb : List Item} (ha : c.getOp .X9 a = .ok la) (hb : c.getOp .X10 b = .ok lb)
    (L : Label) (lab : Label → Int64) (pc : Int64) (σ : AS) :
    okBlk (-(c.frame : Int)) 0 ⟨-(c.frame : Int), []⟩ (directives (la ++ lb ++ addChecked .X9 .X9 .X10 L)) = true ∧
    ∃ va vb : BitVec 64, opdVal (rsOf c) σ.slot a = some va.toNat ∧ opdVal (rsOf c) σ.slot b = some vb.toNat ∧
      (arun lab (directives (la ++ lb ++ addChecked .X9 .X9 .X10 L)) ⟨pc, ⟨-(c.frame : Int), []⟩, σ⟩).pc =
        (if va.toNat + vb.toNat < 2 ^ 64 then
          pc + Int64.ofNat (4 * (directives (la ++ lb ++ addChecked .X9 .X9 .X10 L)).length) else lab L) ∧
      (arun lab (directives (la ++ lb ++ addChecked .X9 .X9 .X10 L)) ⟨pc, ⟨-(c.frame : Int), []⟩, σ⟩).so =
        ⟨-(c.frame : Int), []⟩ ∧
      (arun lab (directives (la ++ lb ++ addChecked .X9 .X9 .X10 L))
          ⟨pc, ⟨-(c.frame : Int), []⟩, σ⟩).σ.regs.X9.toBitVec = va + vb ∧
      (arun lab (directives (la ++ lb ++ addChecked .X9 .X9 .X10 L)) ⟨pc, ⟨-(c.frame : Int), []⟩, σ⟩).σ.slot =
        σ.slot := by
  refine ⟨?_, ?_⟩
  · rw [directives_append, directives_append, List.append_assoc, okBlk_getOp hf h1 h16 ha,
      okBlk_getOp hf h1 h16 hb]
    exact okBlk_addChecked L
  obtain ⟨va, hva, hra⟩ := arun_getOp hf h1 ha lab pc σ
  obtain ⟨vb, hvb, hrb⟩ := arun_getOp hf h1 hb lab (pc + Int64.ofNat (4 * (directives la).length))
    { σ with regs := σ.regs.setXReg .X9 va }
  refine ⟨va, vb, hva, hvb, ?_⟩
  have hlen : (directives (la ++ lb ++ addChecked .X9 .X9 .X10 L)).length =
      (directives la).length + (directives lb).length + 2 := by
    simp [directives_append, directives_addChecked]; omega
  rw [hlen, directives_append, directives_append, arun_append, arun_append, hra, hrb]
  obtain ⟨e1, e2, e3, e4⟩ := arun_addChecked lab (pc + Int64.ofNat (4 * (directives la).length) +
    Int64.ofNat (4 * (directives lb).length)) (-(c.frame : Int))
    { σ with regs := (σ.regs.setXReg .X9 va).setXReg .X10 vb } L
  have h9 : ((σ.regs.setXReg .X9 va).setXReg .X10 vb).X9 = UInt64.ofBitVec va := by
    simp [Reg64s.setXReg]
  have h10 : ((σ.regs.setXReg .X9 va).setXReg .X10 vb).X10 = UInt64.ofBitVec vb := by
    simp [Reg64s.setXReg]
  simp only [h9, h10] at e1 e3
  refine ⟨?_, e2, ?_, e4⟩
  · rw [e1, pc_add3]; simp
  · rw [e3]; simp [Reg64s.setXReg]

end Spike.Lib.LowerA64
