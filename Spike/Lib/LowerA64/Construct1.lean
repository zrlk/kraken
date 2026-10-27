/-
**Per-construct lowering lemmas of `Accepted1`** (AArch64), symbolic in the
frame, the IR registers' slots and the pc, in the style of
`Spike/Lib/LowerA64/Construct.lean`.

- `sub_block`: the saturating `-`'s block `la ++ lb ++ subs; csel hs` (the
  operand loads into `x9`, `x10`) is covered in the frame, falls through,
  and leaves `x9` the truncated difference of the operands' values;
- `breq_block`, `jmp_block`: the `if`'s terminator `la ++ lb ++ cmp; b.eq T`
  then `b F` (two blocks: only a block's last instruction may branch): the
  first branches to `T` exactly when the operands' values are equal, else
  falls through to the second, which branches to `F`.
-/
import Spike.Lib.LowerA64.Construct

namespace Spike.Lib.LowerA64

open Kraken Kraken.AArch64.Parser Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.Form (opdVal)

set_option linter.unusedSimpArgs false

/-! ## Saturating `-` -/

theorem directives_subSat :
    directives (subSat .X9 .X9 .X10) =
      [.instr ⟨.W64, .SUBS_s (xz .X9) (xz .X9) ⟨xz .X10, 0, .LSL⟩⟩,
       .instr ⟨.W64, .CSEL (xz .X9) (xz .X9) (zr .W64) .CS⟩] := rfl

theorem okBlk_subSat {lo hi sp : Int} :
    okBlk lo hi ⟨sp, []⟩ (directives (subSat .X9 .X9 .X10)) = true := by
  simp [directives_subSat, xz, zr, okBlk, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg, regDst, zrB,
    SO.write, SO.kill, SO.killZ, rm]

/-- **The saturating `-`'s run**: `x9 := x9 - x10` if `x10 ≤ x9`, else `0`;
it falls through; the slots are unchanged. -/
theorem arun_subSat (lab : Label → Int64) (pc : Int64) (sp : Int) (σ : AS) :
    (arun lab (directives (subSat .X9 .X9 .X10)) ⟨pc, ⟨sp, []⟩, σ⟩).pc = pc + 4 + 4 ∧
      (arun lab (directives (subSat .X9 .X9 .X10)) ⟨pc, ⟨sp, []⟩, σ⟩).so = ⟨sp, []⟩ ∧
      (arun lab (directives (subSat .X9 .X9 .X10)) ⟨pc, ⟨sp, []⟩, σ⟩).σ.regs.X9.toNat =
        σ.regs.X9.toNat - σ.regs.X10.toNat ∧
      (arun lab (directives (subSat .X9 .X9 .X10)) ⟨pc, ⟨sp, []⟩, σ⟩).σ.slot = σ.slot := by
  have h9 := UInt64.toNat_lt σ.regs.X9
  have h10 := UInt64.toNat_lt σ.regs.X10
  have hc : ∀ a b : Nat, a < 2 ^ 64 → b < 2 ^ 64 →
      ((((2 ^ 64 - b : Nat) : Int) + (a : Int)) % 18446744073709551616 = (a : Int) - (b : Int) ↔ b ≤ a) := by
    intro a b ha hb
    constructor
    · intro h
      apply Classical.byContradiction; intro hlt
      have : (((2 ^ 64 - b : Nat) : Int) + (a : Int)) % 18446744073709551616 =
          ((2 ^ 64 - b : Nat) : Int) + (a : Int) := Int.emod_eq_of_lt (by omega) (by omega)
      omega
    · intro h
      have : (((2 ^ 64 - b : Nat) : Int) + (a : Int)) = (a - b : Int) + 18446744073709551616 := by omega
      rw [this, Int.add_emod_right]; exact Int.emod_eq_of_lt (by omega) (by omega)
  simp only [directives_subSat, xz, zr, arun, List.foldl, A64.Flow.dstep, classify, RegOnly, AI.so, AI.step,
    AI.tgt, soReg, regDst, regRes, zrB, SO.write, SO.kill, SO.killZ, rm]
  simp [Operation.interp, MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64, ConstExpr.interp,
    Reg64s.getRegOrZr_X, CondCode.interp, StatusFlags.subs, StatusFlags.from_result, BitVec.unsigned,
    Reg64s.setXReg, Reg64s.getRegOrZr, Reg64s.getRegOrZr64, Reg64s.getXReg, RegOrZr.base, rm]
  have := hc _ _ h9 h10
  simp only [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl] at this
  by_cases hle : σ.regs.X10.toNat ≤ σ.regs.X9.toNat
  · rw [ite_eq_left (this.mpr hle)]
    simp only [BitVec.toNat_sub, UInt64.toNat_toBitVec]
    omega
  · rw [ite_eq_right (fun h => hle (this.mp h))]
    simp only [BitVec.toNat_ofNat]
    omega

/-- **The saturating `-`'s block** `la ++ lb ++ subs; csel hs` (the operand
loads into `x9`, `x10`): covered in the frame; it computes the operands'
values `va`, `vb` (`opdVal` at `rsOf`), falls through past the block, and
leaves `x9 = va - vb` (truncated), the static offsets and the slots. -/
theorem sub_block {c : FnCtx} (hf : FrameOk c) (h1 : c.frame ≤ 4095) (h16 : c.frame % 16 = 0)
    {a b : Scc.IR.Operand} {la lb : List Item} (ha : c.getOp .X9 a = .ok la) (hb : c.getOp .X10 b = .ok lb)
    (lab : Label → Int64) (pc : Int64) (σ : AS) :
    okBlk (-(c.frame : Int)) 0 ⟨-(c.frame : Int), []⟩ (directives (la ++ lb ++ subSat .X9 .X9 .X10)) = true ∧
    ∃ va vb : BitVec 64, opdVal (rsOf c) σ.slot a = some va.toNat ∧ opdVal (rsOf c) σ.slot b = some vb.toNat ∧
      (arun lab (directives (la ++ lb ++ subSat .X9 .X9 .X10)) ⟨pc, ⟨-(c.frame : Int), []⟩, σ⟩).pc =
        pc + Int64.ofNat (4 * (directives (la ++ lb ++ subSat .X9 .X9 .X10)).length) ∧
      (arun lab (directives (la ++ lb ++ subSat .X9 .X9 .X10)) ⟨pc, ⟨-(c.frame : Int), []⟩, σ⟩).so =
        ⟨-(c.frame : Int), []⟩ ∧
      (arun lab (directives (la ++ lb ++ subSat .X9 .X9 .X10))
          ⟨pc, ⟨-(c.frame : Int), []⟩, σ⟩).σ.regs.X9.toNat = va.toNat - vb.toNat ∧
      (arun lab (directives (la ++ lb ++ subSat .X9 .X9 .X10)) ⟨pc, ⟨-(c.frame : Int), []⟩, σ⟩).σ.slot =
        σ.slot := by
  refine ⟨?_, ?_⟩
  · rw [directives_append, directives_append, List.append_assoc, okBlk_getOp hf h1 h16 ha,
      okBlk_getOp hf h1 h16 hb]
    exact okBlk_subSat
  obtain ⟨va, hva, hra⟩ := arun_getOp hf h1 ha lab pc σ
  obtain ⟨vb, hvb, hrb⟩ := arun_getOp hf h1 hb lab (pc + Int64.ofNat (4 * (directives la).length))
    { σ with regs := σ.regs.setXReg .X9 va }
  refine ⟨va, vb, hva, hvb, ?_⟩
  have hlen : (directives (la ++ lb ++ subSat .X9 .X9 .X10)).length =
      (directives la).length + (directives lb).length + 2 := by
    simp [directives_append, directives_subSat]; omega
  rw [hlen, directives_append, directives_append, arun_append, arun_append, hra, hrb]
  obtain ⟨e1, e2, e3, e4⟩ := arun_subSat lab (pc + Int64.ofNat (4 * (directives la).length) +
    Int64.ofNat (4 * (directives lb).length)) (-(c.frame : Int))
    { σ with regs := (σ.regs.setXReg .X9 va).setXReg .X10 vb }
  have h9 : ((σ.regs.setXReg .X9 va).setXReg .X10 vb).X9 = UInt64.ofBitVec va := by
    simp [Reg64s.setXReg]
  have h10 : ((σ.regs.setXReg .X9 va).setXReg .X10 vb).X10 = UInt64.ofBitVec vb := by
    simp [Reg64s.setXReg]
  simp only [h9, h10] at e3
  refine ⟨?_, e2, ?_, e4⟩
  · rw [e1, pc_add3]
  · rw [e3]; simp

/-! ## `if a = b`: compare and branch -/

/-- The first block of the `if`'s terminator: both operands' loads, the
compare, the conditional branch to the `then` block `T`. -/
def brDirs (la lb : List Item) (T : Label) : List Directive :=
  directives (la ++ lb ++ [cmpReg .W64 .X9 .X10, jcc .EQ T])

theorem directives_cmpJcc (T : Label) :
    directives [cmpReg .W64 .X9 .X10, jcc .EQ T] =
      [.instr ⟨.W64, .SUBS_s (zr .W64) (xz .X9) ⟨xz .X10, 0, .LSL⟩⟩, .instr ⟨.W64, .B_cond .EQ (.label T)⟩] := rfl

theorem okBlk_cmpJcc {lo hi sp : Int} (T : Label) :
    okBlk lo hi ⟨sp, []⟩ (directives [cmpReg .W64 .X9 .X10, jcc .EQ T]) = true := by
  simp [directives_cmpJcc, xz, zr, okBlk, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg, regDst, zrB,
    SO.write, SO.kill, SO.killZ, rm]

/-- **The compare-and-branch's run**: to `T` exactly when `x9 = x10`, else
past it; registers, static offsets and slots unchanged. -/
theorem arun_cmpJcc (lab : Label → Int64) (pc : Int64) (sp : Int) (σ : AS) (T : Label) :
    (arun lab (directives [cmpReg .W64 .X9 .X10, jcc .EQ T]) ⟨pc, ⟨sp, []⟩, σ⟩).pc =
        (if σ.regs.X9 = σ.regs.X10 then lab T else pc + 4 + 4) ∧
      (arun lab (directives [cmpReg .W64 .X9 .X10, jcc .EQ T]) ⟨pc, ⟨sp, []⟩, σ⟩).so = ⟨sp, []⟩ ∧
      (arun lab (directives [cmpReg .W64 .X9 .X10, jcc .EQ T]) ⟨pc, ⟨sp, []⟩, σ⟩).σ.regs = σ.regs ∧
      (arun lab (directives [cmpReg .W64 .X9 .X10, jcc .EQ T]) ⟨pc, ⟨sp, []⟩, σ⟩).σ.slot = σ.slot := by
  simp only [directives_cmpJcc, xz, zr, arun, List.foldl, A64.Flow.dstep, classify, RegOnly, AI.so, AI.step,
    AI.tgt, soReg, regDst, regRes, zrB, SO.write, SO.kill, SO.killZ, rm]
  simp [Operation.interp, MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64, ConstExpr.interp,
    Reg64s.getRegOrZr_X, CondCode.interp, StatusFlags.subs, StatusFlags.from_result,
    Reg64s.getRegOrZr, Reg64s.getRegOrZr64, Reg64s.getXReg, RegOrZr.base, rm]
  have : (σ.regs.X9.toBitVec - σ.regs.X10.toBitVec = 0#64) ↔ σ.regs.X9 = σ.regs.X10 := by
    constructor
    · intro h
      apply UInt64.toBitVec_inj.mp
      have := congrArg (· + σ.regs.X10.toBitVec) h
      simp only [BitVec.sub_add_cancel, BitVec.zero_add] at this
      exact this
    · intro h; rw [h]; simp
  by_cases h : σ.regs.X9 = σ.regs.X10
  · rw [ite_eq_left (this.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (this.mp h')), ite_eq_right h]

/-- **The `if`'s compare block** `la ++ lb ++ cmp; b.eq T` (the operand
loads into `x9`, `x10`): covered in the frame; it computes the operands'
values `va`, `vb` and branches to `T` exactly when they are equal, else
falls through past the block; static offsets and slots unchanged. -/
theorem br_block {c : FnCtx} (hf : FrameOk c) (h1 : c.frame ≤ 4095) (h16 : c.frame % 16 = 0)
    {a b : Scc.IR.Operand} {la lb : List Item} (ha : c.getOp .X9 a = .ok la) (hb : c.getOp .X10 b = .ok lb)
    (T : Label) (lab : Label → Int64) (pc : Int64) (σ : AS) :
    okBlk (-(c.frame : Int)) 0 ⟨-(c.frame : Int), []⟩ (brDirs la lb T) = true ∧
    ∃ va vb : BitVec 64, opdVal (rsOf c) σ.slot a = some va.toNat ∧ opdVal (rsOf c) σ.slot b = some vb.toNat ∧
      (arun lab (brDirs la lb T) ⟨pc, ⟨-(c.frame : Int), []⟩, σ⟩).pc =
        (if va = vb then lab T else pc + Int64.ofNat (4 * (brDirs la lb T).length)) ∧
      (arun lab (brDirs la lb T) ⟨pc, ⟨-(c.frame : Int), []⟩, σ⟩).so = ⟨-(c.frame : Int), []⟩ ∧
      (arun lab (brDirs la lb T) ⟨pc, ⟨-(c.frame : Int), []⟩, σ⟩).σ.slot = σ.slot := by
  refine ⟨?_, ?_⟩
  · rw [brDirs, directives_append, directives_append, List.append_assoc, okBlk_getOp hf h1 h16 ha,
      okBlk_getOp hf h1 h16 hb]
    exact okBlk_cmpJcc T
  obtain ⟨va, hva, hra⟩ := arun_getOp hf h1 ha lab pc σ
  obtain ⟨vb, hvb, hrb⟩ := arun_getOp hf h1 hb lab (pc + Int64.ofNat (4 * (directives la).length))
    { σ with regs := σ.regs.setXReg .X9 va }
  refine ⟨va, vb, hva, hvb, ?_⟩
  have hlen : (brDirs la lb T).length = (directives la).length + (directives lb).length + 2 := by
    simp [brDirs, directives_append, directives_cmpJcc]; omega
  rw [hlen, brDirs, directives_append, directives_append, arun_append, arun_append, hra, hrb]
  obtain ⟨e1, e2, -, e4⟩ := arun_cmpJcc lab (pc + Int64.ofNat (4 * (directives la).length) +
    Int64.ofNat (4 * (directives lb).length)) (-(c.frame : Int))
    { σ with regs := (σ.regs.setXReg .X9 va).setXReg .X10 vb } T
  have h9 : ((σ.regs.setXReg .X9 va).setXReg .X10 vb).X9 = UInt64.ofBitVec va := by
    simp [Reg64s.setXReg]
  have h10 : ((σ.regs.setXReg .X9 va).setXReg .X10 vb).X10 = UInt64.ofBitVec vb := by
    simp [Reg64s.setXReg]
  simp only [h9, h10] at e1
  refine ⟨?_, e2, e4⟩
  rw [e1, pc_add3]
  by_cases h : va = vb
  · simp [h]
  · have : UInt64.ofBitVec va ≠ UInt64.ofBitVec vb := fun h' => h (congrArg UInt64.toBitVec h')
    simp [h, this]

/-- The second block of the `if`'s terminator: `b F` to the `else` block. -/
def jmpDirs (F : Label) : List Directive := directives [jmp F]

theorem okBlk_jmp {lo hi sp : Int} (F : Label) : okBlk lo hi ⟨sp, []⟩ (jmpDirs F) = true := by
  simp [jmpDirs, directives, jmp, ins, okBlk, classify, AI.ok, AI.so, AI.isTerm]

/-- **`b F`'s run**: to `F`, nothing else changes. -/
theorem arun_jmp (lab : Label → Int64) (pc : Int64) (sp : Int) (σ : AS) (F : Label) :
    arun lab (jmpDirs F) ⟨pc, ⟨sp, []⟩, σ⟩ = ⟨lab F, ⟨sp, []⟩, σ⟩ := by
  simp [jmpDirs, directives, jmp, ins, arun, A64.Flow.dstep, classify, AI.so, AI.step, AI.tgt]

end Spike.Lib.LowerA64
