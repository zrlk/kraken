/-
**`print`'s argument block** (AArch64): the code `callBlock`'s `.print`
case (`Scc/Lower/Term.lean`) lowers before `bl scc_rt_print`, run from any
caller's frame (`FrameOk`, `frame ≤ 4095`) on any operands.

- The operations: `arun_ext32`, `arun_binAdd`, `arun_binMul`, `arun_cmp`,
  `arun_cselCC`.
- The instructions' blocks (`FnCtx.inst`'s code run at `oF c`):
  `ext32_step` (`ext false .w32`), `bin_step` (`add`, `mul`),
  `select_step` (`select .ult`), `args2_step` (two arguments into `x0`,
  `x1`; `getArgs_two`, `callArgs_two`).
- `printK_run`: `cap := m · 8`, `k := select (n < cap) n cap` and the
  arguments `s`, `k`.
- `printArgs_run` (a register offset: `lo := ext.w32 o`, `s := b + lo`) and
  `printArgsImm_run` (an immediate offset `w ≠ 0` on a base: `s := b + w`):
  the whole block; `x0` is the buffer's address, `x1` is
  `min(n, 8·m)` (unsigned, wrapping), every slot but the block's fresh
  registers' kept.
- `inst_print_call`: the code of `call [] print [s, k]`.
- Coverage in the frame `[-frame, 0)` (`okBlk`): `okBlk_printArgs`,
  `okBlk_printArgsImm`, from the operations' and instructions'
  (`okBlk_setReg9`, `okBlk_inst_ext32`, `okBlk_inst_bin`,
  `okBlk_inst_select`, `okBlk_args2`).

`Spike/Test/LowerA64PrintArgs.lean` instantiates the block at `hello1`'s
frame.
-/
import Spike.Lib.LowerA64.Construct1
import Spike.Lib.LowerA64.Node

namespace Spike.Lib.LowerA64

open Kraken Kraken.AArch64.Parser Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.Form (opdVal)

set_option linter.unusedSimpArgs false

/-! ## The operations -/

theorem directives_ext32 : directives (extOp false .w32) = [.instr ⟨.W64, .UBFM (xz .X9) (xz .X9) 0 31⟩] := rfl

theorem arun_ext32 (lab : Label → Int64) (pc : Int64) (sp : Int) (σ : AS) :
    arun lab (directives (extOp false .w32)) ⟨pc, ⟨sp, []⟩, σ⟩ =
      ⟨pc + 4, ⟨sp, []⟩, { σ with regs := σ.regs.setXReg .X9 ((σ.regs.X9.toBitVec.take 32).setWidth 64) }⟩ := by
  simp only [directives_ext32, xz, arun, List.foldl, A64.Flow.dstep, classify, RegOnly, AI.so, AI.step,
    AI.tgt, soReg, regDst, regRes, zrB, SO.write, SO.kill, SO.killZ, rm]
  simp [Operation.interp, MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64,
    Reg64s.getRegOrZr_X, Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, rm]

theorem arun_binAdd (lab : Label → Int64) (pc : Int64) (sp : Int) (σ : AS) :
    arun lab (directives (binOp .add)) ⟨pc, ⟨sp, []⟩, σ⟩ =
      ⟨pc + 4, ⟨sp, []⟩, { σ with regs := σ.regs.setXReg .X9 (σ.regs.X9.toBitVec + σ.regs.X10.toBitVec) }⟩ := by
  simp only [binOp, addReg, directives, List.filterMap, ins, xz, zr, rz, arun, List.foldl, A64.Flow.dstep,
    classify, RegOnly, AI.so, AI.step, AI.tgt, soReg, regDst, regRes, zrB, SO.write, SO.kill, SO.killZ, rm]
  simp [Operation.interp, MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64,
    Reg64s.getRegOrZr_X, Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, rm]

theorem arun_binMul (lab : Label → Int64) (pc : Int64) (sp : Int) (σ : AS) :
    arun lab (directives (binOp .mul)) ⟨pc, ⟨sp, []⟩, σ⟩ =
      ⟨pc + 4, ⟨sp, []⟩, { σ with regs := σ.regs.setXReg .X9 (σ.regs.X9.toBitVec * σ.regs.X10.toBitVec) }⟩ := by
  simp only [binOp, directives, List.filterMap, ins, xz, zr, rz, arun, List.foldl, A64.Flow.dstep,
    classify, RegOnly, AI.so, AI.step, AI.tgt, soReg, regDst, regRes, zrB, SO.write, SO.kill, SO.killZ, rm]
  simp [Operation.interp, MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64,
    Reg64s.getRegOrZr_X, Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, rm]

theorem arun_cmp (lab : Label → Int64) (pc : Int64) (sp : Int) (σ : AS) :
    ∃ st, st.c = decide (σ.regs.X10.toNat ≤ σ.regs.X9.toNat) ∧
      arun lab (directives [cmpReg .W64 .X9 .X10]) ⟨pc, ⟨sp, []⟩, σ⟩ = ⟨pc + 4, ⟨sp, []⟩, { σ with status := st }⟩ := by
  simp only [cmpReg, directives, List.filterMap, ins, xz, zr, rz, arun, List.foldl, A64.Flow.dstep,
    classify, RegOnly, AI.so, AI.step, AI.tgt, soReg, regDst, regRes, zrB, SO.write, SO.kill, SO.killZ, rm]
  simp [Operation.interp, MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64,
    Reg64s.getRegOrZr_X, Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, rm, StatusFlags.subs,
    StatusFlags.from_result]
  have h9 := UInt64.toNat_lt σ.regs.X9
  have h10 := UInt64.toNat_lt σ.regs.X10
  by_cases hle : σ.regs.X10.toNat ≤ σ.regs.X9.toNat
  · have : (((18446744073709551616 - σ.regs.X10.toNat : Nat) : Int) + (σ.regs.X9.toNat : Int)) =
        ((σ.regs.X9.toNat : Int) - σ.regs.X10.toNat) + 18446744073709551616 := by omega
    rw [this, Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]
    simp [hle]
  · have : (((18446744073709551616 - σ.regs.X10.toNat : Nat) : Int) + (σ.regs.X9.toNat : Int)) %
        18446744073709551616 = ((18446744073709551616 - σ.regs.X10.toNat : Nat) : Int) + σ.regs.X9.toNat :=
      Int.emod_eq_of_lt (by omega) (by omega)
    rw [this]
    simp only [hle, decide_false, beq_eq_false_iff_ne, ne_eq]
    omega

theorem arun_cselCC (lab : Label → Int64) (pc : Int64) (sp : Int) (σ : AS) :
    arun lab (directives [ins (.CSEL (xz .X9) (xz .X11) (xz .X12) (condCode .ult))]) ⟨pc, ⟨sp, []⟩, σ⟩ =
      ⟨pc + 4, ⟨sp, []⟩,
        { σ with regs := σ.regs.setXReg .X9 (if σ.status.c then σ.regs.X12.toBitVec else σ.regs.X11.toBitVec) }⟩ := by
  simp only [condCode, directives, List.filterMap, ins, xz, zr, rz, arun, List.foldl, A64.Flow.dstep,
    classify, RegOnly, AI.so, AI.step, AI.tgt, soReg, regDst, regRes, zrB, SO.write, SO.kill, SO.killZ, rm]
  simp [Operation.interp, MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64,
    Reg64s.getRegOrZr_X, Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, rm, CondCode.interp]
  cases σ.status.c <;> rfl

/-! ## The instructions' blocks -/

theorem exc_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

section Steps

variable {c : FnCtx} (hf : FrameOk c) (h1 : c.frame ≤ 4095)

theorem pc_add4 (pc : Int64) (a b : Nat) :
    pc + Int64.ofNat (4 * a) + Int64.ofNat (4 * b) = pc + Int64.ofNat (4 * (a + b)) := by
  rw [show 4 * (a + b) = 4 * a + 4 * b by omega, Int64.ofNat_add, Int64.add_assoc]

include hf h1 in
/-- **The store of `x9` into `d`'s slot** (`setReg d .X9`). -/
theorem arun_setReg9 {d : Scc.IR.Reg} {off : Int} (hd : c.slotOff d = .ok off) {l : List Item}
    (hl : c.setReg d .X9 = .ok l) (lab : Label → Int64) (pc : Int64) (σ : AS) :
    (directives l).length = 1 ∧
    arun lab (directives l) ⟨pc, oF c, σ⟩ =
      ⟨pc + 4, oF c, { σ with slot := upd σ.slot (off - c.frame) σ.regs.X9.toBitVec }⟩ := by
  rw [setReg_eq hf (by omega) hd] at hl
  cases hl
  obtain ⟨h0, h8, hle⟩ := slotOff_bounds hf hd
  have ho : (Int64.ofInt off).toInt = off := toInt_ofInt_small (by omega) (by omega)
  have hds : directives [ins (.STR (rz .W64 .X9) ⟨spW64, .imm ⟨i64 off, none⟩⟩)] =
      [spStr .X9 (Int64.ofInt off)] := rfl
  refine ⟨by rw [hds]; rfl, ?_⟩
  rw [hds]
  simp only [arun, List.foldl, oF]
  rw [dstep_spStr, ho, show -(c.frame : Int) + off = off - c.frame by omega]
  rfl

/-- The register file after loading `t`. -/
theorem setXReg_X9_X9 (r : Reg64s) (v : BitVec 64) : (r.setXReg .X9 v).X9.toBitVec = v := by
  simp [Reg64s.setXReg]

theorem pc_four (pc : Int64) (a : Nat) : pc + Int64.ofNat (4 * a) + 4 = pc + Int64.ofNat (4 * (a + 1)) := by
  rw [show 4 * (a + 1) = 4 * a + 4 by omega, Int64.ofNat_add, Int64.add_assoc]; rfl

include hf h1 in
/-- **The code of `ext false .w32 d o`**: `o`'s load into `x9`, `ubfm`, the
store into `d`'s slot; `d`'s slot gets `o`'s value's low 32 bits. -/
theorem ext32_step {k : Nat} {d : Scc.IR.Reg} {o : Scc.IR.Operand} {l : List Item}
    (h : c.inst k (.ext false .w32 d o) = .ok l) (lab : Label → Int64) (pc : Int64) (σ : AS) :
    ∃ off, c.slotOff d = .ok off ∧ ∃ vo : BitVec 64, opdVal (rsOf c) σ.slot o = some vo.toNat ∧ ∃ rg : Reg64s,
      arun lab (directives l) ⟨pc, oF c, σ⟩ =
        ⟨pc + Int64.ofNat (4 * (directives l).length), oF c,
          ⟨rg, σ.status, upd σ.slot (off - c.frame) ((vo.take 32).setWidth 64)⟩⟩ := by
  cases ha : c.getOp .X9 o <;> cases hd : c.slotOff d
  case ok.ok la off =>
    have hs := setReg_eq hf (by omega) hd .X9
    have hn := (arun_setReg9 hf h1 hd hs lab 0 σ).1
    have hst := fun pc σ => (arun_setReg9 hf h1 hd hs lab pc σ).2
    simp only [FnCtx.inst, ha, hs, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨vo, hvo, hr⟩ := arun_getOp hf h1 ha lab pc σ
    refine ⟨off, rfl, vo, hvo, ?_⟩
    rw [directives_append, directives_append, arun_append, arun_append]
    simp only [oF] at hst ⊢
    rw [hr, arun_ext32, hst]
    simp only [List.length_append, hn, directives_ext32, List.length_singleton, setXReg_X9_X9, pc_four]
    exact ⟨_, rfl⟩
  all_goals simp [FnCtx.inst, FnCtx.setReg, ha, hd, bind, Except.bind] at h

include hf h1 in
/-- **The code of `bin op d a b`** for `op ∈ {add, mul}`: the operands'
loads into `x9`, `x10`, the operation, the store into `d`'s slot. -/
theorem bin_step {k : Nat} {op : Scc.IR.BinOp} (hop : op = .add ∨ op = .mul) {d : Scc.IR.Reg}
    {a b : Scc.IR.Operand} {l : List Item}
    (h : c.inst k (.bin op d a b) = .ok l) (lab : Label → Int64) (pc : Int64) (σ : AS) :
    ∃ off, c.slotOff d = .ok off ∧ ∃ va vb : BitVec 64, opdVal (rsOf c) σ.slot a = some va.toNat ∧
      opdVal (rsOf c) σ.slot b = some vb.toNat ∧ ∃ rg : Reg64s,
      arun lab (directives l) ⟨pc, oF c, σ⟩ =
        ⟨pc + Int64.ofNat (4 * (directives l).length), oF c,
          ⟨rg, σ.status, upd σ.slot (off - c.frame) (if op = .add then va + vb else va * vb)⟩⟩ := by
  cases ha : c.getOp .X9 a <;> cases hb : c.getOp .X10 b <;> cases hd : c.slotOff d
  case ok.ok.ok la lb off =>
    have hs := setReg_eq hf (by omega) hd .X9
    have hn := (arun_setReg9 hf h1 hd hs lab 0 σ).1
    have hst := fun pc σ => (arun_setReg9 hf h1 hd hs lab pc σ).2
    simp only [FnCtx.inst, ha, hb, hs, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨va, hva, hra⟩ := arun_getOp hf h1 ha lab pc σ
    obtain ⟨vb, hvb, hrb⟩ := arun_getOp hf h1 hb lab (pc + Int64.ofNat (4 * (directives la).length))
      { σ with regs := σ.regs.setXReg .X9 va }
    refine ⟨off, rfl, va, vb, hva, hvb, ?_⟩
    simp only [directives_append, arun_append]
    simp only [oF] at hst ⊢
    rw [hra, hrb]
    have h9 : ((σ.regs.setXReg .X9 va).setXReg .X10 vb).X9.toBitVec = va := by simp [Reg64s.setXReg]
    have h10 : ((σ.regs.setXReg .X9 va).setXReg .X10 vb).X10.toBitVec = vb := by simp [Reg64s.setXReg]
    rcases hop with rfl | rfl
    · rw [arun_binAdd, hst]
      simp only [List.length_append, hn, binOp, directives, List.filterMap, ins, addReg, List.length_singleton,
        setXReg_X9_X9, h9, h10, pc_four, pc_add4, ite_true]
      simp only [← pc_add4, pc_four]
      exact ⟨_, rfl⟩
    · rw [arun_binMul, hst]
      simp only [List.length_append, hn, binOp, directives, List.filterMap, ins, List.length_singleton,
        setXReg_X9_X9, h9, h10, pc_four, pc_add4]
      simp only [← pc_add4, pc_four]
      exact ⟨_, rfl⟩
  all_goals simp [FnCtx.inst, FnCtx.setReg, ha, hb, hd, bind, Except.bind] at h

include hf h1 in
/-- **The code of `select .ult d a b t f`**: the operands' loads into
`x9`, `x10`, `cmp`, `t`'s and `f`'s into `x11`, `x12`, `csel lo`, the store
into `d`'s slot; `d`'s slot gets `t`'s value when `a`'s is below `b`'s,
else `f`'s. -/
theorem select_step {k : Nat} {d : Scc.IR.Reg} {a b t f : Scc.IR.Operand} {l : List Item}
    (h : c.inst k (.select .ult d a b t f) = .ok l) (lab : Label → Int64) (pc : Int64) (σ : AS) :
    ∃ off, c.slotOff d = .ok off ∧ ∃ va vb vt vf : BitVec 64, opdVal (rsOf c) σ.slot a = some va.toNat ∧
      opdVal (rsOf c) σ.slot b = some vb.toNat ∧ opdVal (rsOf c) σ.slot t = some vt.toNat ∧
      opdVal (rsOf c) σ.slot f = some vf.toNat ∧ ∃ (rg : Reg64s) (st : StatusFlags),
      arun lab (directives l) ⟨pc, oF c, σ⟩ =
        ⟨pc + Int64.ofNat (4 * (directives l).length), oF c,
          ⟨rg, st, upd σ.slot (off - c.frame) (if va.toNat < vb.toNat then vt else vf)⟩⟩ := by
  simp only [FnCtx.inst] at h
  obtain ⟨la, ha, h⟩ := exc_bind_ok h
  obtain ⟨lb, hb, h⟩ := exc_bind_ok h
  obtain ⟨lt, ht, h⟩ := exc_bind_ok h
  obtain ⟨lf, hfo, h⟩ := exc_bind_ok h
  obtain ⟨ls, hls, h⟩ := exc_bind_ok h
  have ⟨off, hd⟩ : ∃ off, c.slotOff d = .ok off := by
    cases hd : c.slotOff d
    · simp [FnCtx.setReg, hd, bind, Except.bind] at hls
    · exact ⟨_, rfl⟩
  · have hs := setReg_eq hf (by omega) hd .X9
    have hn := (arun_setReg9 hf h1 hd hs lab 0 σ).1
    have hst := fun pc σ => (arun_setReg9 hf h1 hd hs lab pc σ).2
    rw [hs] at hls
    cases hls
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨va, hva, hra⟩ := arun_getOp hf h1 ha lab pc σ
    obtain ⟨vb, hvb, hrb⟩ := arun_getOp hf h1 hb lab (pc + Int64.ofNat (4 * (directives la).length))
      { σ with regs := σ.regs.setXReg .X9 va }
    refine ⟨off, hd, va, vb, ?_⟩
    obtain ⟨st, hc, hcmp⟩ := arun_cmp lab (pc + Int64.ofNat (4 * (directives la).length) +
      Int64.ofNat (4 * (directives lb).length)) (-(c.frame : Int))
      { σ with regs := (σ.regs.setXReg .X9 va).setXReg .X10 vb }
    obtain ⟨vt, hvt, hrt⟩ := arun_getOp hf h1 ht lab (pc + Int64.ofNat (4 * (directives la).length) +
      Int64.ofNat (4 * (directives lb).length) + 4)
      { σ with regs := (σ.regs.setXReg .X9 va).setXReg .X10 vb, status := st }
    obtain ⟨vf, hvf, hrf⟩ := arun_getOp hf h1 hfo lab (pc + Int64.ofNat (4 * (directives la).length) +
      Int64.ofNat (4 * (directives lb).length) + 4 + Int64.ofNat (4 * (directives lt).length))
      { σ with regs := ((σ.regs.setXReg .X9 va).setXReg .X10 vb).setXReg .X11 vt, status := st }
    refine ⟨vt, vf, hva, hvb, hvt, hvf, ?_⟩
    simp only [directives_append, arun_append]
    simp only [oF] at hst ⊢
    rw [hra, hrb, hcmp, hrt, hrf, arun_cselCC, hst]
    have h9 : ((σ.regs.setXReg .X9 va).setXReg .X10 vb).X9.toNat = va.toNat := by simp [Reg64s.setXReg]
    have h10 : ((σ.regs.setXReg .X9 va).setXReg .X10 vb).X10.toNat = vb.toNat := by simp [Reg64s.setXReg]
    have h11 : ((((σ.regs.setXReg .X9 va).setXReg .X10 vb).setXReg .X11 vt).setXReg .X12 vf).X11.toBitVec = vt := by
      simp [Reg64s.setXReg]
    have h12 : ((((σ.regs.setXReg .X9 va).setXReg .X10 vb).setXReg .X11 vt).setXReg .X12 vf).X12.toBitVec = vf := by
      simp [Reg64s.setXReg]
    rw [h9, h10] at hc
    have hsel : (if st.c then vf else vt) = (if va.toNat < vb.toNat then vt else vf) := by
      rw [hc]; by_cases hlt : va.toNat < vb.toNat
      · simp [hlt, show ¬ vb.toNat ≤ va.toNat by omega]
      · simp [hlt, show vb.toNat ≤ va.toNat by omega]
    have l1 : (directives [cmpReg .W64 .X9 .X10]).length = 1 := rfl
    have l2 : (directives [ins (.CSEL (xz .X9) (xz .X11) (xz .X12) (condCode .ult))]).length = 1 := rfl
    simp only [h11, h12, hsel, setXReg_X9_X9, List.length_append, hn, l1, l2]
    simp only [← pc_add4, pc_four]
    exact ⟨_, _, rfl⟩

/-- **Two register arguments**: `a` into `x0`, `b` into `x1`. -/
theorem getArgs_two (a b : Scc.IR.Operand) :
    c.getArgs [a, b] = (do let la ← c.getOp .X0 a; let lb ← c.getOp .X1 b; return la ++ lb) := by
  have hr : argRegs = .X0 :: .X1 :: argRegs.drop 2 := rfl
  have hl : argRegs.length = 8 := rfl
  simp only [FnCtx.getArgs, hl]
  rw [hr]
  cases ha : c.getOp .X0 a <;> cases hb : c.getOp .X1 b <;>
    simp [ha, hb, bind, Except.bind, pure, Except.pure, forIn, ForIn.forIn]

/-- **Two call arguments**: no stack argument, `getArgs`. -/
theorem callArgs_two (a b : Scc.IR.Operand) (base : Nat) : c.callArgs [a, b] base = c.getArgs [a, b] := by
  cases hv : c.getArgs [a, b] <;>
    simp [FnCtx.callArgs, argRegs, xregs, Scc.IR.maxArgs, hv, bind, Except.bind, pure, Except.pure, forIn,
      ForIn.forIn] <;>
    rw [show (List.drop 8 [a, b]).zipIdx = ([] : List (Scc.IR.Operand × Nat)) from rfl] <;> rfl

include hf h1 in
/-- **The loads of two arguments** into `x0`, `x1`: the slots and flags
unchanged. -/
theorem args2_step {a b : Scc.IR.Operand} {l : List Item} (h : c.getArgs [a, b] = .ok l)
    (lab : Label → Int64) (pc : Int64) (σ : AS) :
    ∃ va vb : BitVec 64, opdVal (rsOf c) σ.slot a = some va.toNat ∧ opdVal (rsOf c) σ.slot b = some vb.toNat ∧
      ∃ rg : Reg64s, rg.X0.toBitVec = va ∧ rg.X1.toBitVec = vb ∧
      arun lab (directives l) ⟨pc, oF c, σ⟩ =
        ⟨pc + Int64.ofNat (4 * (directives l).length), oF c, ⟨rg, σ.status, σ.slot⟩⟩ := by
  rw [getArgs_two] at h
  cases ha : c.getOp .X0 a <;> cases hb : c.getOp .X1 b
  case ok.ok la lb =>
    simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨va, hva, hra⟩ := arun_getOp hf h1 ha lab pc σ
    obtain ⟨vb, hvb, hrb⟩ := arun_getOp hf h1 hb lab (pc + Int64.ofNat (4 * (directives la).length))
      { σ with regs := σ.regs.setXReg .X0 va }
    refine ⟨va, vb, hva, hvb, (σ.regs.setXReg .X0 va).setXReg .X1 vb, by simp [Reg64s.setXReg],
      by simp [Reg64s.setXReg], ?_⟩
    simp only [directives_append, arun_append, oF]
    rw [hra, hrb, List.length_append, pc_add4]
  all_goals simp [ha, hb, bind, Except.bind] at h

end Steps

/-! ## `print`'s argument block -/

section PrintArgs

variable {c : FnCtx} (hf : FrameOk c) (h1 : c.frame ≤ 4095)

/-- A slot write leaves every operand on another register. -/
theorem opdVal_updOff {d : Scc.IR.Reg} {off : Int} (hd : c.slotOff d = .ok off) {a : Scc.IR.Operand}
    (ha : ∀ r, a = .reg r → r ≠ d) (sl : Int → BitVec 64) (v : BitVec 64) :
    opdVal (rsOf c) (upd sl (off - c.frame) v) a = opdVal (rsOf c) sl a := by
  cases a with
  | imm => rfl
  | reg r =>
    simp only [opdVal]
    cases hr : rsOf c r with
    | none => rfl
    | some j =>
      simp only [Option.map_some, Option.some.injEq, upd_apply]
      split
      · rename_i hj
        exact absurd (rsOf_inj hr (by simp [rsOf, hd, hj])) (ha r rfl)
      · rfl

/-- A slot write is read back. -/
theorem opdVal_updSelf {d : Scc.IR.Reg} {off : Int} (hd : c.slotOff d = .ok off) (sl : Int → BitVec 64)
    (v : BitVec 64) : opdVal (rsOf c) (upd sl (off - c.frame) v) (.reg d) = some v.toNat := by
  simp [opdVal, rsOf, hd, upd_apply]

theorem toNat_some_inj {x y : BitVec 64} (h : some x.toNat = some y.toNat) : x = y :=
  BitVec.eq_of_toNat_eq (Option.some.inj h)

include hf h1 in
/-- **`print`'s count and the call's arguments**: `cap := m · 8`,
`k := select (n < cap) n cap`, then `s`, `k` into `x0`, `x1`, for any
caller's frame and any operands `s`, `m`, `n` (each `opdVal` at the
caller's slots) of fresh registers `cap`, `k`: `x0` is `s`'s value and `x1`
is `min(n, 8·m)` (unsigned, wrapping); the code falls through, the static
offsets and every slot but `cap`'s and `k`'s kept. -/
theorem printK_run {i3 i4 : Nat} {cap kk : Scc.IR.Reg} {s m n : Scc.IR.Operand} {l3 l4 l5 : List Item}
    (c3 : c.inst i3 (.bin .mul cap m (Scc.Lower.imm 8)) = .ok l3)
    (c4 : c.inst i4 (.select .ult kk n (.reg cap) n (.reg cap)) = .ok l4)
    (c5 : c.getArgs [s, .reg kk] = .ok l5)
    (hn : ∀ r, n = .reg r → r ≠ cap) (hs : ∀ r, s = .reg r → r ≠ cap ∧ r ≠ kk)
    (lab : Label → Int64) (pc : Int64) (σ : AS) :
    ∃ vs vm vn : BitVec 64, opdVal (rsOf c) σ.slot s = some vs.toNat ∧
      opdVal (rsOf c) σ.slot m = some vm.toNat ∧ opdVal (rsOf c) σ.slot n = some vn.toNat ∧
      ∃ (rg : Reg64s) (st : StatusFlags) (sl : Int → BitVec 64),
        rg.X0.toBitVec = vs ∧
        rg.X1.toBitVec = (if vn.toNat < (vm * 8#64).toNat then vn else vm * 8#64) ∧
        arun lab (directives (l3 ++ l4 ++ l5)) ⟨pc, oF c, σ⟩ =
          ⟨pc + Int64.ofNat (4 * (directives (l3 ++ l4 ++ l5)).length), oF c, ⟨rg, st, sl⟩⟩ ∧
        ∀ j, (∀ q, rsOf c q = some j → q ≠ cap ∧ q ≠ kk) → sl j = σ.slot j := by
  obtain ⟨ocap, hcap, vm, v8, hvm, hv8, rg3, e3⟩ := bin_step hf h1 (.inr rfl) c3 lab pc σ
  simp only [show (Scc.IR.BinOp.mul = Scc.IR.BinOp.add) = False from by simp, ite_false] at e3
  obtain ⟨okk, hkk, vn, vc, vn', vc', hvn, hvc, hvn', hvc', rg4, st4, e4⟩ := select_step hf h1 c4 lab
    (pc + Int64.ofNat (4 * (directives l3).length)) ⟨rg3, σ.status, upd σ.slot (ocap - c.frame) (vm * v8)⟩
  obtain ⟨vs, vk, hvs, hvk, rg5, hx0, hx1, e5⟩ := args2_step hf h1 c5 lab
    (pc + Int64.ofNat (4 * (directives l3).length) + Int64.ofNat (4 * (directives l4).length))
    ⟨rg4, st4, upd (upd σ.slot (ocap - c.frame) (vm * v8)) (okk - c.frame) (if vn.toNat < vc.toNat then vn' else vc')⟩
  have ev8 : v8 = 8#64 := by
    simp only [opdVal, Scc.Lower.imm] at hv8
    exact (BitVec.eq_of_toNat_eq (Option.some.inj hv8)).symm ▸ rfl
  rw [opdVal_updOff hcap hn] at hvn hvn'
  have evn := toNat_some_inj (hvn'.symm.trans hvn)
  rw [opdVal_updSelf hcap] at hvc hvc'
  have evc := toNat_some_inj hvc
  have evc' := toNat_some_inj hvc'
  rw [opdVal_updOff hkk (fun r h => (hs r h).2), opdVal_updOff hcap (fun r h => (hs r h).1)] at hvs
  rw [opdVal_updSelf hkk] at hvk
  have evk := toNat_some_inj hvk
  refine ⟨vs, vm, vn, hvs, hvm, hvn, rg5, st4,
    upd (upd σ.slot (ocap - c.frame) (vm * v8)) (okk - c.frame) (if vn.toNat < vc.toNat then vn' else vc'),
    hx0, ?_, ?_, ?_⟩
  · rw [hx1, ← evk, ← evn, ← evc, ← evc', ev8]
  · simp only [directives_append, arun_append]
    rw [e3, e4, e5]
    simp only [List.length_append, pc_add4]
  · intro j hj
    have ne : ∀ q off, c.slotOff q = .ok off → (∀ q', rsOf c q' = some j → q' ≠ q) → ¬ j = off - c.frame :=
      fun q off hq h hj' => h q (by simp [rsOf, hq, hj']) rfl
    simp only [upd_apply, ne _ _ hkk fun q h => (hj q h).2, ne _ _ hcap fun q h => (hj q h).1, ↓reduceIte]

/-- A slot write keeps the slots off the written one. -/
theorem upd_off {d : Scc.IR.Reg} {off : Int} (hd : c.slotOff d = .ok off) {j : Int}
    (hj : ∀ q, rsOf c q = some j → q ≠ d) (sl : Int → BitVec 64) (v : BitVec 64) :
    upd sl (off - c.frame) v j = sl j := by
  have : ¬ j = off - c.frame := fun hj' => hj d (by simp [rsOf, hd, hj']) rfl
  simp only [upd_apply, this, ↓reduceIte]

include hf h1 in
/-- **`print`'s argument block** (`callBlock`'s `.print` case, a register
offset `o`): `lo := ext.w32 o`, `s := b + lo`, then `printK_run`: `x0` is
`b + lo(o)` and `x1` is `min(n, 8·m)` (unsigned, wrapping), for any
caller's frame and any operands `b`, `o`, `m`, `n` of fresh registers
`lo`, `s`, `cap`, `k`; every other slot kept. -/
theorem printArgs_run {i1 i2 i3 i4 : Nat} {lo s cap kk : Scc.IR.Reg} {b o m n : Scc.IR.Operand}
    {l1 l2 l3 l4 l5 : List Item}
    (c1 : c.inst i1 (.ext false .w32 lo o) = .ok l1) (c2 : c.inst i2 (.bin .add s b (.reg lo)) = .ok l2)
    (c3 : c.inst i3 (.bin .mul cap m (Scc.Lower.imm 8)) = .ok l3)
    (c4 : c.inst i4 (.select .ult kk n (.reg cap) n (.reg cap)) = .ok l4)
    (c5 : c.getArgs [.reg s, .reg kk] = .ok l5)
    (hb : ∀ r, b = .reg r → r ≠ lo) (hm : ∀ r, m = .reg r → r ≠ lo ∧ r ≠ s)
    (hn : ∀ r, n = .reg r → r ≠ lo ∧ r ≠ s ∧ r ≠ cap) (hsc : s ≠ cap) (hsk : s ≠ kk)
    (lab : Label → Int64) (pc : Int64) (σ : AS) :
    ∃ vb vo vm vn : BitVec 64, opdVal (rsOf c) σ.slot b = some vb.toNat ∧
      opdVal (rsOf c) σ.slot o = some vo.toNat ∧ opdVal (rsOf c) σ.slot m = some vm.toNat ∧
      opdVal (rsOf c) σ.slot n = some vn.toNat ∧
      ∃ (rg : Reg64s) (st : StatusFlags) (sl : Int → BitVec 64),
        rg.X0.toBitVec = vb + (vo.take 32).setWidth 64 ∧
        rg.X1.toBitVec = (if vn.toNat < (vm * 8#64).toNat then vn else vm * 8#64) ∧
        arun lab (directives (l1 ++ l2 ++ l3 ++ l4 ++ l5)) ⟨pc, oF c, σ⟩ =
          ⟨pc + Int64.ofNat (4 * (directives (l1 ++ l2 ++ l3 ++ l4 ++ l5)).length), oF c, ⟨rg, st, sl⟩⟩ ∧
        ∀ j, (∀ q, rsOf c q = some j → q ≠ lo ∧ q ≠ s ∧ q ≠ cap ∧ q ≠ kk) → sl j = σ.slot j := by
  obtain ⟨olo, hlo, vo, hvo, rg1, e1⟩ := ext32_step hf h1 c1 lab pc σ
  obtain ⟨os, hs, vb, vl, hvb, hvl, rg2, e2⟩ := bin_step hf h1 (.inl rfl) c2 lab
    (pc + Int64.ofNat (4 * (directives l1).length))
    ⟨rg1, σ.status, upd σ.slot (olo - c.frame) ((vo.take 32).setWidth 64)⟩
  simp only [ite_true] at e2
  obtain ⟨vs, vm, vn, hvs, hvm, hvn, rg, st, sl, hx0, hx1, e, hsl⟩ := printK_run hf h1 c3 c4 c5
    (fun r h => (hn r h).2.2) (fun r h => by cases h; exact ⟨hsc, hsk⟩) lab
    (pc + Int64.ofNat (4 * (directives l1).length) + Int64.ofNat (4 * (directives l2).length))
    ⟨rg2, σ.status, upd (upd σ.slot (olo - c.frame) ((vo.take 32).setWidth 64)) (os - c.frame) (vb + vl)⟩
  rw [opdVal_updOff hlo hb] at hvb
  rw [opdVal_updSelf hlo] at hvl
  have evl := toNat_some_inj hvl
  rw [opdVal_updOff hs (fun r h => (hm r h).2), opdVal_updOff hlo (fun r h => (hm r h).1)] at hvm
  rw [opdVal_updOff hs (fun r h => (hn r h).2.1), opdVal_updOff hlo (fun r h => (hn r h).1)] at hvn
  rw [opdVal_updSelf hs] at hvs
  have evs := toNat_some_inj hvs
  refine ⟨vb, vo, vm, vn, hvb, hvo, hvm, hvn, rg, st, sl, by rw [hx0, ← evs, ← evl], hx1, ?_, ?_⟩
  · have hl : directives (l1 ++ l2 ++ l3 ++ l4 ++ l5) = directives l1 ++ directives l2 ++
        directives (l3 ++ l4 ++ l5) := by simp only [directives_append, List.append_assoc]
    rw [hl, arun_append, arun_append, e1, e2, e]
    simp only [directives_append, List.length_append, pc_add4, Nat.add_assoc]
  · intro j hj
    rw [hsl j fun q h => ⟨(hj q h).2.2.1, (hj q h).2.2.2⟩]
    show upd (upd σ.slot _ _) _ _ j = _
    rw [upd_off hs fun q h => (hj q h).2.1, upd_off hlo fun q h => (hj q h).1]

include hf h1 in
/-- **`print`'s argument block at an immediate offset `w ≠ 0`** on a
register base (`offAdd b (.imm w)`): `s := b + w`, then `printK_run`. -/
theorem printArgsImm_run {i2 i3 i4 : Nat} {s cap kk : Scc.IR.Reg} {b m n : Scc.IR.Operand} {w : UInt64}
    {l2 l3 l4 l5 : List Item}
    (c2 : c.inst i2 (.bin .add s b (.imm w)) = .ok l2)
    (c3 : c.inst i3 (.bin .mul cap m (Scc.Lower.imm 8)) = .ok l3)
    (c4 : c.inst i4 (.select .ult kk n (.reg cap) n (.reg cap)) = .ok l4)
    (c5 : c.getArgs [.reg s, .reg kk] = .ok l5)
    (hm : ∀ r, m = .reg r → r ≠ s) (hn : ∀ r, n = .reg r → r ≠ s ∧ r ≠ cap) (hsc : s ≠ cap) (hsk : s ≠ kk)
    (lab : Label → Int64) (pc : Int64) (σ : AS) :
    ∃ vb vm vn : BitVec 64, opdVal (rsOf c) σ.slot b = some vb.toNat ∧
      opdVal (rsOf c) σ.slot m = some vm.toNat ∧ opdVal (rsOf c) σ.slot n = some vn.toNat ∧
      ∃ (rg : Reg64s) (st : StatusFlags) (sl : Int → BitVec 64),
        rg.X0.toBitVec = vb + w.toBitVec ∧
        rg.X1.toBitVec = (if vn.toNat < (vm * 8#64).toNat then vn else vm * 8#64) ∧
        arun lab (directives (l2 ++ l3 ++ l4 ++ l5)) ⟨pc, oF c, σ⟩ =
          ⟨pc + Int64.ofNat (4 * (directives (l2 ++ l3 ++ l4 ++ l5)).length), oF c, ⟨rg, st, sl⟩⟩ ∧
        ∀ j, (∀ q, rsOf c q = some j → q ≠ s ∧ q ≠ cap ∧ q ≠ kk) → sl j = σ.slot j := by
  obtain ⟨os, hs, vb, vw, hvb, hvw, rg2, e2⟩ := bin_step hf h1 (.inl rfl) c2 lab pc σ
  simp only [ite_true] at e2
  obtain ⟨vs, vm, vn, hvs, hvm, hvn, rg, st, sl, hx0, hx1, e, hsl⟩ := printK_run hf h1 c3 c4 c5
    (fun r h => (hn r h).2) (fun r h => by cases h; exact ⟨hsc, hsk⟩) lab
    (pc + Int64.ofNat (4 * (directives l2).length)) ⟨rg2, σ.status, upd σ.slot (os - c.frame) (vb + vw)⟩
  have evw : vw = w.toBitVec := by
    simp only [opdVal] at hvw
    exact BitVec.eq_of_toNat_eq (by rw [← Option.some.inj hvw]; rfl)
  rw [opdVal_updOff hs hm] at hvm
  rw [opdVal_updOff hs (fun r h => (hn r h).1)] at hvn
  rw [opdVal_updSelf hs] at hvs
  have evs := toNat_some_inj hvs
  refine ⟨vb, vm, vn, hvb, hvm, hvn, rg, st, sl, by rw [hx0, ← evs, evw], hx1, ?_, ?_⟩
  · have hl : directives (l2 ++ l3 ++ l4 ++ l5) = directives l2 ++ directives (l3 ++ l4 ++ l5) := by
      simp only [directives_append, List.append_assoc]
    rw [hl, arun_append, e2, e]
    simp only [directives_append, List.length_append, pc_add4, Nat.add_assoc]
  · intro j hj
    rw [hsl j fun q h => ⟨(hj q h).2.1, (hj q h).2.2⟩]
    show upd σ.slot _ _ j = _
    rw [upd_off hs fun q h => (hj q h).1]

/-- **The code of a call of `print`** (`call [] print [s, k]`): `s`'s and
`k`'s loads into `x0`, `x1`, `bl scc_rt_print`, then the stack-map label
when the function places them. -/
theorem inst_print_call {i : Nat} {s k : Scc.IR.Operand} {l : List Item}
    (h : c.inst i (.call [] Scc.Lower.Names.print [s, k]) = .ok l) :
    ∃ la, c.getArgs [s, k] = .ok la ∧
      l = la ++ [call Scc.Lower.Names.print] ++ (if c.maps then [lbl (c.local s!"sp{i}")] else []) := by
  simp only [FnCtx.inst, callArgs_two] at h
  have hok : labelOk Scc.Lower.Names.print = true := by decide
  simp only [hok, ↓reduceIte] at h
  obtain ⟨la, ha, h⟩ := exc_bind_ok h
  refine ⟨la, ha, ?_⟩
  simp [FnCtx.setResults, Scc.IR.maxRets, bind, Except.bind, pure, Except.pure, forIn, ForIn.forIn] at h
  subst h
  simp only [List.append_assoc, List.singleton_append]
  rfl

end PrintArgs

/-! ## Coverage -/

theorem okBlk_ext32 {lo hi sp : Int} (ds : List Directive) :
    okBlk lo hi ⟨sp, []⟩ (directives (extOp false .w32) ++ ds) = okBlk lo hi ⟨sp, []⟩ ds := by
  simp [directives_ext32, xz, okBlk, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg, regDst, zrB,
    SO.write, SO.kill, SO.killZ, rm]

theorem okBlk_binAdd {lo hi sp : Int} (ds : List Directive) :
    okBlk lo hi ⟨sp, []⟩ (directives (binOp .add) ++ ds) = okBlk lo hi ⟨sp, []⟩ ds := by
  simp [binOp, addReg, directives, ins, xz, zr, rz, okBlk, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg,
    regDst, zrB, SO.write, SO.kill, SO.killZ, rm]

theorem okBlk_binMul {lo hi sp : Int} (ds : List Directive) :
    okBlk lo hi ⟨sp, []⟩ (directives (binOp .mul) ++ ds) = okBlk lo hi ⟨sp, []⟩ ds := by
  simp [binOp, directives, ins, xz, zr, rz, okBlk, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg,
    regDst, zrB, SO.write, SO.kill, SO.killZ, rm]

theorem okBlk_cmp {lo hi sp : Int} (ds : List Directive) :
    okBlk lo hi ⟨sp, []⟩ (directives [cmpReg .W64 .X9 .X10] ++ ds) = okBlk lo hi ⟨sp, []⟩ ds := by
  simp [cmpReg, directives, ins, xz, zr, rz, okBlk, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg,
    regDst, zrB, SO.write, SO.kill, SO.killZ, rm]

theorem okBlk_csel {lo hi sp : Int} (ds : List Directive) :
    okBlk lo hi ⟨sp, []⟩ (directives [ins (.CSEL (xz .X9) (xz .X11) (xz .X12) (condCode .ult))] ++ ds) =
      okBlk lo hi ⟨sp, []⟩ ds := by
  simp [condCode, directives, ins, xz, zr, rz, okBlk, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg,
    regDst, zrB, SO.write, SO.kill, SO.killZ, rm]


section Cover

variable {c : FnCtx} (hf : FrameOk c) (h1 : c.frame ≤ 4095) (h16 : c.frame % 16 = 0)

include hf h1 h16 in
/-- **The store of `x9` into `d`'s slot is covered** in the frame `[-frame, 0)`. -/
theorem okBlk_setReg9 {d : Scc.IR.Reg} {off : Int} (hd : c.slotOff d = .ok off) {l : List Item}
    (hl : c.setReg d .X9 = .ok l) (ds : List Directive) :
    okBlk (-(c.frame : Int)) 0 ⟨-(c.frame : Int), []⟩ (directives l ++ ds) =
      okBlk (-(c.frame : Int)) 0 ⟨-(c.frame : Int), []⟩ ds := by
  rw [setReg_eq hf (by omega) hd] at hl
  cases hl
  obtain ⟨h0, h8, hle⟩ := slotOff_bounds hf hd
  have ho : (Int64.ofInt off).toInt = off := toInt_ofInt_small (by omega) (by omega)
  have hds : directives [ins (.STR (rz .W64 .X9) ⟨spW64, .imm ⟨i64 off, none⟩⟩)] =
      [spStr .X9 (Int64.ofInt off)] := rfl
  have hc : classify (spStr .X9 (Int64.ofInt off)) = some (AI.str (.low (.reg .X9) .W64) (Int64.ofInt off)) := rfl
  have h16' : (-(c.frame : Int)) % 16 = 0 := by omega
  rw [hds, List.singleton_append]
  simp [okBlk, hc, AI.ok, AI.so, AI.isTerm, ho, offOk, h16']
  intro _; omega

include hf h1 h16 in
/-- **The code of `ext false .w32 d o` is covered.** -/
theorem okBlk_inst_ext32 {k : Nat} {d : Scc.IR.Reg} {o : Scc.IR.Operand} {l : List Item}
    (h : c.inst k (.ext false .w32 d o) = .ok l) (ds : List Directive) :
    okBlk (-(c.frame : Int)) 0 ⟨-(c.frame : Int), []⟩ (directives l ++ ds) =
      okBlk (-(c.frame : Int)) 0 ⟨-(c.frame : Int), []⟩ ds := by
  simp only [FnCtx.inst] at h
  obtain ⟨la, ha, h⟩ := exc_bind_ok h
  obtain ⟨ls, hls, h⟩ := exc_bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have ⟨off, hd⟩ : ∃ off, c.slotOff d = .ok off := by
    cases hd : c.slotOff d
    · simp [FnCtx.setReg, hd, bind, Except.bind] at hls
    · exact ⟨_, rfl⟩
  simp only [directives_append, List.append_assoc]
  rw [okBlk_getOp hf h1 h16 ha, okBlk_ext32, okBlk_setReg9 hf h1 h16 hd hls]

include hf h1 h16 in
/-- **The code of `bin op d a b` is covered** for `op ∈ {add, mul}`. -/
theorem okBlk_inst_bin {k : Nat} {op : Scc.IR.BinOp} (hop : op = .add ∨ op = .mul) {d : Scc.IR.Reg}
    {a b : Scc.IR.Operand} {l : List Item} (h : c.inst k (.bin op d a b) = .ok l) (ds : List Directive) :
    okBlk (-(c.frame : Int)) 0 ⟨-(c.frame : Int), []⟩ (directives l ++ ds) =
      okBlk (-(c.frame : Int)) 0 ⟨-(c.frame : Int), []⟩ ds := by
  rcases hop with rfl | rfl <;>
  · simp only [FnCtx.inst] at h
    obtain ⟨la, ha, h⟩ := exc_bind_ok h
    obtain ⟨lb, hb, h⟩ := exc_bind_ok h
    obtain ⟨ls, hls, h⟩ := exc_bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have ⟨off, hd⟩ : ∃ off, c.slotOff d = .ok off := by
      cases hd : c.slotOff d
      · simp [FnCtx.setReg, hd, bind, Except.bind] at hls
      · exact ⟨_, rfl⟩
    simp only [directives_append, List.append_assoc]
    rw [okBlk_getOp hf h1 h16 ha, okBlk_getOp hf h1 h16 hb]
    first | rw [okBlk_binAdd, okBlk_setReg9 hf h1 h16 hd hls] | rw [okBlk_binMul, okBlk_setReg9 hf h1 h16 hd hls]

include hf h1 h16 in
/-- **The code of `select .ult d a b t f` is covered.** -/
theorem okBlk_inst_select {k : Nat} {d : Scc.IR.Reg} {a b t f : Scc.IR.Operand} {l : List Item}
    (h : c.inst k (.select .ult d a b t f) = .ok l) (ds : List Directive) :
    okBlk (-(c.frame : Int)) 0 ⟨-(c.frame : Int), []⟩ (directives l ++ ds) =
      okBlk (-(c.frame : Int)) 0 ⟨-(c.frame : Int), []⟩ ds := by
  simp only [FnCtx.inst] at h
  obtain ⟨la, ha, h⟩ := exc_bind_ok h
  obtain ⟨lb, hb, h⟩ := exc_bind_ok h
  obtain ⟨lt, ht, h⟩ := exc_bind_ok h
  obtain ⟨lf, hfo, h⟩ := exc_bind_ok h
  obtain ⟨ls, hls, h⟩ := exc_bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have ⟨off, hd⟩ : ∃ off, c.slotOff d = .ok off := by
    cases hd : c.slotOff d
    · simp [FnCtx.setReg, hd, bind, Except.bind] at hls
    · exact ⟨_, rfl⟩
  simp only [directives_append, List.append_assoc]
  rw [okBlk_getOp hf h1 h16 ha, okBlk_getOp hf h1 h16 hb, okBlk_cmp, okBlk_getOp hf h1 h16 ht,
    okBlk_getOp hf h1 h16 hfo, okBlk_csel, okBlk_setReg9 hf h1 h16 hd hls]

include hf h1 h16 in
/-- **The loads of two arguments are covered.** -/
theorem okBlk_args2 {a b : Scc.IR.Operand} {l : List Item} (h : c.getArgs [a, b] = .ok l)
    (ds : List Directive) :
    okBlk (-(c.frame : Int)) 0 ⟨-(c.frame : Int), []⟩ (directives l ++ ds) =
      okBlk (-(c.frame : Int)) 0 ⟨-(c.frame : Int), []⟩ ds := by
  rw [getArgs_two] at h
  obtain ⟨la, ha, h⟩ := exc_bind_ok h
  obtain ⟨lb, hb, h⟩ := exc_bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  simp only [directives_append, List.append_assoc]
  rw [okBlk_getOp hf h1 h16 ha, okBlk_getOp hf h1 h16 hb]

include hf h1 h16 in
/-- **`print`'s argument block is covered** in the frame `[-frame, 0)` at
the body's offsets (`printArgs_run`'s code). -/
theorem okBlk_printArgs {i1 i2 i3 i4 : Nat} {lo s cap kk : Scc.IR.Reg} {b o m n : Scc.IR.Operand}
    {l1 l2 l3 l4 l5 : List Item}
    (c1 : c.inst i1 (.ext false .w32 lo o) = .ok l1) (c2 : c.inst i2 (.bin .add s b (.reg lo)) = .ok l2)
    (c3 : c.inst i3 (.bin .mul cap m (Scc.Lower.imm 8)) = .ok l3)
    (c4 : c.inst i4 (.select .ult kk n (.reg cap) n (.reg cap)) = .ok l4)
    (c5 : c.getArgs [.reg s, .reg kk] = .ok l5) :
    okBlk (-(c.frame : Int)) 0 (oF c) (directives (l1 ++ l2 ++ l3 ++ l4 ++ l5)) = true := by
  simp only [oF, directives_append, List.append_assoc]
  rw [okBlk_inst_ext32 hf h1 h16 c1, okBlk_inst_bin hf h1 h16 (.inl rfl) c2, okBlk_inst_bin hf h1 h16 (.inr rfl) c3,
    okBlk_inst_select hf h1 h16 c4, ← List.append_nil (directives l5), okBlk_args2 hf h1 h16 c5]
  rfl

include hf h1 h16 in
/-- **`print`'s argument block at an immediate offset is covered**
(`printArgsImm_run`'s code). -/
theorem okBlk_printArgsImm {i2 i3 i4 : Nat} {s cap kk : Scc.IR.Reg} {b m n : Scc.IR.Operand} {w : UInt64}
    {l2 l3 l4 l5 : List Item}
    (c2 : c.inst i2 (.bin .add s b (.imm w)) = .ok l2)
    (c3 : c.inst i3 (.bin .mul cap m (Scc.Lower.imm 8)) = .ok l3)
    (c4 : c.inst i4 (.select .ult kk n (.reg cap) n (.reg cap)) = .ok l4)
    (c5 : c.getArgs [.reg s, .reg kk] = .ok l5) :
    okBlk (-(c.frame : Int)) 0 (oF c) (directives (l2 ++ l3 ++ l4 ++ l5)) = true := by
  simp only [oF, directives_append, List.append_assoc]
  rw [okBlk_inst_bin hf h1 h16 (.inl rfl) c2, okBlk_inst_bin hf h1 h16 (.inr rfl) c3,
    okBlk_inst_select hf h1 h16 c4, ← List.append_nil (directives l5), okBlk_args2 hf h1 h16 c5]
  rfl

end Cover

end Spike.Lib.LowerA64
