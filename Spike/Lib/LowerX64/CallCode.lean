/-
**The code of an `Accepted1` call's depth bracket** (x86-64), symbolic in
the frame, the IR registers' slots, the pc and the cell sizes, in the style
of `Spike/Lib/LowerX64/Construct1.lean`: what `emitInst`/`emitTerm` write for
the instructions of `depthPre`, `depthTerm`, `deepBlock` and `callPost`
(`Scc/Lower/InvC1.lean`), and the frame-local runs of the parts the block
model covers (`classify`).

- `emitInst_getTp`: `getTp d` is `movq %fs:0, %rax` then `%rax` into `d`;
- `emitInst_load64`, `emitInst_store64`: a 64-bit load or store through an
  IR register's address is its base into `%rcx`, then `movq disp(%rcx),
  %rax` and `%rax` into `d`, or the value into `%rax` and `movq %rax,
  disp(%rcx)`;
- `emitInst_bin_add`, `addItems`, `okBlk_add`, `arun_add`: the depth's bump
  `add d a b` (no carry check) is the operand loads, `addq %rcx, %rax`, the
  store;
- `emitTerm_br`, `cmpJcc`, `arun_cmpJa`, `brU_block`: any `br c a b t f` is
  the operand loads, `cmpq %rcx, %rax`, `j<cc c>` to `t`'s label, `jmp` to
  `f`'s; with `.ugt` (`ja`) the first block branches exactly when the first
  operand's value is above the second's;
- `emitInst_call0`, `emitInst_call1`: a call of one register argument and at
  most one result is the argument into `%rdi`, `call f`, the safepoint
  (a label when the frame records maps), then the result from `%rax`;
- `emitTerm_unreachable`: `ud2`.

The `%fs:0` read and the accesses through the thread pointer's cell
(`64(%rcx)`) are not frame-local: their segments are memory-level
(`fsld_ndW`, `ownLd_ndW`, `rtst_ndW`).
-/
import Spike.Lib.LowerX64.Construct1

namespace Spike.Lib.LowerX64

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Emit.X64 (S E Item ld st i64 xr xm om or_ mem emitInst emitTerm ins cmpAB cc labelOf jmpTo movFs
  callSym safepoint callArgs loadArgs ud2)
open Scc.Lower.InvX64
open Spike.Lib.Form (opdVal)

set_option linter.unusedSimpArgs false

/-! ## The thread pointer and its cell -/

/-- **The code of `getTp d`**: `movq %fs:0, %rax`, `%rax` into `d`. -/
theorem emitInst_getTp (fr : Scc.Emit.X64.Frame) (sm : Option Scc.IR.StackMap.Entry) (d : Scc.IR.Reg) :
    emitInst fr sm (.getTp d) = (do movFs .rax Scc.IR.Tcb.self; st fr .rax d) := rfl

/-- **The code of a 64-bit load** `d := [a.base + a.disp]`: the base into
`%rcx`, `movq disp(%rcx), %rax`, `%rax` into `d`. -/
theorem emitInst_load64 (fr : Scc.Emit.X64.Frame) (sm : Option Scc.IR.StackMap.Entry) (k : Scc.IR.Order)
    (d : Scc.IR.Reg) (a : Scc.IR.Addr) :
    emitInst fr sm (.load k .w64 d a) = (do
      ld fr (.reg a.base) .rcx
      ins (i64 (.mov (xr .rax) (om (mem .rcx a.disp))))
      st fr .rax d) := rfl

/-- **The code of a 64-bit store** `[a.base + a.disp] := v`: the base into
`%rcx`, `v` into `%rax`, `movq %rax, disp(%rcx)`. -/
theorem emitInst_store64 (fr : Scc.Emit.X64.Frame) (sm : Option Scc.IR.StackMap.Entry) (k : Scc.IR.Order)
    (a : Scc.IR.Addr) (v : Scc.IR.Operand) :
    emitInst fr sm (.store k .w64 a v) = (do
      ld fr (.reg a.base) .rcx
      ld fr v .rax
      ins (i64 (.mov (xm (mem .rcx a.disp)) (or_ .rax)))) := rfl

/-! ## The depth's bump: `add` without a carry check -/

/-- **The code of `add d a b`**: `a` into `%rax`, `b` into `%rcx`, `addq
%rcx, %rax`, `%rax` into `d`. -/
theorem emitInst_bin_add (fr : Scc.Emit.X64.Frame) (sm : Option Scc.IR.StackMap.Entry) (d : Scc.IR.Reg)
    (a b : Scc.IR.Operand) :
    emitInst fr sm (.bin .add d a b) = (do
      ld fr a .rax; ld fr b .rcx
      ins (i64 (.add (xr .rax) (or_ .rcx)))
      st fr .rax d) := rfl

/-- `addq %rcx, %rax` (`emitInst_bin_add`, after the operand loads). -/
def addItems : List Item := [.d (i64 (.add (xr .rax) (or_ .rcx)))]

theorem dirs_add : dirs addItems = [i64 (.add (xr .rax) (or_ .rcx))] := rfl

theorem okBlk_add {lo hi : Int} {o : SO} (ho : o.kill .rax = o) {z : Nat} :
    okBlk lo hi o ((dirs addItems).zip [z]) = true := by
  simp [dirs_add, okBlk, i64, Scc.Emit.X64.op, xr, or_, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg,
    regDst, SO.write, Reg.base, ho]

/-- **`addq %rcx, %rax`'s run**: `rax := rax + rcx` (wrapping), past its
cell; the static offsets and the slots unchanged. -/
theorem arun_add {o : SO} (ho : o.kill .rax = o) (lab : String → Int64) (pc : Int64) (σ : AS) (z : Nat) :
    (arun lab ((dirs addItems).zip [z]) ⟨pc, o, σ⟩).pc = pc + Int64.ofNat z ∧
      (arun lab ((dirs addItems).zip [z]) ⟨pc, o, σ⟩).so = o ∧
      (arun lab ((dirs addItems).zip [z]) ⟨pc, o, σ⟩).σ.regs.get64 .rax = σ.regs.get64 .rax + σ.regs.get64 .rcx ∧
      (arun lab ((dirs addItems).zip [z]) ⟨pc, o, σ⟩).σ.slot = σ.slot := by
  simp [dirs_add, arun, dstep, i64, Scc.Emit.X64.op, xr, or_, classify, RegOnly, AI.step, AI.tgt, AI.so,
    soReg, regDst, SO.write, Reg.base, ho, regRes, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.set, StatusFlags.from_result]
  rw [BitVec.add_comm]

/-! ## Compare and branch at any condition -/

/-- `cmpq %rcx, %rax; j<k> T` (`emitTerm_br`'s first block, after the
operand loads). -/
def cmpJcc (k : CondCode) (T : String) : List Item :=
  [.d (i64 (.cmp (xr .rax) (or_ .rcx))), .d (i64 (.jcc k T))]

theorem cmpJe_eq (T : String) : cmpJe T = cmpJcc .z T := rfl

/-- **The code of `br c a b t f`**: the operand loads into `%rax`, `%rcx`,
`cmpq %rcx, %rax`, `j<cc c>` to `t`'s label, `jmp` to `f`'s. -/
theorem emitTerm_br {fr : Scc.Emit.X64.Frame} {a b : Scc.IR.Operand} {la lb : List Item}
    (ha : getOp fr .rax a = .ok la) (hb : getOp fr .rcx b = .ok lb) (c : Scc.IR.Cond) (t f : Scc.IR.Label)
    (s : S) :
    emitTerm fr (.br c a b t f) s = .ok ((), { s with out :=
      (la ++ lb ++ cmpJcc (cc c) (labelOf fr.fn t) ++
        [Item.d (i64 (.jmp (Scc.Emit.X64.rel (labelOf fr.fn f))))]).reverse ++ s.out }) := by
  simp only [emitTerm, cmpAB, bind, StateT.bind, ld_getOp ha s, ld_getOp hb, ins, Scc.Emit.X64.item, jmpTo, modify,
    modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure, Except.pure, Except.bind]
  simp [cmpJcc]

theorem dirs_cmpJcc (k : CondCode) (T : String) :
    dirs (cmpJcc k T) = [i64 (.cmp (xr .rax) (or_ .rcx)), i64 (.jcc k T)] := rfl

theorem okBlk_cmpJcc {lo hi : Int} {o : SO} (k : CondCode) (T : String) {z1 z2 : Nat} :
    okBlk lo hi o ((dirs (cmpJcc k T)).zip [z1, z2]) = true := by
  simp [dirs_cmpJcc, okBlk, i64, Scc.Emit.X64.op, xr, or_, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg,
    regDst, SO.write, Reg.base]

/-- **`cmpq %rcx, %rax; ja T`'s run**: to `T` exactly when `%rax` is above
`%rcx` (unsigned), else past the two cells; registers, offsets and slots
unchanged. -/
theorem arun_cmpJa {o : SO} (lab : String → Int64) (pc : Int64) (σ : AS) (T : String) (z1 z2 : Nat) :
    (arun lab ((dirs (cmpJcc .a T)).zip [z1, z2]) ⟨pc, o, σ⟩).pc =
        (if (σ.regs.get64 .rcx).toNat < (σ.regs.get64 .rax).toNat then lab T else pc + Int64.ofNat [z1, z2].sum) ∧
      (arun lab ((dirs (cmpJcc .a T)).zip [z1, z2]) ⟨pc, o, σ⟩).so = o ∧
      (arun lab ((dirs (cmpJcc .a T)).zip [z1, z2]) ⟨pc, o, σ⟩).σ.regs = σ.regs ∧
      (arun lab ((dirs (cmpJcc .a T)).zip [z1, z2]) ⟨pc, o, σ⟩).σ.slot = σ.slot := by
  simp [dirs_cmpJcc, arun, dstep, i64, Scc.Emit.X64.op, xr, or_, classify, RegOnly, AI.step, AI.tgt, AI.so,
    soReg, regDst, SO.write, Reg.base, regRes, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.set, StatusFlags.from_result, CondCode.interp]
  have h9 := UInt64.toNat_lt σ.regs.rax
  have h10 := UInt64.toNat_lt σ.regs.rcx
  have hc : ((((18446744073709551616 - σ.regs.rcx.toNat : Nat) : Int) + (σ.regs.rax.toNat : Int)) %
      18446744073709551616 = (σ.regs.rax.toNat : Int) - (σ.regs.rcx.toNat : Int) ↔
      σ.regs.rcx.toNat ≤ σ.regs.rax.toNat) := by
    constructor
    · intro h
      apply Classical.byContradiction; intro hlt
      have : (((18446744073709551616 - σ.regs.rcx.toNat : Nat) : Int) + (σ.regs.rax.toNat : Int)) %
          18446744073709551616 = ((18446744073709551616 - σ.regs.rcx.toNat : Nat) : Int) + σ.regs.rax.toNat :=
        Int.emod_eq_of_lt (by omega) (by omega)
      omega
    · intro h
      have : (((18446744073709551616 - σ.regs.rcx.toNat : Nat) : Int) + (σ.regs.rax.toNat : Int)) =
          ((σ.regs.rax.toNat : Int) - σ.regs.rcx.toNat) + 18446744073709551616 := by omega
      rw [this, Int.add_emod_right]; exact Int.emod_eq_of_lt (by omega) (by omega)
  have hz : σ.regs.rax.toBitVec - σ.regs.rcx.toBitVec = 0#64 ↔ σ.regs.rax.toNat = σ.regs.rcx.toNat := by
    constructor
    · intro h
      have := congrArg (· + σ.regs.rcx.toBitVec) h
      simp only [BitVec.sub_add_cancel, BitVec.zero_add] at this
      exact congrArg BitVec.toNat this
    · intro h
      have : σ.regs.rax.toBitVec = σ.regs.rcx.toBitVec := BitVec.eq_of_toNat_eq h
      rw [this]; simp
  have hiff : (((((18446744073709551616 - σ.regs.rcx.toNat : Nat) : Int) + (σ.regs.rax.toNat : Int)) %
      18446744073709551616 = (σ.regs.rax.toNat : Int) - (σ.regs.rcx.toNat : Int)) ∧
      ¬σ.regs.rax.toBitVec - σ.regs.rcx.toBitVec = 0#64) ↔ σ.regs.rcx.toNat < σ.regs.rax.toNat := by
    rw [hc, hz]; omega
  simp only [hiff, Int64.add_assoc]

/-- **The `br .ugt` compare block** `la ++ lb ++ cmpq; ja T` (the operand
loads into `%rax`, `%rcx`), at any cell sizes `zs`: covered in the frame's
region; it computes the operands' values `va`, `vb` and branches to `T`
exactly when `va > vb` (unsigned), else falls through past the block; static
offsets and slots unchanged. -/
theorem brU_block {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {a b : Scc.IR.Operand} {la lb : List Item} (ha : getOp fr .rax a = .ok la) (hb : getOp fr .rcx b = .ok lb)
    (T : String) (lab : String → Int64) (pc : Int64) (σ : AS) {zs : List Nat}
    (hz : zs.length = (dirs (la ++ lb ++ cmpJcc .a T)).length) :
    okBlk (-(fr.size : Int)) 16 (oB fr) ((dirs (la ++ lb ++ cmpJcc .a T)).zip zs) = true ∧
    ∃ va vb : BitVec 64, opdVal (rsOf fr) σ.slot a = some va.toNat ∧ opdVal (rsOf fr) σ.slot b = some vb.toNat ∧
      (arun lab ((dirs (la ++ lb ++ cmpJcc .a T)).zip zs) ⟨pc, oB fr, σ⟩).pc =
        (if vb.toNat < va.toNat then lab T else pc + Int64.ofNat zs.sum) ∧
      (arun lab ((dirs (la ++ lb ++ cmpJcc .a T)).zip zs) ⟨pc, oB fr, σ⟩).so = oB fr ∧
      (arun lab ((dirs (la ++ lb ++ cmpJcc .a T)).zip zs) ⟨pc, oB fr, σ⟩).σ.slot = σ.slot := by
  obtain ⟨da, hda⟩ := dirs_getOp ha
  obtain ⟨db, hdb⟩ := dirs_getOp hb
  have hd : dirs (la ++ lb ++ cmpJcc .a T) = dirs la ++ dirs lb ++ dirs (cmpJcc .a T) := by
    rw [dirs_append, dirs_append]
  rw [hd, hda, hdb, dirs_cmpJcc] at hz
  match zs, hz with
  | [z0, z1, z2, z3], _ =>
  have hsplit : (dirs (la ++ lb ++ cmpJcc .a T)).zip [z0, z1, z2, z3] =
      (dirs la).zip [z0] ++ ((dirs lb).zip [z1] ++ (dirs (cmpJcc .a T)).zip [z2, z3]) := by
    rw [hd, hda, hdb, dirs_cmpJcc]; rfl
  refine ⟨?_, ?_⟩
  · rw [hsplit, okBlk_getOp hf h1 (by decide) (by decide) ha (by simp [hda]),
      okBlk_getOp hf h1 (by decide) (by decide) hb (by simp [hdb])]
    exact okBlk_cmpJcc .a T
  obtain ⟨va, hva, hra⟩ := arun_getOp hf h1 (by decide) ha lab pc σ (zs := [z0]) (by simp [hda])
  obtain ⟨vb, hvb, hrb⟩ := arun_getOp hf h1 (by decide) hb lab (pc + Int64.ofNat [z0].sum)
    { σ with regs := σ.regs.set64 .rax va } (zs := [z1]) (by simp [hdb])
  refine ⟨va, vb, hva, hvb, ?_⟩
  rw [hsplit, arun_append, arun_append, hra, hrb]
  obtain ⟨e1, e2, -, e4⟩ := arun_cmpJa (o := oB fr) lab (pc + Int64.ofNat [z0].sum + Int64.ofNat [z1].sum)
    { σ with regs := (σ.regs.set64 .rax va).set64 .rcx vb } T z2 z3
  have h9 : ((σ.regs.set64 .rax va).set64 .rcx vb).get64 .rax = va := by
    rw [Reg64s.get64_set64_ne _ (by decide), Reg64s.get64_set64_self]
  have h10 : ((σ.regs.set64 .rax va).set64 .rcx vb).get64 .rcx = vb := Reg64s.get64_set64_self _ _ _
  simp only [h9, h10] at e1
  refine ⟨?_, e2, e4⟩
  rw [e1]
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add, Int64.add_assoc]

/-! ## The call and the abort block -/

/-- **The code of a call of one argument and no result** `call [] f [w]`:
`w` into `%rdi`, `call f`, the safepoint. -/
theorem emitInst_call0 (fr : Scc.Emit.X64.Frame) (sm : Option Scc.IR.StackMap.Entry) (f : String)
    (w : Scc.IR.Operand) :
    emitInst fr sm (.call [] f [w]) = (do ld fr w .rdi; callSym f; safepoint fr sm) := by
  simp [emitInst, callArgs, loadArgs, Scc.Emit.X64.argRegs, Scc.Emit.X64.retRegs, Scc.IR.maxArgs, forIn,
    ForIn.forIn, List.forIn', List.zipIdx]
  rfl

/-- **The code of a call of one argument and one result** `call [d] f [w]`:
`w` into `%rdi`, `call f`, the safepoint, `%rax` into `d`. -/
theorem emitInst_call1 (fr : Scc.Emit.X64.Frame) (sm : Option Scc.IR.StackMap.Entry) (d : Scc.IR.Reg)
    (f : String) (w : Scc.IR.Operand) :
    emitInst fr sm (.call [d] f [w]) = (do ld fr w .rdi; callSym f; safepoint fr sm; st fr .rax d) := by
  simp [emitInst, callArgs, loadArgs, Scc.Emit.X64.argRegs, Scc.Emit.X64.retRegs, Scc.IR.maxArgs, forIn,
    ForIn.forIn, List.forIn', List.zipIdx]
  rfl

/-- **The code of `unreachable`**: `ud2`. -/
theorem emitTerm_unreachable (fr : Scc.Emit.X64.Frame) : emitTerm fr .unreachable = ud2 := rfl

end Spike.Lib.LowerX64
