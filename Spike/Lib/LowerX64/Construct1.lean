/-
**Per-construct lowering lemmas of `Accepted1`** (x86-64), symbolic in the
frame, the IR registers' slots, the pc and the cell sizes, in the style of
`Spike/Lib/LowerX64/Construct.lean`; the twin of
`Spike/Lib/LowerA64/Construct1.lean`.

- `emitInst_subSat`, `sub_block`: the saturating `-`'s block `la ++ lb ++
  subq; movl $0, %edx; cmovb %rdx, %rax` (the operand loads into `%rax`,
  `%rcx`) is covered in the frame, falls through, and leaves `%rax` the
  truncated difference of the operands' values;
- `emitTerm_br_eq`, `br_block`, `arun_jmp`: the `if`'s terminator `la ++ lb ++
  cmpq; je T` then `jmp F` (two blocks: only a block's last instruction may
  branch): the first branches to `T` exactly when the operands' values are
  equal, else falls through to the second, which branches to `F`.

Where x86-64 differs from AArch64: `movl $0, %edx` zeroes `%rdx` (a 32-bit
write clears the upper half) and `cmovb` (`CF`, the borrow of `subq`) picks
it; the compare is `cmpq %rcx, %rax` (the flags of `rax - rcx`) and `je`
tests `ZF`.
-/
import Spike.Lib.LowerX64.Construct

namespace Spike.Lib.LowerX64

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Emit.X64 (S E Item ld st frameOf i64 i32 xr xm om or_ oi mem emitInst emitTerm ins rax64 cmpAB cc
  labelOf jmpTo movl)
open Scc.Lower.InvX64
open Spike.Lib.Form (opdVal)

set_option linter.unusedSimpArgs false

/-! ## Saturating `-` -/

/-- `subq %rcx, %rax; movl $0, %edx; cmovb %rdx, %rax`: the saturating
`-` of `subSat` (`emitInst_subSat`), after the operand loads. -/
def subSatItems : List Item :=
  [.d (i64 (.sub (xr .rax) (or_ .rcx))), .d (i32 (.mov (xr .rdx) (oi 0))),
   .d (i64 (.cmovcc .c rax64 (xr .rdx)))]

/-- **The code of `subSat d a b`**: `a` into `%rax`, `b` into `%rcx`, the
saturating `-`, `%rax` into `d`. -/
theorem emitInst_subSat (fr : Scc.Emit.X64.Frame) (sm : Option Scc.IR.StackMap.Entry) (d : Scc.IR.Reg)
    (a b : Scc.IR.Operand) :
    emitInst fr sm (.subSat d a b) = (do
      ld fr a .rax; ld fr b .rcx
      ins (i64 (.sub (xr .rax) (or_ .rcx)))
      movl .rdx 0
      ins (i64 (.cmovcc .c rax64 (xr .rdx)))
      st fr .rax d) := rfl

theorem dirs_subSat :
    dirs subSatItems = [i64 (.sub (xr .rax) (or_ .rcx)), i32 (.mov (xr .rdx) (oi 0)),
      i64 (.cmovcc .c rax64 (xr .rdx))] := rfl

theorem okBlk_subSat {lo hi : Int} {o : SO} (hr : o.kill .rax = o) (hd : o.kill .rdx = o)
    {z1 z2 z3 : Nat} :
    okBlk lo hi o ((dirs subSatItems).zip [z1, z2, z3]) = true := by
  simp [dirs_subSat, okBlk, i64, i32, Scc.Emit.X64.op, xr, or_, oi, rax64, Scc.Emit.X64.lw, classify, RegOnly,
    AI.ok, AI.so, AI.isTerm, soReg, regDst, SO.write, Reg.base, hr, hd]

theorem arun_subSat {o : SO} (hr : o.kill .rax = o) (hd : o.kill .rdx = o) (lab : String → Int64) (pc : Int64)
    (σ : AS) (z1 z2 z3 : Nat) :
    (arun lab ((dirs subSatItems).zip [z1, z2, z3]) ⟨pc, o, σ⟩).pc = pc + Int64.ofNat [z1, z2, z3].sum ∧
      (arun lab ((dirs subSatItems).zip [z1, z2, z3]) ⟨pc, o, σ⟩).so = o ∧
      ((arun lab ((dirs subSatItems).zip [z1, z2, z3]) ⟨pc, o, σ⟩).σ.regs.get64 .rax).toNat =
        (σ.regs.get64 .rax).toNat - (σ.regs.get64 .rcx).toNat ∧
      (arun lab ((dirs subSatItems).zip [z1, z2, z3]) ⟨pc, o, σ⟩).σ.slot = σ.slot := by
  simp [dirs_subSat, arun, dstep, i64, i32, Scc.Emit.X64.op, xr, or_, oi, rax64, Scc.Emit.X64.lw, classify, RegOnly,
    AI.step, AI.tgt, AI.so, soReg, regDst, SO.write, Reg.base, hr, hd, regRes, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.setReg, Reg64s.set, StatusFlags.from_result, CondCode.interp,
    ConstExpr.interp]
  refine ⟨by simp only [Int64.add_assoc], ?_⟩
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
  by_cases hle : σ.regs.rcx.toNat ≤ σ.regs.rax.toNat
  · rw [ite_eq_left (hc.mpr hle)]
    simp only [BitVec.toNat_sub, UInt64.toNat_toBitVec]
    omega
  · rw [ite_eq_right (fun h => hle (hc.mp h))]
    simp only [BitVec.toNat_ofNat]
    omega

/-- **The saturating `-`'s block** `la ++ lb ++ subq; movl; cmovb` (the
operand loads into `%rax`, `%rcx`), at any cell sizes `zs`: covered in the
frame's region; it computes the operands' values `va`, `vb` (`opdVal` at
`rsOf`), falls through past the block, and leaves `%rax = va - vb`
(truncated), the static offsets and the slots. -/
theorem sub_block {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {a b : Scc.IR.Operand} {la lb : List Item} (ha : getOp fr .rax a = .ok la) (hb : getOp fr .rcx b = .ok lb)
    (lab : String → Int64) (pc : Int64) (σ : AS) {zs : List Nat}
    (hz : zs.length = (dirs (la ++ lb ++ subSatItems)).length) :
    okBlk (-(fr.size : Int)) 16 (oB fr) ((dirs (la ++ lb ++ subSatItems)).zip zs) = true ∧
    ∃ va vb : BitVec 64, opdVal (rsOf fr) σ.slot a = some va.toNat ∧ opdVal (rsOf fr) σ.slot b = some vb.toNat ∧
      (arun lab ((dirs (la ++ lb ++ subSatItems)).zip zs) ⟨pc, oB fr, σ⟩).pc = pc + Int64.ofNat zs.sum ∧
      (arun lab ((dirs (la ++ lb ++ subSatItems)).zip zs) ⟨pc, oB fr, σ⟩).so = oB fr ∧
      ((arun lab ((dirs (la ++ lb ++ subSatItems)).zip zs) ⟨pc, oB fr, σ⟩).σ.regs.get64 .rax).toNat =
        va.toNat - vb.toNat ∧
      (arun lab ((dirs (la ++ lb ++ subSatItems)).zip zs) ⟨pc, oB fr, σ⟩).σ.slot = σ.slot := by
  obtain ⟨da, hda⟩ := dirs_getOp ha
  obtain ⟨db, hdb⟩ := dirs_getOp hb
  have hd : dirs (la ++ lb ++ subSatItems) = dirs la ++ dirs lb ++ dirs subSatItems := by
    rw [dirs_append, dirs_append]
  rw [hd, hda, hdb, dirs_subSat] at hz
  match zs, hz with
  | [z0, z1, z2, z3, z4], _ =>
  have hsplit : (dirs (la ++ lb ++ subSatItems)).zip [z0, z1, z2, z3, z4] =
      (dirs la).zip [z0] ++ ((dirs lb).zip [z1] ++ (dirs subSatItems).zip [z2, z3, z4]) := by
    rw [hd, hda, hdb, dirs_subSat]; rfl
  have hk : (oB fr).kill .rax = oB fr := by simp [oB, SO.kill, rm]
  have hk' : (oB fr).kill .rdx = oB fr := by simp [oB, SO.kill, rm]
  refine ⟨?_, ?_⟩
  · rw [hsplit, okBlk_getOp hf h1 (by decide) (by decide) ha (by simp [hda]),
      okBlk_getOp hf h1 (by decide) (by decide) hb (by simp [hdb])]
    exact okBlk_subSat hk hk'
  obtain ⟨va, hva, hra⟩ := arun_getOp hf h1 (by decide) ha lab pc σ (zs := [z0]) (by simp [hda])
  obtain ⟨vb, hvb, hrb⟩ := arun_getOp hf h1 (by decide) hb lab (pc + Int64.ofNat [z0].sum)
    { σ with regs := σ.regs.set64 .rax va } (zs := [z1]) (by simp [hdb])
  refine ⟨va, vb, hva, hvb, ?_⟩
  rw [hsplit, arun_append, arun_append, hra, hrb]
  obtain ⟨e1, e2, e3, e4⟩ := arun_subSat hk hk' lab (pc + Int64.ofNat [z0].sum + Int64.ofNat [z1].sum)
    { σ with regs := (σ.regs.set64 .rax va).set64 .rcx vb } z2 z3 z4
  have h9 : ((σ.regs.set64 .rax va).set64 .rcx vb).get64 .rax = va := by
    rw [Reg64s.get64_set64_ne _ (by decide), Reg64s.get64_set64_self]
  have h10 : ((σ.regs.set64 .rax va).set64 .rcx vb).get64 .rcx = vb := Reg64s.get64_set64_self _ _ _
  simp only [h9, h10] at e3
  refine ⟨?_, e2, e3, e4⟩
  rw [e1]
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add, Int64.add_assoc]

/-! ## `if a = b`: compare and branch -/

/-- `cmpq %rcx, %rax; je T` (`emitTerm_br`'s first block, after the operand
loads). -/
def cmpJe (T : String) : List Item := [.d (i64 (.cmp (xr .rax) (or_ .rcx))), .d (i64 (.jcc .z T))]

theorem dirs_cmpJe (T : String) : dirs (cmpJe T) = [i64 (.cmp (xr .rax) (or_ .rcx)), i64 (.jcc .z T)] := rfl

theorem okBlk_cmpJe {lo hi : Int} {o : SO} (T : String) {z1 z2 : Nat} :
    okBlk lo hi o ((dirs (cmpJe T)).zip [z1, z2]) = true := by
  simp [dirs_cmpJe, okBlk, i64, Scc.Emit.X64.op, xr, or_, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg,
    regDst, SO.write, Reg.base]

theorem arun_cmpJe {o : SO} (lab : String → Int64) (pc : Int64) (σ : AS) (T : String) (z1 z2 : Nat) :
    (arun lab ((dirs (cmpJe T)).zip [z1, z2]) ⟨pc, o, σ⟩).pc =
        (if σ.regs.get64 .rax = σ.regs.get64 .rcx then lab T else pc + Int64.ofNat [z1, z2].sum) ∧
      (arun lab ((dirs (cmpJe T)).zip [z1, z2]) ⟨pc, o, σ⟩).so = o ∧
      (arun lab ((dirs (cmpJe T)).zip [z1, z2]) ⟨pc, o, σ⟩).σ.regs = σ.regs ∧
      (arun lab ((dirs (cmpJe T)).zip [z1, z2]) ⟨pc, o, σ⟩).σ.slot = σ.slot := by
  simp [dirs_cmpJe, arun, dstep, i64, Scc.Emit.X64.op, xr, or_, classify, RegOnly, AI.step, AI.tgt, AI.so,
    soReg, regDst, SO.write, Reg.base, regRes, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.set, StatusFlags.from_result, CondCode.interp]
  have : (σ.regs.rax.toBitVec - σ.regs.rcx.toBitVec = 0#64) ↔ σ.regs.rax.toBitVec = σ.regs.rcx.toBitVec := by
    constructor
    · intro h
      have := congrArg (· + σ.regs.rcx.toBitVec) h
      simp only [BitVec.sub_add_cancel, BitVec.zero_add] at this
      exact this
    · intro h; rw [h]; simp
  simp only [this, Int64.add_assoc]

/-- The first block of the `if`'s terminator: both operands' loads, the
compare, the conditional branch to the `then` block `T`. -/
def brDirs (la lb : List Item) (T : String) : List Directive := dirs (la ++ lb ++ cmpJe T)

/-- **The `if`'s compare block** `la ++ lb ++ cmpq; je T` (the operand
loads into `%rax`, `%rcx`), at any cell sizes `zs`: covered in the frame's
region; it computes the operands' values `va`, `vb` and branches to `T`
exactly when they are equal, else falls through past the block; static
offsets and slots unchanged. -/
theorem br_block {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {a b : Scc.IR.Operand} {la lb : List Item} (ha : getOp fr .rax a = .ok la) (hb : getOp fr .rcx b = .ok lb)
    (T : String) (lab : String → Int64) (pc : Int64) (σ : AS) {zs : List Nat}
    (hz : zs.length = (brDirs la lb T).length) :
    okBlk (-(fr.size : Int)) 16 (oB fr) ((brDirs la lb T).zip zs) = true ∧
    ∃ va vb : BitVec 64, opdVal (rsOf fr) σ.slot a = some va.toNat ∧ opdVal (rsOf fr) σ.slot b = some vb.toNat ∧
      (arun lab ((brDirs la lb T).zip zs) ⟨pc, oB fr, σ⟩).pc =
        (if va = vb then lab T else pc + Int64.ofNat zs.sum) ∧
      (arun lab ((brDirs la lb T).zip zs) ⟨pc, oB fr, σ⟩).so = oB fr ∧
      (arun lab ((brDirs la lb T).zip zs) ⟨pc, oB fr, σ⟩).σ.slot = σ.slot := by
  obtain ⟨da, hda⟩ := dirs_getOp ha
  obtain ⟨db, hdb⟩ := dirs_getOp hb
  have hd : brDirs la lb T = dirs la ++ dirs lb ++ dirs (cmpJe T) := by
    rw [brDirs, dirs_append, dirs_append]
  rw [hd, hda, hdb, dirs_cmpJe] at hz
  match zs, hz with
  | [z0, z1, z2, z3], _ =>
  have hsplit : (brDirs la lb T).zip [z0, z1, z2, z3] =
      (dirs la).zip [z0] ++ ((dirs lb).zip [z1] ++ (dirs (cmpJe T)).zip [z2, z3]) := by
    rw [hd, hda, hdb, dirs_cmpJe]; rfl
  refine ⟨?_, ?_⟩
  · rw [hsplit, okBlk_getOp hf h1 (by decide) (by decide) ha (by simp [hda]),
      okBlk_getOp hf h1 (by decide) (by decide) hb (by simp [hdb])]
    exact okBlk_cmpJe T
  obtain ⟨va, hva, hra⟩ := arun_getOp hf h1 (by decide) ha lab pc σ (zs := [z0]) (by simp [hda])
  obtain ⟨vb, hvb, hrb⟩ := arun_getOp hf h1 (by decide) hb lab (pc + Int64.ofNat [z0].sum)
    { σ with regs := σ.regs.set64 .rax va } (zs := [z1]) (by simp [hdb])
  refine ⟨va, vb, hva, hvb, ?_⟩
  rw [hsplit, arun_append, arun_append, hra, hrb]
  obtain ⟨e1, e2, -, e4⟩ := arun_cmpJe (o := oB fr) lab (pc + Int64.ofNat [z0].sum + Int64.ofNat [z1].sum)
    { σ with regs := (σ.regs.set64 .rax va).set64 .rcx vb } T z2 z3
  have h9 : ((σ.regs.set64 .rax va).set64 .rcx vb).get64 .rax = va := by
    rw [Reg64s.get64_set64_ne _ (by decide), Reg64s.get64_set64_self]
  have h10 : ((σ.regs.set64 .rax va).set64 .rcx vb).get64 .rcx = vb := Reg64s.get64_set64_self _ _ _
  simp only [h9, h10] at e1
  refine ⟨?_, e2, e4⟩
  rw [e1]
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add, Int64.add_assoc]

/-- The second block of the `if`'s terminator: `jmp F` to the `else` block. -/
def jmpDirs (F : String) : List Directive := [i64 (.jmp (Scc.Emit.X64.rel F))]

theorem okBlk_jmp {lo hi : Int} {o : SO} (F : String) {z : Nat} : okBlk lo hi o ((jmpDirs F).zip [z]) = true := by
  simp [jmpDirs, okBlk, i64, Scc.Emit.X64.op, Scc.Emit.X64.rel, classify, AI.ok, AI.so, AI.isTerm]

/-- **`jmp F`'s run**: to `F`, nothing else changes. -/
theorem arun_jmp {o : SO} (lab : String → Int64) (pc : Int64) (σ : AS) (F : String) (z : Nat) :
    arun lab ((jmpDirs F).zip [z]) ⟨pc, o, σ⟩ = ⟨lab F, o, σ⟩ := by
  simp [jmpDirs, arun, dstep, i64, Scc.Emit.X64.op, Scc.Emit.X64.rel, classify, AI.step, AI.tgt, AI.so]

/-- **The code of `br .eq a b t f`**: the operand loads into `%rax`, `%rcx`,
`cmpq %rcx, %rax`, `je` to `t`'s label, `jmp` to `f`'s. -/
theorem emitTerm_br_eq {fr : Scc.Emit.X64.Frame} {a b : Scc.IR.Operand} {la lb : List Item}
    (ha : getOp fr .rax a = .ok la) (hb : getOp fr .rcx b = .ok lb) (t f : Scc.IR.Label) (s : S) :
    emitTerm fr (.br .eq a b t f) s = .ok ((), { s with out :=
      (la ++ lb ++ cmpJe (labelOf fr.fn t) ++ [Item.d (i64 (.jmp (Scc.Emit.X64.rel (labelOf fr.fn f))))]).reverse ++
        s.out }) := by
  simp only [emitTerm, cmpAB, bind, StateT.bind, ld_getOp ha s, ld_getOp hb, ins, Scc.Emit.X64.item, jmpTo, modify,
    modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure, Except.pure, Except.bind, cc]
  simp [cmpJe]

end Spike.Lib.LowerX64
