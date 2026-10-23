/-
**Per-construct lowering lemmas** (x86-64), symbolic in the frame, the
IR register's slot, the pc and the cell sizes; the twin of
`Spike/Lib/LowerA64/Construct.lean`.

- `emitTerm_ret_slot`, `dirs_ret_slot`: `ret r` for an IR register `r` in
  slot `off` emits `retBlk [.slot off]` (`Spike/Lib/X64Ret.lean`);
- `rsOf`, `getOp`, `okBlk_getOp`, `arun_getOp`: an operand's load (`movq`
  of its slot, or of the constant) is covered and puts its `opdVal` in the
  temporary;
- `addChecked`, `okBlk_addChecked`, `arun_addChecked`, `add_block`: the
  checked add's block (the operand loads, `addq`, `jc`) is covered and
  computes the sum, falling through exactly without carry.

Where x86-64 differs from AArch64:
- the cells are sized and the sizes come from the assembler, so a block is
  `ds.zip zs` for any sizes `zs` of its length, and the pc after it is
  `pc + Int64.ofNat zs.sum` (AArch64: `pc + 4 * length`);
- the emitter is a state monad (`Scc.Emit.X64.E`): `getOp fr t a` is the
  item list `ld fr a t` appends (`ld_getOp`), the twin of AArch64's
  `FnCtx.getOp`;
- the static offsets are `%rbp`-based: the frame's region has its base at
  the frame record (`%rbp`), the body runs at `oB fr` (`%rsp` at
  `-fr.size`, `%rbp` at `0`), and an IR register's cell is its slot offset
  `-8 (k + 1)` (`rsOf`);
- any constant is one `movq $imm, %r` (no `movImm` sequence).
-/
import Scc.Lower.InvX64
import Spike.Lib.X64Ret
import Spike.Lib.Form

namespace Spike.Lib.LowerX64

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Emit.X64 (S E Item ld st frameOf i64 xr xm om or_ mem emitTerm epilogue ins)
open Scc.Lower.InvX64
open Spike.Lib.Form (opdVal)

set_option linter.unusedSimpArgs false

/-! ## Items and frames -/

/-- The directives of an item list (its instructions and labels, in order). -/
def dirs (l : List Item) : List Directive := l.filterMap fun | .d x => some x | _ => none

theorem dirs_append (l l' : List Item) : dirs (l ++ l') = dirs l ++ dirs l' := by
  simp [dirs, List.filterMap_append]

/-- **A frame as the emitter builds it** (`frameOf`): its slots and size. -/
def FrameOk (fr : Scc.Emit.X64.Frame) : Prop :=
  ∃ areas f, fr.slots = (frameOf areas f).slots ∧ fr.size = (frameOf areas f).size

/-- **The body's static offsets**: `%rsp` at the frame's bottom, `%rbp` at
the frame record (the region's base). -/
def oB (fr : Scc.Emit.X64.Frame) : SO := ⟨-(fr.size : Int), [(.rbp, 0)]⟩

/-- **The slot map of a frame**: an IR register's cell, relative to the
frame record. -/
def rsOf (fr : Scc.Emit.X64.Frame) (r : Scc.IR.Reg) : Option Int :=
  match fr.slotOff r {} with
  | .ok (off, _) => some off
  | .error _ => none

theorem slotOff_state {fr : Scc.Emit.X64.Frame} {r : Scc.IR.Reg} {s s' : S} {off : Int}
    (h : fr.slotOff r s = .ok (off, s')) (t : S) : fr.slotOff r t = .ok (off, t) := by
  cases hf : fr.slots.find? (·.1 == r) with
  | none => simp only [Scc.Emit.X64.Frame.slotOff, hf] at h; cases h
  | some v =>
    obtain ⟨r', k⟩ := v
    rw [slotOff_find hf] at h ⊢
    cases h; rfl

theorem rsOf_eq {fr : Scc.Emit.X64.Frame} {r : Scc.IR.Reg} {s s' : S} {off : Int} (h : fr.slotOff r s = .ok (off, s')) :
    rsOf fr r = some off := by
  simp only [rsOf, slotOff_state h]

/-! ## Operands -/

/-- **An operand's load into `t`**: the items `ld fr a t` emits. -/
def getOp (fr : Scc.Emit.X64.Frame) (t : Reg64) (a : Scc.IR.Operand) : Except String (List Item) :=
  match ld fr a t {} with
  | .ok (_, s) => .ok s.out.reverse
  | .error e => .error e

/-- What `getOp` says about the emitter: `ld` appends its items. -/
theorem ld_getOp {fr : Scc.Emit.X64.Frame} {t : Reg64} {a : Scc.IR.Operand} {l : List Item} (h : getOp fr t a = .ok l)
    (s : S) : ld fr a t s = .ok ((), { s with out := l.reverse ++ s.out }) := by
  cases a with
  | reg x =>
    cases hs : fr.slotOff x {} with
    | error e =>
      simp only [getOp, ld, Scc.Emit.X64.Frame.slot, bind, StateT.bind, hs, Except.bind] at h; cases h
    | ok p =>
      obtain ⟨off, s'⟩ := p
      have h0 := slotOff_state hs {}
      rw [getOp, ld_reg h0] at h
      cases h
      rw [ld_reg (slotOff_state hs s)]
      rfl
  | imm v =>
    rw [getOp, ld_imm] at h
    cases h
    rw [ld_imm]; rfl

theorem toInt_ofInt_small {k : Int} (h0 : -(2 ^ 62) ≤ k) (h1 : k ≤ 2 ^ 62) : (Int64.ofInt k).toInt = k := by
  have hs : Int64.size = 18446744073709551616 := rfl
  rw [Int64.toInt_ofInt, hs]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- An operand's load: the directive and its register effect. -/
theorem getOp_cases {fr : Scc.Emit.X64.Frame} {t : Reg64} {a : Scc.IR.Operand} {l : List Item} (ha : getOp fr t a = .ok l) :
    (∃ r off, a = .reg r ∧ rsOf fr r = some off ∧ dirs l = [(AI.ld t .rbp (Int64.ofInt off)).toDir]) ∨
    (∃ v, a = .imm v ∧ dirs l = [i64 (.mov (xr t) (.imm (.int64 v.toInt64)))]) := by
  cases a with
  | reg r =>
    left
    cases hs : fr.slotOff r {} with
    | error e =>
      simp only [getOp, ld, Scc.Emit.X64.Frame.slot, bind, StateT.bind, hs, Except.bind] at ha; cases ha
    | ok p =>
      obtain ⟨off, s'⟩ := p
      have h0 := slotOff_state hs {}
      refine ⟨r, off, rfl, rsOf_eq hs, ?_⟩
      rw [getOp, ld_reg h0] at ha
      cases ha
      rfl
  | imm v =>
    right
    refine ⟨v, rfl, ?_⟩
    rw [getOp, ld_imm] at ha
    cases ha
    rfl

theorem length_one {α : Type} {zs : List α} (h : zs.length = 1) : ∃ z, zs = [z] := by
  match zs, h with
  | [z], _ => exact ⟨z, rfl⟩

/-- **An operand's load is covered** in the frame's region `[-size, 16)`
at the body's offsets, which it keeps. -/
theorem okBlk_getOp {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) {t : Reg64}
    (ht : t ≠ .rsp) (ht' : t ≠ .rbp) {a : Scc.IR.Operand} {l : List Item} (ha : getOp fr t a = .ok l)
    {zs : List Nat} (hz : zs.length = (dirs l).length) (ds : List (Directive × Nat)) :
    okBlk (-(fr.size : Int)) 16 (oB fr) ((dirs l).zip zs ++ ds) = okBlk (-(fr.size : Int)) 16 (oB fr) ds := by
  rcases getOp_cases ha with ⟨r, off, rfl, hs, hl⟩ | ⟨v, rfl, hl⟩
  · rw [hl] at hz ⊢
    obtain ⟨z, rfl⟩ := length_one hz
    obtain ⟨areas, f, hsl, hsz⟩ := hf
    cases h : fr.slotOff r {} with
    | error e => simp [rsOf, h] at hs
    | ok p =>
      obtain ⟨off', s'⟩ := p
      have he : off' = off := by simp [rsOf, h] at hs; exact hs
      subst he
      obtain ⟨h8, hm, hle, hsize⟩ := slotOff_bounds hsl hsz h
      have ho : (Int64.ofInt off').toInt = off' := toInt_ofInt_small (by omega) (by omega)
      simp [okBlk, AI.toDir, classify, AI.ok, AI.so, AI.isTerm, oB, SO.get, SO.kill, lk, rm, ho, offOk, ht, ht', Ne.symm ht']
      intro _; omega
  · rw [hl] at hz ⊢
    obtain ⟨z, rfl⟩ := length_one hz
    simp [okBlk, i64, Scc.Emit.X64.op, xr, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg, regDst, SO.write,
      oB, SO.get, SO.kill, lk, rm, ht, ht', Ne.symm ht', Reg.base]

/-- **An operand's load runs** to `t := ` its value (`opdVal` at `rsOf`),
past its cell. -/
theorem arun_getOp {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) {t : Reg64}
    (ht' : t ≠ .rbp) {a : Scc.IR.Operand} {l : List Item} (ha : getOp fr t a = .ok l)
    (lab : String → Int64) (pc : Int64) (σ : AS) {zs : List Nat} (hz : zs.length = (dirs l).length) :
    ∃ v : BitVec 64, opdVal (rsOf fr) σ.slot a = some v.toNat ∧
      arun lab ((dirs l).zip zs) ⟨pc, oB fr, σ⟩ =
        ⟨pc + Int64.ofNat zs.sum, oB fr, { σ with regs := σ.regs.set64 t v }⟩ := by
  rcases getOp_cases ha with ⟨r, off, rfl, hs, hl⟩ | ⟨v, rfl, hl⟩
  · rw [hl] at hz ⊢
    obtain ⟨z, rfl⟩ := length_one hz
    obtain ⟨areas, f, hsl, hsz⟩ := hf
    cases h : fr.slotOff r {} with
    | error e => simp [rsOf, h] at hs
    | ok p =>
      obtain ⟨off', s'⟩ := p
      have he : off' = off := by simp [rsOf, h] at hs; exact hs
      subst he
      obtain ⟨h8, hm, hle, hsize⟩ := slotOff_bounds hsl hsz h
      have ho : (Int64.ofInt off').toInt = off' := toInt_ofInt_small (by omega) (by omega)
      refine ⟨σ.slot off', by simp [opdVal, hs], ?_⟩
      simp [arun, dstep, AI.toDir, classify, AI.step, AI.tgt, AI.so, oB, SO.get, SO.kill, lk, rm, ho, ht',
        Ne.symm ht']
  · rw [hl] at hz ⊢
    obtain ⟨z, rfl⟩ := length_one hz
    refine ⟨v.toBitVec, by simp [opdVal], ?_⟩
    simp [arun, dstep, i64, Scc.Emit.X64.op, xr, classify, RegOnly, AI.step, AI.tgt, AI.so, soReg, regDst,
      SO.write, oB, SO.get, SO.kill, lk, rm, ht', Ne.symm ht', Reg.base, regRes, Operation.interp,
      Operand.interp, MachineData.set, MachineData.setReg, Reg64s.set, ConstExpr.interp]
    split <;> rfl


/-! ## Checked `+`

The source's checked `+` adds unbounded naturals (`TermRun.addW`) and
overflows exactly when the operands' sum is at least `2^64` (the overflow
edge's source, `OvfRep`): an unsigned carry. `addq %rcx, %rax` sets `CF`
exactly on an unsigned carry and `jc` tests `CF`, the same test as
AArch64's `adds` and `b.cs`. -/

/-- `addq %rcx, %rax; jc L`: the add and the overflow branch of `addChk`
(`emitInst_addChk`), after the operand loads. -/
def addChecked (L : String) : List Item :=
  [.d (i64 (.add (xr .rax) (or_ .rcx))), .d (i64 (.jcc .c L))]

theorem dirs_addChecked (L : String) :
    dirs (addChecked L) = [i64 (.add (xr .rax) (or_ .rcx)), i64 (.jcc .c L)] := rfl

theorem okBlk_addChecked {lo hi : Int} {o : SO} (ho : o.kill .rax = o) (L : String) {z1 z2 : Nat} :
    okBlk lo hi o ((dirs (addChecked L)).zip [z1, z2]) = true := by
  simp [dirs_addChecked, okBlk, i64, Scc.Emit.X64.op, xr, or_, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg,
    regDst, SO.write, Reg.base, ho]

/-- **The checked add's run**: `rax := rax + rcx`; the branch is taken
exactly when the unsigned sum does not fit in 64 bits; the static offsets
and the slots are unchanged. -/
theorem arun_addChecked {o : SO} (ho : o.kill .rax = o) (lab : String → Int64) (pc : Int64) (σ : AS)
    (L : String) (z1 z2 : Nat) :
    (arun lab ((dirs (addChecked L)).zip [z1, z2]) ⟨pc, o, σ⟩).pc =
        (if (σ.regs.get64 .rax).toNat + (σ.regs.get64 .rcx).toNat < 2 ^ 64 then
          pc + Int64.ofNat [z1, z2].sum else lab L) ∧
      (arun lab ((dirs (addChecked L)).zip [z1, z2]) ⟨pc, o, σ⟩).so = o ∧
      (arun lab ((dirs (addChecked L)).zip [z1, z2]) ⟨pc, o, σ⟩).σ.regs =
        σ.regs.set64 .rax (σ.regs.get64 .rax + σ.regs.get64 .rcx) ∧
      (arun lab ((dirs (addChecked L)).zip [z1, z2]) ⟨pc, o, σ⟩).σ.slot = σ.slot := by
  simp [dirs_addChecked, arun, dstep, i64, Scc.Emit.X64.op, xr, or_, classify, RegOnly, AI.step, AI.tgt, AI.so,
    soReg, regDst, SO.write, Reg.base, ho, regRes, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.set, StatusFlags.from_result, CondCode.interp]
  refine ⟨?_, by rw [BitVec.add_comm]⟩
  have ha := σ.regs.rax.toNat_lt
  have hb := σ.regs.rcx.toNat_lt
  have hiff : ((σ.regs.rcx.toNat : Int) + σ.regs.rax.toNat) % 18446744073709551616 =
      (σ.regs.rcx.toNat : Int) + σ.regs.rax.toNat ↔ σ.regs.rax.toNat + σ.regs.rcx.toNat < 18446744073709551616 := by
    constructor
    · intro h; omega
    · intro h; exact Int.emod_eq_of_lt (by omega) (by omega)
  by_cases h : σ.regs.rax.toNat + σ.regs.rcx.toNat < 18446744073709551616
  · simp only [hiff.mpr h, h, ↓reduceIte, Int64.add_assoc]
  · have h' : ¬ ((σ.regs.rcx.toNat : Int) + σ.regs.rax.toNat) % 18446744073709551616 =
        (σ.regs.rcx.toNat : Int) + σ.regs.rax.toNat := fun h' => h (hiff.mp h')
    simp only [h, h', ↓reduceIte]

theorem dirs_getOp {fr : Scc.Emit.X64.Frame} {t : Reg64} {a : Scc.IR.Operand} {l : List Item}
    (ha : getOp fr t a = .ok l) : ∃ d, dirs l = [d] := by
  rcases getOp_cases ha with ⟨_, _, _, _, hl⟩ | ⟨_, _, hl⟩ <;> exact ⟨_, hl⟩

theorem arun_append (lab : String → Int64) (a b : List (Directive × Nat)) (am : AM) :
    arun lab (a ++ b) am = arun lab b (arun lab a am) := by
  simp [arun, List.foldl_append]

/-- **The checked add's block** `la ++ lb ++ addq; jc L` (the operand
loads into `%rax`, `%rcx`), at any cell sizes `zs`: covered in the frame's
region; it computes the operands' values `va`, `vb` (`opdVal` at `rsOf`),
falls through past the block exactly when `va + vb < 2^64` (else jumps to
`L`), leaves `%rax = va + vb`, the static offsets and the slots. -/
theorem add_block {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {a b : Scc.IR.Operand} {la lb : List Item} (ha : getOp fr .rax a = .ok la) (hb : getOp fr .rcx b = .ok lb)
    (L : String) (lab : String → Int64) (pc : Int64) (σ : AS) {zs : List Nat}
    (hz : zs.length = (dirs (la ++ lb ++ addChecked L)).length) :
    okBlk (-(fr.size : Int)) 16 (oB fr) ((dirs (la ++ lb ++ addChecked L)).zip zs) = true ∧
    ∃ va vb : BitVec 64, opdVal (rsOf fr) σ.slot a = some va.toNat ∧ opdVal (rsOf fr) σ.slot b = some vb.toNat ∧
      (arun lab ((dirs (la ++ lb ++ addChecked L)).zip zs) ⟨pc, oB fr, σ⟩).pc =
        (if va.toNat + vb.toNat < 2 ^ 64 then pc + Int64.ofNat zs.sum else lab L) ∧
      (arun lab ((dirs (la ++ lb ++ addChecked L)).zip zs) ⟨pc, oB fr, σ⟩).so = oB fr ∧
      (arun lab ((dirs (la ++ lb ++ addChecked L)).zip zs) ⟨pc, oB fr, σ⟩).σ.regs.get64 .rax = va + vb ∧
      (arun lab ((dirs (la ++ lb ++ addChecked L)).zip zs) ⟨pc, oB fr, σ⟩).σ.slot = σ.slot := by
  obtain ⟨da, hda⟩ := dirs_getOp ha
  obtain ⟨db, hdb⟩ := dirs_getOp hb
  have hd : dirs (la ++ lb ++ addChecked L) = dirs la ++ dirs lb ++ dirs (addChecked L) := by
    rw [dirs_append, dirs_append]
  rw [hd, hda, hdb, dirs_addChecked] at hz
  match zs, hz with
  | [z0, z1, z2, z3], _ =>
  have hsplit : (dirs (la ++ lb ++ addChecked L)).zip [z0, z1, z2, z3] =
      (dirs la).zip [z0] ++ ((dirs lb).zip [z1] ++ (dirs (addChecked L)).zip [z2, z3]) := by
    rw [hd, hda, hdb, dirs_addChecked]; rfl
  have hk : (oB fr).kill .rax = oB fr := by simp [oB, SO.kill, rm]
  refine ⟨?_, ?_⟩
  · rw [hsplit, okBlk_getOp hf h1 (by decide) (by decide) ha (by simp [hda]),
      okBlk_getOp hf h1 (by decide) (by decide) hb (by simp [hdb])]
    exact okBlk_addChecked hk L
  obtain ⟨va, hva, hra⟩ := arun_getOp hf h1 (by decide) ha lab pc σ (zs := [z0]) (by simp [hda])
  obtain ⟨vb, hvb, hrb⟩ := arun_getOp hf h1 (by decide) hb lab (pc + Int64.ofNat [z0].sum)
    { σ with regs := σ.regs.set64 .rax va } (zs := [z1]) (by simp [hdb])
  refine ⟨va, vb, hva, hvb, ?_⟩
  rw [hsplit, arun_append, arun_append, hra, hrb]
  obtain ⟨e1, e2, e3, e4⟩ := arun_addChecked hk lab (pc + Int64.ofNat [z0].sum + Int64.ofNat [z1].sum)
    { σ with regs := (σ.regs.set64 .rax va).set64 .rcx vb } L z2 z3
  have h9 : ((σ.regs.set64 .rax va).set64 .rcx vb).get64 .rax = va := by
    rw [Reg64s.get64_set64_ne _ (by decide), Reg64s.get64_set64_self]
  have h10 : ((σ.regs.set64 .rax va).set64 .rcx vb).get64 .rcx = vb := Reg64s.get64_set64_self _ _ _
  simp only [h9, h10] at e1 e3
  refine ⟨?_, e2, ?_, e4⟩
  · rw [e1]
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add, Int64.add_assoc]
  · rw [e3, Reg64s.get64_set64_self]


/-! ## `ret` -/

/-- The epilogue's items (`epilogue`, then `ret`). -/
def epiItems : List Item := [.d (i64 (.mov (xr .rsp) (or_ .rbp))), .d (i64 (.pop (xr .rbp))), .d (i64 .ret)]

/-- **The code of `ret [v]`**: the operand's load into `%rax`, the
epilogue, `ret`. -/
theorem emitTerm_ret {fr : Scc.Emit.X64.Frame} {v : Scc.IR.Operand} {l : List Item}
    (hl : getOp fr .rax v = .ok l) (s : S) :
    emitTerm fr (.ret [v]) s = .ok ((), { s with out := (l ++ epiItems).reverse ++ s.out }) := by
  rw [emitTerm_ret1]
  simp only [bind, StateT.bind, ld_getOp hl s, epilogue, Scc.Emit.X64.movRR, ins, Scc.Emit.X64.item, modify,
    modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure, Except.pure, Except.bind]
  simp [epiItems]

/-- **`ret` of a slot register**: the emitted code is `retBlk`. -/
theorem dirs_ret_slot {fr : Scc.Emit.X64.Frame} {r : Scc.IR.Reg} {off : Int} (h : rsOf fr r = some off)
    {l : List Item} (hl : getOp fr .rax (.reg r) = .ok l) :
    dirs (l ++ epiItems) = retBlk [.slot (Int64.ofInt off)] := by
  rcases getOp_cases hl with ⟨r', off', he, hs, hd⟩ | ⟨v, he, _⟩
  · cases he
    rw [h] at hs; cases hs
    rw [dirs_append, hd]
    rfl
  · cases he

end Spike.Lib.LowerX64
