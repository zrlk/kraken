/-
**`print`'s argument block** (x86-64): the code `callBlock`'s `.print`
case (`Scc/Lower/Term.lean`) lowers before `call scc_rt_print`, run from any
caller's frame (`FrameOk`, `size ≤ 2^31`) on any operands, at any cell
sizes; the twin of `Spike/Lib/LowerA64/PrintArgs.lean`.

- The operations: `arun_ext32D` (`movl %eax, %eax`), `arun_addD`
  (`addq %rcx, %rax`), `arun_sel` (`cmpq %rcx, %rax; movq %rsi, %rax;
  cmovb %rdx, %rax`).
- `RunsP`: a block falls through at any cell sizes and pc, the static
  offsets kept, into a postcondition; `RunsP.append`, `RunsP.mono`,
  `RunsP.one`.
- The instructions' runs: `runsP_getOp`, `runsP_loads2`, `runsP_st`,
  `ext32_runs`, `add_runs`, `select_runs`; the slot-write facts
  `opdVal_updX`, `opdVal_updSelfX`, `upd_offX`.
- `printPre_runs` (`lo := ext.w32 o`, `s := b + lo`, `m` and `8` loaded),
  `printPost_runs` (after the multiply: `cap`'s store, `k := select (n <
  cap) n cap`, `s` and `k` into `%rdi`, `%rsi`), and the whole block
  `printArgs_runs`; at an immediate offset `w ≠ 0`, `printPreImm_runs` and
  `printArgsImm_runs`.
- The code: `st_rax`, `emitInst_ext32_items`, `emitInst_add_items`,
  `emitInst_mul_items`, `emitInst_select_items`, `emitInst_print`,
  `emitInst_print_items`.
- Coverage in the frame's region `[-size, 16)` (`okBlk`): `CovP` (a
  non-branching prefix keeping the offsets, at any cell sizes; `CovP.ok`),
  `covP_printPre`, `covP_printPreImm`, `covP_printPost`.

Where x86-64 differs from AArch64: `imulq` leaves flags undefined, so the
block model (`classify`) does not cover it and it is a node of its own
(`mulFI`, `flag_ndW`): the block is the run before it and, from its step at
any flags, the run after it.
`Spike/Test/LowerX64PrintArgs.lean` instantiates the block at `hello1`'s
frame.
-/
import Spike.Lib.LowerX64.Node
import Spike.Lib.LowerX64.Construct1
import Spike.Lib.X64Flags

namespace Spike.Lib.LowerX64

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Emit.X64 (S E Item ld st i64 i32 xr xm om or_ mem emitInst ins rax64 cc callSym safepoint)
open Scc.Lower.InvX64
open Spike.Lib.Form (opdVal)

set_option linter.unusedSimpArgs false

/-! ## The operations -/

/-- `movl %eax, %eax` (`ext false .w32`: zero the upper half). -/
def ext32D : Directive := i32 (.mov (xr .rax) (or_ .rax))
/-- `addq %rcx, %rax`. -/
def addD : Directive := i64 (.add (xr .rax) (or_ .rcx))
/-- `cmpq %rcx, %rax` (the flags of `rax - rcx`). -/
def cmpD : Directive := i64 (.cmp (xr .rax) (or_ .rcx))
/-- `movq %rsi, %rax`. -/
def movRsiD : Directive := i64 (.mov (xr .rax) (or_ .rsi))
/-- `cmov<k> %rdx, %rax`. -/
def cmovD (k : CondCode) : Directive := i64 (.cmovcc k rax64 (xr .rdx))

/-- **`addq`'s run**: `rax := rax + rcx` (wrapping); the flags set. -/
theorem arun_addD {o : SO} (ho : o.kill .rax = o) (lab : String → Int64) (pc : Int64) (σ : AS) (z : Nat) :
    ∃ st, arun lab [(addD, z)] ⟨pc, o, σ⟩ =
      ⟨pc + Int64.ofNat z, o,
        { σ with regs := σ.regs.set64 .rax (σ.regs.get64 .rax + σ.regs.get64 .rcx), status := st }⟩ := by
  simp [addD, arun, dstep, i64, Scc.Emit.X64.op, xr, or_, classify, RegOnly, AI.step, AI.tgt, AI.so,
    soReg, regDst, SO.write, Reg.base, ho, regRes, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.set]
  rw [BitVec.add_comm]

/-- **The select's run** (`select .ult`'s tail): `rax := rdx` when
`rax < rcx` (unsigned, the borrow `cmovb` tests), else `rsi`. -/
theorem arun_sel {o : SO} (ho : o.kill .rax = o) (hsi : o.get .rsi = none)
    (lab : String → Int64) (pc : Int64) (σ : AS) (z1 z2 z3 : Nat) :
    ∃ st, arun lab [(cmpD, z1), (movRsiD, z2), (cmovD .c, z3)] ⟨pc, o, σ⟩ =
      ⟨pc + Int64.ofNat z1 + Int64.ofNat z2 + Int64.ofNat z3, o,
        { σ with status := st, regs := σ.regs.set64 .rax (if (σ.regs.get64 .rax).toNat < (σ.regs.get64 .rcx).toNat
          then σ.regs.get64 .rdx else σ.regs.get64 .rsi) }⟩ := by
  simp [cmpD, movRsiD, cmovD, arun, dstep, i64, Scc.Emit.X64.op, xr, or_, rax64, Scc.Emit.X64.lw, classify, RegOnly,
    AI.step, AI.tgt, AI.so, soReg, regDst, SO.write, Reg.base, ho, regRes, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.setReg, Reg64s.set, StatusFlags.from_result, CondCode.interp,
    ConstExpr.interp, hsi]
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
  · simp only [hc.mpr hle, ↓reduceIte, show ¬ σ.regs.rax.toNat < σ.regs.rcx.toNat by omega]
  · simp only [show ¬ _ from fun h => hle (hc.mp h), ↓reduceIte, show σ.regs.rax.toNat < σ.regs.rcx.toNat by omega]

/-- **`movl %eax, %eax`'s run**: `rax` keeps its low 32 bits. -/
theorem arun_ext32D {o : SO} (ho : o.kill .rax = o) (lab : String → Int64) (pc : Int64) (σ : AS) (z : Nat) :
    arun lab [(ext32D, z)] ⟨pc, o, σ⟩ =
      ⟨pc + Int64.ofNat z, o, { σ with regs := σ.regs.set64 .rax (((σ.regs.get64 .rax).take 32).setWidth 64) }⟩ := by
  simp [ext32D, arun, dstep, i32, Scc.Emit.X64.op, xr, or_, classify, RegOnly, AI.step, AI.tgt, AI.so,
    soReg, regDst, SO.write, Reg.base, ho, regRes, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.get, Reg.offset, BitVec.drop]

theorem toNat_some_injX {x y : BitVec 64} (h : some x.toNat = some y.toNat) : x = y :=
  BitVec.eq_of_toNat_eq (Option.some.inj h)

/-! ## Runs at any cell sizes -/

/-- **A block runs from `σ` into `P`**: at any cell sizes and any pc, the
directives `ds` fall through past their cells, the static offsets `o` kept,
to a state satisfying `P`. -/
def RunsP (lab : String → Int64) (o : SO) (ds : List Directive) (σ : AS) (P : AS → Prop) : Prop :=
  ∀ (zs : List Nat) (pc : Int64), zs.length = ds.length →
    ∃ σ', arun lab (ds.zip zs) ⟨pc, o, σ⟩ = ⟨pc + Int64.ofNat zs.sum, o, σ'⟩ ∧ P σ'

theorem RunsP.mono {lab : String → Int64} {o : SO} {ds : List Directive} {σ : AS} {P Q : AS → Prop}
    (h : RunsP lab o ds σ P) (hPQ : ∀ σ', P σ' → Q σ') : RunsP lab o ds σ Q := fun zs pc hz =>
  let ⟨σ', e, hp⟩ := h zs pc hz
  ⟨σ', e, hPQ σ' hp⟩

theorem RunsP.append {lab : String → Int64} {o : SO} {A B : List Directive} {σ : AS} {P Q : AS → Prop}
    (h1 : RunsP lab o A σ P) (h2 : ∀ σ', P σ' → RunsP lab o B σ' Q) : RunsP lab o (A ++ B) σ Q := by
  intro zs pc hz
  rw [List.length_append] at hz
  have ht : (zs.take A.length).length = A.length := by simp; omega
  have hd : (zs.drop A.length).length = B.length := by simp; omega
  obtain ⟨σ1, e1, hp1⟩ := h1 _ pc ht
  obtain ⟨σ2, e2, hp2⟩ := h2 σ1 hp1 _ (pc + Int64.ofNat (zs.take A.length).sum) hd
  refine ⟨σ2, ?_, hp2⟩
  rw [← List.take_append_drop A.length zs, List.zip_append ht.symm, arun_append, e1, e2, List.sum_append,
    Int64.ofNat_add, Int64.add_assoc]

/-- A one-directive step as a run. -/
theorem RunsP.one {lab : String → Int64} {o : SO} {d : Directive} {σ σ' : AS}
    (h : ∀ pc z, arun lab [(d, z)] ⟨pc, o, σ⟩ = ⟨pc + Int64.ofNat z, o, σ'⟩) : RunsP lab o [d] σ (· = σ') := by
  intro zs pc hz
  obtain ⟨z, rfl⟩ := length_one hz
  exact ⟨σ', by simpa using h pc z, rfl⟩

/-- The body's offsets know only `%rbp`. -/
theorem oB_kill (fr : Scc.Emit.X64.Frame) {r : Reg64} (hr : r ≠ .rbp) : (oB fr).kill r = oB fr := by
  cases r <;> simp_all [oB, SO.kill, rm]

theorem oB_get_rsi (fr : Scc.Emit.X64.Frame) : (oB fr).get .rsi = none := by simp [oB, SO.get, lk]

section Runs

variable {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) (lab : String → Int64)

include hf h1 in
/-- **An operand's load as a run**: `t := ` the operand's value. -/
theorem runsP_getOp {t : Reg64} (ht : t ≠ .rbp) {a : Scc.IR.Operand} {l : List Item} (ha : getOp fr t a = .ok l)
    (σ : AS) : ∃ v : BitVec 64, opdVal (rsOf fr) σ.slot a = some v.toNat ∧
      RunsP lab (oB fr) (dirs l) σ (· = { σ with regs := σ.regs.set64 t v }) := by
  obtain ⟨d, hd⟩ := dirs_getOp ha
  obtain ⟨v, hv, -⟩ := arun_getOp hf h1 ht ha lab 0 σ (zs := [0]) (by simp [hd])
  refine ⟨v, hv, fun zs pc hz => ?_⟩
  obtain ⟨v', hv', e⟩ := arun_getOp hf h1 ht ha lab pc σ hz
  have : v' = v := BitVec.eq_of_toNat_eq (Option.some.inj (hv'.symm.trans hv))
  exact ⟨_, e, by rw [this]⟩

include hf h1 in
/-- **The store of `%rax` into `d`'s slot as a run.** -/
theorem runsP_st {d : Scc.IR.Reg} {off : Int} (hd : rsOf fr d = some off) (σ : AS) :
    RunsP lab (oB fr) [stDir off] σ (· = { σ with slot := upd σ.slot off (σ.regs.get64 .rax) }) := by
  obtain ⟨h8, hm, hle⟩ := rsOf_bounds hf hd
  have ho : (Int64.ofInt off).toInt = off := toInt_ofInt_small (by omega) (by omega)
  have hc : classify (stDir off) = some (AI.st .rbp (Int64.ofInt off) .rax) := rfl
  refine RunsP.one fun pc z => ?_
  simp [arun, dstep, hc, AI.tgt, AI.so, AI.step, oB, SO.get, lk, ho]


include hf h1 in
/-- **Two loads as a run**: `t1`, `t2` get the operands' values. -/
theorem runsP_loads2 {t1 t2 : Reg64} (ht1 : t1 ≠ .rbp) (ht2 : t2 ≠ .rbp) {a b : Scc.IR.Operand}
    {la lb : List Item} (ha : getOp fr t1 a = .ok la) (hb : getOp fr t2 b = .ok lb) (σ : AS) :
    ∃ va vb : BitVec 64, opdVal (rsOf fr) σ.slot a = some va.toNat ∧ opdVal (rsOf fr) σ.slot b = some vb.toNat ∧
      RunsP lab (oB fr) (dirs la ++ dirs lb) σ (· = { σ with regs := (σ.regs.set64 t1 va).set64 t2 vb }) := by
  obtain ⟨va, hva, r1⟩ := runsP_getOp hf h1 lab ht1 ha σ
  obtain ⟨vb, hvb, r2⟩ := runsP_getOp hf h1 lab ht2 hb { σ with regs := σ.regs.set64 t1 va }
  exact ⟨va, vb, hva, hvb, r1.append fun σ1 e1 => e1 ▸ r2⟩

include hf h1 in
/-- **The code of `ext false .w32 d a` as a run**: `a` into `%rax`, `movl
%eax, %eax`, the store; `d`'s slot gets the value's low 32 bits. -/
theorem ext32_runs {a : Scc.IR.Operand} {la : List Item} (ha : getOp fr .rax a = .ok la) {d : Scc.IR.Reg}
    {off : Int} (hd : rsOf fr d = some off) (σ : AS) :
    ∃ va : BitVec 64, opdVal (rsOf fr) σ.slot a = some va.toNat ∧
      RunsP lab (oB fr) (dirs la ++ [ext32D, stDir off]) σ
        (fun σ' => σ'.slot = upd σ.slot off ((va.take 32).setWidth 64)) := by
  obtain ⟨va, hva, r1⟩ := runsP_getOp hf h1 lab (by decide) ha σ
  refine ⟨va, hva, ?_⟩
  rw [show dirs la ++ [ext32D, stDir off] = dirs la ++ ([ext32D] ++ [stDir off]) from rfl]
  refine r1.append fun σ1 e1 => ?_
  subst e1
  refine (RunsP.one fun pc z => arun_ext32D (oB_kill fr (by decide)) lab pc _ z).append fun σ2 e2 => ?_
  subst e2
  refine (runsP_st hf h1 lab hd _).mono fun σ3 e3 => ?_
  subst e3
  simp only [Reg64s.get64_set64_self]

include hf h1 in
/-- **The code of `bin .add d a b` as a run**: `a` into `%rax`, `b` into
`%rcx`, `addq`, the store; `d`'s slot gets the (wrapping) sum. -/
theorem add_runs {a b : Scc.IR.Operand} {la lb : List Item} (ha : getOp fr .rax a = .ok la)
    (hb : getOp fr .rcx b = .ok lb) {d : Scc.IR.Reg} {off : Int} (hd : rsOf fr d = some off) (σ : AS) :
    ∃ va vb : BitVec 64, opdVal (rsOf fr) σ.slot a = some va.toNat ∧ opdVal (rsOf fr) σ.slot b = some vb.toNat ∧
      RunsP lab (oB fr) (dirs la ++ dirs lb ++ [addD, stDir off]) σ (fun σ' => σ'.slot = upd σ.slot off (va + vb)) := by
  obtain ⟨va, vb, hva, hvb, r1⟩ := runsP_loads2 hf h1 lab (by decide) (by decide) ha hb σ
  refine ⟨va, vb, hva, hvb, ?_⟩
  rw [show dirs la ++ dirs lb ++ [addD, stDir off] = (dirs la ++ dirs lb) ++ ([addD] ++ [stDir off]) by simp]
  refine r1.append fun σ1 e1 => ?_
  subst e1
  refine RunsP.append (P := fun σ2 => σ2.regs.get64 .rax = va + vb ∧ σ2.slot = σ.slot) (fun zs pc hz => ?_)
    fun σ2 ⟨e2, es2⟩ => (runsP_st hf h1 lab hd σ2).mono fun σ3 e3 => by rw [e3]; simp only [es2, e2]
  obtain ⟨z, rfl⟩ := length_one hz
  obtain ⟨st, e⟩ := arun_addD (oB_kill fr (by decide)) lab pc _ z
  rw [show [z].sum = z by simp]
  refine ⟨_, e, ?_, rfl⟩
  simp [Reg64s.get64_set64_self, Reg64s.get64_set64_ne]

include hf h1 in
/-- **The code of `select .ult d a b t f` as a run**: `t` into `%rdx`, `f`
into `%rsi`, `a` into `%rax`, `b` into `%rcx`, `cmpq`, `movq %rsi, %rax`,
`cmovb %rdx, %rax`, the store; `d`'s slot gets `t`'s value when `a`'s is
below `b`'s, else `f`'s. -/
theorem select_runs {a b t f : Scc.IR.Operand} {la lb lt lf : List Item} (ht : getOp fr .rdx t = .ok lt)
    (hfo : getOp fr .rsi f = .ok lf) (ha : getOp fr .rax a = .ok la) (hb : getOp fr .rcx b = .ok lb)
    {d : Scc.IR.Reg} {off : Int} (hd : rsOf fr d = some off) (σ : AS) :
    ∃ va vb vt vf : BitVec 64, opdVal (rsOf fr) σ.slot a = some va.toNat ∧
      opdVal (rsOf fr) σ.slot b = some vb.toNat ∧ opdVal (rsOf fr) σ.slot t = some vt.toNat ∧
      opdVal (rsOf fr) σ.slot f = some vf.toNat ∧
      RunsP lab (oB fr) (dirs lt ++ dirs lf ++ dirs la ++ dirs lb ++ [cmpD, movRsiD, cmovD .c, stDir off]) σ
        (fun σ' => σ'.slot = upd σ.slot off (if va.toNat < vb.toNat then vt else vf)) := by
  obtain ⟨vt, vf, hvt, hvf, r1⟩ := runsP_loads2 hf h1 lab (by decide) (by decide) ht hfo σ
  obtain ⟨va, vb, hva, hvb, -⟩ := runsP_loads2 hf h1 lab (by decide) (by decide) ha hb σ
  refine ⟨va, vb, vt, vf, hva, hvb, hvt, hvf, ?_⟩
  rw [show dirs lt ++ dirs lf ++ dirs la ++ dirs lb ++ [cmpD, movRsiD, cmovD .c, stDir off] =
    (dirs lt ++ dirs lf) ++ ((dirs la ++ dirs lb) ++ ([cmpD, movRsiD, cmovD .c] ++ [stDir off])) by simp]
  refine r1.append fun σ1 e1 => ?_
  subst e1
  obtain ⟨va', vb', hva', hvb', r2⟩ := runsP_loads2 hf h1 lab (by decide) (by decide) ha hb
    { σ with regs := (σ.regs.set64 .rdx vt).set64 .rsi vf }
  rw [hva] at hva'
  rw [hvb] at hvb'
  cases toNat_some_injX hva'
  cases toNat_some_injX hvb'
  refine r2.append fun σ2 e2 => ?_
  subst e2
  refine RunsP.append (P := fun σ3 => σ3.regs.get64 .rax = (if va.toNat < vb.toNat then vt else vf) ∧
    σ3.slot = σ.slot) (fun zs pc hz => ?_)
    fun σ3 ⟨e5, es3⟩ => (runsP_st hf h1 lab hd σ3).mono fun σ4 e6 => by rw [e6]; simp only [es3, e5]
  match zs, hz with
  | [z1, z2, z3], _ =>
  obtain ⟨st, e⟩ := arun_sel (oB_kill fr (by decide)) (oB_get_rsi fr) lab pc _ z1 z2 z3
  simp only [List.zip_cons_cons, List.zip_nil_left]
  rw [show pc + Int64.ofNat [z1, z2, z3].sum = pc + Int64.ofNat z1 + Int64.ofNat z2 + Int64.ofNat z3 by
    simp [Int64.ofNat_add, Int64.add_assoc]]
  refine ⟨_, e, ?_, rfl⟩
  simp [Reg64s.get64_set64_self, Reg64s.get64_set64_ne]

/-! ## Slot writes -/

include hf in
/-- A slot write leaves every operand on another register. -/
theorem opdVal_updX {d : Scc.IR.Reg} {off : Int} (hd : rsOf fr d = some off) {a : Scc.IR.Operand}
    (ha : ∀ r, a = .reg r → r ≠ d) (sl : Int → BitVec 64) (v : BitVec 64) :
    opdVal (rsOf fr) (upd sl off v) a = opdVal (rsOf fr) sl a := by
  cases a with
  | imm => rfl
  | reg r =>
    simp only [opdVal]
    cases hr : rsOf fr r with
    | none => rfl
    | some j =>
      simp only [Option.map_some, Option.some.injEq, upd_apply]
      split
      · rename_i hj
        subst hj
        exact absurd (rsOf_inj hf hr hd) (ha r rfl)
      · rfl

/-- A slot write is read back. -/
theorem opdVal_updSelfX {d : Scc.IR.Reg} {off : Int} (hd : rsOf fr d = some off) (sl : Int → BitVec 64)
    (v : BitVec 64) : opdVal (rsOf fr) (upd sl off v) (.reg d) = some v.toNat := by
  simp [opdVal, hd, upd_apply]

/-- A slot write keeps the slots off the written one. -/
theorem upd_offX {d : Scc.IR.Reg} {off : Int} (hd : rsOf fr d = some off) {j : Int}
    (hj : ∀ q, rsOf fr q = some j → q ≠ d) (sl : Int → BitVec 64) (v : BitVec 64) : upd sl off v j = sl j := by
  have : ¬ j = off := fun hj' => hj d (by rw [hd, hj']) rfl
  simp only [upd_apply, this, ↓reduceIte]

/-! ## `print`'s argument block -/

/-- The multiply `imulq %rcx, %rax` (its flags undefined: a node of its own,
`flag_ndW`). -/
abbrev mulFI : FI := .imul_rr .rax .rcx

include hf h1 in
/-- **`print`'s count and the call's arguments**, after the multiply:
`%rax` (`m · 8`) into `cap`'s slot, `k := select (n < cap) n cap`, then `s`,
`k` into `%rdi`, `%rsi`: `%rdi` is `s`'s value and `%rsi` is
`min(n, %rax)` (unsigned); every slot but `cap`'s and `k`'s kept. -/
theorem printPost_runs {cap kk : Scc.IR.Reg} {ocap okk : Int} (hcap : rsOf fr cap = some ocap)
    (hk : rsOf fr kk = some okk) {s n : Scc.IR.Operand} {lN lC lN' lC' lS lK : List Item}
    (hN : getOp fr .rdx n = .ok lN) (hC : getOp fr .rsi (.reg cap) = .ok lC) (hN' : getOp fr .rax n = .ok lN')
    (hC' : getOp fr .rcx (.reg cap) = .ok lC') (hS : getOp fr .rdi s = .ok lS) (hK : getOp fr .rsi (.reg kk) = .ok lK)
    (hn : ∀ r, n = .reg r → r ≠ cap) (hs : ∀ r, s = .reg r → r ≠ cap ∧ r ≠ kk) (σ : AS) :
    ∃ vs vn : BitVec 64, opdVal (rsOf fr) σ.slot s = some vs.toNat ∧ opdVal (rsOf fr) σ.slot n = some vn.toNat ∧
      RunsP lab (oB fr) ([stDir ocap] ++ (dirs lN ++ dirs lC ++ dirs lN' ++ dirs lC' ++
          [cmpD, movRsiD, cmovD .c, stDir okk]) ++ (dirs lS ++ dirs lK)) σ
        (fun σ' => σ'.regs.get64 .rdi = vs ∧
          σ'.regs.get64 .rsi = (if vn.toNat < (σ.regs.get64 .rax).toNat then vn else σ.regs.get64 .rax) ∧
          ∀ j, (∀ q, rsOf fr q = some j → q ≠ cap ∧ q ≠ kk) → σ'.slot j = σ.slot j) := by
  obtain ⟨vn, -, -, -, hvn, -, -, -, -⟩ := select_runs hf h1 lab hN hC hN' hC' hk σ
  obtain ⟨vs, -, hvs, -, -⟩ := runsP_loads2 hf h1 lab (by decide) (by decide) hS hK σ
  refine ⟨vs, vn, hvs, hvn, (runsP_st hf h1 lab hcap σ).append fun σ1 e1 => ?_⟩
  subst e1
  obtain ⟨vn2, vc2, vn1, vc1, hvn2, hvc2, hvn1, hvc1, r2⟩ := select_runs hf h1 lab hN hC hN' hC' hk
    { σ with slot := upd σ.slot ocap (σ.regs.get64 .rax) }
  dsimp only at hvn2 hvc2 hvn1 hvc1
  rw [opdVal_updX hf hcap hn, hvn] at hvn1 hvn2
  rw [opdVal_updSelfX hcap] at hvc1 hvc2
  cases toNat_some_injX hvn1
  cases toNat_some_injX hvn2
  cases toNat_some_injX hvc1
  cases toNat_some_injX hvc2
  refine r2.append fun σ2 e2 => ?_
  obtain ⟨vs', vk, hvs', hvk, r3⟩ := runsP_loads2 hf h1 lab (by decide) (by decide) hS hK σ2
  rw [e2] at hvs' hvk
  dsimp only at hvs'
  rw [opdVal_updX hf hk (fun r h => (hs r h).2), opdVal_updX hf hcap (fun r h => (hs r h).1), hvs] at hvs'
  rw [opdVal_updSelfX hk] at hvk
  cases toNat_some_injX hvs'
  cases toNat_some_injX hvk
  refine r3.mono fun σ3 e3 => ?_
  subst e3
  refine ⟨by simp [Reg64s.get64_set64_self, Reg64s.get64_set64_ne], by simp [Reg64s.get64_set64_self], ?_⟩
  intro j hj
  dsimp only
  rw [e2]
  dsimp only
  rw [upd_offX hk fun q h => (hj q h).2, upd_offX hcap fun q h => (hj q h).1]

/-- The value of `imm 8`. -/
theorem imm8_val {sl : Int → BitVec 64} {v : BitVec 64} (h : opdVal (rsOf fr) sl (Scc.Lower.imm 8) = some v.toNat) :
    v = 8#64 := by
  simp only [opdVal, Scc.Lower.imm] at h
  exact (BitVec.eq_of_toNat_eq (Option.some.inj h)).symm ▸ rfl

include hf h1 in
/-- **`print`'s argument block up to the multiply** (a register offset `o`):
`lo := ext.w32 o`, `s := b + lo`, then `m` into `%rax` and `8` into
`%rcx`. -/
theorem printPre_runs {lo s : Scc.IR.Reg} {olo os : Int} (hlo : rsOf fr lo = some olo) (hs : rsOf fr s = some os)
    {o b m : Scc.IR.Operand} {lO lB lL lM l8 : List Item} (hO : getOp fr .rax o = .ok lO)
    (hB : getOp fr .rax b = .ok lB) (hL : getOp fr .rcx (.reg lo) = .ok lL) (hM : getOp fr .rax m = .ok lM)
    (h8 : getOp fr .rcx (Scc.Lower.imm 8) = .ok l8) (hb : ∀ r, b = .reg r → r ≠ lo)
    (hm : ∀ r, m = .reg r → r ≠ lo ∧ r ≠ s) (σ : AS) :
    ∃ vb vo vm : BitVec 64, opdVal (rsOf fr) σ.slot b = some vb.toNat ∧
      opdVal (rsOf fr) σ.slot o = some vo.toNat ∧ opdVal (rsOf fr) σ.slot m = some vm.toNat ∧
      RunsP lab (oB fr) (dirs lO ++ [ext32D, stDir olo] ++ (dirs lB ++ dirs lL ++ [addD, stDir os]) ++
          (dirs lM ++ dirs l8)) σ
        (fun σ' => σ'.regs.get64 .rax = vm ∧ σ'.regs.get64 .rcx = 8#64 ∧
          σ'.slot = upd (upd σ.slot olo ((vo.take 32).setWidth 64)) os (vb + (vo.take 32).setWidth 64)) := by
  obtain ⟨vo, hvo, r1⟩ := ext32_runs hf h1 lab hO hlo σ
  obtain ⟨vb, hvb, -⟩ := runsP_getOp hf h1 lab (by decide) hB σ
  obtain ⟨vm, hvm, -⟩ := runsP_getOp hf h1 lab (by decide) hM σ
  refine ⟨vb, vo, vm, hvb, hvo, hvm, ?_⟩
  rw [List.append_assoc]
  refine r1.append fun σ1 e1 => ?_
  obtain ⟨vb', vl, hvb', hvl, r2⟩ := add_runs hf h1 lab hB hL hs σ1
  rw [e1, opdVal_updX hf hlo hb, hvb] at hvb'
  rw [e1, opdVal_updSelfX hlo] at hvl
  cases toNat_some_injX hvb'
  cases toNat_some_injX hvl
  refine r2.append fun σ2 e2 => ?_
  obtain ⟨vm', v8, hvm', hv8, r3⟩ := runsP_loads2 hf h1 lab (by decide) (by decide) hM h8 σ2
  rw [e2, e1, opdVal_updX hf hs (fun r h => (hm r h).2), opdVal_updX hf hlo (fun r h => (hm r h).1), hvm] at hvm'
  cases toNat_some_injX hvm'
  cases imm8_val hv8
  refine r3.mono fun σ3 e3 => ?_
  subst e3
  refine ⟨by simp [Reg64s.get64_set64_self, Reg64s.get64_set64_ne], by simp [Reg64s.get64_set64_self], ?_⟩
  dsimp only
  rw [e2, e1]

include hf h1 in
/-- **`print`'s argument block** (`callBlock`'s `.print` case, a register
offset `o`), around the multiply `imulq %rcx, %rax` (`mulFI`, a flag node of
its own): the block before it (`printPre_runs`) and, from the multiply's
step at any flags, the block after it (`printPost_runs`): `%rdi` is
`b + lo(o)` and `%rsi` is `min(n, 8·m)` (unsigned, wrapping), for any
caller's frame and any operands `b`, `o`, `m`, `n` of fresh registers `lo`,
`s`, `cap`, `k`; every other slot kept. -/
theorem printArgs_runs {lo s cap kk : Scc.IR.Reg} {olo os ocap okk : Int} (hlo : rsOf fr lo = some olo)
    (hs : rsOf fr s = some os) (hcap : rsOf fr cap = some ocap) (hk : rsOf fr kk = some okk)
    {o b m n : Scc.IR.Operand} {lO lB lL lM l8 lN lC lN' lC' lS lK : List Item}
    (hO : getOp fr .rax o = .ok lO) (hB : getOp fr .rax b = .ok lB) (hL : getOp fr .rcx (.reg lo) = .ok lL)
    (hM : getOp fr .rax m = .ok lM) (h8 : getOp fr .rcx (Scc.Lower.imm 8) = .ok l8)
    (hN : getOp fr .rdx n = .ok lN) (hC : getOp fr .rsi (.reg cap) = .ok lC) (hN' : getOp fr .rax n = .ok lN')
    (hC' : getOp fr .rcx (.reg cap) = .ok lC') (hS : getOp fr .rdi (.reg s) = .ok lS)
    (hK : getOp fr .rsi (.reg kk) = .ok lK)
    (hb : ∀ r, b = .reg r → r ≠ lo) (hm : ∀ r, m = .reg r → r ≠ lo ∧ r ≠ s)
    (hn : ∀ r, n = .reg r → r ≠ lo ∧ r ≠ s ∧ r ≠ cap) (hsc : s ≠ cap) (hsk : s ≠ kk) (σ : AS) :
    ∃ vb vo vm vn : BitVec 64, opdVal (rsOf fr) σ.slot b = some vb.toNat ∧
      opdVal (rsOf fr) σ.slot o = some vo.toNat ∧ opdVal (rsOf fr) σ.slot m = some vm.toNat ∧
      opdVal (rsOf fr) σ.slot n = some vn.toNat ∧
      RunsP lab (oB fr) (dirs lO ++ [ext32D, stDir olo] ++ (dirs lB ++ dirs lL ++ [addD, stDir os]) ++
          (dirs lM ++ dirs l8)) σ (fun σ1 => ∀ fl : StatusFlags,
        RunsP lab (oB fr) ([stDir ocap] ++ (dirs lN ++ dirs lC ++ dirs lN' ++ dirs lC' ++
            [cmpD, movRsiD, cmovD .c, stDir okk]) ++ (dirs lS ++ dirs lK)) (mulFI.step σ1 fl)
          (fun σ' => σ'.regs.get64 .rdi = vb + (vo.take 32).setWidth 64 ∧
            σ'.regs.get64 .rsi = (if vn.toNat < (vm * 8#64).toNat then vn else vm * 8#64) ∧
            ∀ j, (∀ q, rsOf fr q = some j → q ≠ lo ∧ q ≠ s ∧ q ≠ cap ∧ q ≠ kk) → σ'.slot j = σ.slot j)) := by
  obtain ⟨vb, vo, vm, hvb, hvo, hvm, r1⟩ := printPre_runs hf h1 lab hlo hs hO hB hL hM h8 hb hm σ
  obtain ⟨vn, hvn, -⟩ := runsP_getOp hf h1 lab (by decide) hN σ
  refine ⟨vb, vo, vm, vn, hvb, hvo, hvm, hvn, r1.mono fun σ1 ⟨e9, e10, es⟩ fl => ?_⟩
  obtain ⟨vs, vn', hvs, hvn', r2⟩ := printPost_runs hf h1 lab hcap hk hN hC hN' hC' hS hK
    (fun r h => (hn r h).2.2) (fun r h => by cases h; exact ⟨hsc, hsk⟩) (mulFI.step σ1 fl)
  simp only [FI.step] at hvs hvn' r2
  rw [es, opdVal_updSelfX hs] at hvs
  rw [es, opdVal_updX hf hs (fun r h => (hn r h).2.1), opdVal_updX hf hlo (fun r h => (hn r h).1), hvn] at hvn'
  cases toNat_some_injX hvs
  cases toNat_some_injX hvn'
  refine r2.mono fun σ' ⟨ed, esi, esl⟩ => ⟨ed, ?_, fun j hj => ?_⟩
  · rw [esi]
    simp [FI.regs, Reg64s.get64_set64_self, e9, e10]
  · rw [esl j fun q h => ⟨(hj q h).2.2.1, (hj q h).2.2.2⟩, es, upd_offX hs fun q h => (hj q h).2.1,
      upd_offX hlo fun q h => (hj q h).1]

include hf h1 in
/-- **`print`'s argument block up to the multiply at an immediate offset
`w ≠ 0`** on a register base (`offAdd b (.imm w)`): `s := b + w`, then `m`
into `%rax` and `8` into `%rcx`. -/
theorem printPreImm_runs {s : Scc.IR.Reg} {os : Int} (hs : rsOf fr s = some os) {b m : Scc.IR.Operand} {w : UInt64}
    {lB lW lM l8 : List Item} (hB : getOp fr .rax b = .ok lB) (hW : getOp fr .rcx (.imm w) = .ok lW)
    (hM : getOp fr .rax m = .ok lM) (h8 : getOp fr .rcx (Scc.Lower.imm 8) = .ok l8)
    (hm : ∀ r, m = .reg r → r ≠ s) (σ : AS) :
    ∃ vb vm : BitVec 64, opdVal (rsOf fr) σ.slot b = some vb.toNat ∧ opdVal (rsOf fr) σ.slot m = some vm.toNat ∧
      RunsP lab (oB fr) ((dirs lB ++ dirs lW ++ [addD, stDir os]) ++ (dirs lM ++ dirs l8)) σ
        (fun σ' => σ'.regs.get64 .rax = vm ∧ σ'.regs.get64 .rcx = 8#64 ∧
          σ'.slot = upd σ.slot os (vb + w.toBitVec)) := by
  obtain ⟨vb, vw, hvb, hvw, r1⟩ := add_runs hf h1 lab hB hW hs σ
  obtain ⟨vm, hvm, -⟩ := runsP_getOp hf h1 lab (by decide) hM σ
  have evw : vw = w.toBitVec := by
    simp only [opdVal] at hvw
    exact BitVec.eq_of_toNat_eq (by rw [← Option.some.inj hvw]; rfl)
  subst evw
  refine ⟨vb, vm, hvb, hvm, r1.append fun σ1 e1 => ?_⟩
  obtain ⟨vm', v8, hvm', hv8, r3⟩ := runsP_loads2 hf h1 lab (by decide) (by decide) hM h8 σ1
  rw [e1, opdVal_updX hf hs hm, hvm] at hvm'
  cases toNat_some_injX hvm'
  cases imm8_val hv8
  refine r3.mono fun σ3 e3 => ?_
  subst e3
  exact ⟨by simp [Reg64s.get64_set64_self, Reg64s.get64_set64_ne], by simp [Reg64s.get64_set64_self], e1⟩

include hf h1 in
/-- **`print`'s argument block at an immediate offset `w ≠ 0`** on a
register base: `printPreImm_runs`, the multiply, `printPost_runs`; `%rdi`
is `b + w`. -/
theorem printArgsImm_runs {s cap kk : Scc.IR.Reg} {os ocap okk : Int} (hs : rsOf fr s = some os)
    (hcap : rsOf fr cap = some ocap) (hk : rsOf fr kk = some okk) {b m n : Scc.IR.Operand} {w : UInt64}
    {lB lW lM l8 lN lC lN' lC' lS lK : List Item}
    (hB : getOp fr .rax b = .ok lB) (hW : getOp fr .rcx (.imm w) = .ok lW)
    (hM : getOp fr .rax m = .ok lM) (h8 : getOp fr .rcx (Scc.Lower.imm 8) = .ok l8)
    (hN : getOp fr .rdx n = .ok lN) (hC : getOp fr .rsi (.reg cap) = .ok lC) (hN' : getOp fr .rax n = .ok lN')
    (hC' : getOp fr .rcx (.reg cap) = .ok lC') (hS : getOp fr .rdi (.reg s) = .ok lS)
    (hK : getOp fr .rsi (.reg kk) = .ok lK)
    (hm : ∀ r, m = .reg r → r ≠ s) (hn : ∀ r, n = .reg r → r ≠ s ∧ r ≠ cap) (hsc : s ≠ cap) (hsk : s ≠ kk)
    (σ : AS) :
    ∃ vb vm vn : BitVec 64, opdVal (rsOf fr) σ.slot b = some vb.toNat ∧
      opdVal (rsOf fr) σ.slot m = some vm.toNat ∧ opdVal (rsOf fr) σ.slot n = some vn.toNat ∧
      RunsP lab (oB fr) ((dirs lB ++ dirs lW ++ [addD, stDir os]) ++ (dirs lM ++ dirs l8)) σ
        (fun σ1 => ∀ fl : StatusFlags,
        RunsP lab (oB fr) ([stDir ocap] ++ (dirs lN ++ dirs lC ++ dirs lN' ++ dirs lC' ++
            [cmpD, movRsiD, cmovD .c, stDir okk]) ++ (dirs lS ++ dirs lK)) (mulFI.step σ1 fl)
          (fun σ' => σ'.regs.get64 .rdi = vb + w.toBitVec ∧
            σ'.regs.get64 .rsi = (if vn.toNat < (vm * 8#64).toNat then vn else vm * 8#64) ∧
            ∀ j, (∀ q, rsOf fr q = some j → q ≠ s ∧ q ≠ cap ∧ q ≠ kk) → σ'.slot j = σ.slot j)) := by
  obtain ⟨vb, vm, hvb, hvm, r1⟩ := printPreImm_runs hf h1 lab hs hB hW hM h8 hm σ
  obtain ⟨vn, hvn, -⟩ := runsP_getOp hf h1 lab (by decide) hN σ
  refine ⟨vb, vm, vn, hvb, hvm, hvn, r1.mono fun σ1 ⟨e9, e10, es⟩ fl => ?_⟩
  obtain ⟨vs, vn', hvs, hvn', r2⟩ := printPost_runs hf h1 lab hcap hk hN hC hN' hC' hS hK
    (fun r h => (hn r h).2) (fun r h => by cases h; exact ⟨hsc, hsk⟩) (mulFI.step σ1 fl)
  simp only [FI.step] at hvs hvn' r2
  rw [es, opdVal_updSelfX hs] at hvs
  rw [es, opdVal_updX hf hs (fun r h => (hn r h).1), hvn] at hvn'
  cases toNat_some_injX hvs
  cases toNat_some_injX hvn'
  refine r2.mono fun σ' ⟨ed, esi, esl⟩ => ⟨ed, ?_, fun j hj => ?_⟩
  · rw [esi]
    simp [FI.regs, Reg64s.get64_set64_self, e9, e10]
  · rw [esl j fun q h => ⟨(hj q h).2.1, (hj q h).2.2⟩, es, upd_offX hs fun q h => (hj q h).1]

end Runs

/-! ## The code -/

section Code

variable {fr : Scc.Emit.X64.Frame}

/-- A slot's offset in any emitter state. -/
theorem slotOff_of_rsOf {d : Scc.IR.Reg} {off : Int} (h : rsOf fr d = some off) (s : S) :
    fr.slotOff d s = .ok (off, s) := by
  unfold rsOf at h
  cases h1 : fr.slotOff d {} with
  | error _ => simp [h1] at h
  | ok q =>
    obtain ⟨o, s'⟩ := q
    simp only [h1, Option.some.injEq] at h
    subst h
    exact slotOff_state h1 s

/-- **`%rax`'s store into `d`'s slot** (`st fr .rax d`) appends `stDir`. -/
theorem st_rax {d : Scc.IR.Reg} {off : Int} (hd : rsOf fr d = some off) (s : S) :
    st fr .rax d s = .ok ((), { s with out := .d (stDir off) :: s.out }) := by
  simp only [st, Scc.Emit.X64.Frame.slot, bind, StateT.bind, slotOff_of_rsOf hd s, pure, StateT.pure, Except.pure,
    Except.bind, ins, Scc.Emit.X64.item, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
  rfl

/-- **The code of `ext false .w32 d a`**: `a` into `%rax`, `movl %eax,
%eax`, the store. -/
theorem emitInst_ext32_items {a : Scc.IR.Operand} {la : List Item} (ha : getOp fr .rax a = .ok la) {d : Scc.IR.Reg}
    {off : Int} (hd : rsOf fr d = some off) (sm : Option Scc.IR.StackMap.Entry) (s : S) :
    emitInst fr sm (.ext false .w32 d a) s =
      .ok ((), { s with out := (la ++ [Item.d ext32D, Item.d (stDir off)]).reverse ++ s.out }) := by
  simp only [emitInst, bind, StateT.bind, ld_getOp ha s, ins, Scc.Emit.X64.item, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure, Except.pure, Except.bind, st_rax hd]
  simp [ext32D]

/-- **The code of `bin .add d a b`**: `a` into `%rax`, `b` into `%rcx`,
`addq`, the store. -/
theorem emitInst_add_items {a b : Scc.IR.Operand} {la lb : List Item} (ha : getOp fr .rax a = .ok la)
    (hb : getOp fr .rcx b = .ok lb) {d : Scc.IR.Reg} {off : Int} (hd : rsOf fr d = some off)
    (sm : Option Scc.IR.StackMap.Entry) (s : S) :
    emitInst fr sm (.bin .add d a b) s =
      .ok ((), { s with out := (la ++ lb ++ [Item.d addD, Item.d (stDir off)]).reverse ++ s.out }) := by
  simp only [emitInst, bind, StateT.bind, ld_getOp ha s, ld_getOp hb, ins, Scc.Emit.X64.item, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure, Except.pure, Except.bind, st_rax hd]
  simp [addD]

/-- **The code of `bin .mul d a b`**: `a` into `%rax`, `b` into `%rcx`,
`imulq` (`mulFI`), the store. -/
theorem emitInst_mul_items {a b : Scc.IR.Operand} {la lb : List Item} (ha : getOp fr .rax a = .ok la)
    (hb : getOp fr .rcx b = .ok lb) {d : Scc.IR.Reg} {off : Int} (hd : rsOf fr d = some off)
    (sm : Option Scc.IR.StackMap.Entry) (s : S) :
    emitInst fr sm (.bin .mul d a b) s =
      .ok ((), { s with out := (la ++ lb ++ [Item.d mulFI.toDir, Item.d (stDir off)]).reverse ++ s.out }) := by
  simp only [emitInst, bind, StateT.bind, ld_getOp ha s, ld_getOp hb, ins, Scc.Emit.X64.item, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure, Except.pure, Except.bind, st_rax hd]
  simp
  rfl

/-- **The code of `select .ult d a b t f`**: `t` into `%rdx`, `f` into
`%rsi`, `a` into `%rax`, `b` into `%rcx`, `cmpq`, `movq %rsi, %rax`, `cmovb
%rdx, %rax`, the store. -/
theorem emitInst_select_items {a b t f : Scc.IR.Operand} {la lb lt lf : List Item} (ht : getOp fr .rdx t = .ok lt)
    (hfo : getOp fr .rsi f = .ok lf) (ha : getOp fr .rax a = .ok la) (hb : getOp fr .rcx b = .ok lb)
    {d : Scc.IR.Reg} {off : Int} (hd : rsOf fr d = some off) (sm : Option Scc.IR.StackMap.Entry) (s : S) :
    emitInst fr sm (.select .ult d a b t f) s = .ok ((), { s with out :=
      (lt ++ lf ++ la ++ lb ++ [Item.d cmpD, Item.d movRsiD, Item.d (cmovD .c), Item.d (stDir off)]).reverse ++
        s.out }) := by
  simp only [emitInst, Scc.Emit.X64.cmpAB, Scc.Emit.X64.movRR, bind, StateT.bind, ld_getOp ht s, ld_getOp hfo,
    ld_getOp ha, ld_getOp hb, ins, Scc.Emit.X64.item, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    pure, StateT.pure, Except.pure, Except.bind, st_rax hd]
  simp [cmpD, movRsiD, cmovD, cc]

/-- **The code of a call of `print`** (`call [] print [s, k]`): `s` into
`%rdi`, `k` into `%rsi`, `call scc_rt_print`, then the safepoint. -/
theorem emitInst_print (fr : Scc.Emit.X64.Frame) (sm : Option Scc.IR.StackMap.Entry) (s k : Scc.IR.Operand) :
    emitInst fr sm (.call [] Scc.Lower.Names.print [s, k]) =
      (do ld fr s .rdi; ld fr k .rsi; callSym Scc.Lower.Names.print; safepoint fr sm) := by
  simp [emitInst, Scc.Emit.X64.callArgs, Scc.Emit.X64.loadArgs, Scc.Emit.X64.argRegs, Scc.Emit.X64.retRegs,
    Scc.IR.maxArgs, forIn, ForIn.forIn, List.forIn', List.zipIdx]
  rfl

/-- **The code of a call of `print`** in a frame placing no safepoint
labels: the argument loads and `call scc_rt_print`. -/
theorem emitInst_print_items (hm : fr.maps = false) {s k : Scc.IR.Operand} {ls lk : List Item}
    (hs : getOp fr .rdi s = .ok ls) (hk : getOp fr .rsi k = .ok lk) (sm : Option Scc.IR.StackMap.Entry) (st : S) :
    emitInst fr sm (.call [] Scc.Lower.Names.print [s, k]) st = .ok ((), { st with out :=
      (ls ++ lk ++ [Item.d (i64 (.call (Scc.Emit.X64.rel Scc.Lower.Names.print)))]).reverse ++ st.out }) := by
  rw [emitInst_print]
  simp only [bind, StateT.bind, ld_getOp hs st, ld_getOp hk, callSym, ins, Scc.Emit.X64.item, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure, Except.pure, Except.bind, safepoint, hm]
  simp
  rfl

end Code

/-! ## Coverage -/

/-- **A block is covered as a prefix**: at any cell sizes, the directives
`ds` are covered in `[lo, hi)` from the static offsets `o`, which they keep,
and none of them branches. -/
def CovP (lo hi : Int) (o : SO) (ds : List Directive) : Prop :=
  ∀ (zs : List Nat) (rest : List (Directive × Nat)), zs.length = ds.length →
    okBlk lo hi o (ds.zip zs ++ rest) = okBlk lo hi o rest

theorem CovP.append {lo hi : Int} {o : SO} {A B : List Directive} (hA : CovP lo hi o A) (hB : CovP lo hi o B) :
    CovP lo hi o (A ++ B) := by
  intro zs rest hz
  rw [List.length_append] at hz
  have ht : (zs.take A.length).length = A.length := by simp; omega
  have hd : (zs.drop A.length).length = B.length := by simp; omega
  rw [← List.take_append_drop A.length zs, List.zip_append ht.symm, List.append_assoc, hA _ _ ht, hB _ _ hd]

theorem CovP.nil {lo hi : Int} {o : SO} : CovP lo hi o [] := fun zs rest _ => by simp

/-- A covered block is covered. -/
theorem CovP.ok {lo hi : Int} {o : SO} {ds : List Directive} (h : CovP lo hi o ds) {zs : List Nat}
    (hz : zs.length = ds.length) : okBlk lo hi o (ds.zip zs) = true := by
  rw [← List.append_nil (ds.zip zs), h zs [] hz]; rfl

theorem CovP.one {lo hi : Int} {o : SO} {d : Directive}
    (h : ∀ z rest, okBlk lo hi o ((d, z) :: rest) = okBlk lo hi o rest) : CovP lo hi o [d] := by
  intro zs rest hz
  obtain ⟨z, rfl⟩ := length_one hz
  exact h z rest

theorem covP_ops {lo hi : Int} {o : SO} (ho : o.kill .rax = o) (hsi : o.get .rsi = none) :
    CovP lo hi o [ext32D] ∧ CovP lo hi o [addD] ∧ CovP lo hi o [cmpD, movRsiD, cmovD .c] := by
  refine ⟨CovP.one fun z rest => ?_, CovP.one fun z rest => ?_, fun zs rest hz => ?_⟩
  · simp [ext32D, okBlk, i32, Scc.Emit.X64.op, xr, or_, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg,
      regDst, SO.write, Reg.base, ho]
  · simp [addD, okBlk, i64, Scc.Emit.X64.op, xr, or_, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg,
      regDst, SO.write, Reg.base, ho]
  · match zs, hz with
    | [z1, z2, z3], _ =>
    simp [cmpD, movRsiD, cmovD, okBlk, i64, Scc.Emit.X64.op, xr, or_, rax64, Scc.Emit.X64.lw, classify, RegOnly,
      AI.ok, AI.so, AI.isTerm, soReg, regDst, SO.write, Reg.base, ho, hsi]

section Cov

variable {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)

include hf h1 in
theorem covP_getOp {t : Reg64} (ht : t ≠ .rsp) (ht' : t ≠ .rbp) {a : Scc.IR.Operand} {l : List Item}
    (ha : getOp fr t a = .ok l) : CovP (-(fr.size : Int)) 16 (oB fr) (dirs l) :=
  fun _ rest hz => okBlk_getOp hf h1 ht ht' ha hz rest

include hf h1 in
theorem covP_st {d : Scc.IR.Reg} {off : Int} (hd : rsOf fr d = some off) :
    CovP (-(fr.size : Int)) 16 (oB fr) [stDir off] := by
  obtain ⟨h8, hm, hle⟩ := rsOf_bounds hf hd
  have ho : (Int64.ofInt off).toInt = off := toInt_ofInt_small (by omega) (by omega)
  have hc : classify (stDir off) = some (AI.st .rbp (Int64.ofInt off) .rax) := rfl
  refine CovP.one fun z rest => ?_
  simp [okBlk, hc, AI.ok, AI.isTerm, AI.so, oB, SO.get, lk, ho, offOk]
  intro _; omega

include hf h1 in
/-- **`print`'s argument block before the multiply is covered** in the
frame's region (`printPre_runs`' code). -/
theorem covP_printPre {lo s : Scc.IR.Reg} {olo os : Int} (hlo : rsOf fr lo = some olo) (hs : rsOf fr s = some os)
    {o b m : Scc.IR.Operand} {lO lB lL lM l8 : List Item} (hO : getOp fr .rax o = .ok lO)
    (hB : getOp fr .rax b = .ok lB) (hL : getOp fr .rcx (.reg lo) = .ok lL) (hM : getOp fr .rax m = .ok lM)
    (h8 : getOp fr .rcx (Scc.Lower.imm 8) = .ok l8) :
    CovP (-(fr.size : Int)) 16 (oB fr) (dirs lO ++ [ext32D, stDir olo] ++
      (dirs lB ++ dirs lL ++ [addD, stDir os]) ++ (dirs lM ++ dirs l8)) := by
  obtain ⟨ce, ca, -⟩ := covP_ops (lo := -(fr.size : Int)) (hi := 16) (oB_kill fr (r := .rax) (by decide))
    (oB_get_rsi fr)
  have g := fun {t} (ht : t ≠ .rsp) (ht' : t ≠ .rbp) {a} {l} (h : getOp fr t a = .ok l) =>
    covP_getOp hf h1 ht ht' h
  exact ((((g (by decide) (by decide) hO).append (ce.append (covP_st hf h1 hlo))).append
    (((g (by decide) (by decide) hB).append (g (by decide) (by decide) hL)).append
      (ca.append (covP_st hf h1 hs)))).append
    ((g (by decide) (by decide) hM).append (g (by decide) (by decide) h8)))

include hf h1 in
/-- **`print`'s argument block before the multiply at an immediate offset
is covered** (`printPreImm_runs`' code). -/
theorem covP_printPreImm {s : Scc.IR.Reg} {os : Int} (hs : rsOf fr s = some os) {b m : Scc.IR.Operand}
    {w : UInt64} {lB lW lM l8 : List Item} (hB : getOp fr .rax b = .ok lB) (hW : getOp fr .rcx (.imm w) = .ok lW)
    (hM : getOp fr .rax m = .ok lM) (h8 : getOp fr .rcx (Scc.Lower.imm 8) = .ok l8) :
    CovP (-(fr.size : Int)) 16 (oB fr) ((dirs lB ++ dirs lW ++ [addD, stDir os]) ++ (dirs lM ++ dirs l8)) := by
  obtain ⟨-, ca, -⟩ := covP_ops (lo := -(fr.size : Int)) (hi := 16) (oB_kill fr (r := .rax) (by decide))
    (oB_get_rsi fr)
  have g := fun {t} (ht : t ≠ .rsp) (ht' : t ≠ .rbp) {a} {l} (h : getOp fr t a = .ok l) =>
    covP_getOp hf h1 ht ht' h
  exact (((g (by decide) (by decide) hB).append (g (by decide) (by decide) hW)).append
      (ca.append (covP_st hf h1 hs))).append
    ((g (by decide) (by decide) hM).append (g (by decide) (by decide) h8))

include hf h1 in
/-- **`print`'s argument block after the multiply is covered**
(`printPost_runs`' code). -/
theorem covP_printPost {cap kk : Scc.IR.Reg} {ocap okk : Int} (hcap : rsOf fr cap = some ocap)
    (hk : rsOf fr kk = some okk) {s n : Scc.IR.Operand} {lN lC lN' lC' lS lK : List Item}
    (hN : getOp fr .rdx n = .ok lN) (hC : getOp fr .rsi (.reg cap) = .ok lC) (hN' : getOp fr .rax n = .ok lN')
    (hC' : getOp fr .rcx (.reg cap) = .ok lC') (hS : getOp fr .rdi s = .ok lS)
    (hK : getOp fr .rsi (.reg kk) = .ok lK) :
    CovP (-(fr.size : Int)) 16 (oB fr) ([stDir ocap] ++ (dirs lN ++ dirs lC ++ dirs lN' ++ dirs lC' ++
      [cmpD, movRsiD, cmovD .c, stDir okk]) ++ (dirs lS ++ dirs lK)) := by
  obtain ⟨-, -, cs⟩ := covP_ops (lo := -(fr.size : Int)) (hi := 16) (oB_kill fr (r := .rax) (by decide))
    (oB_get_rsi fr)
  have g := fun {t} (ht : t ≠ .rsp) (ht' : t ≠ .rbp) {a} {l} (h : getOp fr t a = .ok l) =>
    covP_getOp hf h1 ht ht' h
  rw [show [cmpD, movRsiD, cmovD .c, stDir okk] = [cmpD, movRsiD, cmovD .c] ++ [stDir okk] from rfl]
  exact ((covP_st hf h1 hcap).append
    ((((g (by decide) (by decide) hN).append (g (by decide) (by decide) hC)).append
      (g (by decide) (by decide) hN')).append (g (by decide) (by decide) hC') |>.append
      (cs.append (covP_st hf h1 hk)))).append
    ((g (by decide) (by decide) hS).append (g (by decide) (by decide) hK))

end Cov

end Spike.Lib.LowerX64
