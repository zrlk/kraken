/-
Kraken AArch64 - acquire/release, exclusive, atomic and barrier instructions

The single-threaded meaning of the instructions that the weak-memory layer
(`Kraken/Promising`) gives a concurrent meaning to, stepped through with `kstep`
on memory the thread owns (`h_mem`), in the style of `Examples.lean`. The
`@[kspec]` lemmas used are `loadK_sep`, `storeK_sep`, `storeK_xcl_sep` and
`rmwK_sep` in `Kraken/AArch64/Sep.lean`; barriers are skips (`Effects.All` of
`fence`).

`kstep` stops where the program text does not determine the outcome: at a `CAS`
compare (decide it from a hypothesis, then step on), and at the success of a
store-exclusive (`cases` on it, then step each branch).
-/

import Kraken.AArch64.Examples.Examples  -- for its `ksimp` set

open Kraken.AArch64
open Kraken.AArch64.Parser
open Std
open Std.ExtHashMap

/-- A 64-bit value read back from its bytes. -/
private theorem ofInt_ofBytes_toBytes64 (v : UInt64) :
    BitVec.ofInt 64 (Int.ofBytes v.toBytes) = v.toBitVec :=
  BitVec.ofInt_ofBytes_toBytes 64 8 rfl v.toBitVec

-- Release store, barriers, acquire loads.
def stlr_ldar : Program := parseAArch64("
    stlr x1, [x0]
    dmb ish
    dmb ishld
    dsb sy
    isb
    ldar x2, [x0]
    ldapr x3, [x0]
")

theorem stlr_ldar_correct [layout : Layout] (s₀ : MachineData)
    (v : UInt64) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (v.At s₀.regs.X0.toBitVec) ⋆ R) :
    Eventually (straightlineStep (layout stlr_ldar))
      (fun s' => s'.1.regs.X2 = s₀.regs.X1 ∧ s'.1.regs.X3 = s₀.regs.X1)
      (s₀, layout.start) := by
  apply step_cps
  kprologue stlr_ldar with s₀
  have h_bs : v.toBytes.length = 8 := UInt64.toBytes_length v
  simp at h_mem
  have h_mem' := Mem.storeInt_sep X0.toBitVec 8 v.toBytes R mem ⟨h_mem, h_bs⟩ X1.toBitVec.toInt
  sym =>
  kstep
  case h_mem => tactic => simp; exact h_mem
  case h_len => exact h_bs
  kstep
  case h_mem => tactic => simp; exact h_mem'
  case h_len => tactic => rfl
  kstep
  case h_mem => tactic => simp; exact h_mem'
  case h_len => tactic => rfl
  kstep
  tactic =>
  apply Eventually.done
  rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  exact ⟨rfl, rfl⟩

-- Atomic add: the old value is returned, the sum is stored.
def ldadd : Program := parseAArch64("
    ldaddal x1, x2, [x0]
    ldr x3, [x0]
")

theorem ldadd_correct [layout : Layout] (s₀ : MachineData)
    (v : UInt64) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (v.At s₀.regs.X0.toBitVec) ⋆ R) :
    Eventually (straightlineStep (layout ldadd))
      (fun s' => s'.1.regs.X2 = v ∧ s'.1.regs.X3 = v + s₀.regs.X1)
      (s₀, layout.start) := by
  apply step_cps
  kprologue ldadd with s₀
  have h_bs : v.toBytes.length = 8 := UInt64.toBytes_length v
  simp at h_mem
  have h_mem' := Mem.storeInt_sep X0.toBitVec 8 v.toBytes R mem ⟨h_mem, h_bs⟩
    (v.toBitVec + X1.toBitVec).toInt
  sym =>
  kstep
  case h_mem => tactic => simp; exact h_mem
  case h_len => exact h_bs
  kstep
  case h_mem => tactic =>
    rename_i arg  -- the instruction's let-bound `Xs` operand
    simp only [arg, ofInt_ofBytes_toBytes64, BitVec.extractLsb'_eq_self, Int64.reduceToInt,
      BitVec.ofInt_ofNat, BitVec.add_zero]
    exact h_mem'
  case h_len => tactic => rfl
  kstep
  tactic =>
  apply Eventually.done
  simp only [ofInt_ofBytes_toBytes64, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, true_and]
  rfl

-- Swap: the old value is returned, the register is stored.
def swp : Program := parseAArch64("
    swpal x1, x2, [x0]
    ldr x3, [x0]
")

theorem swp_correct [layout : Layout] (s₀ : MachineData)
    (v : UInt64) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (v.At s₀.regs.X0.toBitVec) ⋆ R) :
    Eventually (straightlineStep (layout swp))
      (fun s' => s'.1.regs.X2 = v ∧ s'.1.regs.X3 = s₀.regs.X1)
      (s₀, layout.start) := by
  apply step_cps
  kprologue swp with s₀
  have h_bs : v.toBytes.length = 8 := UInt64.toBytes_length v
  simp at h_mem
  have h_mem' := Mem.storeInt_sep X0.toBitVec 8 v.toBytes R mem ⟨h_mem, h_bs⟩ X1.toBitVec.toInt
  sym =>
  kstep
  case h_mem => tactic => simp; exact h_mem
  case h_len => exact h_bs
  kstep
  case h_mem => tactic =>
    rename_i new  -- the instruction's let-bound `Xs` operand
    simp only [new, BitVec.extractLsb'_eq_self, Int64.reduceToInt, BitVec.ofInt_ofNat,
      BitVec.add_zero]
    exact h_mem'
  case h_len => tactic => rfl
  kstep
  tactic =>
  apply Eventually.done
  simp only [ofInt_ofBytes_toBytes64, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, true_and]

-- Compare-and-swap whose compare succeeds: the store happens, and `x1` receives
-- the old value either way.
def cas : Program := parseAArch64("
    casal x1, x2, [x0]
    ldr x3, [x0]
")

theorem cas_success [layout : Layout] (s₀ : MachineData)
    (v : UInt64) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (v.At s₀.regs.X0.toBitVec) ⋆ R)
    (h_eq : s₀.regs.X1 = v) :
    Eventually (straightlineStep (layout cas))
      (fun s' => s'.1.regs.X1 = v ∧ s'.1.regs.X3 = s₀.regs.X2)
      (s₀, layout.start) := by
  apply step_cps
  kprologue cas with s₀
  have h_bs : v.toBytes.length = 8 := UInt64.toBytes_length v
  simp at h_mem h_eq
  have h_mem' := Mem.storeInt_sep X0.toBitVec 8 v.toBytes R mem ⟨h_mem, h_bs⟩ X2.toBitVec.toInt
  sym =>
  kstep
  case h_mem => tactic => simp; exact h_mem
  case h_len => exact h_bs
  tactic =>
  rename_i cmp new
  -- The compare: kstep stops at the `match` on its outcome.
  simp only [cmp, ofInt_ofBytes_toBytes64, BitVec.extractLsb'_eq_self, h_eq, beq_self_eq_true,
    ite_true]
  sym =>
  kstep
  case h_mem => tactic =>
    simp only [new, BitVec.extractLsb'_eq_self, Int64.reduceToInt, BitVec.ofInt_ofNat,
      BitVec.add_zero]
    exact h_mem'
  case h_len => tactic => rfl
  kstep
  tactic =>
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, true_and]

-- The same compare-and-swap when the compare fails: nothing is stored.
theorem cas_failure [layout : Layout] (s₀ : MachineData)
    (v : UInt64) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (v.At s₀.regs.X0.toBitVec) ⋆ R)
    (h_ne : s₀.regs.X1 ≠ v) :
    Eventually (straightlineStep (layout cas))
      (fun s' => s'.1.regs.X1 = v ∧ s'.1.regs.X3 = v)
      (s₀, layout.start) := by
  apply step_cps
  kprologue cas with s₀
  have h_bs : v.toBytes.length = 8 := UInt64.toBytes_length v
  simp at h_mem h_ne
  have h_c : (v.toBitVec == X1.toBitVec) = false := by
    rw [beq_eq_false_iff_ne]
    exact fun h => h_ne (UInt64.toBitVec_inj.mp h).symm
  sym =>
  kstep
  case h_mem => tactic => simp; exact h_mem
  case h_len => exact h_bs
  tactic =>
  rename_i cmp _new
  simp only [cmp, ofInt_ofBytes_toBytes64, BitVec.extractLsb'_eq_self, h_c, Bool.false_eq_true,
    ite_false]
  sym =>
  kstep
  case h_mem => tactic => simp; exact h_mem
  case h_len => exact h_bs
  kstep
  tactic =>
  apply Eventually.done
  simp only [ofInt_ofBytes_toBytes64, true_and]

-- Load-exclusive/store-exclusive: the store-exclusive may fail, and `w3` reports
-- whether it did (0 on success).
def ldxr_stxr : Program := parseAArch64("
    ldaxr x2, [x0]
    stlxr w3, x1, [x0]
    ldr x4, [x0]
")

theorem ldxr_stxr_correct [layout : Layout] (s₀ : MachineData)
    (v : UInt64) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (v.At s₀.regs.X0.toBitVec) ⋆ R) :
    Eventually (straightlineStep (layout ldxr_stxr))
      (fun s' => s'.1.regs.X2 = v ∧
        (s'.1.regs.X3 = 0 ∧ s'.1.regs.X4 = s₀.regs.X1 ∨ s'.1.regs.X3 = 1 ∧ s'.1.regs.X4 = v))
      (s₀, layout.start) := by
  apply step_cps
  kprologue ldxr_stxr with s₀
  have h_bs : v.toBytes.length = 8 := UInt64.toBytes_length v
  simp at h_mem
  have h_mem' := Mem.storeInt_sep X0.toBitVec 8 v.toBytes R mem ⟨h_mem, h_bs⟩ X1.toBitVec.toInt
  sym =>
  kstep
  case h_mem => tactic => simp; exact h_mem
  case h_len => exact h_bs
  kstep
  case h_mem => tactic => simp; exact h_mem
  case h_len => exact h_bs
  kstep
  -- kstep stops at the `undefined` outcome of the store-exclusive.
  tactic =>
  rename_i ok
  cases ok
  case false =>
    sym =>
    kstep
    case h_mem => tactic => simp; exact h_mem
    case h_len => exact h_bs
    kstep
    tactic =>
    apply Eventually.done
    simp [ofInt_ofBytes_toBytes64]
  case true =>
    sym =>
    kstep
    case h_mem => tactic => simp; exact h_mem'
    case h_len => tactic => rfl
    kstep
    tactic =>
    apply Eventually.done
    simp [ofInt_ofBytes_toBytes64, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
