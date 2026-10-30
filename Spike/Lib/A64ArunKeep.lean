/-
**What a block's prefixes keep** (AArch64): facts of the
abstract state that every directive of a block keeps hold at every prefix
`arun lab (blk.take k)`, the states `BlkW` (`Spike/Lib/A64Nodes.lean`) and
`seg_ndW`'s `hW` quantify over. Generic in the block, the labels and the
thread: a `BlkW` obligation that needs a register's or a cell's value at a
block's internal states (a word's place for `Placed`, an address for a
mapping test) reduces to the per-directive facts, which `simp` decides on
the concrete directives (as `LowerA64.ProW2.dstep_chkHead` does).

- `arun_take_inv`: a predicate on the abstract machine kept by every
  directive holds at every prefix.
- `arun_take_reg`: a register no directive writes keeps its value.
- `arun_take_slot`: a cell no directive writes keeps its value.
- `arun_take_regs`: a family of registers (`∀ r, P r → …`) at once.
- `dstep_keep`: the tactic closing the per-directive goals on a concrete
  block (after `simp only [blk, List.mem_cons, …]; rintro d (rfl | …) am`).
-/
import Spike.Lib.A64Flow

namespace Spike.Lib.A64.Flow

open Kraken Kraken.Promising Kraken.Promising.AArch64

variable {lab : Label → Int64}

/-- **A predicate kept by every directive of a block holds at every
prefix.** -/
theorem arun_take_inv (Q : AM → Prop) :
    ∀ {blk : List Directive}, (∀ d ∈ blk, ∀ am, Q am → Q (dstep lab am d)) →
      ∀ (k : Nat) (am : AM), Q am → Q (arun lab (blk.take k) am)
  | [], _, k, am, h0 => by simpa [arun] using h0
  | _ :: _, _, 0, am, h0 => by simpa [arun] using h0
  | d :: ds, h, k + 1, am, h0 => by
    have h1 := h d List.mem_cons_self am h0
    have h2 := arun_take_inv Q (fun d' hd' => h d' (List.mem_cons_of_mem _ hd')) k (dstep lab am d) h1
    simpa only [List.take_succ_cons, arun, List.foldl_cons] using h2

/-- **A register no directive of the block writes** keeps its value at
every prefix. -/
theorem arun_take_reg {blk : List Directive} (r : XReg)
    (h : ∀ d ∈ blk, ∀ am : AM, (dstep lab am d).σ.regs.getXReg r = am.σ.regs.getXReg r) (k : Nat) (am : AM) :
    (arun lab (blk.take k) am).σ.regs.getXReg r = am.σ.regs.getXReg r :=
  arun_take_inv (fun am' => am'.σ.regs.getXReg r = am.σ.regs.getXReg r)
    (fun d hd am' h' => (h d hd am').trans h') k am rfl

/-- **Registers no directive of the block writes** (every `r` with `P r`)
keep their values at every prefix. -/
theorem arun_take_regs {blk : List Directive} (P : XReg → Prop)
    (h : ∀ d ∈ blk, ∀ am : AM, ∀ r, P r → (dstep lab am d).σ.regs.getXReg r = am.σ.regs.getXReg r)
    (k : Nat) (am : AM) : ∀ r, P r → (arun lab (blk.take k) am).σ.regs.getXReg r = am.σ.regs.getXReg r :=
  fun r hr => arun_take_reg r (fun d hd am' => h d hd am' r hr) k am

/-- **A cell no directive of the block writes** keeps its value at every
prefix. -/
theorem arun_take_slot {blk : List Directive} (j : Int)
    (h : ∀ d ∈ blk, ∀ am : AM, (dstep lab am d).σ.slot j = am.σ.slot j) (k : Nat) (am : AM) :
    (arun lab (blk.take k) am).σ.slot j = am.σ.slot j :=
  arun_take_inv (fun am' => am'.σ.slot j = am.σ.slot j) (fun d hd am' h' => (h d hd am').trans h') k am rfl

/-- **A cell no directive of the block writes, at fixed offsets `o`**: every
directive keeps the static offsets `o` and, under them, the cell `j`, so the
cell keeps its value at every prefix run from `o` (for blocks whose stores
are `sp`-relative: the written cell depends on `o.sp`). -/
theorem arun_take_slotO {blk : List Directive} (o : SO) (j : Int)
    (h : ∀ d ∈ blk, ∀ pc σ, (dstep lab ⟨pc, o, σ⟩ d).so = o ∧ (dstep lab ⟨pc, o, σ⟩ d).σ.slot j = σ.slot j)
    (k : Nat) (pc : Int64) (σ : AS) :
    (arun lab (blk.take k) ⟨pc, o, σ⟩).σ.slot j = σ.slot j :=
  (arun_take_inv (fun am => am.so = o ∧ am.σ.slot j = σ.slot j)
    (fun d hd am h' => by
      obtain ⟨pc', o', σ'⟩ := am
      obtain ⟨h1, h2⟩ := h'
      simp only at h1 h2
      subst h1
      exact ⟨(h d hd pc' σ').1, (h d hd pc' σ').2.trans h2⟩) k _ ⟨rfl, rfl⟩).2

/-- **A concrete directive's abstract step**, unfolded: closes the
per-directive goals of `arun_take_reg`/`arun_take_slot` on a covered
directive that does not write the register or cell. -/
macro "dstep_keep" : tactic =>
  `(tactic| (set_option linter.unusedSimpArgs false in
    simp [Spike.Lib.A64.Flow.dstep, Spike.Lib.A64.Flow.classify, Spike.Lib.A64.Flow.RegOnly,
    Spike.Lib.A64.Flow.AI.so, Spike.Lib.A64.Flow.AI.step, Spike.Lib.A64.Flow.AI.tgt, Spike.Lib.A64.Flow.soReg,
    Spike.Lib.A64.Flow.regRes, Operation.interp, MachineData.setRegOrSp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64,
    ConstExpr.interp, Spike.Lib.A64.Flow.SO.set, ExtOrImmReg.interp, Reg64s.getRegOrSp, Reg64s.getRegOrSp64,
    RegOrSp.base, Spike.Lib.A64.Flow.SO.get, MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64,
    Spike.Lib.A64.Flow.zrB, Spike.Lib.A64.Flow.SO.write, Spike.Lib.A64.Flow.SO.kill, Spike.Lib.A64.Flow.SO.killZ,
    Reg64s.getXReg, Reg64s.setXReg]))

/-- info: 'Spike.Lib.A64.Flow.arun_take_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms arun_take_reg

end Spike.Lib.A64.Flow
