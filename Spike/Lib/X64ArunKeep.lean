/-
**What a block's prefixes keep** (x86-64): facts of the abstract state that
every directive of a block keeps hold at every prefix
`arun lab (blk.take k)` (`Spike/Lib/X64Block.lean`), the states `BlkW`
quantifies over. Generic in the block, the labels and the thread: a `BlkW`
obligation that needs a register's or a cell's value at a block's internal
states reduces to the per-directive facts, decided on the concrete sized
directives.

- `arun_take_inv`: a predicate on the abstract machine kept by every
  directive holds at every prefix.
- `arun_take_reg`: a register no directive writes keeps its value.
- `arun_take_slot`: a cell no directive writes keeps its value.
- `arun_take_slotO`: a cell no directive writes at fixed static offsets
  keeps its value (blocks whose stores are `rsp`-relative).

x86-64 twin of `Spike/Lib/A64ArunKeep.lean` (same names, `X64` namespace;
blocks are lists of sized directives, registers read by `get64`).
-/
import Spike.Lib.X64Block

namespace Spike.Lib.X64

open Kraken Kraken.Promising Kraken.Promising.X64

variable {lab : String → Int64}

/-- **A predicate kept by every directive of a block holds at every
prefix.** -/
theorem arun_take_inv (Q : AM → Prop) :
    ∀ {blk : List (Directive × Nat)}, (∀ d ∈ blk, ∀ am, Q am → Q (dstep lab am d)) →
      ∀ (k : Nat) (am : AM), Q am → Q (arun lab (blk.take k) am)
  | [], _, k, am, h0 => by simpa [arun] using h0
  | _ :: _, _, 0, am, h0 => by simpa [arun] using h0
  | d :: ds, h, k + 1, am, h0 => by
    have h1 := h d List.mem_cons_self am h0
    have h2 := arun_take_inv Q (fun d' hd' => h d' (List.mem_cons_of_mem _ hd')) k (dstep lab am d) h1
    simpa only [List.take_succ_cons, arun, List.foldl_cons] using h2

/-- **A register no directive of the block writes** keeps its value at
every prefix. -/
theorem arun_take_reg {blk : List (Directive × Nat)} (r : Reg64)
    (h : ∀ d ∈ blk, ∀ am : AM, (dstep lab am d).σ.regs.get64 r = am.σ.regs.get64 r) (k : Nat) (am : AM) :
    (arun lab (blk.take k) am).σ.regs.get64 r = am.σ.regs.get64 r :=
  arun_take_inv (fun am' => am'.σ.regs.get64 r = am.σ.regs.get64 r)
    (fun d hd am' h' => (h d hd am').trans h') k am rfl

/-- **A cell no directive of the block writes** keeps its value at every
prefix. -/
theorem arun_take_slot {blk : List (Directive × Nat)} (j : Int)
    (h : ∀ d ∈ blk, ∀ am : AM, (dstep lab am d).σ.slot j = am.σ.slot j) (k : Nat) (am : AM) :
    (arun lab (blk.take k) am).σ.slot j = am.σ.slot j :=
  arun_take_inv (fun am' => am'.σ.slot j = am.σ.slot j) (fun d hd am' h' => (h d hd am').trans h') k am rfl

/-- **A cell no directive of the block writes, at fixed offsets `o`**: every
directive keeps the static offsets `o` and, under them, the cell `j`, so the
cell keeps its value at every prefix run from `o` (for blocks whose stores
are `rsp`-relative: the written cell depends on `o.sp`). -/
theorem arun_take_slotO {blk : List (Directive × Nat)} (o : SO) (j : Int)
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

/-- `arun_take_reg` on a block of one unclassified directive (`dstep` the
identity): `rsp` is kept at every prefix. -/
example (am : AM) (k : Nat) :
    (arun lab ([((.label "l" : Directive), 0)].take k) am).σ.regs.get64 .rsp = am.σ.regs.get64 .rsp :=
  arun_take_reg .rsp (fun d hd am' => by
    simp only [List.mem_singleton] at hd; subst hd; simp [dstep, classify]) k am

end Spike.Lib.X64

/-- info: 'Spike.Lib.X64.arun_take_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.arun_take_inv

/-- info: 'Spike.Lib.X64.arun_take_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.arun_take_reg

/-- info: 'Spike.Lib.X64.arun_take_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.arun_take_slot

/-- info: 'Spike.Lib.X64.arun_take_slotO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.arun_take_slotO
