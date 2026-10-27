/-
**Every register of a function has an x86-64 slot**: `Emit.X64.frameOf`
numbers exactly the parameters and the registers of the instructions and
terminators (`instRegs`, `termRegs`), so `Frame.slotOff` succeeds on each.

- `find?_zipIdx_of_mem`: a member of a list is found in its numbering;
- `slots_find?_of_mem`, `slotOff_of_mem`: for a register of `frameOf`'s list;
- `slotOff_param`, `slotOff_inst`, `slotOff_term`: for a parameter, a
  register of an instruction, and one of a terminator of a block.
-/
import Scc.Emit.X64

namespace Spike.Lib.LowerShape

open Scc.IR

/-- **A member of a list is found in its numbering**, at some index. -/
theorem find?_zipIdx_of_mem {r : Reg} : ∀ {l : List Reg} (n : Nat), r ∈ l →
    ∃ k, (l.zipIdx n).find? (·.1 == r) = some (r, k)
  | [], _, h => absurd h (List.not_mem_nil)
  | a :: l, n, h => by
    by_cases ha : a = r
    · subst ha
      exact ⟨n, by simp [List.zipIdx_cons]⟩
    · have hr : r ∈ l := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm ha
        · exact h
      obtain ⟨k, hk⟩ := find?_zipIdx_of_mem (n + 1) hr
      exact ⟨k, by simp [List.zipIdx_cons, ha, hk]⟩

/-- `frameOf`'s register list. -/
theorem frameOf_slots (areas : List (Sym × Nat)) (f : Func) :
    (Scc.Emit.X64.frameOf areas f).slots =
      (f.params ++ f.blocks.flatMap fun b => b.insts.flatMap Scc.Emit.X64.instRegs ++
        Scc.Emit.X64.termRegs b.term).eraseDups.zipIdx := rfl

/-- **A register of `frameOf`'s list has a slot.** -/
theorem slots_find?_of_mem (areas : List (Sym × Nat)) (f : Func) {r : Reg}
    (h : r ∈ f.params ++ f.blocks.flatMap fun b => b.insts.flatMap Scc.Emit.X64.instRegs ++
        Scc.Emit.X64.termRegs b.term) :
    ∃ k, (Scc.Emit.X64.frameOf areas f).slots.find? (·.1 == r) = some (r, k) := by
  rw [frameOf_slots]
  exact find?_zipIdx_of_mem 0 (List.mem_eraseDups.mpr h)

/-- **`slotOff` succeeds on a register of `frameOf`'s list**, in any
emitter state, at `-8(k+1)` for its index `k`. -/
theorem slotOff_of_mem (areas : List (Sym × Nat)) (f : Func) {r : Reg}
    (h : r ∈ f.params ++ f.blocks.flatMap fun b => b.insts.flatMap Scc.Emit.X64.instRegs ++
        Scc.Emit.X64.termRegs b.term) :
    ∃ k, (Scc.Emit.X64.frameOf areas f).slots.find? (·.1 == r) = some (r, k) ∧
      ∀ s, (Scc.Emit.X64.frameOf areas f).slotOff r s = .ok (-(8 * ((k : Int) + 1)), s) := by
  obtain ⟨k, hk⟩ := slots_find?_of_mem areas f h
  refine ⟨k, hk, fun s => ?_⟩
  simp only [Scc.Emit.X64.Frame.slotOff, hk]
  rfl

/-- **A parameter has a slot.** -/
theorem slotOff_param (areas : List (Sym × Nat)) (f : Func) {r : Reg} (h : r ∈ f.params) :
    ∃ k, ∀ s, (Scc.Emit.X64.frameOf areas f).slotOff r s = .ok (-(8 * ((k : Int) + 1)), s) :=
  let ⟨k, _, hk⟩ := slotOff_of_mem areas f (List.mem_append_left _ h)
  ⟨k, hk⟩

/-- **A register of an instruction of a block has a slot.** -/
theorem slotOff_inst (areas : List (Sym × Nat)) (f : Func) {b : Block} (hb : b ∈ f.blocks) {i : Inst}
    (hi : i ∈ b.insts) {r : Reg} (h : r ∈ Scc.Emit.X64.instRegs i) :
    ∃ k, ∀ s, (Scc.Emit.X64.frameOf areas f).slotOff r s = .ok (-(8 * ((k : Int) + 1)), s) := by
  obtain ⟨k, _, hk⟩ := slotOff_of_mem areas f (r := r) (by
    refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨b, hb, ?_⟩)
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨i, hi, h⟩))
  exact ⟨k, hk⟩

/-- **A register of a block's terminator has a slot.** -/
theorem slotOff_term (areas : List (Sym × Nat)) (f : Func) {b : Block} (hb : b ∈ f.blocks) {r : Reg}
    (h : r ∈ Scc.Emit.X64.termRegs b.term) :
    ∃ k, ∀ s, (Scc.Emit.X64.frameOf areas f).slotOff r s = .ok (-(8 * ((k : Int) + 1)), s) := by
  obtain ⟨k, _, hk⟩ := slotOff_of_mem areas f (r := r) (by
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨b, hb, List.mem_append_right _ h⟩))
  exact ⟨k, hk⟩

end Spike.Lib.LowerShape
