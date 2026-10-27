/-
**A piece of a user block's code followed by a position off the write
abort** (x86-64): the code predicate `CdCL`
(`Spike/Lib/LowerX64/UserAbC.lean`) with the pc right after the piece a
position off the write abort (`PosOff`) unless the piece ends with a `jmp`
or a `ret` (`endJ`, a block's terminator's last cell). Every piece of an
`Accepted2` block's code but its terminator's is followed in the code by
another piece or a call's `callq` (`Spike/Lib/LowerX64/FnCodeLE.lean`).

- `isJR`, `endJ`, `endJ_snoc`: a `jmp` or a `ret`; a piece ending with one.
- `CdCLE`, `CdCLE.toCdCL`, `CdCLE.toCdC`: the code predicate.
- `posOff_start`: a nonempty piece at `CdCL` starts at a position off the
  write abort.
- `posOff_end_subCdLE`: the pc right after a nonempty part of a piece at
  `CdCLE` not ending with a `jmp` or a `ret` is a position off the write
  abort (`blkW_abSt_subCdL`'s `hend`).
- `isJR_stDir`, `posOff_end_lane`: a lane store's `movq %rax, disp(%rcx)`
  ends no terminator; the pc after a piece ending with it.
-/
import Spike.Lib.LowerX64.UserAbC

namespace Spike.Lib.LowerX64

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64 (cellOff classify AI)

/-! ## Terminators' last cells -/

/-- **A `jmp` or a `ret`**: the last cell of a block's terminator. -/
def isJR (d : Directive) : Bool :=
  match classify d with
  | some (.jmp _) => true
  | some .ret => true
  | _ => false

/-- **A piece ending with a `jmp` or a `ret`** (not an empty one). -/
def endJ (blk : List (Directive × Nat)) : Bool :=
  match (blk.map Prod.fst).getLast? with
  | some d => isJR d
  | none => false

theorem endJ_snoc (blk : List (Directive × Nat)) (d : Directive) (z : Nat) :
    endJ (blk ++ [(d, z)]) = isJR d := by
  simp [endJ]

/-! ## The code predicate -/

/-- **A piece of a block's code at `pc` off the write abort's labels,
followed by a position off the write abort**: `CdCL`, and unless the piece
ends with a `jmp` or a `ret`, the pc right after it a `PosOff`. -/
def CdCLE (cells : List (Directive × Nat)) (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64)
    (ra : Int64) (pc : Int64) (blk : List (Directive × Nat)) : Prop :=
  CdCL cells okPc ph lab ra pc blk ∧
    (endJ blk = false → PosOff cells lab (pc + Int64.ofNat (cellOff blk blk.length)))

section

variable {cells : List (Directive × Nat)} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
  {ra pc : Int64} {blk : List (Directive × Nat)}

theorem CdCLE.toCdCL (h : CdCLE cells okPc ph lab ra pc blk) : CdCL cells okPc ph lab ra pc blk := h.1

theorem CdCLE.toCdC (h : CdCLE cells okPc ph lab ra pc blk) : CdC cells okPc ph lab ra pc blk := h.1.toCdC

/-- **A nonempty piece at `CdCL` starts at a position off the write
abort.** -/
theorem posOff_start (h : CdCL cells okPc ph lab ra pc blk) (hne : blk ≠ []) : PosOff cells lab pc := by
  have := posOff_of_subCdL (SubCd.whole h) (i := 0) (List.length_pos_iff.mpr hne)
  rwa [Spike.Lib.X64.cellOff_zero, show Int64.ofNat 0 = 0 from rfl, Int64.add_zero] at this

/-- **The pc right after a part of a piece at `CdCLE`** is a position off
the write abort, the part nonempty and not ending with a `jmp` or a `ret`:
inside the piece by `posOff_of_subCdL`, at its end by `CdCLE`. -/
theorem posOff_end_subCdLE (h : SubCd (CdCLE cells okPc ph lab ra) pc blk) (hne : blk ≠ [])
    (hj : endJ blk = false) : PosOff cells lab (pc + Int64.ofNat (cellOff blk blk.length)) := by
  obtain ⟨pc0, pre, post, hc, rfl⟩ := h
  have hcb : cellOff blk blk.length = (blk.map (·.2)).sum := by simp [cellOff]
  rcases post with _ | ⟨q, post⟩
  · have hj' : endJ (pre ++ blk) = false := by
      obtain ⟨b0, ⟨d, z⟩, rfl⟩ : ∃ b0 x, blk = b0 ++ [x] :=
        ⟨blk.dropLast, blk.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
      rw [← List.append_assoc, endJ_snoc]; rw [endJ_snoc] at hj; exact hj
    have := hc.2 (by simpa using hj')
    have e : cellOff (pre ++ blk ++ []) (pre ++ blk ++ []).length = (pre.map (·.2)).sum + (blk.map (·.2)).sum := by
      unfold cellOff; rw [List.take_of_length_le (by simp)]; simp
    rw [e, Int64.ofNat_add, ← Int64.add_assoc] at this
    rwa [hcb]
  · have hs : SubCd (CdCL cells okPc ph lab ra) (pc0 + Int64.ofNat (pre.map (·.2)).sum) (blk ++ [q]) :=
      ⟨pc0, pre, post, by simpa using hc.1, rfl⟩
    have := posOff_of_subCdL hs (i := blk.length) (by simp)
    have e : cellOff (blk ++ [q]) blk.length = cellOff blk blk.length := by simp [cellOff]
    rwa [e] at this

/-- A lane store's `movq %rax, disp(%rcx)` is neither a `jmp` nor a `ret`. -/
theorem isJR_stDir (b : Reg64) (i : Int64) (r : Reg64) : isJR (X64.stDir b i r) = false := by
  simp [isJR, X64.stDir, Spike.Lib.X64.AI.toDir, classify]

/-- **The pc right after a piece at `CdCLE` ending with a lane store's
`movq %rax, disp(%rcx)`** is a position off the write abort. -/
theorem posOff_end_lane {pc' : Int64} {blk : List (Directive × Nat)} {i : Int64} {z : Nat}
    (h : CdCLE cells okPc ph lab ra pc' (blk ++ [(X64.stDir .rcx i .rax, z)])) :
    PosOff cells lab (pc' + Int64.ofNat (cellOff blk blk.length + z)) := by
  have := h.2 (by rw [endJ_snoc, isJR_stDir])
  have e : cellOff (blk ++ [(X64.stDir .rcx i .rax, z)]) (blk ++ [(X64.stDir .rcx i .rax, z)]).length =
      cellOff blk blk.length + z := by
    unfold cellOff; rw [List.take_of_length_le (by simp), List.take_of_length_le (by simp)]; simp
  rwa [e] at this

end

/-- info: 'Spike.Lib.LowerX64.posOff_end_subCdLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms posOff_end_subCdLE

/-- info: 'Spike.Lib.LowerX64.posOff_end_lane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms posOff_end_lane

end Spike.Lib.LowerX64
