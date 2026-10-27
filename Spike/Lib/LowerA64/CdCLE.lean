/-
**A piece of a user block's code followed by a position off the write
abort** (AArch64): the code predicate `CdCL`
(`Spike/Lib/LowerA64/UserAbC.lean`) with the pc right after the piece a
position off the write abort (`PosOff`) unless the piece ends with a `b` or
a `ret` (`endJ`, a block's terminator's last instruction). Every piece of an
`Accepted2` block's code but its terminator's is followed in the code by
another piece or a call's `bl` (`Spike/Lib/LowerA64/FnCodeLE.lean`).

- `isJR`, `endJ`, `endJ_snoc`, `endJ_append`: a `b` or a `ret`; a piece
  ending with one.
- `CdCLE`, `CdCLE.toCdCL`, `CdCLE.toCdC`: the code predicate.
- `posOff_start`: a nonempty piece at `CdCL` starts at a position off the
  write abort.
- `posOff_end_subCdLE`: the pc right after a nonempty part of a piece at
  `CdCLE` not ending with a `b` or a `ret` is a position off the write
  abort (`blkW_abSt_subCdL`'s `hend`).
- `endJ_strOff`, `posOff_end_lane`: a lane store's `strOff` ends no
  terminator; the pc after a piece ending with it.
-/
import Spike.Lib.LowerA64.UserAbC

namespace Spike.Lib.LowerA64

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Flow (classify AI ofNat4_add ofNat4_zero)
open Scc.Emit.A64 (strOff xs directives)

/-! ## Terminators' last instructions -/

/-- **A `b` or a `ret`**: the last instruction of a block's terminator. -/
def isJR (d : Directive) : Bool :=
  match classify d with
  | some (.b _) => true
  | some (.ret _) => true
  | _ => false

/-- **A piece ending with a `b` or a `ret`** (not an empty one). -/
def endJ (blk : List Directive) : Bool :=
  match blk.getLast? with
  | some d => isJR d
  | none => false

theorem endJ_snoc (blk : List Directive) (d : Directive) : endJ (blk ++ [d]) = isJR d := by
  simp [endJ]

/-- A piece ending with a nonempty one ends as it does. -/
theorem endJ_append (pre : List Directive) {blk : List Directive} (hne : blk ≠ []) :
    endJ (pre ++ blk) = endJ blk := by
  obtain ⟨b0, d, rfl⟩ : ∃ b0 d, blk = b0 ++ [d] :=
    ⟨blk.dropLast, blk.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
  rw [← List.append_assoc, endJ_snoc, endJ_snoc]

/-! ## The code predicate -/

/-- **A piece of a block's code at `pc` off the write abort's labels,
followed by a position off the write abort**: `CdCL`, and unless the piece
ends with a `b` or a `ret`, the pc right after it a `PosOff`. -/
def CdCLE (prog : List Directive) (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (ra : Int64)
    (pc : Int64) (blk : List Directive) : Prop :=
  CdCL prog okPc ph lab ra pc blk ∧ (endJ blk = false → PosOff prog lab (pc + Int64.ofNat (4 * blk.length)))

section

variable {prog : List Directive} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
  {ra pc : Int64} {blk : List Directive}

theorem CdCLE.toCdCL (h : CdCLE prog okPc ph lab ra pc blk) : CdCL prog okPc ph lab ra pc blk := h.1

theorem CdCLE.toCdC (h : CdCLE prog okPc ph lab ra pc blk) : CdC prog okPc ph lab ra pc blk := h.1.toCdC

/-- **A nonempty piece at `CdCL` starts at a position off the write
abort.** -/
theorem posOff_start (h : CdCL prog okPc ph lab ra pc blk) (hne : blk ≠ []) : PosOff prog lab pc := by
  have := posOff_of_subCdL (SubCd.whole h) (i := 0) (List.length_pos_iff.mpr hne)
  rwa [ofNat4_zero] at this

/-- **The pc right after a part of a piece at `CdCLE`** is a position off
the write abort, the part nonempty and not ending with a `b` or a `ret`:
inside the piece by `posOff_of_subCdL`, at its end by `CdCLE`. -/
theorem posOff_end_subCdLE (h : SubCd (CdCLE prog okPc ph lab ra) pc blk) (hne : blk ≠ [])
    (hj : endJ blk = false) : PosOff prog lab (pc + Int64.ofNat (4 * blk.length)) := by
  obtain ⟨pc0, pre, post, hc, rfl⟩ := h
  rcases post with _ | ⟨q, post⟩
  · have := hc.2 (by rw [List.append_nil, endJ_append _ hne]; exact hj)
    rw [List.append_nil, List.length_append, ofNat4_add] at this
    exact this
  · have hs : SubCd (CdCL prog okPc ph lab ra) (pc0 + Int64.ofNat (4 * pre.length)) (blk ++ [q]) :=
      ⟨pc0, pre, post, by simpa using hc.1, rfl⟩
    exact posOff_of_subCdL hs (i := blk.length) (by simp)

/-- A lane store's `strOff` ends with neither a `b` nor a `ret`. -/
theorem endJ_strOff (blk : List Directive) (disp : Int) :
    endJ (blk ++ directives (strOff .W64 .X9 (xs .X10) disp)) = false := by
  unfold strOff
  split
  · simp [endJ, directives, Scc.Emit.A64.ins, isJR, classify, xs]
  · split
    · simp [endJ, directives, Scc.Emit.A64.ins, isJR, classify, xs]
    · simp [endJ, directives, Scc.Emit.A64.ins, isJR, classify, xs]

/-- **The pc right after a piece at `CdCLE` ending with a lane store's
`strOff`** is a position off the write abort. -/
theorem posOff_end_lane {pc' : Int64} {blk : List Directive} {disp : Int}
    (h : CdCLE prog okPc ph lab ra pc' (blk ++ directives (strOff .W64 .X9 (xs .X10) disp))) :
    PosOff prog lab (pc' + Int64.ofNat (4 * (blk ++ directives (strOff .W64 .X9 (xs .X10) disp)).length)) :=
  h.2 (endJ_strOff blk disp)

end

/-- info: 'Spike.Lib.LowerA64.posOff_end_subCdLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms posOff_end_subCdLE

/-- info: 'Spike.Lib.LowerA64.posOff_end_lane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms posOff_end_lane

end Spike.Lib.LowerA64
