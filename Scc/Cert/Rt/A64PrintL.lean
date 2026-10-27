import Scc.Cert.Rt.A64PrintLMs

/-!
# `wc_printL` in an emitted AArch64 program

`Spike.Lib.A64.PrintL.seg_printL` proves `hello.w`'s `wc_printL` one
segment from hypotheses on the layout: each block at its node's pc
(`Code`), the stack-check label at the function's address (`hcheck`) and
the prologue's fall-through into `.0_entry` (`hentry`);
`Scc.Cert.Rt.A64.Morestack.hms_printL` adds `.sp_check` at the grow stub's
return address (`hsp`). `printLIn prog` checks them on a directive list:
every block at its label and instruction offset (`blockAt`) and the three
label distances (`labelGap`). The function's blocks start at
`.stack_check`, the label right after `wc_printL` (the run after
`wc_printL` itself is empty). `code_printL`, `check_printL`,
`entry_printL` and `sp_printL` are the hypotheses in any valid layout of a
program with `printLIn prog = true`: the AArch64 twin of
`Scc/Cert/Rt/X64PrintL.lean`.
-/

namespace Scc.Cert.Rt.A64.PrintL

open Kraken Kraken.Promising Kraken.Promising.AArch64 Spike.Lib Spike.Lib.A64 Spike.Lib.A64.PrintL
open Scc.Cert.Rt.A64.Print (add4 add0 code_field)

/-- **The code of `wc_printL` in `prog`**: its blocks at their labels and
offsets, `.stack_check` at `wc_printL`, `.0_entry` 14 instructions behind
it, and `.sp_check` 14 instructions behind `.stack_grow`. -/
def printLIn (prog : List Directive) : Bool :=
  blockAt prog ".L21_wc_printL.stack_check" 0 b0 &&
  blockAt prog ".L21_wc_printL.stack_check" 3 b1 &&
  blockAt prog ".L21_wc_printL.stack_check" 5 b2 &&
  blockAt prog ".L21_wc_printL.0_entry" 0 b3 &&
  blockAt prog ".L21_wc_printL.0_entry" 17 b4 &&
  blockAt prog ".L21_wc_printL.sp5" 0 b5 &&
  blockAt prog ".L21_wc_printL.sp5" 5 b6 &&
  blockAt prog ".L21_wc_printL.1_then6" 0 b7 &&
  blockAt prog ".L21_wc_printL.2_else7" 0 b8 &&
  blockAt prog ".L21_wc_printL.2_else7" 9 b9 &&
  blockAt prog ".L21_wc_printL.stack_grow" 0 b10 &&
  blockAt prog ".L21_wc_printL.sp_check" 0 b11 &&
  blockAt prog ".L21_wc_printL.abort_overflow" 0 b12 &&
  labelGap prog "wc_printL" ".L21_wc_printL.stack_check" 0 &&
  labelGap prog ".L21_wc_printL.stack_check" ".L21_wc_printL.0_entry" 14 &&
  labelGap prog ".L21_wc_printL.stack_grow" ".L21_wc_printL.sp_check" 14

section Layout

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive}

/-- The three label distances of `printLIn`. -/
private theorem gaps (h : printLIn prog = true) :
    labelGap prog "wc_printL" ".L21_wc_printL.stack_check" 0 = true ∧
    labelGap prog ".L21_wc_printL.stack_check" ".L21_wc_printL.0_entry" 14 = true ∧
    labelGap prog ".L21_wc_printL.stack_grow" ".L21_wc_printL.sp_check" 14 = true := by
  simp only [printLIn, Bool.and_eq_true, and_assoc] at h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- `.stack_check` at `wc_printL` (`seg_printL`'s `hcheck`). -/
theorem check_printL {kp : Nat} (hp : Lays exe prog kp) (h : printLIn prog = true) :
    (_root_.Executable.labels exe).label ".L21_wc_printL.stack_check" =
      (_root_.Executable.labels exe).label "wc_printL" := by
  rw [label_labelGap hp (gaps h).1, add0]

set_option linter.unusedSimpArgs false in
/-- `.0_entry` 14 instructions behind `wc_printL` (`seg_printL`'s `hentry`). -/
theorem entry_printL {kp : Nat} (hp : Lays exe prog kp) (h : printLIn prog = true) :
    (_root_.Executable.labels exe).label ".L21_wc_printL.0_entry" =
      (_root_.Executable.labels exe).label "wc_printL" + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4
        + 4 := by
  rw [label_labelGap hp (gaps h).2.1, check_printL hp h]; simp only [add4, add0]

set_option linter.unusedSimpArgs false in
/-- `.sp_check` 14 instructions behind `.stack_grow`. -/
theorem spGap_printL {kp : Nat} (hp : Lays exe prog kp) (h : printLIn prog = true) :
    (_root_.Executable.labels exe).label ".L21_wc_printL.sp_check" =
      (_root_.Executable.labels exe).label ".L21_wc_printL.stack_grow" + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4
        + 4 + 4 + 4 + 4 + 4 := by
  rw [label_labelGap hp (gaps h).2.2]; simp only [add4, add0]

set_option linter.unusedSimpArgs false in
/-- **The layout of `wc_printL`** (`seg_printL`'s `hcode`). -/
theorem code_printL {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) (h : printLIn prog = true)
    (c0 : Ctl) (x29 ra : BitVec 64) : Code c0 x29 ra exe endPc := by
  have hc := check_printL hp h
  simp only [printLIn, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact code_field hp hend h0 (by simp only [N, hc, add4, add0])
  · exact code_field hp hend h1 (by simp only [N, hc, add4, add0])
  · exact code_field hp hend h2 (by simp only [N, hc, add4, add0])
  · exact code_field hp hend h3 (by simp only [N, add4, add0])
  · exact code_field hp hend h4 (by simp only [N, add4, add0])
  · exact code_field hp hend h5 (by simp only [N, add4, add0])
  · exact code_field hp hend h6 (by simp only [N, add4, add0])
  · exact code_field hp hend h7 (by simp only [N, add4, add0])
  · exact code_field hp hend h8 (by simp only [N, add4, add0])
  · exact code_field hp hend h9 (by simp only [N, add4, add0])
  · exact code_field hp hend h10 (by simp only [N, add4, add0])
  · exact code_field hp hend h11 (by simp only [N, add4, add0])
  · exact code_field hp hend h12 (by simp only [N, add4, add0])

/-- `.sp_check` at the grow stub's return address (`hms_printL`'s `hsp`). -/
theorem sp_printL {kp : Nat} (hp : Lays exe prog kp) (h : printLIn prog = true) :
    (_root_.Executable.labels exe).label ".L21_wc_printL.sp_check" =
      Int64.ofBitVec (Scc.Cert.Rt.A64.Morestack.printLRet (_root_.Executable.labels exe).label) := by
  rw [spGap_printL hp h]
  apply Int64.toBitVec_inj.mp
  simp only [Int64.toBitVec_add, Int64.toBitVec_ofBitVec]
  apply BitVec.eq_of_toInt_eq
  simp only [BitVec.toInt_add, BitVec.toInt_ofInt, Int.bmod_bmod, Int64.toInt_toBitVec, Int.bmod_add_bmod,
    show (4 : Int64).toInt = 4 from rfl, show (18446744073709551616 : Nat) = 2 ^ 64 from rfl]

end Layout

end Scc.Cert.Rt.A64.PrintL
