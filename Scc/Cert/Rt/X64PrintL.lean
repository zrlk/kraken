import Scc.Cert.Rt.CodeX64
import Spike.Lib.X64PrintL

/-!
# `wc_printL` in an emitted x64 program

`Spike.Lib.X64.PrintL.seg_printL` proves `hello.w`'s `wc_printL` one segment
from hypotheses on the layout: each block at its node's pc (`Code`), and the
labels `.chk` and `.entry` at their fall-through addresses (`hchk`,
`hentry`); `Scc.Cert.Rt.X64.Morestack.hms_printL` adds `.x18` 18 bytes
behind `.stk` (`hx18`). `printLIn cells` checks them on the code cells:
every block at its label and byte offset (`blockAtB`) and the three label
distances (`labelGapB`). `code_printL`, `chk_printL`, `entry_printL` and
`x18_printL` are the hypotheses in any valid layout of code cells with
`printLIn cells = true`.
-/

namespace Scc.Cert.Rt.X64.PrintL

open Kraken Kraken.Promising Kraken.Promising.X64 Spike.Lib Spike.Lib.X64 Spike.Lib.X64.PrintL

/-- **The code of `wc_printL` in `cells`**: its blocks at their labels and
byte offsets, and the labels `.chk`, `.entry` and `.x18` at their
fall-through addresses. -/
def printLIn (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells "wc_printL" 0 b0 &&
  blockAtB cells ".Lwc_printL.chk" 0 b1 &&
  blockAtB cells ".Lwc_printL.chk" 14 b2 &&
  blockAtB cells ".Lwc_printL.chk" 23 b3 &&
  blockAtB cells ".Lwc_printL.entry" 0 b4 &&
  blockAtB cells ".Lwc_printL.entry" 15 b5 &&
  blockAtB cells ".Lwc_printL.entry" 11 [(FI.toDir (.imul_rr .rax .rcx), 4)] &&
  blockAtB cells ".Lwc_printL.entry" 66 b6 &&
  blockAtB cells ".Lwc_printL.x17" 0 b7 &&
  blockAtB cells ".Lwc_printL.x17" 20 b8 &&
  blockAtB cells ".Lwc_printL.then6" 0 b9 &&
  blockAtB cells ".Lwc_printL.else7" 0 b10 &&
  blockAtB cells ".Lwc_printL.else7" 43 b11 &&
  blockAtB cells ".Lwc_printL.ovf" 0 b12 &&
  blockAtB cells ".Lwc_printL.stk" 0 b13 &&
  blockAtB cells ".Lwc_printL.x18" 0 b14 &&
  labelGapB cells "wc_printL" ".Lwc_printL.chk" 4 &&
  labelGapB cells ".Lwc_printL.chk" ".Lwc_printL.entry" 47 &&
  labelGapB cells ".Lwc_printL.stk" ".Lwc_printL.x18" 18

section Layout

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)}

private theorem off0 (a : Int64) : a + Int64.ofNat 0 = a := by
  rw [show Int64.ofNat 0 = 0 by decide, Int64.add_zero]

/-- **The layout of `wc_printL`** (`seg_printL`'s `hcode`). -/
theorem code_printL {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (h : printLIn cells = true)
    (c0 : Ctl) (rbp0 ra : BitVec 64) : Code c0 rbp0 ra exe endPc := by
  simp only [printLIn, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, hm, h6, h7, h8, h9, h10, h11, h12, h13, h14, -⟩ := h
  exact ⟨code_field hp hend h0 (off0 _),
    code_field hp hend h1 (off0 _),
    code_field hp hend h2 rfl,
    code_field hp hend h3 rfl,
    code_field hp hend h4 (off0 _),
    code_field hp hend h5 rfl,
    code_field hp hend hm rfl,
    code_field hp hend h6 rfl,
    code_field hp hend h7 (off0 _),
    code_field hp hend h8 rfl,
    code_field hp hend h9 (off0 _),
    code_field hp hend h10 (off0 _),
    code_field hp hend h11 rfl,
    code_field hp hend h12 (off0 _),
    code_field hp hend h13 (off0 _),
    code_field hp hend h14 (off0 _)⟩

/-- `.chk` 4 bytes behind `wc_printL` (`seg_printL`'s `hchk`). -/
theorem chk_printL {kp : Nat} (hp : Lays exe cells kp) (h : printLIn cells = true) :
    (_root_.Executable.labels exe).label ".Lwc_printL.chk" =
      (_root_.Executable.labels exe).label "wc_printL" + 4 := by
  simp only [printLIn, Bool.and_eq_true, and_assoc] at h
  rw [label_labelGapB hp h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; rfl

/-- `.entry` 47 bytes behind `.chk` (`seg_printL`'s `hentry`). -/
theorem entry_printL {kp : Nat} (hp : Lays exe cells kp) (h : printLIn cells = true) :
    (_root_.Executable.labels exe).label ".Lwc_printL.entry" =
      (_root_.Executable.labels exe).label ".Lwc_printL.chk" + 47 := by
  simp only [printLIn, Bool.and_eq_true, and_assoc] at h
  rw [label_labelGapB hp h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; rfl

/-- `.x18` 18 bytes behind `.stk` (`hms_printL`'s `hx18`). -/
theorem x18_printL {kp : Nat} (hp : Lays exe cells kp) (h : printLIn cells = true) :
    (_root_.Executable.labels exe).label ".Lwc_printL.x18" =
      (_root_.Executable.labels exe).label ".Lwc_printL.stk" + 18 := by
  simp only [printLIn, Bool.and_eq_true, and_assoc] at h
  rw [label_labelGapB hp h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]; rfl

end Layout

end Scc.Cert.Rt.X64.PrintL
