/-
**hello.w on x86-64: the code facts of `wc_worker`** (the twin of
`Spike/Lib/A64HelloWorker.lean`), decided on `SccCode.helloCells` by
`decide +kernel` on `blockAtB`/`labelGapB`/`prologueIn`, for any valid
layout `exe` laying the cells out (`Lays exe helloCells kp`).

- `wkIn`, `hello_wkIn`: `wc_worker`'s `.entry` blocks (`Body.wkE1`, the
  multiply, `Body.wkE2`), the gap `.entry` → `.x17` (87 bytes) and the
  tail's blocks (`Labels.wkTailIn`);
- `wcPs`, `wcPro`, `hello_wcPro`: the stack-checked prologue (frame 80,
  `%rdi … %r9` at `-8 … -48(%rbp)`);
- `hello_printIn` (`= SccCode.hello_print`): `scc_rt_print`'s code;
- `wkE1Code`, `wkMulCode`, `wkE2Code`, `hgap`, `printCode` (`Print.Code`),
  `printEntry`: the code facts the head and `print` take (the tail's are
  `Labels.wkTailCode`, `Labels.hx18`).

## Differences from the AArch64 version

- The head is three code facts (`wkE1Code`, `wkMulCode`, `wkE2Code`: the
  multiply is a node of its own) for A64's `wkECode`; the gap is in bytes
  (`hgap`: `.x17 = .entry + 87`; A64: 21 instructions).
- The tail's facts are `X64HelloWorkerLabels`' (`wkTailCode`, `hx18`), so
  A64's `tailCode`, `hsp6` are not restated here; `wkIn` includes
  `wkTailIn`.
- `printCode` is x86-64's `Print.Code` from `Scc.Cert.Rt.X64.Print.printIn`
  (15 fields, as `Flow.seg_print_ofW`), `printEntry` its 16-byte frame
  set-up (A64: `PrintF.Code`, six instructions).
- The prologue's frame is 80 (A64: 96), its spills `%rbp`-relative; its
  `jb .stk` is the 6-byte form (the body is past `rel8`'s reach).
- A64's `wc_prologue_seg` (dead) is not twinned.
-/
import Spike.Lib.X64HelloWorkerBody
import Spike.Lib.X64HelloWorkerLabels
import Spike.Lib.X64Print
import Spike.Lib.X64CodeAcross

namespace Spike.Lib.X64.Flow.Worker.Hello.Wk

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Worker
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)
open Scc.Cert.Rt.X64.Print (printIn off0)
open Spike.Lib.X64.Flow.Worker.Hello.Labels (wkTailIn hello_wkTailIn)

set_option linter.unusedSimpArgs false

/-! ## The checks -/

/-- `wc_worker`'s blocks at hello's labels: the head's blocks and the
multiply, the gap to `.x17`, the tail's. -/
def wkIn (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells ".Lwc_worker.entry" 0 Body.wkE1 &&
  blockAtB cells ".Lwc_worker.entry" 36 [(Body.wkMul.toDir, 4)] &&
  blockAtB cells ".Lwc_worker.entry" 40 Body.wkE2 &&
  labelGapB cells ".Lwc_worker.entry" ".Lwc_worker.x0" 87 &&
  wkTailIn cells

/-- `wc_worker`'s six argument registers, spilled at `-8 … -48(%rbp)`, with
their sizes. -/
abbrev wcPs : List (Reg64 × Int64 × Nat) :=
  [(.rdi, -8, 4), (.rsi, -16, 4), (.rdx, -24, 4), (.rcx, -32, 4), (.r8, -40, 4), (.r9, -48, 4)]

/-- `wc_worker`'s prologue: frame 80, its six arguments at `-8 … -48(%rbp)`. -/
def wcPro (cells : List (Directive × Nat)) : Bool :=
  prologueIn cells "wc_worker" ".Lwc_worker.chk" ".Lwc_worker.entry" 80 8 ".Lwc_worker.stk" 5 9 3 6 4 wcPs

theorem hello_wkIn : wkIn SccCode.helloCells = true := by decide +kernel
theorem hello_wcPro : wcPro SccCode.helloCells = true := by decide +kernel
theorem hello_printIn : printIn SccCode.helloCells = true := SccCode.hello_print

/-! ## The code facts -/

section Code

variable {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
include hp hend

/-- **`wc_worker`'s `.entry` block up to the multiply.** -/
theorem wkE1Code : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s ((_root_.Executable.labels exe).label ".Lwc_worker.entry") Body.wkE1 := by
  have h := hello_wkIn
  simp only [wkIn, Bool.and_eq_true, and_assoc] at h
  exact code_field hp hend h.1 (ofNat_zero' _)

/-- **The multiply.** -/
theorem wkMulCode : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s ((_root_.Executable.labels exe).label ".Lwc_worker.entry" + 36) [(Body.wkMul.toDir, 4)] := by
  have h := hello_wkIn
  simp only [wkIn, Bool.and_eq_true, and_assoc] at h
  exact code_field hp hend h.2.1 rfl

/-- **`wc_worker`'s `.entry` block after the multiply.** -/
theorem wkE2Code : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s ((_root_.Executable.labels exe).label ".Lwc_worker.entry" + 40) Body.wkE2 := by
  have h := hello_wkIn
  simp only [wkIn, Bool.and_eq_true, and_assoc] at h
  exact code_field hp hend h.2.2.1 rfl

omit hend in
/-- **`.x17` right after the `.entry` block** (87 bytes). -/
theorem hgap : (_root_.Executable.labels exe).label ".Lwc_worker.x0" =
    (_root_.Executable.labels exe).label ".Lwc_worker.entry" + Int64.ofNat 87 := by
  have h := hello_wkIn
  simp only [wkIn, Bool.and_eq_true, and_assoc] at h
  exact label_labelGapB hp h.2.2.2.1

/-- **`scc_rt_print`'s code** (`Print.Code`), any ghosts, from `printIn`
(`hello_print`). -/
theorem printCode {c0 : Ctl} {rbp0 ra : BitVec 64} : Print.Code c0 rbp0 ra exe endPc := by
  have hprog := hello_printIn
  simp only [printIn, Bool.and_eq_true, and_assoc] at hprog
  obtain ⟨h0, h1, h2, h3, h4, hs, h5, h6, h7, h8, h9, h10, h11, h12, h13, -⟩ := hprog
  exact ⟨code_field hp hend h0 (off0 _), code_field hp hend h1 (off0 _), code_field hp hend h2 (off0 _),
    code_field hp hend h3 rfl, code_field hp hend h4 (off0 _), code_field hp hend h5 rfl,
    code_field hp hend h6 rfl, code_field hp hend h7 (off0 _), code_field hp hend h8 rfl,
    code_field hp hend h9 (off0 _), code_field hp hend h10 rfl, code_field hp hend h11 (off0 _),
    code_field hp hend h12 (off0 _),
    Spike.Lib.X64.code_field_blockAcrossB hp hend h13 (List.take_append_drop _ _) (off0 _),
    code_field hp hend hs rfl⟩

omit hend in
/-- **`scc_rt_print`'s frame set-up falls through to `.entry`.** -/
theorem printEntry : (_root_.Executable.labels exe).label ".Lscc_rt_print.entry" =
    (_root_.Executable.labels exe).label "scc_rt_print" + 16 := by
  have hprog := hello_printIn
  simp only [printIn, Bool.and_eq_true, and_assoc] at hprog
  rw [label_labelGapB hp hprog.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]; rfl

end Code

end Spike.Lib.X64.Flow.Worker.Hello.Wk

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.Wk.printCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.Wk.printCode

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.Wk.hgap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.Wk.hgap

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.Wk.wkE2Code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.Wk.wkE2Code

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.Wk.printEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.Wk.printEntry
