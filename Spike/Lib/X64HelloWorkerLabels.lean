/-
**hello.w on x86-64: the code facts of `scc_rt_unpark` and of `wc_worker`'s
tail** (the twin of `Spike/Lib/A64HelloWorkerLabels.lean`), decided on
hello.w's cells (`SccCode.helloCells`, `Spike/Lib/X64HelloCode.lean`) by
`decide +kernel` on `blockAtB`/`labelGapB`, for any valid layout `exe` that
lays the cells out (`Lays exe helloCells kp`). The unpark part of
`Spike/Lib/X64WakeWorkerLabels.lean` at `helloCells` (its check
`Wake.Labels.unpkIn` is generic in the cells and reused; the runtime's
`scc_rt_unpark` is wake.w's).

- `hello_unpkIn`; `unpkCode`: `Unpark.Code`; `hpentry`: `scc_rt_unpark`'s
  frame set-up falls through to `.entry`.
- `wkTailIn`, `hello_wkTailIn`; `wkTailCode`: `HelloTail.Code`
  (`Spike/Lib/X64HelloWkTail.lean`); `hx18`: `.x18` right after the tail's
  `call`.

## Differences from the AArch64 version

- The checks take the cells (`unpkIn cells`) and the labels carry no
  numbered prefix (`.Lscc_rt_unpark.entry`, A64: `.L11_scc_rt_unpark.0_entry`);
  the frame set-up is 12 bytes (A64: five instructions).
- `wkTailIn`, `wkTailCode`, `hx18` are new (A64 defers the `wc_worker`
  facts): they inhabit `HelloTail.Code` and give `seg_wkTailUNN`'s `hx18`.
-/
import Spike.Lib.X64HelloWkTail
import Spike.Lib.X64WakeWorkerLabels
import Spike.Lib.X64HelloCode

namespace Spike.Lib.X64.Flow.Worker.Hello.Labels

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib.X64
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB blockAcrossB)
open Spike.Lib Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Worker
open Spike.Lib.X64.Flow.Worker.Wake.Labels (unpkIn)

set_option linter.unusedSimpArgs false

/-! ## The checks -/

/-- `wc_worker`'s tail blocks, from `.x17`. -/
def wkTailIn (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells ".Lwc_worker.x0" 0 HelloTail.b0 &&
  blockAtB cells ".Lwc_worker.x0" 11 [(stDir .rcx 0 .rax, 3)] &&
  blockAtB cells ".Lwc_worker.x0" 14 HelloTail.b1 &&
  blockAcrossB cells ".Lwc_worker.x1" 0 (HelloTail.b2.take 2) ".Lwc_worker.x2" (HelloTail.b2.drop 2) &&
  labelGapB cells ".Lwc_worker.x0" ".Lwc_worker.x1" 23

theorem hello_unpkIn : unpkIn SccCode.helloCells = true := by decide +kernel

theorem hello_wkTailIn : wkTailIn SccCode.helloCells = true := by decide +kernel

/-! ## The code facts -/

section Code

variable {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
include hp hend

/-- **`scc_rt_unpark`'s code**, any ghosts. -/
theorem unpkCode {c0 c1 : Ctl} {B rbp0 ra tp : BitVec 64} : Unpark.Code c0 c1 B rbp0 ra tp exe endPc := by
  have h := hello_unpkIn
  simp only [unpkIn, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h0, -, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨code_field hp hend h0 (ofNat_zero' _), code_field hp hend h1 (ofNat_zero' _), code_field hp hend h2 rfl,
    code_field hp hend h3 rfl, code_field hp hend h4 rfl, code_field hp hend h5 (ofNat_zero' _),
    code_field hp hend h6 rfl, Spike.Lib.X64.code_field_blockAcrossB hp hend h7 (List.take_append_drop _ _) rfl,
    Spike.Lib.X64.code_field_blockAcrossB hp hend h8 (List.take_append_drop _ _) (ofNat_zero' _)⟩

/-- **`wc_worker`'s tail code**, any ghosts. -/
theorem wkTailCode {c0 c1 c2 : Ctl} {A B rbp0 ra tp sp : BitVec 64} :
    HelloTail.Code c0 c1 c2 A B rbp0 ra tp sp exe endPc := by
  have h := hello_wkTailIn
  simp only [wkTailIn, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h0, h1, h2, h3, -⟩ := h
  exact ⟨code_field hp hend h0 (ofNat_zero' _), code_field hp hend h1 rfl, code_field hp hend h2 rfl,
    Spike.Lib.X64.code_field_blockAcrossB hp hend h3 (List.take_append_drop _ _) (ofNat_zero' _)⟩

omit hend in
/-- **`.x18` right after the tail's `call`.** -/
theorem hx18 : (_root_.Executable.labels exe).label ".Lwc_worker.x1" =
    (_root_.Executable.labels exe).label ".Lwc_worker.x0" + 14 + 9 := by
  have h := hello_wkTailIn
  simp only [wkTailIn, Bool.and_eq_true, and_assoc] at h
  rw [label_labelGapB hp h.2.2.2.2, Int64.add_assoc]; rfl

omit hend in
/-- **`scc_rt_unpark`'s frame set-up falls through to `.entry`.** -/
theorem hpentry : (_root_.Executable.labels exe).label ".Lscc_rt_unpark.entry" =
    (_root_.Executable.labels exe).label "scc_rt_unpark" + 12 := by
  have h := hello_unpkIn
  simp only [unpkIn, Bool.and_eq_true, and_assoc] at h
  rw [label_labelGapB hp h.2.1]; rfl

end Code

end Spike.Lib.X64.Flow.Worker.Hello.Labels

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.Labels.unpkCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.Labels.unpkCode

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.Labels.wkTailCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.Labels.wkTailCode

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.Labels.hx18' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.Labels.hx18

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.Labels.hpentry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.Labels.hpentry
