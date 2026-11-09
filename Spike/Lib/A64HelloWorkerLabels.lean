/-
**hello.w on AArch64: the code facts of `scc_rt_unpark`** (B2), decided on the program the canonical loader reads from
hello.w's
listing (`SccCode.helloProg`, `Spike/Lib/A64HelloCode.lean`) by
`decide +kernel` on `blockAt`/`labelGap`, for any valid layout `exe` that
lays the program out (`Lays exe helloProg kp`). The unpark part of
`A64WakeWorkerLabels.lean` restated at `helloProg` (the runtime's
`.L11_scc_rt_unpark` is wake's).

- `unpkIn`, `hello_unpkIn`; `unpkCode`: `Unpark.Code`.
- `hpentry`: `scc_rt_unpark`'s frame set-up falls through to `.0_entry`.

Deferred (these checks fail on `helloProg`, whose worker functions differ
from wake's):
- `wkIn`, `wcPro` and the `wc_worker` facts (`wkCode`, `hsp1`,
  `wc_prologue_seg`, `seg_wcWorker`) at `.L20_wc_worker` to B5 (the worker
  prints);
- `thrIn`, `thrPro` and the `scc_rt_thr_worker` facts (`thrCode`, `thECode`,
  `hsp0`, `thr_prologue_seg`, `seg_thrWorker`) to B4 (the five-word packet);
- wake's per-node files `A64WakeEndOff` and `A64WakeAbOffW` (over the
  child's segments) to B4/B5.
-/
import Spike.Lib.A64WakeWorker
import Spike.Lib.A64HelloCode
import Spike.Lib.A64CodeSegs
import Spike.Lib.A64CodeAcross

namespace Spike.Lib.A64.Flow.Worker.Hello.Labels

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap blockAcross label_labelGap)
open Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Park (swpDir)
open SccCode (helloProg)

set_option linter.unusedSimpArgs false

/-- `scc_rt_unpark`'s blocks. -/
abbrev unpkIn : Bool :=
  blockAt helloProg "scc_rt_unpark" 0 Unpark.b0 &&
  labelGap helloProg "scc_rt_unpark" ".L11_scc_rt_unpark.0_entry" 5 &&
  blockAt helloProg ".L11_scc_rt_unpark.0_entry" 0 Unpark.b1 &&
  blockAt helloProg ".L11_scc_rt_unpark.0_entry" 3 [swpDir .acqRel .X9 .X11 .X10] &&
  blockAt helloProg ".L11_scc_rt_unpark.0_entry" 4 Unpark.b2 &&
  blockAt helloProg ".L11_scc_rt_unpark.0_entry" 9 Unpark.b3 &&
  blockAt helloProg ".L11_scc_rt_unpark.1_wake" 0 Unpark.b4 &&
  blockAt helloProg ".L11_scc_rt_unpark.1_wake" 11 [svcDir] &&
  blockAcross helloProg ".L11_scc_rt_unpark.1_wake" 12 (Unpark.b5.take 4)
    ".L11_scc_rt_unpark.x4" (Unpark.b5.drop 4) &&
  blockAcross helloProg ".L11_scc_rt_unpark.2_done" 0 (Unpark.b6.take 3)
    ".L11_scc_rt_unpark.x5" (Unpark.b6.drop 3)

theorem hello_unpkIn : unpkIn = true := by decide +kernel

section Code

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
include hp hend

/-- **`scc_rt_unpark`'s code**, any ghosts. -/
theorem unpkCode {c0 c1 : Ctl} {B x29 ra tp : BitVec 64} : Unpark.Code c0 c1 B x29 ra tp exe endPc := by
  have h := hello_unpkIn
  simp only [unpkIn, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h0, -, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨code_of hp hend h0 (by simp only [Unpark.N, ofNat4_succ, ofNat4_zero]),
    code_of hp hend h1 (by simp only [Unpark.N, ofNat4_succ, ofNat4_zero]),
    code_of hp hend h2 (by simp only [Unpark.N, ofNat4_succ, ofNat4_zero]),
    code_of hp hend h3 (by simp only [Unpark.N, ofNat4_succ, ofNat4_zero]),
    code_of hp hend h4 (by simp only [Unpark.N, ofNat4_succ, ofNat4_zero]),
    code_of hp hend h5 (by simp only [Unpark.N, ofNat4_succ, ofNat4_zero]),
    code_of hp hend h6 (by simp only [Unpark.N, Unpark.pcSvc, ofNat4_succ, ofNat4_zero]),
    Spike.Lib.A64.code_field_blockAcross hp hend h7 (List.take_append_drop _ _)
      (by simp only [Unpark.N, Unpark.pcSvc, ofNat4_succ, ofNat4_zero]),
    Spike.Lib.A64.code_field_blockAcross hp hend h8 (List.take_append_drop _ _)
      (by simp only [Unpark.N, ofNat4_succ, ofNat4_zero])⟩

omit hend in
/-- **`scc_rt_unpark`'s frame set-up falls through to `.0_entry`.** -/
theorem hpentry : (_root_.Executable.labels exe).label ".L11_scc_rt_unpark.0_entry" =
    (_root_.Executable.labels exe).label "scc_rt_unpark" + 4 + 4 + 4 + 4 + 4 := by
  have h := hello_unpkIn
  simp only [unpkIn, Bool.and_eq_true, and_assoc] at h
  rw [label_labelGap hp h.2.1]
  simp only [ofNat4_succ, ofNat4_zero]

end Code

end Spike.Lib.A64.Flow.Worker.Hello.Labels

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.Labels.unpkCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64.Flow.Worker.Hello.Labels.unpkCode
