import Scc.Cert.Rt.A64Print
import Spike.Lib.A64Abort

/-!
# The abort stubs, `scc_rt_abort` and the tail of `scc_rt_main` in an emitted AArch64 program

`Spike.Lib.A64.Abort` proves the runtime's never-returning code segments to
any fragment, from hypotheses on the layout (`Code`: each block at its node's
pc, and labels at fixed distances):

- the five abort stubs (`seg_stub`, `seg_overflow`, …, `seg_threads`);
- the dispatcher `scc_rt_abort` composed with them (`Disp.seg_abort`);
- the tail of `scc_rt_main`, from the return of `wc_main` to `exit_group`
  (`MainTail.seg_main_tail` after a setup block, `MainTail0.seg_main_tail`
  without one).

`abortIn prog` checks the stubs' and the dispatcher's layout hypotheses on
a directive list (`blockAt`, `labelGap` of `Scc/Cert/Rt/LayoutA64.lean`),
`mainIn prog` and `mainIn0 prog` those of the tail of `scc_rt_main` in its
two shapes (which one a program has depends on `main`'s argument), each
decided once per program by `decide +kernel`. The `seg_*_of` theorems are
the Spike theorems for any valid layout of a program with the checks; only
the stubs' `write` system calls stay given nodes (`hsvc`), and the tail of
`scc_rt_main` needs none.

The labels are scc's (`.L12_scc_rt_abort.*`, `.L13_scc_rt_abort_overflow.*`,
…, `.L1_scc_rt_main.*`: the runtime's functions come first in every program,
in a fixed order).

The theorems stated over the segment predicate (`Spike.Lib.Seg`, `MemSide`)
are in `Spike/Lib/Rt/Seg/A64Abort.lean` (same namespace and names).
-/

namespace Scc.Cert.Rt.A64.Abort

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Spike.Lib Spike.Lib.A64 Spike.Lib.A64.Flow
  Spike.Lib.A64.Abort Scc.Cert.Rt.A64.Print

/-! ## The checks -/

/-- **The code of a stub in `prog`**: its blocks at their labels and offsets
(the `write` system call 7 instructions after the entry among them), the
prologue's fall-through (4 instructions) and the exit call's label (11
instructions after the entry). -/
def stubIn (prog : List Directive) (st : Stub) (b1 : List Directive) : Bool :=
  blockAt prog st.fn 0 b0 &&
  blockAt prog st.entry 0 [(SI.adrp .X9 st.msg).toDir] &&
  blockAt prog st.entry 1 [(SI.addLo12 .X9 .X9 st.msg).toDir] &&
  blockAt prog st.entry 2 b1 &&
  blockAt prog st.entry 7 [svcDir] &&
  blockAt prog st.entry 8 b2 &&
  blockAt prog st.exit 0 [svcDir] &&
  labelGap prog st.fn st.entry 4 &&
  labelGap prog st.entry st.exit 11

/-- **The code of `scc_rt_abort` in `prog`.** -/
def dispIn (prog : List Directive) : Bool :=
  blockAt prog "scc_rt_abort" 0 Disp.d0 &&
  blockAt prog ".L12_scc_rt_abort.0_entry" 0 Disp.t1 &&
  blockAt prog ".L12_scc_rt_abort.0_entry" 4 Disp.j1 &&
  blockAt prog ".L12_scc_rt_abort.1_is0" 0 Disp.g1 &&
  blockAt prog ".L12_scc_rt_abort.2_next1" 0 Disp.t2 &&
  blockAt prog ".L12_scc_rt_abort.2_next1" 4 Disp.j2 &&
  blockAt prog ".L12_scc_rt_abort.3_is2" 0 Disp.g2 &&
  blockAt prog ".L12_scc_rt_abort.4_next3" 0 Disp.t3 &&
  blockAt prog ".L12_scc_rt_abort.4_next3" 4 Disp.j3 &&
  blockAt prog ".L12_scc_rt_abort.5_is4" 0 Disp.g3 &&
  blockAt prog ".L12_scc_rt_abort.6_next5" 0 Disp.t4 &&
  blockAt prog ".L12_scc_rt_abort.6_next5" 4 Disp.j4 &&
  blockAt prog ".L12_scc_rt_abort.7_is6" 0 Disp.g4 &&
  blockAt prog ".L12_scc_rt_abort.8_next7" 0 Disp.t5 &&
  blockAt prog ".L12_scc_rt_abort.8_next7" 4 Disp.j5 &&
  blockAt prog ".L12_scc_rt_abort.9_is8" 0 Disp.g5 &&
  labelGap prog "scc_rt_abort" ".L12_scc_rt_abort.0_entry" 5

/-- **The code of the tail of `scc_rt_main` in `prog`**, after a setup
block (`MainTail`). -/
def mainIn (prog : List Directive) : Bool :=
  blockAt prog ".L1_scc_rt_main.sp1" 0 MainTail.m0 && blockAt prog ".L1_scc_rt_main.sp1" 3 [svcDir]

/-- **The code of the tail of `scc_rt_main` in `prog`**, without a setup
block (`MainTail0`). -/
def mainIn0 (prog : List Directive) : Bool :=
  blockAt prog ".L1_scc_rt_main.sp0" 0 MainTail0.m0 && blockAt prog ".L1_scc_rt_main.sp0" 3 [svcDir]

/-- **The stubs and the dispatcher in `prog`.** -/
def abortIn (prog : List Directive) : Bool :=
  stubIn prog overflow b1Overflow && stubIn prog heap b1Heap && stubIn prog stack b1Stack &&
  stubIn prog write b1Write && stubIn prog threads b1Threads && dispIn prog

/-! ## The layout hypotheses from the checks -/

section Layout

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive}
  {endPc : Int64} {c0 : Ctl}

set_option linter.unusedSimpArgs false in
/-- A stub's `Code` from `stubIn`. -/
theorem code_stub {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    {st : Stub} {b1 : List Directive} (h : stubIn prog st b1 = true) : Code st c0 b1 exe endPc := by
  simp only [stubIn, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h0, h1, h1b, h2, hs, h5, hx, hg, hg'⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact code_field hp hend h0 (by simp only [N, add4, add0])
  · exact code_field hp hend h1 (by simp only [N, add4, add0])
  · exact code_field hp hend h1b (by simp only [N, add4, add0])
  · exact code_field hp hend h2 (by simp only [N, add4, add0])
  · exact code_field hp hend h5 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend hx (by simp only [N, add4, add0])
  · rw [label_labelGap hp hg]; simp only [add4, add0]
  · rw [label_labelGap hp hg']; simp only [pcSvc, add4, add0]
  · exact code_field hp hend hs (by simp only [N, pcSvc, add4, add0])

set_option linter.unusedSimpArgs false in
/-- The dispatcher's `Code` from `dispIn`. -/
theorem code_disp {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (h : dispIn prog = true) : Disp.Code c0 exe endPc := by
  simp only [dispIn, Bool.and_eq_true, and_assoc] at h
  obtain ⟨he, h1, i1, g1, h2, i2, g2, h3, i3, g3, h4, i4, g4, h5, i5, g5, hg⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact code_field hp hend he (by simp only [Disp.DN.nd, add4, add0])
  · exact code_field hp hend h1 (by simp only [Disp.DN.nd, add4, add0])
  · exact code_field hp hend i1 (by simp only [Disp.DN.nd, add4, add0])
  · exact code_field hp hend g1 (by simp only [Disp.DN.nd, add4, add0])
  · exact code_field hp hend h2 (by simp only [Disp.DN.nd, add4, add0])
  · exact code_field hp hend i2 (by simp only [Disp.DN.nd, add4, add0])
  · exact code_field hp hend g2 (by simp only [Disp.DN.nd, add4, add0])
  · exact code_field hp hend h3 (by simp only [Disp.DN.nd, add4, add0])
  · exact code_field hp hend i3 (by simp only [Disp.DN.nd, add4, add0])
  · exact code_field hp hend g3 (by simp only [Disp.DN.nd, add4, add0])
  · exact code_field hp hend h4 (by simp only [Disp.DN.nd, add4, add0])
  · exact code_field hp hend i4 (by simp only [Disp.DN.nd, add4, add0])
  · exact code_field hp hend g4 (by simp only [Disp.DN.nd, add4, add0])
  · exact code_field hp hend h5 (by simp only [Disp.DN.nd, add4, add0])
  · exact code_field hp hend i5 (by simp only [Disp.DN.nd, add4, add0])
  · exact code_field hp hend g5 (by simp only [Disp.DN.nd, add4, add0])
  · rw [label_labelGap hp hg]; simp only [add4, add0]

set_option linter.unusedSimpArgs false in
/-- The tail's `Code` from `mainIn`. -/
theorem code_main {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    {ret : BitVec 64} (h : mainIn prog = true) : MainTail.Code c0 ret exe endPc := by
  simp only [mainIn, Bool.and_eq_true] at h
  exact ⟨code_field hp hend h.1 (by simp only [MainTail.MN.nd, add4, add0]),
    code_field hp hend h.2 (by simp only [MainTail.MN.nd, add4, add0])⟩

set_option linter.unusedSimpArgs false in
/-- The tail's `Code` from `mainIn0`. -/
theorem code_main0 {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    {ret : BitVec 64} (h : mainIn0 prog = true) : MainTail0.Code c0 ret exe endPc := by
  simp only [mainIn0, Bool.and_eq_true] at h
  exact ⟨code_field hp hend h.1 (by simp only [MainTail0.MN.nd, add4, add0]),
    code_field hp hend h.2 (by simp only [MainTail0.MN.nd, add4, add0])⟩

end Layout

/-! ## The segments in an emitted program -/

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive} {endPc : Int64}
  {R : Region} {m0 : MachineData} {c0 : Ctl} {Q : Frag isaLSE2}

/-- The stubs' code from `abortIn`. -/
theorem code_stubs {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : abortIn prog = true) (x : Disp.DX) : Code x.stub c0 x.b1 exe endPc := by
  simp only [abortIn, Bool.and_eq_true, and_assoc] at hprog
  cases x
  · exact code_stub hp hend hprog.1
  · exact code_stub hp hend hprog.2.1
  · exact code_stub hp hend hprog.2.2.1
  · exact code_stub hp hend hprog.2.2.2.1
  · exact code_stub hp hend hprog.2.2.2.2.1

end Seg

end Scc.Cert.Rt.A64.Abort
