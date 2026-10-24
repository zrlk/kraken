import Scc.Cert.Rt.X64Print
import Spike.Lib.X64Abort

/-!
# The abort stubs, `scc_rt_abort` and the tail of `scc_rt_main` in an emitted x64 program

The x64 twin of `Scc/Cert/Rt/A64Abort.lean`. `Spike.Lib.X64.Abort` proves
the runtime's never-returning code segments to any fragment, from
hypotheses on the layout (`Code`: each block at its node's pc, and labels at
fixed distances):

- the five abort stubs (`seg_overflow`, …, `seg_threads`);
- the dispatcher `scc_rt_abort` composed with them (`Disp.seg_abort`);
- the tail of `scc_rt_main`, from the return of `wc_main` to `exit_group`
  (`MainTail.seg_main_tail`).

`abortIn cells` checks the stubs' and `scc_rt_abort`'s layout hypotheses on
the code cells (`blockAtB`, `labelGapB` of `Scc/Cert/Rt/CodeX64.lean`), and
`mainIn cells` the tail's, each decided once per program by
`decide +kernel`. The tail is Spike's (`MainTail`) as `hello1.w` compiles:
`.x3` after `wc_main`'s call, the result at `-48(%rbp)`, so `mainIn` holds
only for programs whose `scc_rt_main` has that shape (one with `wc_rodata`
before `wc_main`). The `seg_*_of` theorems are the Spike theorems in any
valid layout of code cells with `abortIn cells = true` (`mainIn cells =
true` for the tail); only the stubs' `write` system calls stay given nodes
(`hsys`), and the tail of `scc_rt_main` needs none.
-/

namespace Scc.Cert.Rt.X64.Abort

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64 Spike.Lib Spike.Lib.X64
  Spike.Lib.X64.Abort
  Scc.Cert.Rt.X64.Print

/-! ## The checks -/

/-- **The code of a stub in `cells`**: its blocks at their labels and
offsets (the `write` system call 34 bytes after the entry among them), the
prologue's fall-through (8 bytes) and the exit call's label (52 bytes after
the entry). -/
def stubIn (cells : List (Directive × Nat)) (st : Stub) (x1 : List (Directive × Nat)) : Bool :=
  blockAtB cells st.fn 0 x0 &&
  blockAtB cells st.entry 0 [((siMsg st).toDir, 7)] &&
  blockAtB cells st.entry 7 x1 &&
  blockAtB cells st.entry 34 [(op64 .syscall, 2)] &&
  blockAtB cells st.entry 36 x2 &&
  blockAtB cells st.exit 0 [(op64 .syscall, 2)] &&
  labelGapB cells st.fn st.entry 8 &&
  labelGapB cells st.entry st.exit 52

/-- **The code of `scc_rt_abort` in `cells`.** -/
def dispIn (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells "scc_rt_abort" 0 Disp.d0 &&
  blockAtB cells ".Lscc_rt_abort.entry" 0 Disp.t1 &&
  blockAtB cells ".Lscc_rt_abort.entry" 16 Disp.j1 &&
  blockAtB cells ".Lscc_rt_abort.is0" 0 Disp.g1 &&
  blockAtB cells ".Lscc_rt_abort.next1" 0 Disp.t2 &&
  blockAtB cells ".Lscc_rt_abort.next1" 16 Disp.j2 &&
  blockAtB cells ".Lscc_rt_abort.is2" 0 Disp.g2 &&
  blockAtB cells ".Lscc_rt_abort.next3" 0 Disp.t3 &&
  blockAtB cells ".Lscc_rt_abort.next3" 16 Disp.j3 &&
  blockAtB cells ".Lscc_rt_abort.is4" 0 Disp.g3 &&
  blockAtB cells ".Lscc_rt_abort.next5" 0 Disp.t4 &&
  blockAtB cells ".Lscc_rt_abort.next5" 16 Disp.j4 &&
  blockAtB cells ".Lscc_rt_abort.is6" 0 Disp.g4 &&
  blockAtB cells ".Lscc_rt_abort.next7" 0 Disp.t5 &&
  blockAtB cells ".Lscc_rt_abort.next7" 16 Disp.j5 &&
  blockAtB cells ".Lscc_rt_abort.is8" 0 Disp.g5 &&
  labelGapB cells "scc_rt_abort" ".Lscc_rt_abort.entry" 12

/-- **The code of the tail of `scc_rt_main` in `cells`** (`hello1.w`'s
shape: see the module docstring). -/
def mainIn (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells ".Lscc_rt_main.x3" 0 MainTail.m0 && blockAtB cells ".Lscc_rt_main.x3" 13 [(op64 .syscall, 2)]

/-- **The stubs and `scc_rt_abort` in `cells`.** -/
def abortIn (cells : List (Directive × Nat)) : Bool :=
  stubIn cells overflow x1Overflow && stubIn cells heap x1Heap && stubIn cells stack x1Stack &&
  stubIn cells write x1Write && stubIn cells threads x1Threads && dispIn cells

/-- `abortIn` from its parts, each decided in its own declaration by a
generated file (the kernel's cache is per declaration, so its memory is the
largest part's). -/
theorem abortIn_of {cells : List (Directive × Nat)}
    (h1 : stubIn cells overflow x1Overflow = true) (h2 : stubIn cells heap x1Heap = true)
    (h3 : stubIn cells stack x1Stack = true) (h4 : stubIn cells write x1Write = true)
    (h5 : stubIn cells threads x1Threads = true) (h6 : dispIn cells = true) : abortIn cells = true := by
  simp only [abortIn, h1, h2, h3, h4, h5, h6, Bool.and_self]

/-! ## The layout hypotheses from the checks -/

section Layout

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)}
  {endPc : Int64} {c0 : Ctl}

/-- A stub's `Code` from `stubIn`. -/
theorem code_stub {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    {st : Stub} {x1 : List (Directive × Nat)} (h : stubIn cells st x1 = true) : Code st c0 x1 exe endPc := by
  simp only [stubIn, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h0, h1, h2, hs, h5, hx, hg, hg'⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact code_field hp hend h0 (off0 _)
  · exact code_field hp hend h1 (off0 _)
  · exact code_field hp hend h2 rfl
  · exact code_field hp hend h5 rfl
  · exact code_field hp hend hx (off0 _)
  · rw [label_labelGapB hp hg]; rfl
  · rw [label_labelGapB hp hg']; rfl
  · exact code_field hp hend hs rfl

/-- The dispatcher's `Code` from `dispIn`. -/
theorem code_disp {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (h : dispIn cells = true) : Disp.Code c0 exe endPc := by
  simp only [dispIn, Bool.and_eq_true, and_assoc] at h
  obtain ⟨he, h1, i1, g1, h2, i2, g2, h3, i3, g3, h4, i4, g4, h5, i5, g5, hg⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact code_field hp hend he (off0 _)
  · exact code_field hp hend h1 (off0 _)
  · exact code_field hp hend i1 rfl
  · exact code_field hp hend g1 (off0 _)
  · exact code_field hp hend h2 (off0 _)
  · exact code_field hp hend i2 rfl
  · exact code_field hp hend g2 (off0 _)
  · exact code_field hp hend h3 (off0 _)
  · exact code_field hp hend i3 rfl
  · exact code_field hp hend g3 (off0 _)
  · exact code_field hp hend h4 (off0 _)
  · exact code_field hp hend i4 rfl
  · exact code_field hp hend g4 (off0 _)
  · exact code_field hp hend h5 (off0 _)
  · exact code_field hp hend i5 rfl
  · exact code_field hp hend g5 (off0 _)
  · rw [label_labelGapB hp hg]; rfl

/-- The tail's `Code` from `mainIn`. -/
theorem code_main {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    {ret : BitVec 64} (h : mainIn cells = true) : MainTail.Code c0 ret exe endPc := by
  simp only [mainIn, Bool.and_eq_true] at h
  exact ⟨code_field hp hend h.1 (off0 _), code_field hp hend h.2 rfl⟩

end Layout

/-! ## The segments in an emitted program -/

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)} {endPc : Int64}
  {R : Region} {m0 : MachineData} {c0 : Ctl} {Q : Frag isa}

/-- The stubs' code from `abortIn`. -/
theorem code_stubs {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hprog : abortIn cells = true) (x : Disp.DX) : Code x.stub c0 x.x1 exe endPc := by
  simp only [abortIn, Bool.and_eq_true, and_assoc] at hprog
  cases x
  · exact code_stub hp hend hprog.1
  · exact code_stub hp hend hprog.2.1
  · exact code_stub hp hend hprog.2.2.1
  · exact code_stub hp hend hprog.2.2.2.1
  · exact code_stub hp hend hprog.2.2.2.2.1

/-- **An abort stub does not return** in any valid layout of code cells
with `abortIn cells = true`, given its `write` call. -/
theorem seg_stub_of {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hprog : abortIn cells = true) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi) (x : Disp.DX)
    (hsys : Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label x.stub c0 .sys))
      (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label x.stub c0 .n5)))
    (hab : ∀ s c, At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label x.stub c0 .ex) s c →
      ms.abortAt s) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label x.stub c0 .e)) Q := by
  have hc := code_stubs (c0 := c0) hp hend hprog x
  cases x
  · exact seg_overflow hR hlo hhi hc hK hsys hab
  · exact seg_heap hR hlo hhi hc hK hsys hab
  · exact seg_stack hR hlo hhi hc hK hsys hab
  · exact seg_write hR hlo hhi hc hK hsys hab
  · exact seg_threads hR hlo hhi hc hK hsys hab

/-- **`scc_rt_abort` does not return** in any valid layout of code cells
with `abortIn cells = true`: from its entry with a code in `[1, 5]`, given
the stubs' `write` calls. -/
theorem seg_abort_of {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hprog : abortIn cells = true) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hsys : ∀ x : Disp.DX,
      Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label x.stub c0 .sys))
        (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label x.stub c0 .n5)))
    (hab : ∀ (x : Disp.DX) s c,
      At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label x.stub c0 .ex) s c → ms.abortAt s) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (Disp.DN.nd (_root_.Executable.labels exe).label c0 .e)) Q := by
  have hd : dispIn cells = true := by
    simp only [abortIn, Bool.and_eq_true, and_assoc] at hprog; exact hprog.2.2.2.2.2
  exact Disp.seg_abort hR hlo hhi (code_disp hp hend hd) hK (code_stubs hp hend hprog) hsys hab

/-- **The tail of `scc_rt_main` does not return** in any valid layout of
code cells with `mainIn cells = true`: from `.x3` with `ret` in `%rax`,
through `exit_group(ret)`. Given that the exit is `main`'s (`hmain`). -/
theorem seg_main_tail_of {ret : BitVec 64} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hprog : mainIn cells = true) (hR : R.OK)
    (hlo : R.lo ≤ -72) (hhi : 16 ≤ R.hi) (hK : ms.K = some Scc.Sem.X64.abi)
    (hmain : ∀ s c,
      At exe endPc R (DFrame R m0) (MainTail.MN.nd (_root_.Executable.labels exe).label c0 ret .ex) s c →
      ¬ ms.abortAt s → MainExit p ms s c ret.toNat) :
    Seg p lbl ms
      (At exe endPc R (DFrame R m0) (MainTail.MN.nd (_root_.Executable.labels exe).label c0 ret .x3)) Q := by
  exact MainTail.seg_main_tail hR hlo hhi (code_main hp hend hprog) hK hmain

end Seg

end Scc.Cert.Rt.X64.Abort
