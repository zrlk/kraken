/-
**hello.w on AArch64: the code facts of `wc_worker`** (B5 check-in 3,
part 2), decided on `SccCode.helloProg` by `decide +kernel` on
`blockAt`/`labelGap`/`prologueIn`, for any valid layout `exe` laying it
out (`Lays exe helloProg kp`): the facts `A64HelloWorkerLabels` deferred
to B5.

- `wkIn`, `hello_wkIn`: `wc_worker`'s `.0_entry` block (`Body.wkE`), its
  tail's blocks at `.sp4`/`.sp6` (`HelloTail`), the gaps `.0_entry` →
  `.sp4` (21) and the `bl`'s return `.sp6`;
- `wcPs`, `wcPro`, `hello_wcPro`: the stack-checked prologue (frame 96,
  `x0..x5` at `0..40`);
- `hello_printIn` (`= SccCode.hello_print`): `scc_rt_print`'s code;
- `wkECode`, `hgap`, `tailCode`, `hsp6`, `printCode` (`PrintF.Code`),
  `printEntry`: the code facts `Body.seg_wkT` and
  `HelloTail.seg_wkTailU` take;
- `wc_prologue_seg`: the prologue, `prologue_seg_of` lifted to the thread
  rows.
-/
import Spike.Lib.A64WorkerBody
import Spike.Lib.A64HelloWorkerLabels
import Scc.Cert.Rt.A64Print
import Spike.Lib.A64CodeAcross

namespace Spike.Lib.A64.Flow.Worker.Hello.Wk

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap blockAcross label_labelGap)
open Scc.Cert.Rt.A64.Print (printIn code_field add4 add0)
open SccCode (helloProg)

set_option linter.unusedSimpArgs false

/-! ## The checks -/

/-- `wc_worker`'s blocks at hello's labels: the head block, the tail's,
the gaps. -/
abbrev wkIn : Bool :=
  blockAt helloProg ".L20_wc_worker.0_entry" 0 Body.wkE &&
  labelGap helloProg ".L20_wc_worker.0_entry" ".L20_wc_worker.sp4" 21 &&
  blockAt helloProg ".L20_wc_worker.sp4" 0 HelloTail.b0 &&
  blockAt helloProg ".L20_wc_worker.sp4" 2
    [.instr ⟨.W64, .STLR .W64 (.low (.reg .X9) .W64) (.low (.reg .X10) .W64)⟩] &&
  blockAt helloProg ".L20_wc_worker.sp4" 3 HelloTail.b1 &&
  blockAt helloProg ".L20_wc_worker.sp4" 4 HelloTail.b2 &&
  blockAcross helloProg ".L20_wc_worker.sp6" 0 (HelloTail.b3.take 3) ".L20_wc_worker.x7" (HelloTail.b3.drop 3) &&
  labelGap helloProg ".L20_wc_worker.sp4" ".L20_wc_worker.sp6" 5

/-- `wc_worker`'s six argument words. -/
abbrev wcPs : List (XReg × Int64) := [(.X0, 0), (.X1, 8), (.X2, 16), (.X3, 24), (.X4, 32), (.X5, 40)]

/-- `wc_worker`'s prologue: frame 96, its six arguments at `0..40`. -/
abbrev wcPro : Bool := prologueIn helloProg "wc_worker" ".L20_wc_worker.stack_check"
  ".L20_wc_worker.0_entry" 96 8 ".L20_wc_worker.stack_grow" wcPs

theorem hello_wkIn : wkIn = true := by decide +kernel
theorem hello_wcPro : wcPro = true := by decide +kernel
theorem hello_printIn : printIn helloProg = true := SccCode.hello_print

/-! ## The code facts -/

section Code

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
include hp hend

/-- **`wc_worker`'s `.0_entry` block.** -/
theorem wkECode : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s ((_root_.Executable.labels exe).label ".L20_wc_worker.0_entry") Body.wkE := by
  have h := hello_wkIn
  simp only [wkIn, Bool.and_eq_true, and_assoc] at h
  exact code_of hp hend h.1 (ofNat4_zero _)

/-- **`wc_worker`'s tail code**, any ghosts. -/
theorem tailCode {c0 c1 c2 : Ctl} {A B x29 ra tp : BitVec 64} :
    HelloTail.Code c0 c1 c2 A B x29 ra tp exe endPc := by
  have h := hello_wkIn
  simp only [wkIn, Bool.and_eq_true, and_assoc] at h
  obtain ⟨-, -, h0, h1, h2, h3, h4, -⟩ := h
  exact ⟨code_of hp hend h0 (by simp only [HelloTail.N, ofNat4_succ, ofNat4_zero]),
    code_of hp hend h1 (by simp only [HelloTail.N, ofNat4_succ, ofNat4_zero]),
    code_of hp hend h2 (by simp only [HelloTail.N, ofNat4_succ, ofNat4_zero]),
    code_of hp hend h3 (by simp only [HelloTail.N, HelloTail.pcBl, ofNat4_succ, ofNat4_zero]),
    Spike.Lib.A64.code_field_blockAcross hp hend h4 (List.take_append_drop _ _)
      (by simp only [HelloTail.N, ofNat4_succ, ofNat4_zero])⟩

omit hend in
/-- **`.sp4` right after the `.0_entry` block** (21 instructions). -/
theorem hgap : (_root_.Executable.labels exe).label ".L20_wc_worker.sp4" =
    (_root_.Executable.labels exe).label ".L20_wc_worker.0_entry" + Int64.ofNat (4 * 21) := by
  have h := hello_wkIn
  simp only [wkIn, Bool.and_eq_true, and_assoc] at h
  exact label_labelGap hp h.2.1

omit hend in
/-- **`.sp6` right after the tail's `bl`.** -/
theorem hsp6 : (_root_.Executable.labels exe).label ".L20_wc_worker.sp6" =
    HelloTail.pcBl (_root_.Executable.labels exe).label + 4 := by
  have h := hello_wkIn
  simp only [wkIn, Bool.and_eq_true, and_assoc] at h
  rw [label_labelGap hp h.2.2.2.2.2.2.2]
  simp only [HelloTail.pcBl, ofNat4_succ, ofNat4_zero]

/-- **`scc_rt_print`'s code** (`PrintF.Code`), any ghosts, from
`printIn` (`hello_print`). -/
theorem printCode {c0 : Ctl} {x29 ra : BitVec 64} : PrintF.Code c0 x29 ra exe endPc := by
  have hprog := hello_printIn
  simp only [printIn, Bool.and_eq_true, and_assoc] at hprog
  obtain ⟨h0, h1, h2, h3, hf, h4, hs, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, -⟩ := hprog
  exact ⟨code_field hp hend h0 (by simp only [PrintF.N, A64.Print.N, add4, add0]),
    code_field hp hend h1 (by simp only [PrintF.N, A64.Print.N, add4, add0]),
    code_field hp hend h2 (by simp only [PrintF.N, A64.Print.N, add4, add0]),
    code_field hp hend h3 (by simp only [PrintF.N, A64.Print.N, add4, add0]),
    code_field hp hend hf (by simp only [PrintF.N, add4, add0]),
    code_field hp hend h4 (by simp only [PrintF.N, add4, add0]),
    code_field hp hend h5 (by simp only [PrintF.N, PrintF.pcSvc, add4, add0]),
    code_field hp hend h6 (by simp only [PrintF.N, PrintF.pcSvc, add4, add0]),
    code_field hp hend h7 (by simp only [PrintF.N, PrintF.pcSvc, add4, add0]),
    code_field hp hend h8 (by simp only [PrintF.N, A64.Print.N, add4, add0]),
    code_field hp hend h9 (by simp only [PrintF.N, A64.Print.N, add4, add0]),
    code_field hp hend h10 (by simp only [PrintF.N, A64.Print.N, add4, add0]),
    code_field hp hend h11 (by simp only [PrintF.N, A64.Print.N, add4, add0]),
    code_field hp hend h12 (by simp only [PrintF.N, A64.Print.N, add4, add0]),
    code_field hp hend h13 (by simp only [PrintF.N, A64.Print.N, add4, add0]),
    code_field hp hend h14 (by simp only [PrintF.N, A64.Print.N, add4, add0]),
    Spike.Lib.A64.code_field_blockAcross hp hend h15 (List.take_append_drop _ _)
      (by simp only [PrintF.N, A64.Print.N, add4, add0]),
    code_field hp hend hs (by simp only [PrintF.N, PrintF.pcSvc, add4, add0])⟩

omit hend in
/-- **`scc_rt_print`'s frame set-up falls through to `.0_entry`.** -/
theorem printEntry : (_root_.Executable.labels exe).label ".L9_scc_rt_print.0_entry" =
    (_root_.Executable.labels exe).label "scc_rt_print" + 4 + 4 + 4 + 4 + 4 + 4 := by
  have hprog := hello_printIn
  simp only [printIn, Bool.and_eq_true, and_assoc] at hprog
  rw [label_labelGap hp hprog.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]
  simp only [add4, add0]

end Code

/-! ## The prologue -/

section Pro

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`wc_worker`'s prologue** in any valid layout of `helloProg`, with the
thread rows: frame 96, `x0..x5` stored at `0..40`. -/
theorem wc_prologue_seg (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    {J : AS → Ctl → Prop} {nb : ND} (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -96) (hhi : 0 ≤ R.hi)
    (hpc : nb.pc = (_root_.Executable.labels exe).label ".L20_wc_worker.0_entry")
    (ho : SO.le nb.o (oFr 96) = true)
    (hedge : ∀ σ c, J σ c →
      ms.rt (tcbA σ.regs 8).toNat ∧ ms.mp ⟨tcbA σ.regs 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs 8) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA σ.regs 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (96 : Int64).toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = frRegs 96 (ldStep .X10 (v.setWidth 64) { σ with regs := chkRegs 96 σ.regs }).regs →
          σ'.slot = stSlots (-(96 : Int64).toInt) σ'.regs wcPs (frSlot σ) → nb.J σ' c) :
    SegT p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_worker", ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  (prologue_seg_of hp hend hello_wcPro (by decide) (by decide) hF hR hal hlo hhi (by decide) hpc ho hedge).toT

end Pro

end Spike.Lib.A64.Flow.Worker.Hello.Wk

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.Wk.printCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.Wk.printCode

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.Wk.wc_prologue_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.Wk.wc_prologue_seg
