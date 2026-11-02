/-
**hello.w's thread worker on x86-64: `scc_rt_thr_worker`**: the target side of
`scc_rt_thr_worker` in hello.w's x86-64 listing (`SccCode.helloCells`, `Spike/Lib/X64HelloCode.lean`).
wake.w's (`Spike.Lib.X64.Flow.Worker.Wake.ThrHeadW`, `ThrTailW`, `X64WakeWorker.lean`) with hello's packet:
the spawn passes six words (`%rdi, %rsi, %rdx, %rcx, %r8, %r9`: the slice's four, the cell, the waiter), so
the frame is 64 bytes below the saved `%rbp` (the six words spilled at `-8(%rbp) .. -48(%rbp)`, the thread
pointer at `-56(%rbp)`, the `exit`'s result at `-64(%rbp)`).

    scc_rt_thr_worker: prologue (frame 64, the six words at -8 .. -48(%rbp))
    .entry: %rdi .. %r9 = the words at -8 .. -48(%rbp); call wc_worker
    .x13:   %rax = %fs:0 (the TCB's self pointer: tp); spilled at -56(%rbp)
            %rcx = tp; %rax = 1
            movq %rax, 24(%rcx)            -- the thread's `exited` word
            %rdi = 0; %eax = 60
            syscall                        -- exit: the thread ends

- `HThrTail`: the tail's blocks (`b0`, `b1`), nodes (`N`) and code (`Code`) from `.x13`.
- `HThrHead`: the `.entry` block (`thE`) and the head's nodes (`tN`).
- `thrIn`, `thrPs`, `thrPro`, `hello_thrIn`, `hello_thrPro`: the blocks and the prologue decided on
  `helloCells`; `thrCode`, `thECode`, `hx13`: their consequences in any valid layout of it.

## Differences from the AArch64 version

`Spike/Lib/A64HelloThr.lean`.

- The labels are the listing's own (`.Lscc_rt_thr_worker.entry`, `.x13`): there is no label prefix
  parameter (`pfx`); the cells are sized, the checks are `blockAtB`/`labelGapB` on `helloCells`.
- The thread pointer is read from the TCB's self word (`movq %fs:0, %rax`, as wake's x86-64 tail), not from
  `tpidr_el0`; the `exited` word's store is a plain `movq` (TSO).
- The frame is addressed from `%rbp` (`oI = ⟨-72, [(.rbp, -8)]⟩`); the prologue is `X64CodeSegs.prologueIn`'s
  (stack check through `%fs:8`, the six argument registers spilled with their sizes).
- Only the live constants are twinned: the segments `seg_thrTail`, `seg_thrHead` and `thr_prologue_seg` are
  not (hello's thread worker is assembled over `SegTCS`/`SegTCSX` from these blocks).
-/
import Spike.Lib.X64WakeWorker
import Spike.Lib.X64HelloCode
import Spike.Lib.X64CodeSegs

namespace Spike.Lib.X64.Flow.Worker.Hello

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64
open Spike.Lib Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Worker
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

set_option linter.unusedSimpArgs false

/-! ## `scc_rt_thr_worker`'s tail -/

namespace HThrTail

def b0 : List (Directive × Nat) := (parse("movq %rax, -56(%rbp)
movq -56(%rbp), %rcx
movq $1, %rax")).zip [4, 4, 7]
def b1 : List (Directive × Nat) := (parse("movq $0, %rdi
movl $60, %eax")).zip [7, 5]

/-- The function's offsets inside the frame. -/
abbrev oI : SO := ⟨-72, [(.rbp, -8)]⟩
/-- The offsets after `wc_worker`'s return (`%rbp` from the invariant). -/
abbrev oP : SO := ⟨-72, []⟩

block_spec b0 (-72) 8 oI b0
block_spec b1 (-72) 8 oI b1

/-- The internal nodes. -/
inductive PN where
  | x13 | n1 | ex | n2 | sys

section Spec

variable (lab : Label → Int64) (c0 : Ctl) (tp sp : BitVec 64)

/-- **The nodes.** Ghosts: the source control `c0` (the worker returned), the thread pointer `tp`, the entry
`%rsp` `sp` (`%rbp = sp - 8`). -/
def N : PN → ND
  | .x13 => ⟨lab ".Lscc_rt_thr_worker.x13", oP, fun σ c => c = c0 ∧ σ.regs.fsBase.toBitVec = tp ∧
      σ.regs.rbp.toBitVec = sp - 8#64⟩
  | .n1 => ⟨lab ".Lscc_rt_thr_worker.x13" + 9, oP, fun σ c => c = c0 ∧ σ.regs.get64 .rax = tp ∧
      σ.regs.rbp.toBitVec = sp - 8#64⟩
  | .ex => ⟨lab ".Lscc_rt_thr_worker.x13" + 24, oI, fun σ c => c = c0 ∧ σ.regs.get64 .rcx = tp ∧
      σ.regs.get64 .rax = 1#64⟩
  | .n2 => ⟨lab ".Lscc_rt_thr_worker.x13" + 28, oI, fun _ c => c = c0⟩
  | .sys => ⟨lab ".Lscc_rt_thr_worker.x13" + 40, oI, fun σ c => c = c0 ∧ σ.regs.get64 .rax = 60#64⟩

/-- **The code**: every block and single instruction at its node's pc. -/
structure Code (exe : _root_.Executable) (endPc : Int64) : Prop where
  x13 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 tp sp .x13).pc [(fsDir .rax 0, 9)]
  n1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 tp sp .n1).pc b0
  ex : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 tp sp .ex).pc [(stDir .rcx 24 .rax, 4)]
  n2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 tp sp .n2).pc b1
  sys : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 tp sp .sys).pc [(op64 .syscall, 2)]

end Spec

end HThrTail

/-! ## `scc_rt_thr_worker`'s head -/

namespace HThrHead

/-- `scc_rt_thr_worker`'s `.entry` block: the six arguments, the call. -/
def thE : List (Directive × Nat) := (parse("movq -8(%rbp), %rdi
movq -16(%rbp), %rsi
movq -24(%rbp), %rdx
movq -32(%rbp), %rcx
movq -40(%rbp), %r8
movq -48(%rbp), %r9
call wc_worker")).zip [4, 4, 4, 4, 4, 4, 5]

/-- The frame's offsets. -/
abbrev oI : SO := ⟨-72, [(.rbp, -8)]⟩

block_spec thE (-80) 8 oI thE

/-- The head's internal nodes. -/
inductive TN where
  | e | call

/-- **The head's nodes**, from the invariant `J` at `.entry`; across the
block the source moves from `c0` to `c` with `L c0 c` (a local run: the
worker's `split` of its argument tuple). `wc_worker` is entered at offset
`-80` (below the frame, the call's return address pushed). -/
def tN (lab : Label → Int64) (J : AS → Ctl → Prop) (L : Ctl → Ctl → Prop) : TN → ND
  | .e => ⟨lab ".Lscc_rt_thr_worker.entry", oI, J⟩
  | .call => ⟨lab "wc_worker", ⟨-80, [(.rbp, -8)]⟩, fun σ c => ∃ σ0 c0, J σ0 c0 ∧ L c0 c ∧
      σ = (arun lab thE ⟨lab ".Lscc_rt_thr_worker.entry", oI, σ0⟩).σ⟩

end HThrHead

/-! ## The checks on hello's listing -/

/-- `scc_rt_thr_worker`'s blocks. -/
def thrIn (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells ".Lscc_rt_thr_worker.entry" 0 HThrHead.thE &&
  labelGapB cells ".Lscc_rt_thr_worker.entry" ".Lscc_rt_thr_worker.x13" 29 &&
  blockAtB cells ".Lscc_rt_thr_worker.x13" 0 [(fsDir .rax 0, 9)] &&
  blockAtB cells ".Lscc_rt_thr_worker.x13" 9 HThrTail.b0 &&
  blockAtB cells ".Lscc_rt_thr_worker.x13" 24 [(stDir .rcx 24 .rax, 4)] &&
  blockAtB cells ".Lscc_rt_thr_worker.x13" 28 HThrTail.b1 &&
  blockAtB cells ".Lscc_rt_thr_worker.x13" 40 [(op64 .syscall, 2)]

/-- The prologue's spills: the six argument registers at `-8 .. -48(%rbp)`, with their sizes. -/
abbrev thrPs : List (Reg64 × Int64 × Nat) :=
  [(.rdi, -8, 4), (.rsi, -16, 4), (.rdx, -24, 4), (.rcx, -32, 4), (.r8, -40, 4), (.r9, -48, 4)]

/-- `scc_rt_thr_worker`'s prologue: frame 64, its six arguments at `-8 .. -48(%rbp)`. -/
def thrPro (cells : List (Directive × Nat)) : Bool :=
  prologueIn cells "scc_rt_thr_worker" ".Lscc_rt_thr_worker.chk" ".Lscc_rt_thr_worker.entry" 64 8
    ".Lscc_rt_thr_worker.stk" 5 9 3 2 4 thrPs

theorem hello_thrIn : thrIn SccCode.helloCells = true := by decide +kernel
theorem hello_thrPro : thrPro SccCode.helloCells = true := by decide +kernel

/-! ## The code facts -/

section Code

variable {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
include hp hend

/-- **`scc_rt_thr_worker`'s tail code**, any ghosts. -/
theorem thrCode {c0 : Ctl} {tp sp : BitVec 64} : HThrTail.Code c0 tp sp exe endPc := by
  have h := hello_thrIn
  simp only [thrIn, Bool.and_eq_true, and_assoc] at h
  obtain ⟨-, -, h0, h1, h2, h3, h4⟩ := h
  exact ⟨code_field hp hend h0 (ofNat_zero' _), code_field hp hend h1 rfl, code_field hp hend h2 rfl,
    code_field hp hend h3 rfl, code_field hp hend h4 rfl⟩

/-- **`scc_rt_thr_worker`'s `.entry` block.** -/
theorem thECode : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s ((_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.entry") HThrHead.thE := by
  have h := hello_thrIn
  simp only [thrIn, Bool.and_eq_true, and_assoc] at h
  exact code_field hp hend h.1 (ofNat_zero' _)

omit hend in
/-- **`.x13` right after `scc_rt_thr_worker`'s `call`.** -/
theorem hx13 : (_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.x13" =
    (_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.entry" + 29 := by
  have h := hello_thrIn
  simp only [thrIn, Bool.and_eq_true, and_assoc] at h
  rw [label_labelGapB hp h.2.1]; rfl

end Code

end Spike.Lib.X64.Flow.Worker.Hello

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.thrCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.X64.Flow.Worker.Hello.thrCode

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.hello_thrPro' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.X64.Flow.Worker.Hello.hello_thrPro
