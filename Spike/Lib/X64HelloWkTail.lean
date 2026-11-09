/-
**hello.w's `wc_worker` tail on x86-64** (the twin of
`Spike/Lib/A64HelloWkTail.lean`): wake.w's x86-64 `WkTailW`
(`Spike/Lib/X64WakeWorker.lean`) at hello.w's labels and frame. hello.w's
`wc_worker` prints its slice first (`.entry`, ending in `call scc_rt_print`);
its tail starts at the print's return point `.Lwc_worker.x0`: the store of
`1` to the cell `c` (`-40(%rbp)`), the call of `scc_rt_unpark` with the tid
`j` (`-48(%rbp)`), the epilogue at `.Lwc_worker.x1`.

    .x17:  %rcx = c (-40(%rbp)); %rax = 1
           movq %rax, (%rcx)               -- the source's `store rel c 1`
           %rdi = j (-48(%rbp))
           call scc_rt_unpark              -- the source's `unpark j` (inside)
    .x18:  epilogue; ret

The region is the frame, offsets `[-96, 8)` from the `%rsp` at entry (the
return address at `0`, the saved `%rbp` at `-8`, the six arguments at
`-16 … -56` (`c` at `-48`, `j` at `-56`), the slice's temporaries at
`-64 … -88`, the return address of the call at `-96`). Ghosts as in
`WkTailW`: the source controls `c0`, `c1`, `c2`, the address `A` of `c`, the
tid `B` of `j`, the caller's `%rbp` `rbp0`, the return address `ra`, the
thread pointer `tp` and the entry `%rsp` `sp` (`%rbp = sp - 8`).

- `HelloTail.N`, `E`, `Code`: the nodes, the exit, the code (the segments
  off the transfer sites are `Spike/Lib/X64HelloWkTailNN.lean`'s).

## Differences from the AArch64 version

- The shape is x86-64's `WkTailW`: `%rbp` frames whose region ends at `8`,
  the call pushing its return address (`.unpk` at offset `-96`), the
  epilogue node `.x18` at offsets knowing `%rsp` alone (`oP`), the
  invariant carrying `%rbp = sp - 8`; AArch64's `.n3`/`.bl` are one node
  `.n3` (`movq -48(%rbp), %rdi; call scc_rt_unpark` is one block).
- The labels are hello.w's x86-64 ones (`.Lwc_worker.x0`, `.x18`; A64:
  `.L20_wc_worker.sp4`, `.sp6`), the frame 80 bytes (A64: 96 with `x29`/`x30`
  saved at its top).
- The store is a plain `movq` (TSO; A64: `stlr`), the thread pointer
  `fsBase`.
- A64's `seg_wkTail`, `seg_unparkCall`, `seg_wkTailU` (dead) are not
  twinned.
-/
import Spike.Lib.X64WorkerRows
import Spike.Lib.X64WaitLoop

namespace Spike.Lib.X64.Flow.Worker

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64
open Spike.Lib Spike.Lib.X64.Flow

namespace HelloTail

def b0 : List (Directive × Nat) := (parse("movq -40(%rbp), %rcx
movq $1, %rax")).zip [4, 7]
def b1 : List (Directive × Nat) := (parse("movq -48(%rbp), %rdi
call scc_rt_unpark")).zip [4, 5]
def b2 : List (Directive × Nat) := (parse("movq %rbp, %rsp
popq %rbp
ret")).zip [3, 1, 1]

/-- The function's offsets inside the frame. -/
abbrev oI : SO := ⟨-88, [(.rbp, -8)]⟩
/-- The offsets after the call's return (`%rbp` from the invariant). -/
abbrev oP : SO := ⟨-88, []⟩
/-- The offsets at the callee's entry. -/
abbrev oS : SO := ⟨-96, [(.rbp, -8)]⟩
/-- The offsets after the return. -/
abbrev oR : SO := ⟨8, []⟩

block_spec b0 (-96) 8 oI b0
block_spec b1 (-96) 8 oI b1
block_spec b2 (-96) 8 oI b2

/-- The internal nodes. -/
inductive PN where
  | e | st | n3 | unpk | x18

/-- The exits. -/
inductive PX where
  | ret

section Spec

variable (lab : Label → Int64) (c0 c1 c2 : Ctl) (A B rbp0 ra tp sp : BitVec 64)

/-- Inside the frame, the source at `c'`: the caller's `%rbp`, the return
address, `A` and `B` in their cells, the thread pointer `tp`, `%rbp` at the
saved `%rbp`. -/
def JI (c' : Ctl) (σ : AS) (c : Ctl) : Prop :=
  c = c' ∧ σ.slot (-8) = rbp0 ∧ σ.slot 0 = ra ∧ σ.slot (-48) = A ∧ σ.slot (-56) = B ∧
    σ.regs.fsBase.toBitVec = tp ∧ σ.regs.rbp.toBitVec = sp - 8#64

/-- The return address of the call. -/
abbrev raU : BitVec 64 := (lab ".Lwc_worker.x0" + 14).toBitVec + 9#64

/-- **The nodes.** -/
def N : PN → ND
  | .e => ⟨lab ".Lwc_worker.x0", oI, JI A B rbp0 ra tp sp c0⟩
  | .st => ⟨lab ".Lwc_worker.x0" + 11, oI, fun σ c => JI A B rbp0 ra tp sp c0 σ c ∧
      σ.regs.get64 .rcx = A ∧ σ.regs.get64 .rax = 1#64⟩
  | .n3 => ⟨lab ".Lwc_worker.x0" + 14, oI, JI A B rbp0 ra tp sp c1⟩
  | .unpk => ⟨lab "scc_rt_unpark", oS, fun σ c => JI A B rbp0 ra tp sp c1 σ c ∧ σ.regs.get64 .rdi = B ∧
      σ.slot (-96) = raU lab⟩
  | .x18 => ⟨lab ".Lwc_worker.x1", oP, JI A B rbp0 ra tp sp c2⟩

/-- **The exit**: the return to `ra` with `%rsp` past the return address,
`%rbp` and the thread pointer as at entry, the source past its `unpark`. -/
def E : PX → ND
  | .ret => ⟨Int64.ofBitVec ra, oR, fun σ c => c = c2 ∧ σ.regs.get64 .rbp = rbp0 ∧
      σ.regs.fsBase.toBitVec = tp⟩

/-- **The code**: every block and the store at its node's pc. -/
structure Code (exe : _root_.Executable) (endPc : Int64) : Prop where
  e : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp sp .e).pc b0
  st : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp sp .st).pc [(stDir .rcx 0 .rax, 3)]
  n3 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp sp .n3).pc b1
  x18 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp sp .x18).pc b2

end Spec

end HelloTail

end Spike.Lib.X64.Flow.Worker

/-- info: 'Spike.Lib.X64.Flow.Worker.HelloTail.b0_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.HelloTail.b0_ok

/-- info: 'Spike.Lib.X64.Flow.Worker.HelloTail.b1_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.HelloTail.b1_run
