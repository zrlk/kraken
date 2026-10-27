/-
**A whole compiled function on x64**: `wc_printL` of `hello.w`'s listing
(plain calls, no stack depth counter, `Scc.Lower.callBlock`) as one `Seg`,
composed from its blocks over its control-flow graph
(`Spike/Lib/X64Cfg.lean`): the x64 twin of `Spike/Lib/A64PrintL.lean` (same
function, same graph up to the given nodes and the `imulq`).

    wc_printL(xs = rdi, o = rsi, i = rdx, n = rcx, acc = r8):
      push rbp; rbp = rsp
      chk: if rsp - 112 < limit (%fs:8) goto stk
      prologue (frame of 112 bytes below rbp, arguments at -8 .. -40)
      e = load(xs + zext32(o + 8 i))              -- imulq, then a heap load
      acc' = wc_emit8(e, acc)                     -- a call
      if n = 0 then return acc'
      n' = n - 1 (saturating); i' = i + 1 (abort on overflow)
      tail call wc_printL(xs, o, i', n', acc')
      stk: push rdi rsi rdx rcx r8 r9; call scc_rt_morestack; pop them; goto chk

The region is `[-120, 16)` from the frame's base: `%rsp` is at offset 8 on
entry, the return address in the cell `[8, 16)`, the caller's `%rbp` pushed
to `[0, 8)`, the frame below (the call's return address at `-120`, the stack
grow path's six registers and return address in `[-56, 0)`). Ghost
parameters: the source control `c0`, the caller's `%rbp` and the return
address `ra`. Entry (`.e`): `%rsp` at offset 8, `%rbp = rbp0`, `ra` in its
cell; the tail call comes back to it. Return (exit `.ret`): pc at `ra`,
`%rsp` at offset 16, `%rbp` restored. Abort (exit `.abort`): pc at
`scc_rt_abort` with `%rdi = 1` (overflow).

The `imulq` (undefined flags) is a node of its own (`flag_nd`,
`Spike/Lib/X64Flags.lean`), landing at the next block for every value of
the flags. Given nodes (hypotheses): the thread-pointer load of the stack
limit (`htls`), the heap load (`hheap`), the call to `wc_emit8` (`hcall`,
from its entry with the return address at `-120` back to `.x17`) and the
call to `scc_rt_morestack` (`hms`). The calls may grow the stack and so
move the frame: the region, the frame condition `F` (any condition no write
inside the region breaks, `FStable`) and the caller's `%rbp` are a ghost
(`fn_seg_g`), and `hcall` and `hms` land at some ghost. The code, the
labels `.chk` and `.entry` at their fall-through addresses are hypotheses.
Each block is zipped with its instructions' sizes in bytes; a node's pc is
a label plus the sizes of the instructions before it.
-/
import Spike.Lib.X64Flags
import Kraken.X64.Parser

namespace Spike.Lib.X64.PrintL

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Spike.Lib.X64

/-! ## The blocks (generated) -/

def b0 : List (Directive × Nat) := (parse("pushq %rbp
movq %rsp, %rbp")).zip [1, 3]
def b1 : List (Directive × Nat) := (parse("leaq -112(%rsp), %rax")).zip [5]
def b2 : List (Directive × Nat) := (parse("cmpq %r11, %rax
jb .Lwc_printL.stk")).zip [3, 6]
def b3 : List (Directive × Nat) := (parse("subq $112, %rsp
movq %rdi, -8(%rbp)
movq %rsi, -16(%rbp)
movq %rdx, -24(%rbp)
movq %rcx, -32(%rbp)
movq %r8, -40(%rbp)")).zip [4, 4, 4, 4, 4, 4]
def b4 : List (Directive × Nat) := (parse("movq -24(%rbp), %rax
movq $8, %rcx")).zip [4, 7]
def b5 : List (Directive × Nat) := (parse("movq %rax, -48(%rbp)
movq -16(%rbp), %rax
movq -48(%rbp), %rcx
addq %rcx, %rax
movq %rax, -56(%rbp)
movq -56(%rbp), %rax
movl %eax, %eax
movq %rax, -64(%rbp)
movq -8(%rbp), %rax
movq -64(%rbp), %rcx
addq %rcx, %rax
movq %rax, -72(%rbp)
movq -72(%rbp), %rcx")).zip [4, 4, 4, 3, 4, 4, 2, 4, 4, 4, 3, 4, 4]
def b6 : List (Directive × Nat) := (parse("movq %rax, -80(%rbp)
movq -80(%rbp), %rdi
movq -40(%rbp), %rsi
call wc_emit8")).zip [4, 4, 4, 5]
def b7 : List (Directive × Nat) := (parse("movq %rax, -88(%rbp)
movq -32(%rbp), %rax
movq $0, %rcx
cmpq %rcx, %rax
je .Lwc_printL.then6")).zip [4, 4, 7, 3, 2]
def b8 : List (Directive × Nat) := (parse("jmp .Lwc_printL.else7")).zip [2]
def b9 : List (Directive × Nat) := (parse("movq -88(%rbp), %rax
movq %rbp, %rsp
popq %rbp
ret")).zip [4, 3, 1, 1]
def b10 : List (Directive × Nat) := (parse("movq -32(%rbp), %rax
movq $1, %rcx
subq %rcx, %rax
movl $0, %edx
cmovb %rdx, %rax
movq %rax, -96(%rbp)
movq -24(%rbp), %rax
movq $1, %rcx
addq %rcx, %rax
jb .Lwc_printL.ovf")).zip [4, 7, 3, 5, 4, 4, 4, 7, 3, 2]
def b11 : List (Directive × Nat) := (parse("movq %rax, -104(%rbp)
movq -8(%rbp), %rdi
movq -16(%rbp), %rsi
movq -104(%rbp), %rdx
movq -96(%rbp), %rcx
movq -88(%rbp), %r8
movq %rbp, %rsp
popq %rbp
jmp wc_printL")).zip [4, 4, 4, 4, 4, 4, 3, 1, 5]
def b12 : List (Directive × Nat) := (parse("movl $1, %edi
call scc_rt_abort")).zip [5, 5]
def b13 : List (Directive × Nat) := (parse("pushq %rdi
pushq %rsi
pushq %rdx
pushq %rcx
pushq %r8
pushq %r9
movl $112, %edi
call scc_rt_morestack")).zip [1, 1, 1, 1, 2, 2, 5, 5]
def b14 : List (Directive × Nat) := (parse("popq %r9
popq %r8
popq %rcx
popq %rdx
popq %rsi
popq %rdi
jmp .Lwc_printL.chk")).zip [2, 2, 1, 1, 1, 1, 5]

/-- The offsets at entry. -/
abbrev oE : SO := ⟨8, []⟩
/-- The offsets at the stack check. -/
abbrev oC : SO := ⟨0, [(.rbp, 0)]⟩
/-- The offsets after the stack check's `leaq` (`%rax` the new `%rsp`). -/
abbrev oX : SO := ⟨0, [(.rax, -112), (.rbp, 0)]⟩
/-- The offsets inside the frame. -/
abbrev oI : SO := ⟨-112, [(.rbp, 0)]⟩
/-- The offsets in the stack grow path after `scc_rt_morestack`. -/
abbrev oG : SO := ⟨-48, [(.rbp, 0)]⟩

block_spec b0 (-120) 16 oE b0
block_spec b1 (-120) 16 oC b1
block_spec b2 (-120) 16 oX b2
block_spec b3 (-120) 16 oX b3
block_spec b4 (-120) 16 oI b4
block_spec b5 (-120) 16 oI b5
block_spec b6 (-120) 16 oI b6
block_spec b7 (-120) 16 oI b7
block_spec b8 (-120) 16 oI b8
block_spec b9 (-120) 16 oI b9
block_spec b10 (-120) 16 oI b10
block_spec b11 (-120) 16 oI b11
block_spec b12 (-120) 16 oI b12
block_spec b13 (-120) 16 oX b13
block_spec b14 (-120) 16 oG b14

/-! ## The graph -/

/-- The internal nodes: one per block, and the given nodes. -/
inductive PN where
  | e | chk | tls | n2 | n3 | entry | mul | n5 | heap | n6 | call | x17 | n8 | then6 | else7 | n11
  | ovf | stk | ms | x18

/-- The exits. -/
inductive PX where
  | ret | abort

section Spec

variable (lab : Label → Int64) (c0 : Ctl) (rbp0 ra : BitVec 64)

/-- At entry: the source has not moved, `%rbp` is the caller's, the return
address in its cell. -/
def JE (σ : AS) (c : Ctl) : Prop := c = c0 ∧ σ.regs.get64 .rbp = rbp0 ∧ σ.slot 8 = ra

/-- Inside the frame: the caller's `%rbp` and the return address are in
their cells. -/
def JI (σ : AS) (c : Ctl) : Prop := c = c0 ∧ σ.slot 0 = rbp0 ∧ σ.slot 8 = ra

/-- **The nodes.** -/
def N : PN → ND
  | .e => ⟨lab "wc_printL", oE, JE c0 rbp0 ra⟩
  | .chk => ⟨lab ".Lwc_printL.chk", oC, JI c0 rbp0 ra⟩
  | .tls => ⟨lab ".Lwc_printL.chk" + 5, oX, JI c0 rbp0 ra⟩
  | .n2 => ⟨lab ".Lwc_printL.chk" + 14, oX, JI c0 rbp0 ra⟩
  | .n3 => ⟨lab ".Lwc_printL.chk" + 23, oX, JI c0 rbp0 ra⟩
  | .entry => ⟨lab ".Lwc_printL.entry", oI, JI c0 rbp0 ra⟩
  | .mul => ⟨lab ".Lwc_printL.entry" + 11, oI, JI c0 rbp0 ra⟩
  | .n5 => ⟨lab ".Lwc_printL.entry" + 15, oI, JI c0 rbp0 ra⟩
  | .heap => ⟨lab ".Lwc_printL.entry" + 63, oI, JI c0 rbp0 ra⟩
  | .n6 => ⟨lab ".Lwc_printL.entry" + 66, oI, JI c0 rbp0 ra⟩
  | .call => ⟨lab "wc_emit8", ⟨-120, [(.rbp, 0)]⟩, fun σ c => JI c0 rbp0 ra σ c ∧
      σ.slot (-120) = (lab ".Lwc_printL.entry" + 83).toBitVec⟩
  | .x17 => ⟨lab ".Lwc_printL.x17", oI, JI c0 rbp0 ra⟩
  | .n8 => ⟨lab ".Lwc_printL.x17" + 20, oI, JI c0 rbp0 ra⟩
  | .then6 => ⟨lab ".Lwc_printL.then6", oI, JI c0 rbp0 ra⟩
  | .else7 => ⟨lab ".Lwc_printL.else7", oI, JI c0 rbp0 ra⟩
  | .n11 => ⟨lab ".Lwc_printL.else7" + 43, oI, JI c0 rbp0 ra⟩
  | .ovf => ⟨lab ".Lwc_printL.ovf", oI, JI c0 rbp0 ra⟩
  | .stk => ⟨lab ".Lwc_printL.stk", oX, JI c0 rbp0 ra⟩
  | .ms => ⟨lab "scc_rt_morestack", ⟨-56, [(.rbp, 0)]⟩, fun σ c => JI c0 rbp0 ra σ c ∧
      σ.slot (-56) = (lab ".Lwc_printL.stk" + 18).toBitVec⟩
  | .x18 => ⟨lab ".Lwc_printL.x18", oG, JI c0 rbp0 ra⟩

/-- **The exits.** -/
def E : PX → ND
  | .ret => ⟨Int64.ofBitVec ra, ⟨16, []⟩, fun σ c => c = c0 ∧ σ.regs.get64 .rbp = rbp0⟩
  | .abort => ⟨lab "scc_rt_abort", ⟨-120, []⟩, fun σ c => c = c0 ∧ σ.regs.get64 .rdi = 1⟩

/-- **The code**: every block at its node's pc. -/
structure Code (exe : _root_.Executable) (endPc : Int64) : Prop where
  e : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .e).pc b0
  chk : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .chk).pc b1
  n2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .n2).pc b2
  n3 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .n3).pc b3
  entry : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .entry).pc b4
  n5 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .n5).pc b5
  mul : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .mul).pc [(FI.toDir (.imul_rr .rax .rcx), 4)]
  n6 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .n6).pc b6
  x17 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .x17).pc b7
  n8 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .n8).pc b8
  then6 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .then6).pc b9
  else7 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .else7).pc b10
  n11 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .n11).pc b11
  ovf : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .ovf).pc b12
  stk : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .stk).pc b13
  x18 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .x18).pc b14

end Spec

/-! ## The proof -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {c0 : Ctl} {ra : BitVec 64} {γ : Sort _} {Rg : γ → Region}
  {Fg : γ → MachineData → Prop} {rb : γ → BitVec 64}

set_option hygiene false in
/-- A block node: the block, its `okBlk`, its code; the edge is left. -/
macro "node " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine seg_fix g (seg_nd (by simp [$b:ident]) $ok hF hR hlo hhi (fun s he hn => hcode.$f s he hn)
    fun σ c hJ => ⟨c, .refl c, ?_⟩))

/-- Hitting node `j`. -/
macro "hit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;>
    simp_all [N, JE, JI, Int64.add_assoc, BitVec.add_assoc, upd_apply, Reg64s.get64_set64_self,
      Reg64s.get64_set64_ne]))

/-- Hitting exit `x`. -/
macro "exit " x:term : tactic =>
  `(tactic| (refine .inr ⟨$x, ?_, rfl, ?_⟩ <;>
    simp_all [N, E, JE, JI, Int64.add_assoc, upd_apply, Reg64s.get64_set64_self, Reg64s.get64_set64_ne]))

/-- **`wc_printL` is one segment** from its entry to its return or its
aborts. Its frame may move (a call that grows the stack, here the stack
grow path's `scc_rt_morestack` and the call to `wc_emit8`): the region, the
frame condition and the caller's `%rbp` are a ghost `g` (`Rg g`, `Fg g`,
`rb g`), the given nodes `hcall` and `hms` land at some ghost, and the
function exits at some ghost (`fn_seg_g`). -/
theorem seg_printL (hF : ∀ g, FStable (Rg g) (Fg g)) (hR : ∀ g, (Rg g).OK) (hlo : ∀ g, (Rg g).lo ≤ -120)
    (hhi : ∀ g, 16 ≤ (Rg g).hi) (hcode : ∀ g, Code c0 (rb g) ra exe endPc)
    (hchk : (_root_.Executable.labels exe).label ".Lwc_printL.chk" =
      (_root_.Executable.labels exe).label "wc_printL" + 4)
    (hentry : (_root_.Executable.labels exe).label ".Lwc_printL.entry" =
      (_root_.Executable.labels exe).label ".Lwc_printL.chk" + 47)
    (htls : ∀ g,
      Seg p lbl ms (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label c0 (rb g) ra .tls))
        (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label c0 (rb g) ra .n2)))
    (hheap : ∀ g,
      Seg p lbl ms (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label c0 (rb g) ra .heap))
        (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label c0 (rb g) ra .n6)))
    (hcall : ∀ g,
      Seg p lbl ms (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label c0 (rb g) ra .call))
        (fun s c => ∃ g', At exe endPc (Rg g') (Fg g') (N (_root_.Executable.labels exe).label c0 (rb g') ra .x17) s c))
    (hms : ∀ g,
      Seg p lbl ms (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label c0 (rb g) ra .ms))
        (fun s c => ∃ g', At exe endPc (Rg g') (Fg g') (N (_root_.Executable.labels exe).label c0 (rb g') ra .x18) s c))
    (g0 : γ) :
    Seg p lbl ms (At exe endPc (Rg g0) (Fg g0) (N (_root_.Executable.labels exe).label c0 (rb g0) ra .e))
      (fun s c => ∃ g x, At exe endPc (Rg g) (Fg g) (E (_root_.Executable.labels exe).label c0 (rb g) ra x) s c) := by
  refine fn_seg_g (Rg := Rg) (Fg := Fg) (N := fun g => N _ c0 (rb g) ra) (E := fun g => E _ c0 (rb g) ra)
    (fun g i => ?_) g0 PN.e
  have hF := hF g; have hR := hR g; have hlo := hlo g; have hhi := hhi g; have hcode := hcode g
  cases i
  case e => node b0 b0_ok e; rw [N, b0_run]; hit PN.chk
  case chk => node b1 b1_ok chk; rw [N, b1_run]; hit PN.tls
  case tls => exact seg_fix g (seg_given PN.n2 (htls g))
  case n2 =>
    node b2 b2_ok n2; rw [N, b2_run]
    split
    · hit PN.n3
    · hit PN.stk
  case n3 => node b3 b3_ok n3; rw [N, b3_run]; hit PN.entry
  case entry => node b4 b4_ok entry; rw [N, b4_run]; hit PN.mul
  case mul =>
    refine seg_fix g (flag_nd (fi := .imul_rr .rax .rcx) rfl hF (fun s he hn => hcode.mul s he hn)
      fun σ c hJ fl => ⟨c, .refl c, ?_⟩)
    refine .inl ⟨PN.n5, ?_, rfl, ?_⟩ <;> simp_all [N, JI, FI.step, Int64.add_assoc]
  case n5 => node b5 b5_ok n5; rw [N, b5_run]; hit PN.heap
  case heap => exact seg_fix g (seg_given PN.n6 (hheap g))
  case n6 => node b6 b6_ok n6; rw [N, b6_run]; hit PN.call
  case call => exact seg_moved PN.x17 (hcall g)
  case x17 =>
    node b7 b7_ok x17; rw [N, b7_run]
    split
    · hit PN.then6
    · hit PN.n8
  case n8 => node b8 b8_ok n8; rw [N, b8_run]; hit PN.else7
  case then6 => node b9 b9_ok then6; rw [N, b9_run]; exit PX.ret
  case else7 =>
    node b10 b10_ok else7; rw [N, b10_run]
    split
    · hit PN.n11
    · hit PN.ovf
  case n11 => node b11 b11_ok n11; rw [N, b11_run]; hit PN.e
  case ovf => node b12 b12_ok ovf; rw [N, b12_run]; exit PX.abort
  case stk => node b13 b13_ok stk; rw [N, b13_run]; hit PN.ms
  case ms => exact seg_moved PN.x18 (hms g)
  case x18 => node b14 b14_ok x18; rw [N, b14_run]; hit PN.chk

end Proof

end Spike.Lib.X64.PrintL
