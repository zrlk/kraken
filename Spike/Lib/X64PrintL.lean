/-
**A whole compiled function on x64**: `wc_printL` of `hello.w`'s listing
(with the stack depth counter, `Scc.Lower.callBlock`) as one `Seg`, composed
from its blocks over its control-flow graph (`Spike/Lib/X64Cfg.lean`): the
x64 twin of `Spike/Lib/A64PrintL.lean` (same function, same graph up to the
given nodes and the `imulq`).

    wc_printL(xs = rdi, o = rsi, i = rdx, n = rcx, acc = r8):
      push rbp; rbp = rsp
      chk: if rsp - 144 < limit (%fs:8) goto stk
      prologue (frame of 144 bytes below rbp, arguments at -8 .. -40)
      e = load(xs + zext32(o + 8 i))              -- imulq, then a heap load
      tp = %fs:0; d = load(tp + 64); d1 = d + 1   -- the depth counter
      if d1 > limit goto deep9                    -- unsigned
      store(tp + 64, d1)
      acc' = wc_emit8(e, acc)                     -- a call
      store(%fs:0 + 64, d)
      if n = 0 then return acc'
      n' = n - 1 (saturating); i' = i + 1 (abort on overflow)
      tail call wc_printL(xs, o, i', n', acc')
      deep9: call scc_rt_abort(3)                 -- out of stack
      stk: push rdi rsi rdx rcx r8 r9; call scc_rt_morestack; pop them; goto chk

The region is `[-152, 16)` from the frame's base: `%rsp` is at offset 8 on
entry, the return address in the cell `[8, 16)`, the caller's `%rbp` pushed
to `[0, 8)`, the frame below (the call's return address at `-152`, the stack
grow path's six registers and return address in `[-56, 0)`). Ghost
parameters: the source control `c0`, the caller's `%rbp` and the return
address `ra`. Entry (`.e`): `%rsp` at offset 8, `%rbp = rbp0`, `ra` in its
cell; the tail call comes back to it. Return (exit `.ret`): pc at `ra`,
`%rsp` at offset 16, `%rbp` restored. Abort (exits `.abort` and `.stack`):
pc at `scc_rt_abort` with `%rdi = 1` (overflow) or `%rdi = 3` (the depth
counter's limit: out of stack).

The `imulq` (undefined flags) is a node of its own (`flag_nd`,
`Spike/Lib/X64Flags.lean`), landing at the next block for every value of
the flags. Given nodes (hypotheses): the thread-pointer load of the stack
limit (`htls`), the heap load (`hheap`), the depth counter's accesses (the
thread-pointer reads `htp0` and `htp1`, the counter's load `hdld` and its
stores `hdst1` and `hdst2`), the call to `wc_emit8` (`hcall`, from its entry
with the return address at `-152` back to `.x18`) and the call to
`scc_rt_morestack` (`hms`). The calls may grow the stack and so move the
frame: the region, the frame condition `F` (any condition no write inside
the region breaks, `FStable`) and the caller's `%rbp` are a ghost
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
def b1 : List (Directive × Nat) := (parse("leaq -144(%rsp), %rax")).zip [8]
def b2 : List (Directive × Nat) := (parse("cmpq %r11, %rax
jb .Lwc_printL.stk")).zip [3, 6]
def b3 : List (Directive × Nat) := (parse("subq $144, %rsp
movq %rdi, -8(%rbp)
movq %rsi, -16(%rbp)
movq %rdx, -24(%rbp)
movq %rcx, -32(%rbp)
movq %r8, -40(%rbp)")).zip [7, 4, 4, 4, 4, 4]
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
def b6 : List (Directive × Nat) := (parse("movq %rax, -80(%rbp)")).zip [4]
def b7 : List (Directive × Nat) := (parse("movq %rax, -88(%rbp)
movq -88(%rbp), %rcx")).zip [4, 4]
def b8 : List (Directive × Nat) := (parse("movq %rax, -96(%rbp)
movq -96(%rbp), %rax
movq $1, %rcx
addq %rcx, %rax
movq %rax, -104(%rbp)
movq -104(%rbp), %rax
movq $161307, %rcx
cmpq %rcx, %rax
ja .Lwc_printL.deep9")).zip [4, 4, 7, 3, 4, 4, 7, 3, 2]
def b9 : List (Directive × Nat) := (parse("jmp .Lwc_printL.call10")).zip [2]
def b10 : List (Directive × Nat) := (parse("movq $3, %rdi
call scc_rt_abort")).zip [7, 5]
def b11 : List (Directive × Nat) := (parse("movq -88(%rbp), %rcx
movq -104(%rbp), %rax")).zip [4, 4]
def b12 : List (Directive × Nat) := (parse("movq -80(%rbp), %rdi
movq -40(%rbp), %rsi
call wc_emit8")).zip [4, 4, 5]
def b13 : List (Directive × Nat) := (parse("movq %rax, -112(%rbp)")).zip [4]
def b14 : List (Directive × Nat) := (parse("movq %rax, -120(%rbp)
movq -120(%rbp), %rcx
movq -96(%rbp), %rax")).zip [4, 4, 4]
def b15 : List (Directive × Nat) := (parse("movq -32(%rbp), %rax
movq $0, %rcx
cmpq %rcx, %rax
je .Lwc_printL.then12")).zip [4, 7, 3, 2]
def b16 : List (Directive × Nat) := (parse("jmp .Lwc_printL.else13")).zip [2]
def b17 : List (Directive × Nat) := (parse("movq -112(%rbp), %rax
movq %rbp, %rsp
popq %rbp
ret")).zip [4, 3, 1, 1]
def b18 : List (Directive × Nat) := (parse("movq -32(%rbp), %rax
movq $1, %rcx
subq %rcx, %rax
movl $0, %edx
cmovb %rdx, %rax
movq %rax, -128(%rbp)
movq -24(%rbp), %rax
movq $1, %rcx
addq %rcx, %rax
jb .Lwc_printL.ovf")).zip [4, 7, 3, 5, 4, 4, 4, 7, 3, 2]
def b19 : List (Directive × Nat) := (parse("movq %rax, -136(%rbp)
movq -8(%rbp), %rdi
movq -16(%rbp), %rsi
movq -136(%rbp), %rdx
movq -128(%rbp), %rcx
movq -112(%rbp), %r8
movq %rbp, %rsp
popq %rbp
jmp wc_printL")).zip [7, 4, 4, 7, 4, 4, 3, 1, 5]
def b20 : List (Directive × Nat) := (parse("movl $1, %edi
call scc_rt_abort")).zip [5, 5]
def b21 : List (Directive × Nat) := (parse("pushq %rdi
pushq %rsi
pushq %rdx
pushq %rcx
pushq %r8
pushq %r9
movl $144, %edi
call scc_rt_morestack")).zip [1, 1, 1, 1, 2, 2, 5, 5]
def b22 : List (Directive × Nat) := (parse("popq %r9
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
abbrev oX : SO := ⟨0, [(.rax, -144), (.rbp, 0)]⟩
/-- The offsets inside the frame. -/
abbrev oI : SO := ⟨-144, [(.rbp, 0)]⟩
/-- The offsets in the stack grow path after `scc_rt_morestack`. -/
abbrev oG : SO := ⟨-48, [(.rbp, 0)]⟩

block_spec b0 (-152) 16 oE b0
block_spec b1 (-152) 16 oC b1
block_spec b2 (-152) 16 oX b2
block_spec b3 (-152) 16 oX b3
block_spec b4 (-152) 16 oI b4
block_spec b5 (-152) 16 oI b5
block_spec b6 (-152) 16 oI b6
block_spec b7 (-152) 16 oI b7
block_spec b8 (-152) 16 oI b8
block_spec b9 (-152) 16 oI b9
block_spec b10 (-152) 16 oI b10
block_spec b11 (-152) 16 oI b11
block_spec b12 (-152) 16 oI b12
block_spec b13 (-152) 16 oI b13
block_spec b14 (-152) 16 oI b14
block_spec b15 (-152) 16 oI b15
block_spec b16 (-152) 16 oI b16
block_spec b17 (-152) 16 oI b17
block_spec b18 (-152) 16 oI b18
block_spec b19 (-152) 16 oI b19
block_spec b20 (-152) 16 oI b20
block_spec b21 (-152) 16 oX b21
block_spec b22 (-152) 16 oG b22

/-! ## The graph -/

/-- The internal nodes: one per block, and the given nodes. -/
inductive PN where
  | e | chk | tls | n2 | n3 | entry | mul | n5 | heap | n6 | tp0 | n7 | dld | n8 | n9 | deep9
  | call10 | dst1 | n12 | call | x18 | tp1 | n14 | dst2 | n15 | n16 | then12 | else13 | n19
  | ovf | stk | ms | x19

/-- The exits. -/
inductive PX where
  | ret | abort | stack

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
  | .tls => ⟨lab ".Lwc_printL.chk" + 8, oX, JI c0 rbp0 ra⟩
  | .n2 => ⟨lab ".Lwc_printL.chk" + 17, oX, JI c0 rbp0 ra⟩
  | .n3 => ⟨lab ".Lwc_printL.chk" + 26, oX, JI c0 rbp0 ra⟩
  | .entry => ⟨lab ".Lwc_printL.entry", oI, JI c0 rbp0 ra⟩
  | .mul => ⟨lab ".Lwc_printL.entry" + 11, oI, JI c0 rbp0 ra⟩
  | .n5 => ⟨lab ".Lwc_printL.entry" + 15, oI, JI c0 rbp0 ra⟩
  | .heap => ⟨lab ".Lwc_printL.entry" + 63, oI, JI c0 rbp0 ra⟩
  | .n6 => ⟨lab ".Lwc_printL.entry" + 66, oI, JI c0 rbp0 ra⟩
  | .tp0 => ⟨lab ".Lwc_printL.entry" + 70, oI, JI c0 rbp0 ra⟩
  | .n7 => ⟨lab ".Lwc_printL.entry" + 79, oI, JI c0 rbp0 ra⟩
  | .dld => ⟨lab ".Lwc_printL.entry" + 87, oI, JI c0 rbp0 ra⟩
  | .n8 => ⟨lab ".Lwc_printL.entry" + 91, oI, JI c0 rbp0 ra⟩
  | .n9 => ⟨lab ".Lwc_printL.entry" + 129, oI, JI c0 rbp0 ra⟩
  | .deep9 => ⟨lab ".Lwc_printL.deep9", oI, JI c0 rbp0 ra⟩
  | .call10 => ⟨lab ".Lwc_printL.call10", oI, JI c0 rbp0 ra⟩
  | .dst1 => ⟨lab ".Lwc_printL.call10" + 8, oI, JI c0 rbp0 ra⟩
  | .n12 => ⟨lab ".Lwc_printL.call10" + 12, oI, JI c0 rbp0 ra⟩
  | .call => ⟨lab "wc_emit8", ⟨-152, [(.rbp, 0)]⟩, fun σ c => JI c0 rbp0 ra σ c ∧
      σ.slot (-152) = (lab ".Lwc_printL.call10" + 25).toBitVec⟩
  | .x18 => ⟨lab ".Lwc_printL.x18", oI, JI c0 rbp0 ra⟩
  | .tp1 => ⟨lab ".Lwc_printL.x18" + 4, oI, JI c0 rbp0 ra⟩
  | .n14 => ⟨lab ".Lwc_printL.x18" + 13, oI, JI c0 rbp0 ra⟩
  | .dst2 => ⟨lab ".Lwc_printL.x18" + 25, oI, JI c0 rbp0 ra⟩
  | .n15 => ⟨lab ".Lwc_printL.x18" + 29, oI, JI c0 rbp0 ra⟩
  | .n16 => ⟨lab ".Lwc_printL.x18" + 45, oI, JI c0 rbp0 ra⟩
  | .then12 => ⟨lab ".Lwc_printL.then12", oI, JI c0 rbp0 ra⟩
  | .else13 => ⟨lab ".Lwc_printL.else13", oI, JI c0 rbp0 ra⟩
  | .n19 => ⟨lab ".Lwc_printL.else13" + 43, oI, JI c0 rbp0 ra⟩
  | .ovf => ⟨lab ".Lwc_printL.ovf", oI, JI c0 rbp0 ra⟩
  | .stk => ⟨lab ".Lwc_printL.stk", oX, JI c0 rbp0 ra⟩
  | .ms => ⟨lab "scc_rt_morestack", ⟨-56, [(.rbp, 0)]⟩, fun σ c => JI c0 rbp0 ra σ c ∧
      σ.slot (-56) = (lab ".Lwc_printL.stk" + 18).toBitVec⟩
  | .x19 => ⟨lab ".Lwc_printL.x19", oG, JI c0 rbp0 ra⟩

/-- **The exits.** -/
def E : PX → ND
  | .ret => ⟨Int64.ofBitVec ra, ⟨16, []⟩, fun σ c => c = c0 ∧ σ.regs.get64 .rbp = rbp0⟩
  | .abort => ⟨lab "scc_rt_abort", ⟨-152, []⟩, fun σ c => c = c0 ∧ σ.regs.get64 .rdi = 1⟩
  | .stack => ⟨lab "scc_rt_abort", ⟨-152, []⟩, fun σ c => c = c0 ∧ σ.regs.get64 .rdi = 3⟩

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
  n7 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .n7).pc b7
  n8 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .n8).pc b8
  n9 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .n9).pc b9
  deep9 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .deep9).pc b10
  call10 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .call10).pc b11
  n12 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .n12).pc b12
  x18 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .x18).pc b13
  n14 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .n14).pc b14
  n15 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .n15).pc b15
  n16 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .n16).pc b16
  then12 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .then12).pc b17
  else13 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .else13).pc b18
  n19 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .n19).pc b19
  ovf : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .ovf).pc b20
  stk : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .stk).pc b21
  x19 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .x19).pc b22

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
theorem seg_printL (hF : ∀ g, FStable (Rg g) (Fg g)) (hR : ∀ g, (Rg g).OK) (hlo : ∀ g, (Rg g).lo ≤ -152)
    (hhi : ∀ g, 16 ≤ (Rg g).hi) (hcode : ∀ g, Code c0 (rb g) ra exe endPc)
    (hchk : (_root_.Executable.labels exe).label ".Lwc_printL.chk" =
      (_root_.Executable.labels exe).label "wc_printL" + 4)
    (hentry : (_root_.Executable.labels exe).label ".Lwc_printL.entry" =
      (_root_.Executable.labels exe).label ".Lwc_printL.chk" + 53)
    (htls : ∀ g,
      Seg p lbl ms (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label c0 (rb g) ra .tls))
        (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label c0 (rb g) ra .n2)))
    (hheap : ∀ g,
      Seg p lbl ms (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label c0 (rb g) ra .heap))
        (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label c0 (rb g) ra .n6)))
    (htp0 : ∀ g,
      Seg p lbl ms (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label c0 (rb g) ra .tp0))
        (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label c0 (rb g) ra .n7)))
    (hdld : ∀ g,
      Seg p lbl ms (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label c0 (rb g) ra .dld))
        (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label c0 (rb g) ra .n8)))
    (hdst1 : ∀ g,
      Seg p lbl ms (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label c0 (rb g) ra .dst1))
        (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label c0 (rb g) ra .n12)))
    (htp1 : ∀ g,
      Seg p lbl ms (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label c0 (rb g) ra .tp1))
        (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label c0 (rb g) ra .n14)))
    (hdst2 : ∀ g,
      Seg p lbl ms (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label c0 (rb g) ra .dst2))
        (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label c0 (rb g) ra .n15)))
    (hcall : ∀ g,
      Seg p lbl ms (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label c0 (rb g) ra .call))
        (fun s c => ∃ g', At exe endPc (Rg g') (Fg g') (N (_root_.Executable.labels exe).label c0 (rb g') ra .x18) s c))
    (hms : ∀ g,
      Seg p lbl ms (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label c0 (rb g) ra .ms))
        (fun s c => ∃ g', At exe endPc (Rg g') (Fg g') (N (_root_.Executable.labels exe).label c0 (rb g') ra .x19) s c))
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
  case n6 => node b6 b6_ok n6; rw [N, b6_run]; hit PN.tp0
  case tp0 => exact seg_fix g (seg_given PN.n7 (htp0 g))
  case n7 => node b7 b7_ok n7; rw [N, b7_run]; hit PN.dld
  case dld => exact seg_fix g (seg_given PN.n8 (hdld g))
  case n8 =>
    node b8 b8_ok n8; rw [N, b8_run]
    split
    · hit PN.deep9
    · hit PN.n9
  case n9 => node b9 b9_ok n9; rw [N, b9_run]; hit PN.call10
  case deep9 => node b10 b10_ok deep9; rw [N, b10_run]; exit PX.stack
  case call10 => node b11 b11_ok call10; rw [N, b11_run]; hit PN.dst1
  case dst1 => exact seg_fix g (seg_given PN.n12 (hdst1 g))
  case n12 => node b12 b12_ok n12; rw [N, b12_run]; hit PN.call
  case call => exact seg_moved PN.x18 (hcall g)
  case x18 => node b13 b13_ok x18; rw [N, b13_run]; hit PN.tp1
  case tp1 => exact seg_fix g (seg_given PN.n14 (htp1 g))
  case n14 => node b14 b14_ok n14; rw [N, b14_run]; hit PN.dst2
  case dst2 => exact seg_fix g (seg_given PN.n15 (hdst2 g))
  case n15 =>
    node b15 b15_ok n15; rw [N, b15_run]
    split
    · hit PN.then12
    · hit PN.n16
  case n16 => node b16 b16_ok n16; rw [N, b16_run]; hit PN.else13
  case then12 => node b17 b17_ok then12; rw [N, b17_run]; exit PX.ret
  case else13 =>
    node b18 b18_ok else13; rw [N, b18_run]
    split
    · hit PN.n19
    · hit PN.ovf
  case n19 => node b19 b19_ok n19; rw [N, b19_run]; hit PN.e
  case ovf => node b20 b20_ok ovf; rw [N, b20_run]; exit PX.abort
  case stk => node b21 b21_ok stk; rw [N, b21_run]; hit PN.ms
  case ms => exact seg_moved PN.x19 (hms g)
  case x19 => node b22 b22_ok x19; rw [N, b22_run]; hit PN.chk

end Proof

end Spike.Lib.X64.PrintL
