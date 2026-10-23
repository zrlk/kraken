/-
**The abort stubs on x64**: `scc_rt_abort_overflow` (and its siblings) of
`hello1.w`'s listing (an earlier revision), each as one `Seg`, composed from
its nodes over its control-flow graph (`Spike/Lib/X64Cfg.lean`), in the style
of `Spike/Lib/X64Print.lean`.

Every stub has the same shape, with its own labels (`Stub`), message and
message length. It writes its message to fd 2 and calls `exit_group(101)`:

- `.e`: the prologue (32-byte frame), falling through into `.entry`;
- `.n1`: `leaq msg(%rip), %rax` (`si_nd`);
- `.n2`: the `write` call's arguments (`%rdi = 2`, `%rax = 1`; the length in
  `%rdx` is the stub's own, so this block is a parameter of the generic
  lemma);
- `.sys`: the `write` system call, a given node (`hsys`), as in
  `X64Print`;
- `.n5`: `%rdi = 101`, `%rax = 231`, falling through into the label
  `<stub>_exit`;
- `.ex`: the `exit_group` system call (`exit_nd`, `Spike/Lib/X64Dead.lean`),
  which does not return.

The `ud2` after the exit is dead: no node lands there (the dead tail needs no
node). A stub has **no exit** (`PX` is empty): under the kernel model it is a
segment to any fragment (`seg_stub`, one theorem per stub).

The region is `[-24, 16)` from the frame's base (the generator's): `%rsp` at
offset 8 on entry (a stub is entered by `jmp` from `scc_rt_abort` after its
epilogue, so the return address of the call to `scc_rt_abort` is in
`[8, 16)`). The code, the prologue's fall-through into `.entry` and the label
of the exit call are hypotheses (`Code`).

**The dispatcher** `scc_rt_abort(k)` (`Disp`): `k` (in `%rdi`) is stored in
its frame and tested against 1, …, 5; on a match the frame is popped and the
stub `k` entered by `jmp`, with `%rsp` back at offset 8, so the stub's frame
base is the dispatcher's and one region serves all six. The `ud2` after the
last test is a dead node (`dead_nd`): for `k ∈ [1, 5]` the failed tests leave
no code (`rng_succ`). `seg_disp_fn` is the dispatcher to the stubs' entries,
`seg_disp` composes it with any segments from them, and `seg_abort` with the
five stubs' theorems.

**The tail of `scc_rt_main`** (`MainTail`): from the return of `wc_main`, with
its result `ret` in `%rax`, `exit_group(ret)`; a segment to any fragment
(`seg_main_tail`).
-/
import Spike.Lib.X64Dead
import Kraken.X64.Parser

namespace Spike.Lib.X64.Abort

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower
  Kraken.Promising.Lower.X64 Spike.Lib.X64

/-! ## The shared blocks (generated) -/

def x0 : List (Directive × Nat) := (parse("pushq %rbp
movq %rsp, %rbp
subq $32, %rsp")).zip [1, 3, 4]
def x2 : List (Directive × Nat) := (parse("movq %rax, -16(%rbp)
movq $101, %rdi
movl $231, %eax")).zip [4, 7, 5]

/-- The function's offsets inside the frame. -/
abbrev oI : SO := ⟨-32, [(.rbp, 0)]⟩
/-- The offsets at entry. -/
abbrev oE : SO := ⟨8, []⟩

block_spec x0 (-24) 16 oE x0
block_spec x2 (-24) 16 oI x2

/-! ## The graph -/

/-- **A stub's labels**: the function, its entry, its exit call and its
message. -/
structure Stub where
  fn : Label
  entry : Label
  exit : Label
  msg : Label

/-- The `leaq` of the message. -/
abbrev siMsg (st : Stub) : SI := .leaRip .rax st.msg

example : parse("leaq scc_rt_msg1(%rip), %rax") = [(SI.leaRip .rax "scc_rt_msg1").toDir] := by
  decide

/-- The internal nodes. -/
inductive PN where
  | e | n1 | n2 | sys | n5 | ex

/-- The exits: none. -/
inductive PX : Type

section Spec

variable (lab : Label → Int64) (st : Stub) (c0 : Ctl)

/-- Inside the frame: the source has not moved. -/
def JI (_ : AS) (c : Ctl) : Prop := c = c0

/-- The pc of the `write` system call. -/
abbrev pcSys : Int64 := lab st.entry + 34

/-- **The nodes.** -/
def N : PN → ND
  | .e => ⟨lab st.fn, oE, fun _ c => c = c0⟩
  | .n1 => ⟨lab st.entry, oI, JI c0⟩
  | .n2 => ⟨lab st.entry + 7, oI, JI c0⟩
  | .sys => ⟨pcSys lab st, oI, fun σ c => JI c0 σ c ∧ σ.regs.get64 .rdi = 2 ∧ σ.regs.get64 .rax = 1⟩
  | .n5 => ⟨lab st.entry + 36, oI, JI c0⟩
  | .ex => ⟨lab st.exit, oI, fun σ c => JI c0 σ c ∧ σ.regs.get64 .rax = 231 ∧ σ.regs.get64 .rdi = 101⟩

/-- **The exits**: none. -/
def E : PX → ND := nofun

/-- **The code**: every node's instructions at its pc (`x1` is the stub's
argument block), the prologue's fall-through into the entry label and the
label of the exit call. -/
structure Code (x1 : List (Directive × Nat)) (exe : _root_.Executable) (endPc : Int64) : Prop where
  e : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label st c0 .e).pc x0
  n1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label st c0 .n1).pc [((siMsg st).toDir, 7)]
  n2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label st c0 .n2).pc x1
  n5 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label st c0 .n5).pc x2
  ex : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label st c0 .ex).pc [(op64 .syscall, 2)]
  hentry : (_root_.Executable.labels exe).label st.entry =
    (_root_.Executable.labels exe).label st.fn + 8
  hexit : (_root_.Executable.labels exe).label st.exit =
    (_root_.Executable.labels exe).label st.entry + 52
  /-- The `write` system call at `.sys` (a given node of the proof, so
  unused by it; its consumers read the instruction there). -/
  sys : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label st c0 .sys).pc [(op64 .syscall, 2)]

end Spec

/-! ## The generic proof -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {m0 : MachineData} {c0 : Ctl}

/-- Hitting node `j`. -/
macro "hit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;>
    simp_all [N, JI, Int64.add_assoc, upd_apply, Reg64s.get64_set64_self, Reg64s.get64_set64_ne]))

/-- **An abort stub does not return**: from its entry it is a segment to any
fragment, given its argument block `x1` (which lands at the system call)
and the `write` call (`hsys`). -/
theorem seg_stub {Q : Frag isa} (st : Stub) {x1 : List (Directive × Nat)} (hne1 : x1 ≠ [])
    (hok1 : okBlk (-24) 16 oI x1 = true)
    (h1 : ∀ σ c, JI c0 σ c → Hit (N (_root_.Executable.labels exe).label st c0 .sys)
      (arun (_root_.Executable.labels exe).label x1
        ⟨(N (_root_.Executable.labels exe).label st c0 .n2).pc, oI, σ⟩) c)
    (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hcode : Code st c0 x1 exe endPc) (hK : ms.K = some Scc.Sem.X64.abi)
    (hsys : Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label st c0 .sys))
      (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label st c0 .n5)))
    (hab : ∀ s c, At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label st c0 .ex) s c →
      ms.abortAt s) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label st c0 .e)) Q := by
  refine (fn_seg (N := N _ st c0) (E := E) (fun i => ?_) PN.e).mono_post fun _ _ ⟨x, _⟩ => nomatch x
  have hentry := hcode.hentry
  have hexit := hcode.hexit
  cases i
  case e =>
    refine seg_nd (by simp [x0]) x0_ok (FStable.dframe R m0) hR hlo hhi (fun s he hn => hcode.e s he hn)
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    rw [N, x0_run]; hit PN.n1
  case n1 =>
    refine si_nd (si := siMsg st) rfl (FStable.dframe R m0) (fun s he hn => hcode.n1 s he hn)
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    hit PN.n2
  case n2 =>
    exact seg_nd hne1 hok1 (FStable.dframe R m0) hR hlo hhi (fun s he hn => hcode.n2 s he hn)
      fun σ c hJ => ⟨c, .refl c, .inl ⟨PN.sys, h1 σ c hJ⟩⟩
  case sys => exact seg_given PN.n5 hsys
  case n5 =>
    refine seg_nd (by simp [x2]) x2_ok (FStable.dframe R m0) hR hlo hhi (fun s he hn => hcode.n5 s he hn)
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    rw [N, x2_run]; hit PN.ex
  case ex =>
    refine exit_nd hK (fun s he hn => hcode.ex s he hn) (fun σ c hJ => ?_)
      fun s c _ hAt _ => SysOk.exitGroup_abort (hab s c hAt)
    have h := hJ.2.1
    simp only [Reg64s.get64] at h
    show σ.regs.rax.toBitVec.toNat = 231
    rw [h]; rfl

end Proof

/-! ## The stubs -/

/-- The argument block: the stub's own, and its landing at the system
call. -/
macro "arg_hit" run:ident : tactic =>
  `(tactic| (intro σ c hJ; rw [N, $run:ident]; refine ⟨?_, rfl, ?_⟩ <;>
    simp_all [N, JI, Int64.add_assoc, upd_apply, Reg64s.get64_set64_self, Reg64s.get64_set64_ne]))

section Stubs

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {m0 : MachineData} {c0 : Ctl} {Q : Frag isa}

/-! ### `scc_rt_abort_overflow` -/

def overflow : Stub :=
  ⟨"scc_rt_abort_overflow", ".Lscc_rt_abort_overflow.entry", "scc_rt_abort_overflow_exit", "scc_rt_msg1"⟩

def x1Overflow : List (Directive × Nat) := (parse("movq %rax, -8(%rbp)
movq $2, %rdi
movq -8(%rbp), %rsi
movq $34, %rdx
movl $1, %eax")).zip [4, 7, 4, 7, 5]

block_spec x1Overflow (-24) 16 oI x1Overflow

/-- **`scc_rt_abort_overflow` does not return.** -/
theorem seg_overflow (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hcode : Code overflow c0 x1Overflow exe endPc) (hK : ms.K = some Scc.Sem.X64.abi)
    (hsys : Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label overflow c0 .sys))
      (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label overflow c0 .n5)))
    (hab : ∀ s c, At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label overflow c0 .ex) s c →
      ms.abortAt s) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label overflow c0 .e)) Q :=
  seg_stub overflow (by simp [x1Overflow]) x1Overflow_ok (by arg_hit x1Overflow_run)
    hR hlo hhi hcode hK hsys hab

/-! ### `scc_rt_abort_heap` -/

def heap : Stub :=
  ⟨"scc_rt_abort_heap", ".Lscc_rt_abort_heap.entry", "scc_rt_abort_heap_exit", "scc_rt_msg2"⟩

def x1Heap : List (Directive × Nat) := (parse("movq %rax, -8(%rbp)
movq $2, %rdi
movq -8(%rbp), %rsi
movq $35, %rdx
movl $1, %eax")).zip [4, 7, 4, 7, 5]

block_spec x1Heap (-24) 16 oI x1Heap

/-- **`scc_rt_abort_heap` does not return.** -/
theorem seg_heap (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hcode : Code heap c0 x1Heap exe endPc) (hK : ms.K = some Scc.Sem.X64.abi)
    (hsys : Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label heap c0 .sys))
      (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label heap c0 .n5)))
    (hab : ∀ s c, At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label heap c0 .ex) s c →
      ms.abortAt s) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label heap c0 .e)) Q :=
  seg_stub heap (by simp [x1Heap]) x1Heap_ok (by arg_hit x1Heap_run)
    hR hlo hhi hcode hK hsys hab

/-! ### `scc_rt_abort_stack` -/

def stack : Stub :=
  ⟨"scc_rt_abort_stack", ".Lscc_rt_abort_stack.entry", "scc_rt_abort_stack_exit", "scc_rt_msg3"⟩

def x1Stack : List (Directive × Nat) := (parse("movq %rax, -8(%rbp)
movq $2, %rdi
movq -8(%rbp), %rsi
movq $25, %rdx
movl $1, %eax")).zip [4, 7, 4, 7, 5]

block_spec x1Stack (-24) 16 oI x1Stack

/-- **`scc_rt_abort_stack` does not return.** -/
theorem seg_stack (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hcode : Code stack c0 x1Stack exe endPc) (hK : ms.K = some Scc.Sem.X64.abi)
    (hsys : Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label stack c0 .sys))
      (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label stack c0 .n5)))
    (hab : ∀ s c, At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label stack c0 .ex) s c →
      ms.abortAt s) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label stack c0 .e)) Q :=
  seg_stub stack (by simp [x1Stack]) x1Stack_ok (by arg_hit x1Stack_run)
    hR hlo hhi hcode hK hsys hab

/-! ### `scc_rt_abort_write` -/

def write : Stub :=
  ⟨"scc_rt_abort_write", ".Lscc_rt_abort_write.entry", "scc_rt_abort_write_exit", "scc_rt_msg4"⟩

def x1Write : List (Directive × Nat) := (parse("movq %rax, -8(%rbp)
movq $2, %rdi
movq -8(%rbp), %rsi
movq $44, %rdx
movl $1, %eax")).zip [4, 7, 4, 7, 5]

block_spec x1Write (-24) 16 oI x1Write

/-- **`scc_rt_abort_write` does not return.** -/
theorem seg_write (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hcode : Code write c0 x1Write exe endPc) (hK : ms.K = some Scc.Sem.X64.abi)
    (hsys : Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label write c0 .sys))
      (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label write c0 .n5)))
    (hab : ∀ s c, At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label write c0 .ex) s c →
      ms.abortAt s) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label write c0 .e)) Q :=
  seg_stub write (by simp [x1Write]) x1Write_ok (by arg_hit x1Write_run)
    hR hlo hhi hcode hK hsys hab

/-! ### `scc_rt_abort_threads` -/

def threads : Stub :=
  ⟨"scc_rt_abort_threads", ".Lscc_rt_abort_threads.entry", "scc_rt_abort_threads_exit", "scc_rt_msg5"⟩

def x1Threads : List (Directive × Nat) := (parse("movq %rax, -8(%rbp)
movq $2, %rdi
movq -8(%rbp), %rsi
movq $35, %rdx
movl $1, %eax")).zip [4, 7, 4, 7, 5]

block_spec x1Threads (-24) 16 oI x1Threads

/-- **`scc_rt_abort_threads` does not return.** -/
theorem seg_threads (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hcode : Code threads c0 x1Threads exe endPc) (hK : ms.K = some Scc.Sem.X64.abi)
    (hsys : Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label threads c0 .sys))
      (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label threads c0 .n5)))
    (hab : ∀ s c, At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label threads c0 .ex) s c →
      ms.abortAt s) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label threads c0 .e)) Q :=
  seg_stub threads (by simp [x1Threads]) x1Threads_ok (by arg_hit x1Threads_run)
    hR hlo hhi hcode hK hsys hab

end Stubs

/-! ## The dispatcher `scc_rt_abort` -/

namespace Disp

/-! `scc_rt_abort(k)` (`%rdi = k`): k is stored at `-8(%rbp)` and compared
against 1, …, 5; on a match the frame is popped and the stub `k` entered by
`jmp` with `%rsp` back at offset 8 (the stub's frame base is the
dispatcher's); otherwise `ud2`, dead for `k ∈ [1, 5]`. -/

def d0 : List (Directive × Nat) := (parse("pushq %rbp
movq %rsp, %rbp
subq $16, %rsp
movq %rdi, -8(%rbp)")).zip [1, 3, 4, 4]
def t1 : List (Directive × Nat) := (parse("movq -8(%rbp), %rax
movq $1, %rcx
cmpq %rcx, %rax
je .Lscc_rt_abort.is0")).zip [4, 7, 3, 2]
def j1 : List (Directive × Nat) := (parse("jmp .Lscc_rt_abort.next1")).zip [2]
def g1 : List (Directive × Nat) := (parse("movq %rbp, %rsp
popq %rbp
jmp scc_rt_abort_overflow")).zip [3, 1, 2]
def t2 : List (Directive × Nat) := (parse("movq -8(%rbp), %rax
movq $2, %rcx
cmpq %rcx, %rax
je .Lscc_rt_abort.is2")).zip [4, 7, 3, 2]
def j2 : List (Directive × Nat) := (parse("jmp .Lscc_rt_abort.next3")).zip [2]
def g2 : List (Directive × Nat) := (parse("movq %rbp, %rsp
popq %rbp
jmp scc_rt_abort_heap")).zip [3, 1, 5]
def t3 : List (Directive × Nat) := (parse("movq -8(%rbp), %rax
movq $3, %rcx
cmpq %rcx, %rax
je .Lscc_rt_abort.is4")).zip [4, 7, 3, 2]
def j3 : List (Directive × Nat) := (parse("jmp .Lscc_rt_abort.next5")).zip [2]
def g3 : List (Directive × Nat) := (parse("movq %rbp, %rsp
popq %rbp
jmp scc_rt_abort_stack")).zip [3, 1, 5]
def t4 : List (Directive × Nat) := (parse("movq -8(%rbp), %rax
movq $4, %rcx
cmpq %rcx, %rax
je .Lscc_rt_abort.is6")).zip [4, 7, 3, 2]
def j4 : List (Directive × Nat) := (parse("jmp .Lscc_rt_abort.next7")).zip [2]
def g4 : List (Directive × Nat) := (parse("movq %rbp, %rsp
popq %rbp
jmp scc_rt_abort_write")).zip [3, 1, 5]
def t5 : List (Directive × Nat) := (parse("movq -8(%rbp), %rax
movq $5, %rcx
cmpq %rcx, %rax
je .Lscc_rt_abort.is8")).zip [4, 7, 3, 2]
def j5 : List (Directive × Nat) := (parse("jmp .Lscc_rt_abort.next9")).zip [2]
def g5 : List (Directive × Nat) := (parse("movq %rbp, %rsp
popq %rbp
jmp scc_rt_abort_threads")).zip [3, 1, 5]

/-- The dispatcher's offsets inside its frame. -/
abbrev oD : SO := ⟨-16, [(.rbp, 0)]⟩

block_spec d0 (-8) 16 oE d0
block_spec t1 (-8) 16 oD t1
block_spec j1 (-8) 16 oD j1
block_spec g1 (-8) 16 oD g1
block_spec t2 (-8) 16 oD t2
block_spec j2 (-8) 16 oD j2
block_spec g2 (-8) 16 oD g2
block_spec t3 (-8) 16 oD t3
block_spec j3 (-8) 16 oD j3
block_spec g3 (-8) 16 oD g3
block_spec t4 (-8) 16 oD t4
block_spec j4 (-8) 16 oD j4
block_spec g4 (-8) 16 oD g4
block_spec t5 (-8) 16 oD t5
block_spec j5 (-8) 16 oD j5
block_spec g5 (-8) 16 oD g5

/-- The internal nodes: the entry, the tests `t`, the jumps to the next test
`j`, the jumps to the stubs `g`, and the dead `ud2`. -/
inductive DN where
  | e | t1 | j1 | g1 | t2 | j2 | g2 | t3 | j3 | g3 | t4 | j4 | g4 | t5 | j5 | g5 | dead

/-- The exits: the five stubs. -/
inductive DX where
  | overflow | heap | stack | write | threads

/-- The stub of an exit. -/
def DX.stub : DX → Stub
  | .overflow => Abort.overflow
  | .heap => Abort.heap
  | .stack => Abort.stack
  | .write => Abort.write
  | .threads => Abort.threads

section Spec

variable (lab : Label → Int64) (c0 : Ctl)

/-- The code `v` is in `[k, 5]`. -/
def Rng (k : Nat) (v : BitVec 64) : Prop := k ≤ v.toNat ∧ v.toNat ≤ 5

/-- Inside the frame, before the test against `k`: the source has not moved,
the stored code is in `[k, 5]`. -/
def JT (k : Nat) (σ : AS) (c : Ctl) : Prop := c = c0 ∧ Rng k (σ.slot (-8))

/-- A failed test against `k`: the code is in `[k + 1, 5]`. -/
theorem rng_succ {k : Nat} {v : BitVec 64} (h : Rng k v) (hne : ¬ v - BitVec.ofNat 64 k = 0#64) :
    Rng (k + 1) v := by
  have hk : v.toNat ≠ k := fun e => hne (by
    have : v = BitVec.ofNat 64 k := BitVec.eq_of_toNat_eq (by simp [e]; unfold Rng at h; omega)
    simp [this])
  unfold Rng at h ⊢; omega

/-- **The nodes.** -/
def DN.nd : DN → ND
  | .e => ⟨lab "scc_rt_abort", oE, fun σ c => c = c0 ∧ Rng 1 (σ.regs.get64 .rdi)⟩
  | .t1 => ⟨lab ".Lscc_rt_abort.entry", oD, JT c0 1⟩
  | .j1 => ⟨lab ".Lscc_rt_abort.entry" + 16, oD, JT c0 2⟩
  | .g1 => ⟨lab ".Lscc_rt_abort.is0", oD, fun _ c => c = c0⟩
  | .t2 => ⟨lab ".Lscc_rt_abort.next1", oD, JT c0 2⟩
  | .j2 => ⟨lab ".Lscc_rt_abort.next1" + 16, oD, JT c0 3⟩
  | .g2 => ⟨lab ".Lscc_rt_abort.is2", oD, fun _ c => c = c0⟩
  | .t3 => ⟨lab ".Lscc_rt_abort.next3", oD, JT c0 3⟩
  | .j3 => ⟨lab ".Lscc_rt_abort.next3" + 16, oD, JT c0 4⟩
  | .g3 => ⟨lab ".Lscc_rt_abort.is4", oD, fun _ c => c = c0⟩
  | .t4 => ⟨lab ".Lscc_rt_abort.next5", oD, JT c0 4⟩
  | .j4 => ⟨lab ".Lscc_rt_abort.next5" + 16, oD, JT c0 5⟩
  | .g4 => ⟨lab ".Lscc_rt_abort.is6", oD, fun _ c => c = c0⟩
  | .t5 => ⟨lab ".Lscc_rt_abort.next7", oD, JT c0 5⟩
  | .j5 => ⟨lab ".Lscc_rt_abort.next7" + 16, oD, JT c0 6⟩
  | .g5 => ⟨lab ".Lscc_rt_abort.is8", oD, fun _ c => c = c0⟩
  | .dead => ⟨lab ".Lscc_rt_abort.next9", oD, fun _ _ => False⟩

/-- **The exits**: the stubs' entries. -/
def DX.nd (x : DX) : ND := Abort.N lab x.stub c0 .e

/-- **The code** and the prologue's fall-through into `.entry`. -/
structure Code (exe : _root_.Executable) (endPc : Int64) : Prop where
  e : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (DN.nd (_root_.Executable.labels exe).label c0 .e).pc d0
  t1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (DN.nd (_root_.Executable.labels exe).label c0 .t1).pc t1
  j1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (DN.nd (_root_.Executable.labels exe).label c0 .j1).pc j1
  g1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (DN.nd (_root_.Executable.labels exe).label c0 .g1).pc g1
  t2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (DN.nd (_root_.Executable.labels exe).label c0 .t2).pc t2
  j2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (DN.nd (_root_.Executable.labels exe).label c0 .j2).pc j2
  g2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (DN.nd (_root_.Executable.labels exe).label c0 .g2).pc g2
  t3 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (DN.nd (_root_.Executable.labels exe).label c0 .t3).pc t3
  j3 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (DN.nd (_root_.Executable.labels exe).label c0 .j3).pc j3
  g3 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (DN.nd (_root_.Executable.labels exe).label c0 .g3).pc g3
  t4 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (DN.nd (_root_.Executable.labels exe).label c0 .t4).pc t4
  j4 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (DN.nd (_root_.Executable.labels exe).label c0 .j4).pc j4
  g4 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (DN.nd (_root_.Executable.labels exe).label c0 .g4).pc g4
  t5 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (DN.nd (_root_.Executable.labels exe).label c0 .t5).pc t5
  j5 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (DN.nd (_root_.Executable.labels exe).label c0 .j5).pc j5
  g5 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (DN.nd (_root_.Executable.labels exe).label c0 .g5).pc g5
  hentry : (_root_.Executable.labels exe).label ".Lscc_rt_abort.entry" =
    (_root_.Executable.labels exe).label "scc_rt_abort" + 12

end Spec

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {m0 : MachineData} {c0 : Ctl}

set_option hygiene false in
/-- A block node: the block, its `okBlk`, its code; the edge is left. -/
macro "dnode " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine seg_nd (by simp [$b:ident]) $ok (FStable.dframe R m0) hR (by omega) hhi
    (fun s he hn => hcode.$f s he hn) fun σ c hJ => ⟨c, .refl c, ?_⟩)

/-- Hitting node `j`. -/
macro "dhit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;>
    simp_all [DN.nd, JT, Rng, Int64.add_assoc, upd_apply, Reg64s.get64_set64_self, Reg64s.get64_set64_ne]))

/-- Hitting exit `x`. -/
macro "dexit " x:term : tactic =>
  `(tactic| (refine .inr ⟨$x, ?_, rfl, ?_⟩ <;>
    simp_all [DN.nd, DX.nd, DX.stub, Abort.N, Abort.overflow, Abort.heap, Abort.stack, Abort.write,
      Abort.threads]))

/-- **`scc_rt_abort` is one segment** from its entry (with a code in
`[1, 5]`) to the entries of the five stubs. -/
theorem seg_disp_fn (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi) (hcode : Code c0 exe endPc) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (DN.nd (_root_.Executable.labels exe).label c0 .e))
      (fun s c => ∃ x, At exe endPc R (DFrame R m0) (DX.nd (_root_.Executable.labels exe).label c0 x) s c) := by
  refine fn_seg (N := DN.nd _ c0) (E := DX.nd _ c0) (fun i => ?_) DN.e
  have hentry := hcode.hentry
  cases i
  case e => dnode d0 d0_ok e; rw [DN.nd, d0_run]; dhit DN.t1
  case t1 =>
    dnode t1 t1_ok t1; rw [DN.nd, t1_run]
    split
    · dhit DN.g1
    · next h => exact .inl ⟨DN.j1, by simp [DN.nd], rfl, hJ.1, rng_succ hJ.2 h⟩
  case j1 => dnode j1 j1_ok j1; rw [DN.nd, j1_run]; dhit DN.t2
  case g1 => dnode g1 g1_ok g1; rw [DN.nd, g1_run]; dexit DX.overflow
  case t2 =>
    dnode t2 t2_ok t2; rw [DN.nd, t2_run]
    split
    · dhit DN.g2
    · next h => exact .inl ⟨DN.j2, by simp [DN.nd], rfl, hJ.1, rng_succ hJ.2 h⟩
  case j2 => dnode j2 j2_ok j2; rw [DN.nd, j2_run]; dhit DN.t3
  case g2 => dnode g2 g2_ok g2; rw [DN.nd, g2_run]; dexit DX.heap
  case t3 =>
    dnode t3 t3_ok t3; rw [DN.nd, t3_run]
    split
    · dhit DN.g3
    · next h => exact .inl ⟨DN.j3, by simp [DN.nd], rfl, hJ.1, rng_succ hJ.2 h⟩
  case j3 => dnode j3 j3_ok j3; rw [DN.nd, j3_run]; dhit DN.t4
  case g3 => dnode g3 g3_ok g3; rw [DN.nd, g3_run]; dexit DX.stack
  case t4 =>
    dnode t4 t4_ok t4; rw [DN.nd, t4_run]
    split
    · dhit DN.g4
    · next h => exact .inl ⟨DN.j4, by simp [DN.nd], rfl, hJ.1, rng_succ hJ.2 h⟩
  case j4 => dnode j4 j4_ok j4; rw [DN.nd, j4_run]; dhit DN.t5
  case g4 => dnode g4 g4_ok g4; rw [DN.nd, g4_run]; dexit DX.write
  case t5 =>
    dnode t5 t5_ok t5; rw [DN.nd, t5_run]
    split
    · dhit DN.g5
    · next h => exact .inl ⟨DN.j5, by simp [DN.nd], rfl, hJ.1, rng_succ hJ.2 h⟩
  case j5 => dnode j5 j5_ok j5; rw [DN.nd, j5_run]; exact absurd hJ.2 (by unfold Rng; omega)
  case g5 => dnode g5 g5_ok g5; rw [DN.nd, g5_run]; dexit DX.threads
  case dead => exact dead_nd fun _ _ h => h

/-- **`scc_rt_abort` does not return**: from its entry (with a code in
`[1, 5]`) it is a segment to any fragment the five stubs are segments to. -/
theorem seg_disp {Q : Frag isa} (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi) (hcode : Code c0 exe endPc)
    (hs : ∀ x, Seg p lbl ms (At exe endPc R (DFrame R m0) (DX.nd (_root_.Executable.labels exe).label c0 x)) Q) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (DN.nd (_root_.Executable.labels exe).label c0 .e)) Q :=
  (seg_disp_fn hR hlo hhi hcode).seq <| Seg.cfg (fun x => At exe endPc R (DFrame R m0) (DX.nd _ c0 x))
    fun x => (hs x).mono_post fun _ _ h => .inr h

/-- A stub's argument block. -/
def DX.x1 : DX → List (Directive × Nat)
  | .overflow => x1Overflow
  | .heap => x1Heap
  | .stack => x1Stack
  | .write => x1Write
  | .threads => x1Threads

/-- **`scc_rt_abort` does not return**, composed with the five stubs: from its
entry (with a code in `[1, 5]`) it is a segment to any fragment, given the
code of the dispatcher and the stubs and the stubs' `write` calls. -/
theorem seg_abort {Q : Frag isa} (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi) (hcode : Code c0 exe endPc)
    (hK : ms.K = some Scc.Sem.X64.abi) (hc : ∀ x : DX, Abort.Code x.stub c0 x.x1 exe endPc)
    (hsys : ∀ x : DX,
      Seg p lbl ms (At exe endPc R (DFrame R m0) (Abort.N (_root_.Executable.labels exe).label x.stub c0 .sys))
        (At exe endPc R (DFrame R m0) (Abort.N (_root_.Executable.labels exe).label x.stub c0 .n5)))
    (hab : ∀ (x : DX) s c,
      At exe endPc R (DFrame R m0) (Abort.N (_root_.Executable.labels exe).label x.stub c0 .ex) s c → ms.abortAt s) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (DN.nd (_root_.Executable.labels exe).label c0 .e)) Q :=
  seg_disp hR hlo hhi hcode fun x => by
    cases x
    · exact seg_overflow hR hlo hhi (hc .overflow) hK (hsys .overflow) (hab .overflow)
    · exact seg_heap hR hlo hhi (hc .heap) hK (hsys .heap) (hab .heap)
    · exact seg_stack hR hlo hhi (hc .stack) hK (hsys .stack) (hab .stack)
    · exact seg_write hR hlo hhi (hc .write) hK (hsys .write) (hab .write)
    · exact seg_threads hR hlo hhi (hc .threads) hK (hsys .threads) (hab .threads)

end Proof

end Disp

/-! ## The tail of `scc_rt_main` -/

namespace MainTail

/-! After `wc_main` returns (`.Lscc_rt_main.x3`, its result `ret` in `%rax`),
`scc_rt_main` stores it, calls `exit_group(ret)` and ends in a dead `ud2`.
The rest of `scc_rt_main` (the stack check and the calls) is left to the
call composition. -/

def m0 : List (Directive × Nat) := (parse("movq %rax, -48(%rbp)
movq -48(%rbp), %rdi
movl $231, %eax")).zip [4, 4, 5]

/-- The offsets in `scc_rt_main`'s frame after the calls (the generator's). -/
abbrev oM : SO := ⟨-64, [(.rbp, 0)]⟩

block_spec m0 (-72) 16 oM m0

/-- The nodes: the tail block and the `exit_group` call. -/
inductive MN where
  | x3 | ex

section Spec

variable (lab : Label → Int64) (c0 : Ctl) (ret : BitVec 64)

/-- **The nodes**: `ret` in `%rax`, then `exit_group(ret)`. -/
def MN.nd : MN → ND
  | .x3 => ⟨lab ".Lscc_rt_main.x3", oM, fun σ c => c = c0 ∧ σ.regs.get64 .rax = ret⟩
  | .ex => ⟨lab ".Lscc_rt_main.x3" + 13, oM,
      fun σ c => c = c0 ∧ σ.regs.get64 .rax = 231 ∧ σ.regs.get64 .rdi = ret⟩

/-- **The code.** -/
structure Code (exe : _root_.Executable) (endPc : Int64) : Prop where
  x3 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (MN.nd (_root_.Executable.labels exe).label c0 ret .x3).pc m0
  ex : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (MN.nd (_root_.Executable.labels exe).label c0 ret .ex).pc [(op64 .syscall, 2)]

end Spec

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {mi : MachineData} {c0 : Ctl} {ret : BitVec 64}

/-- **The tail of `scc_rt_main` does not return**: from `.x3` with `ret` in
`%rax` it is a segment to any fragment (through `exit_group(ret)`). -/
theorem seg_main_tail {Q : Frag isa} (hR : R.OK) (hlo : R.lo ≤ -72) (hhi : 16 ≤ R.hi)
    (hcode : Code c0 ret exe endPc) (hK : ms.K = some Scc.Sem.X64.abi)
    (hmain : ∀ s c, At exe endPc R (DFrame R mi) (MN.nd (_root_.Executable.labels exe).label c0 ret .ex) s c →
      ¬ ms.abortAt s → MainExit p ms s c ret.toNat) :
    Seg p lbl ms (At exe endPc R (DFrame R mi) (MN.nd (_root_.Executable.labels exe).label c0 ret .x3)) Q := by
  refine (fn_seg (N := MN.nd _ c0 ret) (E := (nofun : PX → ND)) (fun i => ?_) MN.x3).mono_post
    fun _ _ ⟨x, _⟩ => nomatch x
  cases i
  case x3 =>
    refine seg_nd (by simp [m0]) m0_ok (FStable.dframe R mi) hR hlo hhi (fun s he hn => hcode.x3 s he hn)
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    rw [MN.nd, m0_run]
    refine .inl ⟨MN.ex, ?_, rfl, ?_⟩ <;> simp_all [MN.nd]
  case ex =>
    refine exit_nd hK (fun s he hn => hcode.ex s he hn) (fun σ c hJ => ?_) fun s c σ hAt hJ => ?_
    · have h := hJ.2.1
      simp only [Reg64s.get64] at h
      show σ.regs.rax.toBitVec.toNat = 231
      rw [h]; rfl
    refine SysOk.exitGroup_main ?_
    have h : σ.regs.rdi.toNat = ret.toNat := by have h := hJ.2.2; simp only [Reg64s.get64] at h; rw [← h]; rfl
    rw [h]; exact hmain s c hAt

end MainTail

end Spike.Lib.X64.Abort
