/-
**The abort stubs on AArch64**: `scc_rt_abort_overflow` (and its siblings)
of `hello1.w`'s listing (an earlier revision), each as one `Seg`, composed
from its nodes over its control-flow graph (`Spike/Lib/A64Cfg.lean`): the
AArch64 twin of `Spike/Lib/X64Abort.lean`.

Every stub has the same shape, with its own labels (`Stub`), message and
message length:

- `.e`: the prologue (48-byte frame, `x29`/`x30` saved at 32/40), falling
  through into `.0_entry`;
- `.n1`, `.n1b`: `adrp x9, msg; add x9, x9, :lo12:msg` (`si_nd`);
- `.n2`: the `write` call's arguments (`x0 = 2`, `x8 = 64`; the length in
  `x2` is the stub's own, so this block is a parameter of the generic lemma);
- `.svc`: the `write` system call, a given node (`hsvc`);
- `.n5`: `x0 = 101`, `x8 = 94`, falling through into the label
  `<stub>_exit`;
- `.ex`: the `exit_group` system call (`exit_nd`, `Spike/Lib/A64Dead.lean`),
  which does not return.

The tail after the exit (a store and the `b .` halt loop) is dead: no node
lands there. A stub has **no exit** (`PX` is empty): under the kernel model
it is a segment to any fragment (`seg_stub`, one theorem per stub).

The region is the frame, `[-48, 0)` from the `sp` at entry (the generator's).
The code, the prologue's fall-through into `.0_entry` and the label of the
exit call are hypotheses (`Code`, fields `hentry` and `hexit`).

**The dispatcher** `scc_rt_abort(k)` (`Disp`): `k` (in `x0`) is stored in its
frame and tested against 1, …, 5; on a match the frame is popped and the stub
`k` entered by `b`, with `sp` back at its entry value, so the stub's frame
base is the dispatcher's and one region serves all six. The halt loop after
the last test is a dead node (`dead_nd`): for `k ∈ [1, 5]` the failed tests
leave no code (`rng_succ`). `seg_disp_fn` is the dispatcher to the stubs'
entries, `seg_disp` composes it with any segments from them, and `seg_abort`
with the five stubs' theorems.

**The tail of `scc_rt_main`** (`MainTail`): from the return of `wc_main`, with
its result `ret` in `x0`, `exit_group(ret)`; a segment to any fragment
(`seg_main_tail`). Its shape depends on `main`'s argument: `MainTail` is
the one after a setup block (`rodata`'s four result words: the 80-byte
frame, `.sp1`), `MainTail0` the one without (`main(u : Unit)` or a
`ThreadId`: the 48-byte frame, `.sp0`).
-/
import Spike.Lib.A64Dead
import Kraken.AArch64.Parser

namespace Spike.Lib.A64.Abort

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64.Flow

/-! ## The shared blocks (generated) -/

def b0 : List Directive := parseAArch64("sub sp, sp, #48
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32")
def b2 : List Directive := parseAArch64("str x0, [sp, #8]
movz x0, #101
movz x8, #94")

/-- The function's offsets inside the frame. -/
abbrev oI : SO := ⟨-48, []⟩
/-- The offsets at entry. -/
abbrev oE : SO := ⟨0, []⟩

block_spec b0 (-48) 0 oE b0
block_spec b2 (-48) 0 oI b2

/-! ## The graph -/

/-- **A stub's labels**: the function, its entry, its exit call and its
message. -/
structure Stub where
  fn : Label
  entry : Label
  exit : Label
  msg : Label

/-- The internal nodes. -/
inductive PN where
  | e | n1 | n1b | n2 | svc | n5 | ex

/-- The exits: none. -/
inductive PX : Type

section Spec

variable (lab : Label → Int64) (st : Stub) (c0 : Ctl)

/-- Inside the frame: the source has not moved. -/
def JI (_ : AS) (c : Ctl) : Prop := c = c0

/-- The pc of the `write` system call. -/
abbrev pcSvc : Int64 := lab st.entry + 4 + 4 + 4 + 4 + 4 + 4 + 4

/-- **The nodes.** -/
def N : PN → ND
  | .e => ⟨lab st.fn, oE, fun _ c => c = c0⟩
  | .n1 => ⟨lab st.entry, oI, JI c0⟩
  | .n1b => ⟨lab st.entry + 4, oI, JI c0⟩
  | .n2 => ⟨lab st.entry + 4 + 4, oI, JI c0⟩
  | .svc => ⟨pcSvc lab st, oI, fun σ c => JI c0 σ c ∧ σ.regs.X0 = 2 ∧ σ.regs.X8 = 64⟩
  | .n5 => ⟨pcSvc lab st + 4, oI, JI c0⟩
  | .ex => ⟨lab st.exit, oI, fun σ c => JI c0 σ c ∧ σ.regs.X8 = 94 ∧ σ.regs.X0 = 101⟩

/-- **The exits**: none. -/
def E : PX → ND := nofun

/-- **The code**: every node's instructions at its pc (`b1` is the stub's
argument block), the prologue's fall-through into the entry label and the
label of the exit call. -/
structure Code (b1 : List Directive) (exe : _root_.Executable) (endPc : Int64) : Prop where
  e : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label st c0 .e).pc b0
  n1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label st c0 .n1).pc [(SI.adrp .X9 st.msg).toDir]
  n1b : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label st c0 .n1b).pc [(SI.addLo12 .X9 .X9 st.msg).toDir]
  n2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label st c0 .n2).pc b1
  n5 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label st c0 .n5).pc b2
  ex : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label st c0 .ex).pc [svcDir]
  hentry : (_root_.Executable.labels exe).label st.entry =
    (_root_.Executable.labels exe).label st.fn + 4 + 4 + 4 + 4
  hexit : (_root_.Executable.labels exe).label st.exit =
    pcSvc (_root_.Executable.labels exe).label st + 4 + 4 + 4 + 4
  /-- The `write` system call at `.svc` (a given node of the proof, so
  unused by it; its consumers read the instruction there). -/
  svc : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label st c0 .svc).pc [svcDir]

end Spec

/-! ## The generic proof -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {m0 : MachineData} {c0 : Ctl}

/-- Hitting node `j`. -/
macro "hit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;> simp_all [N, JI, upd_apply]))

/-- **An abort stub does not return**: from its entry it is a segment to any
fragment, given its argument block `b1` (which lands at the system call)
and the `write` call (`hsvc`). -/
theorem seg_stub {Q : Frag isaLSE2} (st : Stub) {b1 : List Directive} (hne1 : b1 ≠ [])
    (hok1 : okBlk (-48) 0 oI b1 = true)
    (h1 : ∀ σ c, JI c0 σ c → Hit (N (_root_.Executable.labels exe).label st c0 .svc)
      (arun (_root_.Executable.labels exe).label b1
        ⟨(N (_root_.Executable.labels exe).label st c0 .n2).pc, oI, σ⟩) c)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hcode : Code st c0 b1 exe endPc) (hK : ms.K = some Scc.Sem.A64.abi)
    (hsvc : Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label st c0 .svc))
      (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label st c0 .n5)))
    (hab : ∀ s c, At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label st c0 .ex) s c →
      ms.abortAt s) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label st c0 .e)) Q := by
  refine (fn_seg (N := N _ st c0) (E := E) (fun i => ?_) PN.e).mono_post fun _ _ ⟨x, _⟩ => nomatch x
  have hentry := hcode.hentry
  have hexit := hcode.hexit
  cases i
  case e =>
    refine seg_nd (by simp [b0]) b0_ok (FStable.dframe R m0) hR hal hlo hhi (fun s he hn => hcode.e s he hn)
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    rw [N, b0_run]; hit PN.n1
  case n1 =>
    refine si_nd (si := .adrp .X9 st.msg) (FStable.dframe R m0) (fun s he hn => hcode.n1 s he hn)
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    hit PN.n1b
  case n1b =>
    refine si_nd (si := .addLo12 .X9 .X9 st.msg) (FStable.dframe R m0) (fun s he hn => hcode.n1b s he hn)
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    hit PN.n2
  case n2 =>
    exact seg_nd hne1 hok1 (FStable.dframe R m0) hR hal hlo hhi (fun s he hn => hcode.n2 s he hn)
      fun σ c hJ => ⟨c, .refl c, .inl ⟨PN.svc, h1 σ c hJ⟩⟩
  case svc => exact seg_given PN.n5 hsvc
  case n5 =>
    refine seg_nd (by simp [b2]) b2_ok (FStable.dframe R m0) hR hal hlo hhi (fun s he hn => hcode.n5 s he hn)
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    rw [N, b2_run]; hit PN.ex
  case ex =>
    refine exit_nd hK (fun s he hn => hcode.ex s he hn) (fun σ c hJ => ?_)
      fun s c _ hAt _ => SysOk.exitGroup_abort (hab s c hAt)
    rw [hJ.2.1]; rfl

end Proof

/-! ## The stubs -/

/-- The argument block: the stub's own, and its landing at the system
call. -/
macro "arg_hit" run:ident : tactic =>
  `(tactic| (intro σ c hJ; rw [N, $run:ident]; refine ⟨?_, rfl, ?_⟩ <;> simp_all [N, JI, upd_apply]))

section Stubs

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {m0 : MachineData} {c0 : Ctl} {Q : Frag isaLSE2}

/-! ### `scc_rt_abort_overflow` -/

def overflow : Stub :=
  ⟨"scc_rt_abort_overflow", ".L13_scc_rt_abort_overflow.0_entry", "scc_rt_abort_overflow_exit", "scc_rt_msg1"⟩

def b1Overflow : List Directive := parseAArch64("str x9, [sp]
movz x0, #2
ldr x1, [sp]
movz x2, #34
movz x8, #64")

block_spec b1Overflow (-48) 0 oI b1Overflow

/-- **`scc_rt_abort_overflow` does not return.** -/
theorem seg_overflow (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hcode : Code overflow c0 b1Overflow exe endPc) (hK : ms.K = some Scc.Sem.A64.abi)
    (hsvc : Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label overflow c0 .svc))
      (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label overflow c0 .n5)))
    (hab : ∀ s c, At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label overflow c0 .ex) s c →
      ms.abortAt s) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label overflow c0 .e)) Q :=
  seg_stub overflow (by simp [b1Overflow]) b1Overflow_ok (by arg_hit b1Overflow_run)
    hR hal hlo hhi hcode hK hsvc hab

/-! ### `scc_rt_abort_heap` -/

def heap : Stub :=
  ⟨"scc_rt_abort_heap", ".L14_scc_rt_abort_heap.0_entry", "scc_rt_abort_heap_exit", "scc_rt_msg2"⟩

def b1Heap : List Directive := parseAArch64("str x9, [sp]
movz x0, #2
ldr x1, [sp]
movz x2, #35
movz x8, #64")

block_spec b1Heap (-48) 0 oI b1Heap

/-- **`scc_rt_abort_heap` does not return.** -/
theorem seg_heap (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hcode : Code heap c0 b1Heap exe endPc) (hK : ms.K = some Scc.Sem.A64.abi)
    (hsvc : Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label heap c0 .svc))
      (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label heap c0 .n5)))
    (hab : ∀ s c, At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label heap c0 .ex) s c →
      ms.abortAt s) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label heap c0 .e)) Q :=
  seg_stub heap (by simp [b1Heap]) b1Heap_ok (by arg_hit b1Heap_run)
    hR hal hlo hhi hcode hK hsvc hab

/-! ### `scc_rt_abort_stack` -/

def stack : Stub :=
  ⟨"scc_rt_abort_stack", ".L15_scc_rt_abort_stack.0_entry", "scc_rt_abort_stack_exit", "scc_rt_msg3"⟩

def b1Stack : List Directive := parseAArch64("str x9, [sp]
movz x0, #2
ldr x1, [sp]
movz x2, #25
movz x8, #64")

block_spec b1Stack (-48) 0 oI b1Stack

/-- **`scc_rt_abort_stack` does not return.** -/
theorem seg_stack (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hcode : Code stack c0 b1Stack exe endPc) (hK : ms.K = some Scc.Sem.A64.abi)
    (hsvc : Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label stack c0 .svc))
      (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label stack c0 .n5)))
    (hab : ∀ s c, At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label stack c0 .ex) s c →
      ms.abortAt s) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label stack c0 .e)) Q :=
  seg_stub stack (by simp [b1Stack]) b1Stack_ok (by arg_hit b1Stack_run)
    hR hal hlo hhi hcode hK hsvc hab

/-! ### `scc_rt_abort_write` -/

def write : Stub :=
  ⟨"scc_rt_abort_write", ".L16_scc_rt_abort_write.0_entry", "scc_rt_abort_write_exit", "scc_rt_msg4"⟩

def b1Write : List Directive := parseAArch64("str x9, [sp]
movz x0, #2
ldr x1, [sp]
movz x2, #44
movz x8, #64")

block_spec b1Write (-48) 0 oI b1Write

/-- **`scc_rt_abort_write` does not return.** -/
theorem seg_write (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hcode : Code write c0 b1Write exe endPc) (hK : ms.K = some Scc.Sem.A64.abi)
    (hsvc : Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label write c0 .svc))
      (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label write c0 .n5)))
    (hab : ∀ s c, At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label write c0 .ex) s c →
      ms.abortAt s) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label write c0 .e)) Q :=
  seg_stub write (by simp [b1Write]) b1Write_ok (by arg_hit b1Write_run)
    hR hal hlo hhi hcode hK hsvc hab

/-! ### `scc_rt_abort_threads` -/

def threads : Stub :=
  ⟨"scc_rt_abort_threads", ".L17_scc_rt_abort_threads.0_entry", "scc_rt_abort_threads_exit", "scc_rt_msg5"⟩

def b1Threads : List Directive := parseAArch64("str x9, [sp]
movz x0, #2
ldr x1, [sp]
movz x2, #35
movz x8, #64")

block_spec b1Threads (-48) 0 oI b1Threads

/-- **`scc_rt_abort_threads` does not return.** -/
theorem seg_threads (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hcode : Code threads c0 b1Threads exe endPc) (hK : ms.K = some Scc.Sem.A64.abi)
    (hsvc : Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label threads c0 .svc))
      (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label threads c0 .n5)))
    (hab : ∀ s c, At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label threads c0 .ex) s c →
      ms.abortAt s) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label threads c0 .e)) Q :=
  seg_stub threads (by simp [b1Threads]) b1Threads_ok (by arg_hit b1Threads_run)
    hR hal hlo hhi hcode hK hsvc hab

end Stubs

/-! ## The dispatcher `scc_rt_abort` -/

namespace Disp

/-! `scc_rt_abort(k)` (`x0 = k`): k is stored at `[sp]` and compared against
1, …, 5; on a match the frame is popped and the stub `k` entered by `b` with
`sp` back at its entry value (the stub's frame base is the dispatcher's);
otherwise the `b .` halt loop, dead for `k ∈ [1, 5]`. -/

def d0 : List Directive := parseAArch64("sub sp, sp, #32
str x29, [sp, #16]
str x30, [sp, #24]
add x29, sp, #16
str x0, [sp]")
def t1 : List Directive := parseAArch64("ldr x9, [sp]
movz x10, #1
subs xzr, x9, x10
b.eq .L12_scc_rt_abort.1_is0")
def j1 : List Directive := parseAArch64("b .L12_scc_rt_abort.2_next1")
def g1 : List Directive := parseAArch64("ldr x29, [sp, #16]
ldr x30, [sp, #24]
add sp, sp, #32
b scc_rt_abort_overflow")
def t2 : List Directive := parseAArch64("ldr x9, [sp]
movz x10, #2
subs xzr, x9, x10
b.eq .L12_scc_rt_abort.3_is2")
def j2 : List Directive := parseAArch64("b .L12_scc_rt_abort.4_next3")
def g2 : List Directive := parseAArch64("ldr x29, [sp, #16]
ldr x30, [sp, #24]
add sp, sp, #32
b scc_rt_abort_heap")
def t3 : List Directive := parseAArch64("ldr x9, [sp]
movz x10, #3
subs xzr, x9, x10
b.eq .L12_scc_rt_abort.5_is4")
def j3 : List Directive := parseAArch64("b .L12_scc_rt_abort.6_next5")
def g3 : List Directive := parseAArch64("ldr x29, [sp, #16]
ldr x30, [sp, #24]
add sp, sp, #32
b scc_rt_abort_stack")
def t4 : List Directive := parseAArch64("ldr x9, [sp]
movz x10, #4
subs xzr, x9, x10
b.eq .L12_scc_rt_abort.7_is6")
def j4 : List Directive := parseAArch64("b .L12_scc_rt_abort.8_next7")
def g4 : List Directive := parseAArch64("ldr x29, [sp, #16]
ldr x30, [sp, #24]
add sp, sp, #32
b scc_rt_abort_write")
def t5 : List Directive := parseAArch64("ldr x9, [sp]
movz x10, #5
subs xzr, x9, x10
b.eq .L12_scc_rt_abort.9_is8")
def j5 : List Directive := parseAArch64("b .L12_scc_rt_abort.10_next9")
def g5 : List Directive := parseAArch64("ldr x29, [sp, #16]
ldr x30, [sp, #24]
add sp, sp, #32
b scc_rt_abort_threads")

/-- The dispatcher's offsets inside its frame. -/
abbrev oD : SO := ⟨-32, []⟩

block_spec d0 (-32) 0 oE d0
block_spec t1 (-32) 0 oD t1
block_spec j1 (-32) 0 oD j1
block_spec g1 (-32) 0 oD g1
block_spec t2 (-32) 0 oD t2
block_spec j2 (-32) 0 oD j2
block_spec g2 (-32) 0 oD g2
block_spec t3 (-32) 0 oD t3
block_spec j3 (-32) 0 oD j3
block_spec g3 (-32) 0 oD g3
block_spec t4 (-32) 0 oD t4
block_spec j4 (-32) 0 oD j4
block_spec g4 (-32) 0 oD g4
block_spec t5 (-32) 0 oD t5
block_spec j5 (-32) 0 oD j5
block_spec g5 (-32) 0 oD g5

/-- The internal nodes: the entry, the tests `t`, the jumps to the next test
`j`, the jumps to the stubs `g`, and the dead halt loop. -/
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

/-- A stub's argument block. -/
def DX.b1 : DX → List Directive
  | .overflow => b1Overflow
  | .heap => b1Heap
  | .stack => b1Stack
  | .write => b1Write
  | .threads => b1Threads

/-- The code `v` is in `[k, 5]`. -/
def Rng (k : Nat) (v : BitVec 64) : Prop := k ≤ v.toNat ∧ v.toNat ≤ 5

/-- A failed test against `k` (`subs` and `b.eq`): the code is in
`[k + 1, 5]`. -/
theorem rng_succ {k : Nat} {v : BitVec 64} (h : Rng k v)
    (hne : ¬ (StatusFlags.subs (v - BitVec.ofNat 64 k) v (BitVec.ofNat 64 k)).z = true) : Rng (k + 1) v := by
  have hz : ¬ v - BitVec.ofNat 64 k = 0#64 := fun e => hne (by
    simp only [StatusFlags.subs, StatusFlags.from_result, e]; decide)
  have hk : v.toNat ≠ k := fun e => hz (by
    have : v = BitVec.ofNat 64 k := BitVec.eq_of_toNat_eq (by simp [e]; unfold Rng at h; omega)
    simp [this])
  unfold Rng at h ⊢; omega

section Spec

variable (lab : Label → Int64) (c0 : Ctl)

/-- Inside the frame, before the test against `k`: the source has not moved,
the stored code is in `[k, 5]`. -/
def JT (k : Nat) (σ : AS) (c : Ctl) : Prop := c = c0 ∧ Rng k (σ.slot (-32))

/-- **The nodes.** -/
def DN.nd : DN → ND
  | .e => ⟨lab "scc_rt_abort", oE, fun σ c => c = c0 ∧ Rng 1 σ.regs.X0.toBitVec⟩
  | .t1 => ⟨lab ".L12_scc_rt_abort.0_entry", oD, JT c0 1⟩
  | .j1 => ⟨lab ".L12_scc_rt_abort.0_entry" + 4 + 4 + 4 + 4, oD, JT c0 2⟩
  | .g1 => ⟨lab ".L12_scc_rt_abort.1_is0", oD, fun _ c => c = c0⟩
  | .t2 => ⟨lab ".L12_scc_rt_abort.2_next1", oD, JT c0 2⟩
  | .j2 => ⟨lab ".L12_scc_rt_abort.2_next1" + 4 + 4 + 4 + 4, oD, JT c0 3⟩
  | .g2 => ⟨lab ".L12_scc_rt_abort.3_is2", oD, fun _ c => c = c0⟩
  | .t3 => ⟨lab ".L12_scc_rt_abort.4_next3", oD, JT c0 3⟩
  | .j3 => ⟨lab ".L12_scc_rt_abort.4_next3" + 4 + 4 + 4 + 4, oD, JT c0 4⟩
  | .g3 => ⟨lab ".L12_scc_rt_abort.5_is4", oD, fun _ c => c = c0⟩
  | .t4 => ⟨lab ".L12_scc_rt_abort.6_next5", oD, JT c0 4⟩
  | .j4 => ⟨lab ".L12_scc_rt_abort.6_next5" + 4 + 4 + 4 + 4, oD, JT c0 5⟩
  | .g4 => ⟨lab ".L12_scc_rt_abort.7_is6", oD, fun _ c => c = c0⟩
  | .t5 => ⟨lab ".L12_scc_rt_abort.8_next7", oD, JT c0 5⟩
  | .j5 => ⟨lab ".L12_scc_rt_abort.8_next7" + 4 + 4 + 4 + 4, oD, JT c0 6⟩
  | .g5 => ⟨lab ".L12_scc_rt_abort.9_is8", oD, fun _ c => c = c0⟩
  | .dead => ⟨lab ".L12_scc_rt_abort.10_next9", oD, fun _ _ => False⟩

/-- **The exits**: the stubs' entries. -/
def DX.nd (x : DX) : ND := Abort.N lab x.stub c0 .e

/-- **The code** and the prologue's fall-through into `.0_entry`. -/
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
  hentry : (_root_.Executable.labels exe).label ".L12_scc_rt_abort.0_entry" =
    (_root_.Executable.labels exe).label "scc_rt_abort" + 4 + 4 + 4 + 4 + 4

end Spec

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {m0 : MachineData} {c0 : Ctl}

set_option hygiene false in
/-- A block node: the block, its `okBlk`, its code; the edge is left. -/
macro "dnode " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine seg_nd (by simp [$b:ident]) $ok (FStable.dframe R m0) hR hal (by omega) hhi
    (fun s he hn => hcode.$f s he hn) fun σ c hJ => ⟨c, .refl c, ?_⟩)

/-- Hitting node `j`. -/
macro "dhit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;> simp_all [DN.nd, JT, Rng, upd_apply]))

/-- Hitting exit `x`. -/
macro "dexit " x:term : tactic =>
  `(tactic| (refine .inr ⟨$x, ?_, rfl, ?_⟩ <;>
    simp_all [DN.nd, DX.nd, DX.stub, Abort.N, Abort.overflow, Abort.heap, Abort.stack, Abort.write,
      Abort.threads]))

/-- **`scc_rt_abort` is one segment** from its entry (with a code in
`[1, 5]`) to the entries of the five stubs. -/
theorem seg_disp_fn (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hcode : Code c0 exe endPc) :
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
theorem seg_disp {Q : Frag isaLSE2} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hcode : Code c0 exe endPc)
    (hs : ∀ x, Seg p lbl ms (At exe endPc R (DFrame R m0) (DX.nd (_root_.Executable.labels exe).label c0 x)) Q) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (DN.nd (_root_.Executable.labels exe).label c0 .e)) Q :=
  (seg_disp_fn hR hal hlo hhi hcode).seq <| Seg.cfg (fun x => At exe endPc R (DFrame R m0) (DX.nd _ c0 x))
    fun x => (hs x).mono_post fun _ _ h => .inr h

/-- **`scc_rt_abort` does not return**, composed with the five stubs: from its
entry (with a code in `[1, 5]`) it is a segment to any fragment, given the
code of the dispatcher and the stubs and the stubs' `write` calls. -/
theorem seg_abort {Q : Frag isaLSE2} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48)
    (hhi : 0 ≤ R.hi) (hcode : Code c0 exe endPc) (hK : ms.K = some Scc.Sem.A64.abi)
    (hc : ∀ x : DX, Abort.Code x.stub c0 x.b1 exe endPc)
    (hsvc : ∀ x : DX,
      Seg p lbl ms (At exe endPc R (DFrame R m0) (Abort.N (_root_.Executable.labels exe).label x.stub c0 .svc))
        (At exe endPc R (DFrame R m0) (Abort.N (_root_.Executable.labels exe).label x.stub c0 .n5)))
    (hab : ∀ (x : DX) s c,
      At exe endPc R (DFrame R m0) (Abort.N (_root_.Executable.labels exe).label x.stub c0 .ex) s c → ms.abortAt s) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (DN.nd (_root_.Executable.labels exe).label c0 .e)) Q :=
  seg_disp hR hal hlo hhi hcode fun x => by
    cases x
    · exact seg_overflow hR hal hlo hhi (hc .overflow) hK (hsvc .overflow) (hab .overflow)
    · exact seg_heap hR hal hlo hhi (hc .heap) hK (hsvc .heap) (hab .heap)
    · exact seg_stack hR hal hlo hhi (hc .stack) hK (hsvc .stack) (hab .stack)
    · exact seg_write hR hal hlo hhi (hc .write) hK (hsvc .write) (hab .write)
    · exact seg_threads hR hal hlo hhi (hc .threads) hK (hsvc .threads) (hab .threads)

end Proof

end Disp

/-! ## The tail of `scc_rt_main` -/

namespace MainTail

/-! After `wc_main` returns (`.L1_scc_rt_main.sp1`, its result `ret` in
`x0`), `scc_rt_main` stores it, calls `exit_group(ret)` and ends in a dead
store and halt loop. The rest of `scc_rt_main` (the stack check and the
calls) is left to the call composition. -/

def m0 : List Directive := parseAArch64("str x0, [sp, #40]
ldr x0, [sp, #40]
movz x8, #94")

/-- The offsets in `scc_rt_main`'s frame after the calls. -/
abbrev oM : SO := ⟨-80, []⟩

block_spec m0 (-80) 0 oM m0

/-- The nodes: the tail block and the `exit_group` call. -/
inductive MN where
  | sp1 | ex

section Spec

variable (lab : Label → Int64) (c0 : Ctl) (ret : BitVec 64)

/-- **The nodes**: `ret` in `x0`, then `exit_group(ret)`. -/
def MN.nd : MN → ND
  | .sp1 => ⟨lab ".L1_scc_rt_main.sp1", oM, fun σ c => c = c0 ∧ σ.regs.X0.toBitVec = ret⟩
  | .ex => ⟨lab ".L1_scc_rt_main.sp1" + 4 + 4 + 4, oM,
      fun σ c => c = c0 ∧ σ.regs.X8 = 94 ∧ σ.regs.X0.toBitVec = ret⟩

/-- **The code.** -/
structure Code (exe : _root_.Executable) (endPc : Int64) : Prop where
  sp1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (MN.nd (_root_.Executable.labels exe).label c0 ret .sp1).pc m0
  ex : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (MN.nd (_root_.Executable.labels exe).label c0 ret .ex).pc [svcDir]

end Spec

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {mi : MachineData} {c0 : Ctl} {ret : BitVec 64}

/-- **The tail of `scc_rt_main` does not return**: from `.sp1` with `ret` in
`x0` it is a segment to any fragment (through `exit_group(ret)`). -/
theorem seg_main_tail {Q : Frag isaLSE2} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -80)
    (hhi : 0 ≤ R.hi) (hcode : Code c0 ret exe endPc) (hK : ms.K = some Scc.Sem.A64.abi)
    (hmain : ∀ s c, At exe endPc R (DFrame R mi) (MN.nd (_root_.Executable.labels exe).label c0 ret .ex) s c →
      ¬ ms.abortAt s → MainExit p ms s c ret.toNat) :
    Seg p lbl ms (At exe endPc R (DFrame R mi) (MN.nd (_root_.Executable.labels exe).label c0 ret .sp1)) Q := by
  refine (fn_seg (N := MN.nd _ c0 ret) (E := (nofun : PX → ND)) (fun i => ?_) MN.sp1).mono_post
    fun _ _ ⟨x, _⟩ => nomatch x
  cases i
  case sp1 =>
    refine seg_nd (by simp [m0]) m0_ok (FStable.dframe R mi) hR hal hlo hhi (fun s he hn => hcode.sp1 s he hn)
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    rw [MN.nd, m0_run]
    refine .inl ⟨MN.ex, ?_, rfl, ?_⟩ <;> simp_all [MN.nd]
  case ex =>
    refine exit_nd hK (fun s he hn => hcode.ex s he hn) (fun σ c hJ => ?_) fun s c σ hAt hJ => ?_
    · rw [hJ.2.1]; rfl
    refine SysOk.exitGroup_main ?_
    have h : σ.regs.X0.toNat = ret.toNat := by rw [← hJ.2.2]; rfl
    rw [h]; exact hmain s c hAt

end MainTail

namespace MainTail0

/-! `MainTail`'s twin for a program whose `main` takes no setup block's
result (`main(u : Unit) : Int`, or a `ThreadId`): `scc_rt_main` calls
`wc_main` only, in a 48-byte frame. After `wc_main` returns
(`.L1_scc_rt_main.sp0`, its result `ret` in `x0`), `scc_rt_main` stores it,
calls `exit_group(ret)` and ends in a dead store and halt loop. -/

def m0 : List Directive := parseAArch64("str x0, [sp, #8]
ldr x0, [sp, #8]
movz x8, #94")

/-- The offsets in `scc_rt_main`'s frame after the calls. -/
abbrev oM : SO := ⟨-48, []⟩

block_spec m0 (-48) 0 oM m0

/-- The nodes: the tail block and the `exit_group` call. -/
inductive MN where
  | sp0 | ex

section Spec

variable (lab : Label → Int64) (c0 : Ctl) (ret : BitVec 64)

/-- **The nodes**: `ret` in `x0`, then `exit_group(ret)`. -/
def MN.nd : MN → ND
  | .sp0 => ⟨lab ".L1_scc_rt_main.sp0", oM, fun σ c => c = c0 ∧ σ.regs.X0.toBitVec = ret⟩
  | .ex => ⟨lab ".L1_scc_rt_main.sp0" + 4 + 4 + 4, oM,
      fun σ c => c = c0 ∧ σ.regs.X8 = 94 ∧ σ.regs.X0.toBitVec = ret⟩

/-- **The code.** -/
structure Code (exe : _root_.Executable) (endPc : Int64) : Prop where
  sp0 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (MN.nd (_root_.Executable.labels exe).label c0 ret .sp0).pc m0
  ex : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (MN.nd (_root_.Executable.labels exe).label c0 ret .ex).pc [svcDir]

end Spec

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {mi : MachineData} {c0 : Ctl} {ret : BitVec 64}

/-- **The tail of `scc_rt_main` does not return**: from `.sp0` with `ret` in
`x0` it is a segment to any fragment (through `exit_group(ret)`), given that
the exit is `main`'s (`hmain`). -/
theorem seg_main_tail {Q : Frag isaLSE2} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48)
    (hhi : 0 ≤ R.hi) (hcode : Code c0 ret exe endPc) (hK : ms.K = some Scc.Sem.A64.abi)
    (hmain : ∀ s c, At exe endPc R (DFrame R mi) (MN.nd (_root_.Executable.labels exe).label c0 ret .ex) s c →
      ¬ ms.abortAt s → MainExit p ms s c ret.toNat) :
    Seg p lbl ms (At exe endPc R (DFrame R mi) (MN.nd (_root_.Executable.labels exe).label c0 ret .sp0)) Q := by
  refine (fn_seg (N := MN.nd _ c0 ret) (E := (nofun : PX → ND)) (fun i => ?_) MN.sp0).mono_post
    fun _ _ ⟨x, _⟩ => nomatch x
  cases i
  case sp0 =>
    refine seg_nd (by simp [m0]) m0_ok (FStable.dframe R mi) hR hal hlo hhi (fun s he hn => hcode.sp0 s he hn)
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    rw [MN.nd, m0_run]
    refine .inl ⟨MN.ex, ?_, rfl, ?_⟩ <;> simp_all [MN.nd]
  case ex =>
    refine exit_nd hK (fun s he hn => hcode.ex s he hn) (fun σ c hJ => ?_) fun s c σ hAt hJ => ?_
    · rw [hJ.2.1]; rfl
    refine SysOk.exitGroup_main ?_
    have h : σ.regs.X0.toNat = ret.toNat := by rw [← hJ.2.2]; rfl
    rw [h]; exact hmain s c hAt

end MainTail0

end Spike.Lib.A64.Abort
