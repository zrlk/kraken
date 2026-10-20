/-
**The Michael–Scott queue `msqueue2.kl` on x64,
hand-lowered to functions under the x64 register-link pilot's stackless register-link
convention** (`Lower/PilotXRProg.lean`: call `leaq ret(%rip), %r11; jmp f`,
return `jmp *%r11`, no stack, `dmem` empty; arguments `rdi`, `rsi`, result
`rax`; callee-saved `rbx rbp r12–r15`; a `main` keeps its link in `rbp`).

`main_e() { enq(&tail, n1); enq(&tail, n2) }`,
`main_d() { r12 := deq(&head, &tail); r13 := deq(&head, &tail) }`; `enq`/`deq`
are msqueue2's loops (`msq2CodeV`) with the scratch registers moved to
caller-saved ones, the re-checks `cmpq %r,(q)` as a load and a register
compare, and a return `jmp *%r11` after the own swing (`deq`: result in
`rax`). Every backward jump follows a shared access in its block: no
zero-step back edge, so no label rank is needed on x64. One text for both
threads (entries `main_e`, `main_d`), ending at `done:`.
-/
import Kraken.Promising.SLR.EnvG.X64MsQueue2Public
import Kraken.Promising.SLR.EnvG.ConcreteX64Layout

namespace Kraken.Promising.Lower.MsqXR

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.EnvG
open Kraken.X64.Parser

def mainEBody : Program := parse("
    movq %r11, %rbp
    movq %rbx, %rdi
    movq %r12, %rsi
    leaq ret_e1(%rip), %r11
    jmp enq
")
def retE1Body : Program := parse("
    movq %rbx, %rdi
    movq %r13, %rsi
    leaq ret_e2(%rip), %r11
    jmp enq
")
def retE2Body : Program := parse("
    jmp *%rbp
")

/-- `main_e`'s three blocks. -/
def mainETxt : Program :=
  .label "main_e" :: mainEBody ++ .label "ret_e1" :: retE1Body ++ .label "ret_e2" :: retE2Body

/-- `enq`'s text, as a fragment of `msqXR`. -/
def enqFrag : Program := parse("
enq:
    movq (%rdi), %rdx
    movq (%rdx), %rcx
    movq (%rdi), %r8
    cmpq %rdx, %r8
    jne enq
    testq %rcx, %rcx
    jne enq_swing
    xorl %eax, %eax
    lock cmpxchgq %rsi, (%rdx)
    jne enq
    movq %rdx, %rax
    lock cmpxchgq %rsi, (%rdi)
    jmp *%r11
enq_swing:
    movq %rdx, %rax
    lock cmpxchgq %rcx, (%rdi)
    jmp enq
")

def mainDBody : Program := parse("
    movq %r11, %rbp
    movq %rbx, %rdi
    movq %r14, %rsi
    leaq ret_d1(%rip), %r11
    jmp deq
")
def retD1Body : Program := parse("
    movq %rax, %r12
    movq %rbx, %rdi
    movq %r14, %rsi
    leaq ret_d2(%rip), %r11
    jmp deq
")
def retD2Body : Program := parse("
    movq %rax, %r13
    jmp *%rbp
")

/-- `main_d`'s three blocks. -/
def mainDTxt : Program :=
  .label "main_d" :: mainDBody ++ .label "ret_d1" :: retD1Body ++ .label "ret_d2" :: retD2Body

/-- `deq`'s text, as a fragment of `msqXR`. -/
def deqFrag : Program := parse("
deq:
    movq (%rdi), %rdx
    movq (%rsi), %r8
    movq (%rdx), %rcx
    movq (%rdi), %r9
    cmpq %rdx, %r9
    jne deq
    cmpq %rdx, %r8
    jne deq_pop
    testq %rcx, %rcx
    je deq
    movq %rdx, %rax
    lock cmpxchgq %rcx, (%rsi)
    jmp deq
deq_pop:
    movq %rdx, %rax
    lock cmpxchgq %rcx, (%rdi)
    jne deq
    movq %rcx, %rax
    jmp *%r11
")

/-- The enqueuer's part of the text. -/
def fragE : Program := mainETxt ++ enqFrag

/-- The dequeuer's part of the text. -/
def fragD : Program := mainDTxt ++ deqFrag

/-- **The hand-lowered program** (one text, four functions, no stack). -/
def msqXR : Program := fragE ++ fragD ++ [.label "done"]

/-- info: (67, 56, 26) -/
#guard_msgs in
#eval (msqXR.length, (msqXR.filter (!·.isLabel)).length,
  ((msqXR.takeWhile (· != .label "main_d")).filter (!·.isLabel)).length)

/-! ## The layout and two start states -/

/-- The `.kl` runner's layout: text at `0x100000`, labels `0` bytes, every
instruction `1`. -/
@[reducible] def mxLayout : _root_.Layout := Concrete.klLayout msqXR 0x100000

instance mxValid : Executable.ValidLayout (mxLayout msqXR) :=
  Concrete.validLayout_of_cells _ (by decide) (by decide)

/-- The end address: `56` instructions of `1` byte. -/
def endMX : Int64 := 0x100000 + 56

/-- The enqueuer: `rbx = &tail`, `r12`/`r13` the nodes, link at the end. -/
def threadE : X64.State where
  exe := mxLayout msqXR
  endPc := endMX
  st := ({ ({} : MachineData) with
    regs := (((({} : MachineData).regs.set64 .rbx 0x1008).set64 .r12 0x2100).set64 .r13 0x2200).set64 .r11
      endMX.toBitVec }, 0x100000)

/-- The dequeuer at `main_d` (`26` in): `rbx = &head`, `r14 = &tail`. -/
def threadD : X64.State where
  exe := mxLayout msqXR
  endPc := endMX
  st := ({ ({} : MachineData) with
    regs := ((({} : MachineData).regs.set64 .rbx 0x1000).set64 .r14 0x1008).set64 .r11 endMX.toBitVec },
    0x100000 + 26)

/-- msqueue2's initial memory: `head = tail = s`, the links zero. -/
def initMemMX : List (Loc × Val) :=
  [(⟨0x1000, 8⟩, 0x2000), (⟨0x1008, 8⟩, 0x2000), (⟨0x2000, 8⟩, 0), (⟨0x2100, 8⟩, 0), (⟨0x2200, 8⟩, 0)]

/-- The explorer under `Arch.tso`: the dequeuer's `(r12, r13)` per final. -/
def exploreFinalsMX (o : ExploreOpts) : List (Nat × Nat) × Bool × List String :=
  let r := explore Arch.tso (Config.init [threadE, threadD] initMemMX : Config isa)
    (fun c => match c.threads.toList with
      | [_, d] => ((d.st.st.1.regs.get64 .r12).toNat, (d.st.st.1.regs.get64 .r13).toNat)
      | _ => (0, 0)) o
  (r.finals, r.boundHit, r.faults)

/-- **msqueue2's verdict** (`Arch.tso`, promise-free, `boundHit = false`):
every final has the dequeuer's `r12 = n1` (`0x2100`), `r13 = n2` (`0x2200`);
no fault. The Promising-level guarantee is `msqXR_promising`. -/
def msqXRRun0 : List (Nat × Nat) × Bool × List String :=
  exploreFinalsMX { fuel := 80, maxPromises := some 0 }

/-- info: ([(8448, 8704)], false, []) -/
#guard_msgs in
#eval msqXRRun0

/-- **The same with up to one promise per thread** (about a minute). -/
def msqXRRun1 : List (Nat × Nat) × Bool × List String :=
  exploreFinalsMX { fuel := 80, maxPromises := some 1 }

/-- info: ([(8448, 8704)], false, []) -/
#guard_msgs in
#eval msqXRRun1

/-! ## The static check of the EnvG link -/

section Static

variable [layout : _root_.Layout]

/-- Every cell is a phase-1 tree. -/
theorem msqXR_phase1FX [Executable.ValidLayout (layout msqXR)] : Phase1TreeFX (layout msqXR) := by
  refine phase1TreeFX_of_dirs (dirsPhase1FX_layout fun d hd e z s pc => ?_)
  simp only [msqXR, fragE, fragD, mainETxt, enqFrag, mainDTxt, deqFrag, mainEBody, retE1Body, retE2Body,
    mainDBody, retD1Body, retD2Body, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals simp only [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    _root_.RelRegOrMem.interp]
  cells_phase1FX

end Static

end Kraken.Promising.Lower.MsqXR
