/-
**The x64 Michael–Scott queue pilot with a
bump-allocating enqueuer** (the x64 counterpart of the allocating MS queue pilot,
`Lower/MsqAllocProg.lean`, on the x64 MS queue pilot, `Lower/MsqXRProg.lean`). ISA: x64.

```
main_e() { n1 := alloc(); [n1 + 8] := 1; enq(&tail, n1); n2 := alloc(); [n2 + 8] := 2; enq(&tail, n2) }
main_d() { r12 := deq(&head, &tail); r13 := deq(&head, &tail) }     -- the x64 MS queue pilot's, unchanged
```

Under the x64 register-link pilot's stackless register-link convention (call
`leaq ret(%rip), %r11; jmp f`, return `jmp *%r11`, no stack, `dmem` empty;
arguments `rdi`, `rsi`, result `rax`; callee-saved `rbx rbp r12–r15`,
the x64 pilot's `Saved`; a `main` keeps its link in `rbp`):

- **`alloc`, a stackless leaf**: `rax := r14; r14 += 16`, `cmpq %r15, %r14;
  ja alloc_oom` (`alloc_oom: jmp alloc_oom`, never taken under the room
  hypothesis), `jmp *%r11`; no memory access. **Registers**: the bump pointer
  `r14` and the limit `r15` are callee-saved for every function except
  `alloc` (which advances `r14`), so they survive `enq` (`EnqPost`'s `Saved`)
  without any spill, as the x64 register-link pilot's inline bump (`Lower/PilotXRProg.lean`)
  already used them; `rax` is the result register; `rbx` (`&tail`) and `rbp`
  (`main_e`'s link) are untouched by `alloc`. The first call returns `base`,
  the second `base + 16` (`allocX_chain`).
- **Node layout (x64)**: the x64 MS queue pilot's protocol (`EnvG/X64MsQueue2Ghost.lean`) puts
  a node's link `[n]` at offset `0` and has **no data word**. The data word
  of WeakCore's `{data, next}` node therefore sits at `[n + 8]` (8 bytes):
  `movl $v, %ecx; movq %rcx, 8(%rax)`. It is not a queue word (`Params.IsW`),
  so its store is a pure message (`Lower/MsqAllocXMain.lean`, `vc_e_strD`).
- **Emitter rule (pre-zeroed arena)**, as the allocating MS queue pilot: WeakCore's `new` lowers a
  `null` initial link to **no store**; the arena is fresh, pre-zeroed and
  never reused, so the links `[base]`, `[base + 16]` are `0` initially
  (the x64 MS queue pilot's `InitV` at `n1 = base`, `n2 = base + 16`). Only the data words are
  stored. (A link store of `0` would be a non-initial link message of value
  `0`, which the x64 MS queue pilot's `form` rejects: `LinkF` admits only `n1`/`n2`.)
- `enq` is **verbatim** the x64 MS queue pilot's `enqFrag` (`msqAX_split`, `msqAX_enq`); the
  dequeuer is the x64 MS queue pilot's thread on `msqXR` itself (entry `main_d`), unchanged.

Contents: `msqAX` and its pieces, the identity checks, the `.kl`-runner
layout, the explorer configuration and run, the static check of the EnvG link.
-/
import Kraken.Promising.Lower.MsqXRProg

namespace Kraken.Promising.Lower.MsqAllocX

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.EnvG
open Kraken.X64.Parser
open Kraken.Promising.Lower.MsqXR (enqFrag)

/-! ## The pieces of `main_e` -/

/-- `main_e`: save the link, call `alloc`. -/
def mainABody : Program := parse("
    movq %r11, %rbp
    leaq ret_a1(%rip), %r11
    jmp alloc
")

/-- Behind the first `alloc`: node 1's data word, `enq(&tail, n1)`. -/
def retA1Body : Program := parse("
    movl $1, %ecx
    movq %rcx, 8(%rax)
    movq %rbx, %rdi
    movq %rax, %rsi
    leaq ret_e1(%rip), %r11
    jmp enq
")

/-- Behind the first `enq`: call `alloc`. -/
def retE1Body : Program := parse("
    leaq ret_a2(%rip), %r11
    jmp alloc
")

/-- Behind the second `alloc`: node 2's data word, `enq(&tail, n2)`. -/
def retA2Body : Program := parse("
    movl $2, %ecx
    movq %rcx, 8(%rax)
    movq %rbx, %rdi
    movq %rax, %rsi
    leaq ret_e2(%rip), %r11
    jmp enq
")

/-- Behind the second `enq`: return. -/
def retE2Body : Program := parse("
    jmp *%rbp
")

/-- `main_e`'s five blocks. -/
def mainATxt : Program :=
  .label "main_e" :: mainABody ++ .label "ret_a1" :: retA1Body ++ .label "ret_e1" :: retE1Body ++
    .label "ret_a2" :: retA2Body ++ .label "ret_e2" :: retE2Body

/-- **`alloc`**, the stackless bump-allocator leaf. -/
def allocFragX : Program := parse("
alloc:
    movq %r14, %rax
    addq $16, %r14
    cmpq %r15, %r14
    ja alloc_oom
    jmp *%r11
alloc_oom:
    jmp alloc_oom
")

/-- **The enqueuer's text** (no stack; ends at `done:`). -/
def msqAX : Program := parse("
main_e:
    movq %r11, %rbp
    leaq ret_a1(%rip), %r11
    jmp alloc
ret_a1:
    movl $1, %ecx
    movq %rcx, 8(%rax)
    movq %rbx, %rdi
    movq %rax, %rsi
    leaq ret_e1(%rip), %r11
    jmp enq
ret_e1:
    leaq ret_a2(%rip), %r11
    jmp alloc
ret_a2:
    movl $2, %ecx
    movq %rcx, 8(%rax)
    movq %rbx, %rdi
    movq %rax, %rsi
    leaq ret_e2(%rip), %r11
    jmp enq
ret_e2:
    jmp *%rbp
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
alloc:
    movq %r14, %rax
    addq $16, %r14
    cmpq %r15, %r14
    ja alloc_oom
    jmp *%r11
alloc_oom:
    jmp alloc_oom
done:
")

/-- **`msqAX` is `main_e`, then the x64 MS queue pilot's `enqFrag` and `alloc`, verbatim.** -/
theorem msqAX_split : msqAX = mainATxt ++ enqFrag ++ allocFragX ++ [.label "done"] := by
  decide +kernel

/-- **`enq` is the x64 MS queue pilot's, unchanged**: the text from `enq:` agrees with
`msqXR`'s for `enq`'s length. -/
theorem msqAX_enq : (Program.fromLabel msqAX "enq").take enqFrag.length =
    (Program.fromLabel MsqXR.msqXR "enq").take enqFrag.length := by
  decide +kernel

/-- info: (50, 40) -/
#guard_msgs in
#eval (msqAX.length, (msqAX.filter (!·.isLabel)).length)

/-! ## The layout and the start state -/

/-- The `.kl` runner's layout: text at `0x100000`, labels `0` bytes, every
instruction `1`. -/
@[reducible] def maLayout : _root_.Layout := Concrete.klLayout msqAX 0x100000

instance maValid : Executable.ValidLayout (maLayout msqAX) :=
  Concrete.validLayout_of_cells _ (by decide) (by decide)

/-- The end address: `40` instructions of `1` byte. -/
def endMA : Int64 := 0x100000 + 40

/-- The enqueuer: `rbx = &tail`, the arena `[0x2100, 0x2200)` in `r14`/`r15`,
the link at the end. -/
def threadA : X64.State where
  exe := maLayout msqAX
  endPc := endMA
  st := ({ ({} : MachineData) with
    regs := (((({} : MachineData).regs.set64 .rbx 0x1008).set64 .r14 0x2100).set64 .r15 0x2200).set64 .r11
      endMA.toBitVec }, 0x100000)

/-- msqueue2's queue words (`head = tail = s = 0x2000`, its link `0`), the
pre-zeroed arena's links `0` and its data words garbage (`7`). -/
def initMemA : List (Loc × Val) :=
  [(⟨0x1000, 8⟩, 0x2000), (⟨0x1008, 8⟩, 0x2000), (⟨0x2000, 8⟩, 0), (⟨0x2100, 8⟩, 0), (⟨0x2110, 8⟩, 0),
    (⟨0x2108, 8⟩, 7), (⟨0x2118, 8⟩, 7)]

/-- The explorer under `Arch.tso` (the dequeuer is the x64 MS queue pilot's `threadD`, on
`msqXR`): per final, the dequeuer's `(r12, r13)` and the enqueuer's `r14`. -/
def exploreFinalsA (o : ExploreOpts) : List (Nat × Nat × Nat) × Bool × List String :=
  let r := explore Arch.tso (Config.init [threadA, MsqXR.threadD] initMemA : Config isa)
    (fun c => match c.threads.toList with
      | [e, d] => ((d.st.st.1.regs.get64 .r12).toNat, (d.st.st.1.regs.get64 .r13).toNat,
          (e.st.st.1.regs.get64 .r14).toNat)
      | _ => (0, 0, 0)) o
  (r.finals, r.boundHit, r.faults)

/-- **msqueue2's verdict** (`Arch.tso`, promise-free, `boundHit = false`):
every final has the dequeuer's `r12 = base` (`0x2100`), `r13 = base + 16`
(`0x2110`), the bump pointer past both nodes (`0x2120`); no fault. The
Promising-level guarantee is `msqAllocX_promising`. -/
def msqAllocXRun0 : List (Nat × Nat × Nat) × Bool × List String :=
  exploreFinalsA { fuel := 90, maxPromises := some 0 }

/-- info: ([(8448, 8464, 8480)], false, []) -/
#guard_msgs in
#eval msqAllocXRun0

/-! ## The static check of the EnvG link -/

section Static

variable [layout : _root_.Layout]

/-- Every cell is a phase-1 tree. -/
theorem msqAX_phase1FX [Executable.ValidLayout (layout msqAX)] : Phase1TreeFX (layout msqAX) := by
  refine phase1TreeFX_of_dirs (dirsPhase1FX_layout fun d hd e z s pc => ?_)
  simp only [msqAX_split, mainATxt, enqFrag, allocFragX, mainABody, retA1Body, retE1Body, retA2Body, retE2Body,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals simp only [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    _root_.RelRegOrMem.interp]
  cells_phase1FX

end Static

end Kraken.Promising.Lower.MsqAllocX
