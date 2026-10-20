/-
**The hand-lowered two-thread Treiber client
on x64 with a stackless register-link convention.**

The x64 lowering of the first lowering pilot's `main`/`push`/`pop` (`Lower/PilotProg.lean`),
as the x64 pilot (`Lower/PilotX64Prog.lean`) but **without a stack**: no `call`, no
`ret`, no `rsp`, and `dmem` empty throughout.

- **Call:** the caller puts its return address in the link register `r11`
  by `leaq ret_k(%rip), %r11` (the assembler's displacement cancels the pc:
  `MachineWP.lea_rip_label_spec`), then `jmp f`.
- **Return:** `jmp *%r11` (`MachineWP.jmp_reg_spec`).
- Arguments `rdi` (`&top`), `rsi` (the node); result `rax`; callee-saved
  `rbx rbp r12 r13 r14 r15` (the x64 pilot's `Saved`); `r11` is the link and
  caller-saved.
- `main` is entered with its own link (the end of the text) in `r11`, keeps
  it in the callee-saved `rbp` across its two calls, and returns by
  `jmp *%rbp`. (`main`'s caller's `rbp` is not preserved: a non-leaf function
  of this convention spends one callee-saved register per nesting level.)
- `push` (leaf): as the x64 pilot's, `jmp *%r11` for `ret`.
- `pop` (leaf): **returns `0` on empty** (WeakCore's pop), with `rax` the
  value read (`0`); otherwise the link load through the loaded pointer and
  `lock cmpxchgq`, retry by `jne`. Both `jmp *%r11` sit in blocks with a
  shared access (the zero-step guard of the CFG rule needs a state change on
  a backward edge).
- `oom: jmp oom`: never taken (`ja` after the bump check).
- The trailing `done:` makes the end of the text stuck.

Contents: `pilotXR`; the `.kl`-runner layout `xrLayout`; two concrete start
states (empty `dmem`); a `#guard_msgs` run of the Promising explorer under
`Arch.tso`; the static checks of the EnvG link (`Phase1TreeFX`,
`DirsNoFault`).
-/
import Kraken.Promising.SLR.EnvG.X64Treiber2Public
import Kraken.Promising.SLR.EnvG.ConcreteX64Layout

namespace Kraken.Promising.Lower.PilotXR

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.EnvG
open Kraken.X64.Parser

/-- **The hand-lowered program** (one text, three functions, no stack). -/
def pilotXR : Program := parse("
main:
    movq %r11, %rbp
    movq %r14, %rsi
    addq $16, %r14
    cmpq %r15, %r14
    ja oom
    movq %rbx, %rdi
    leaq ret_push(%rip), %r11
    jmp push
ret_push:
    movq %rbx, %rdi
    leaq ret_pop(%rip), %r11
    jmp pop
ret_pop:
    movq %rax, %r12
    jmp *%rbp
oom:
    jmp oom
push:
    movq (%rdi), %rax
    movq %rax, (%rsi)
    lock cmpxchgq %rsi, (%rdi)
    jne push
    jmp *%r11
pop:
    movq (%rdi), %rax
    testq %rax, %rax
    jne pop_nz
    jmp *%r11
pop_nz:
    movq (%rax), %rcx
    lock cmpxchgq %rcx, (%rdi)
    jne pop
    jmp *%r11
done:
")

/-- info: 35 -/
#guard_msgs in
#eval pilotXR.length

/-! ## The layout and two start states -/

/-- The `.kl` runner's layout: text at `0x100000`, labels `0` bytes, every
instruction `1`. -/
@[reducible] def xrLayout : _root_.Layout := Concrete.klLayout pilotXR 0x100000

instance xrValid : Executable.ValidLayout (xrLayout pilotXR) :=
  Concrete.validLayout_of_cells _ (by decide) (by decide)

/-- The end address: `27` instructions of `1` byte. -/
def endXR : Int64 := 0x100000 + 27

/-- Thread start: `rbx = &top` (`0x1000`), arena `[r14, r15)`, the link
`r11` the end of the text, `dmem` empty. -/
def threadXR (base : UInt64) : X64.State where
  exe := xrLayout pilotXR
  endPc := endXR
  st := ({ ({} : MachineData) with
    regs := (((({} : MachineData).regs.set64 .rbx 0x1000).set64 .r14 base.toBitVec).set64 .r15
      (base.toBitVec + 0x100)).set64 .r11 endXR.toBitVec }, 0x100000)

/-- `top = 0`; the link word of the first node of each arena `0`. -/
def initMemXR : List (Loc × Val) := [(⟨0x1000, 8⟩, 0), (⟨0x2000, 8⟩, 0), (⟨0x3000, 8⟩, 0)]

/-- The explorer under `Arch.tso`: per final configuration, each thread's
`(r12, r14)` (popped node, bumped arena pointer). -/
def exploreFinalsXR (o : ExploreOpts) : List (List (Nat × Nat)) × Bool × List String :=
  let r := explore Arch.tso (Config.init [threadXR 0x2000, threadXR 0x3000] initMemXR : Config isa)
    (fun c => c.threads.toList.map fun t =>
      ((t.st.st.1.regs.get64 .r12).toNat, (t.st.st.1.regs.get64 .r14).toNat)) o
  (r.finals, r.boundHit, r.faults)

/-- **The program terminates with the expected results** (`Arch.tso`, the
explorer's default options: no cap on promises): in every final configuration each thread popped one of the two
nodes (`0x2000`, `0x3000`), never `0`, the nodes are distinct, each arena
pointer moved by one node; no fault. -/
def pilotXRRun : List (List (Nat × Nat)) × Bool × List String :=
  exploreFinalsXR { fuel := 64 }

/-- info: ([[(12288, 8208), (8192, 12304)], [(8192, 8208), (12288, 12304)]], false, []) -/
#guard_msgs in
#eval pilotXRRun

/-! ## The static checks of the EnvG link -/

section Static

variable [layout : _root_.Layout]

/-- Every cell is a phase-1 tree (`leaq sym(%rip)`, `jmp *%r`, `ja`,
`lock cmpxchgq` included). -/
theorem pilotXR_phase1FX [Executable.ValidLayout (layout pilotXR)] : Phase1TreeFX (layout pilotXR) := by
  refine phase1TreeFX_of_dirs (dirsPhase1FX_layout fun d hd e z s pc => ?_)
  simp only [pilotXR, List.mem_cons, List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals simp only [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    _root_.RelRegOrMem.interp]
  cells_phase1FX

/-- No cell faults. -/
theorem pilotXR_noFault : DirsNoFault (layout pilotXR) := by dirs_no_fault pilotXR

end Static

end Kraken.Promising.Lower.PilotXR
