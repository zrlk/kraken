/-
**The hand-lowered two-thread Treiber client
on x64, with `call`/`ret` through a `dmem` stack.**

The x64 lowering of the first lowering pilot's `main`/`push`/`pop` (`Lower/PilotProg.lean`)
under the draft calling convention for x64 (arguments `rdi`, `rsi`; result `rax`;
callee-saved `rbx rbp r12 r13` and `rsp`; allocator bump/limit `r14`/`r15`;
the stack in `dmem`, 16-byte aligned at a call, no red zone):

- `main` is entered as if called by the runtime: `rsp` points at the slot
  holding the return address (the end of the text), so `rsp + 8` is 16-byte
  aligned. It realigns (`subq $8, %rsp`), allocates the node by an inline
  bump from `r14` with the `r15` limit check (`ja oom`), calls
  `push(rdi = &top, rsi = node)`, then `pop(rdi = &top)`, keeps the popped
  node in `r12` (the per-thread result the final check reads), restores
  `rsp` and returns. `&top` is in the callee-saved `rbx` (a global's address,
  set up by the runtime).
- `push` (leaf): `movq` of `top`, the link store (offset `0`, as in
  `LockFree/X64/treiber2.kl`), `lock cmpxchgq`, retry by `jne`.
- `pop` (leaf): `movq` of `top`, spin on empty (`je pop`, as in
  `treiber2.kl`; the x64 treiber2 VCs have no empty-return case), the link
  load through the loaded pointer, `lock cmpxchgq`, retry by `jne`; returns
  the node in `rax`.
- `call` pushes the return address into the `dmem` slot at `rsp - 8` and
  `ret` pops it: with the slots mapped, neither is a memory event.
- `oom: jmp oom`: x64 has no halting instruction in Kraken's syntax; the
  branch is proved never taken.
- `ret_pop:` names the return point behind `call pop`, so that the tail is
  its own block; the trailing `done:` makes the end of the text stuck.

Payload: the x64 treiber2 plan has no data word (`EnvG/X64Treiber2VC.lean`),
so unlike the first lowering pilot the node carries no payload; the final check is the popped
nodes only (`treiber2.kl`'s property).

Contents: `pilotX`; the `.kl`-runner layout `xLayout` (text at `0x100000`,
labels `0` bytes, instructions `1`); two concrete start states with a
24-byte stack in `dmem`; a `#guard_msgs` run of the Promising explorer under
`Arch.tso`; the static checks of the EnvG link (`Phase1TreeFX`,
`DirsNoFault`).
-/
import Kraken.Promising.SLR.EnvG.X64Treiber2Public
import Kraken.Promising.SLR.EnvG.ConcreteX64Layout

namespace Kraken.Promising.Lower.PilotX

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.EnvG
open Kraken.X64.Parser

/-- **The hand-lowered program** (one text, three functions). -/
def pilotX : Program := parse("
main:
    subq $8, %rsp
    movq %r14, %rsi
    addq $16, %r14
    cmpq %r15, %r14
    ja oom
    movq %rbx, %rdi
    call push
    movq %rbx, %rdi
    call pop
ret_pop:
    movq %rax, %r12
    addq $8, %rsp
    ret
oom:
    jmp oom
push:
    movq (%rdi), %rax
    movq %rax, (%rsi)
    lock cmpxchgq %rsi, (%rdi)
    jne push
    ret
pop:
    movq (%rdi), %rax
    testq %rax, %rax
    je pop
    movq (%rax), %rcx
    lock cmpxchgq %rcx, (%rdi)
    jne pop
    ret
done:
")

/-- info: 31 -/
#guard_msgs in
#eval pilotX.length

/-! ## The layout and two start states -/

/-- The `.kl` runner's layout: text at `0x100000`, labels `0` bytes, every
instruction `1`. -/
@[reducible] def xLayout : _root_.Layout := Concrete.klLayout pilotX 0x100000

instance xValid : Executable.ValidLayout (xLayout pilotX) :=
  Concrete.validLayout_of_cells _ (by decide) (by decide)

/-- The end address: `25` instructions of `1` byte. -/
def endX : Int64 := 0x100000 + 25

/-- The stack: `rsp` at entry. The 24 bytes `[0x7fe8, 0x8000)` are mapped:
the return-address slot `[rsp, rsp + 8)` and the two slots below it (`main`'s
alignment pad and the callees' return-address slot). -/
def sp0 : BitVec 64 := 0x7ff8

/-- The private memory at entry: the stack region, with the runtime's return
address `ra` at `rsp`. -/
def stack0 (ra : BitVec 64) : DataMem :=
  Mem.storeInt (Mem.storeInt ∅ (sp0 - 16) 16 0) sp0 8 ra.toInt

/-- Thread start: `rbx = &top` (`0x1000`), arena `[r14, r15)`, `rsp = sp0`
with the end address in its slot. -/
def threadX (base : UInt64) : X64.State where
  exe := xLayout pilotX
  endPc := endX
  st := ({ ({} : MachineData) with
    regs := (((({} : MachineData).regs.set64 .rbx 0x1000).set64 .r14 base.toBitVec).set64 .r15
      (base.toBitVec + 0x100)).set64 .rsp sp0
    dmem := stack0 endX.toBitVec }, 0x100000)

/-- `top = 0`; the link word of the first node of each arena `0`. -/
def initMemX : List (Loc × Val) := [(⟨0x1000, 8⟩, 0), (⟨0x2000, 8⟩, 0), (⟨0x3000, 8⟩, 0)]

/-- The explorer under `Arch.tso`: per final configuration, each thread's
`(r12, r14)` (popped node, bumped arena pointer). -/
def exploreFinalsX (o : ExploreOpts) : List (List (Nat × Nat)) × Bool × List String :=
  let r := explore Arch.tso (Config.init [threadX 0x2000, threadX 0x3000] initMemX : Config isa)
    (fun c => c.threads.toList.map fun t =>
      ((t.st.st.1.regs.get64 .r12).toNat, (t.st.st.1.regs.get64 .r14).toNat)) o
  (r.finals, r.boundHit, r.faults)

/-- **The program terminates with the expected results** (`Arch.tso`): in
every final configuration each thread popped one of the two nodes
(`0x2000`, `0x3000`), the nodes are distinct, each arena pointer moved by one
node; no fault. -/
def pilotXRun : List (List (Nat × Nat)) × Bool × List String :=
  exploreFinalsX { fuel := 64 }

/-- info: ([[(12288, 8208), (8192, 12304)], [(8192, 8208), (12288, 12304)]], false, []) -/
#guard_msgs in
#eval pilotXRun

/-! ## The static checks of the EnvG link -/

section Static

variable [layout : _root_.Layout]

/-- Every cell is a phase-1 tree (`call`, `ret`, `ja`, `lock cmpxchgq`
included). -/
theorem pilotX_phase1FX [Executable.ValidLayout (layout pilotX)] : Phase1TreeFX (layout pilotX) := by
  refine phase1TreeFX_of_dirs (dirsPhase1FX_layout fun d hd e z s pc => ?_)
  simp only [pilotX, List.mem_cons, List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals simp only [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    _root_.RelRegOrMem.interp]
  cells_phase1FX

/-- No cell faults. -/
theorem pilotX_noFault : DirsNoFault (layout pilotX) := by dirs_no_fault pilotX

end Static

end Kraken.Promising.Lower.PilotX
