import Scc.Emit.X64Func

/-!
# The x64 emitter

IR → GNU assembler, AT&T syntax, for a static Linux binary with no libc.

**Output.** The emitter builds a list of `Item`s (`Scc.Emit.X64Print`):
Kraken x64 `Directive`s for every instruction and label Kraken's syntax has,
and assembler directive lines for sections, symbols and data.  There are no
raw instruction lines: `syscall`, `ud2`, the `%fs:` moves of `getTp` and the
stack check (`Kraken/SYSCALL.md`), `divq`/`cqto`/`idivq` and `popcntq` are
Kraken directives.  `render` prints the list; `Scc/Emit/X64Test.lean` checks that
every item reads back as itself with Kraken's parser.

**Register allocation.**  Every IR register lives in its own 8-byte frame slot
below `%rbp`; each instruction loads its operands into scratch registers
(`%rax`, `%rcx`, `%rdx`, `%rsi`), computes, and stores the result back.  So no
IR register survives in a machine register across instructions, and calls
need no save/restore.

**Calling convention** (SysV-like, scc-internal): arguments in `%rdi`, `%rsi`,
`%rdx`, `%rcx`, `%r8`, `%r9`, then on the stack: argument `6 + j` at
`8j(%rsp)` at the call, so at `16+8j(%rbp)` in the callee, which copies it to
its slot in the prologue; results in `%rax`, `%rdx`, `%rcx`, `%rsi`,
`%rdi`, `%r8`.  The frame is `push %rbp; mov %rsp, %rbp; sub $F, %rsp` with
`F` a multiple of 16, so `%rsp` is 16-byte aligned at every call; its bottom
`8·outWords` bytes are the outgoing argument area, as large as the argument
area of any callee (`StackMap.argAreas`).  A tail call writes its stack
arguments over the function's own incoming area, which the argument areas
make large enough, so every tail call runs in constant stack.  The
prologue's stack check (when `Func.checkStack`) compares `%rsp - F` with the
TCB's stack limit at `%fs:8`, loaded into `%r11` first (Kraken's `%fs:`
operand is `mov` only; `%r11` is free there: it is neither an argument
register nor used anywhere else by the emitter); below it, the abort routine,
or (with `Program.growth`) the grow stub.

**Growable stacks** (`Scc.IR.StackMap`).  `%rbp` is the frame-record pointer
(`[%rbp]` the caller's `%rbp`, `[%rbp+8]` the return address).  The grow
stub of a function pushes the six argument registers (`%rdi` at
`-8(%rbp)` … `%r9` at `-48(%rbp)`; stack parameters are still at
`16+8j(%rbp)`, where the check's map designates them), passes `F` in `%rdi` to
`scc_rt_morestack`, pops the registers and repeats the check.  Every call is
followed by a local label, its safepoint, and the stack-map table lists the
slots `-8(k+1)(%rbp)` of the registers the map designates.  Frame slots are
addressed from `%rbp` only, and no other machine register holds a stack
address across a call, so a moved frame works once `%rbp` and the saved
`%rbp` values are rewritten.

**Thread pointer.**  `%fs` base = the TCB address; the TCB's first word is its
own address, so `getTp` is `mov %fs:0, %reg`.  `switchTo` sets it with
`arch_prctl(ARCH_SET_FS)`, and `clone` with `CLONE_SETTLS`.

**Division.**  `div`/`idiv` fault on a zero divisor and on `-2^63 / -1`; the
emitter branches around both to produce the IR's results (`x / 0 = 0`,
`x % 0 = x`, `-2^63 / -1 = -2^63`, `-2^63 % -1 = 0`).

**Bit counts.**  `ctz` is `tzcntq` (BMI1, which Kraken assumes; it gives 64
on a zero source); `popcnt` is `popcntq`.

**Sub-word loads.**  An 8- or 16-bit load is a narrow `mov` into `%al`/`%ax`
followed by a register `movzbl`/`movzwl` (one memory access, the same as a
`movz*` with a memory source, which Kraken's parser does not read).

**Threads.**  A `clone` passes its argument in `%r12` and the `spawnReg`s
in `%rbx`, `%r13`, `%r14`, `%r15`, `%r9` (`spawnArgs`; the `clone` system
call keeps every register but `%rax`, `%rcx`, `%r11`), and the child jumps
(`jz`) to the function's child stub of the entry (`childL`, after the
function's code), which zeroes `%rbp`, moves them into the argument
registers and calls the entry.

**Fences.**  Under TSO, `Fence.ld` and `Fence.st` need no code; `Fence.full`
is `mfence`.  Acquire loads and release stores are plain `mov`s.

This emitter is not verified; the certificates re-parse its output.
-/

namespace Scc.Emit.X64
open Scc.IR
/-- `--host raw`: the kernel routine trampolines, one per slot of
`Tcb.kabiSlots` in slot order, between the global labels `Tcb.kabiStartSym`
and `Tcb.kabiEndSym`. The trampoline `scc_rt_X` of slot `n` loads the
routine table's address from the TCB (`movq %fs:96, %r11`, `Tcb.kabi`) and
jumps through the slot (`jmp *8n(%r11)`): the routine returns to the
trampoline's caller. `%r11` is free at every call (caller-saved, no
argument). -/
def emitKabi : E Unit := do
  dir s!".globl {Tcb.kabiStartSym}"
  lbl Tcb.kabiStartSym
  for (f, n) in Tcb.kabiSlots do
    dir s!".type {f}, @function"
    lbl f
    movFs .r11 Tcb.kabi
    ins (i64 (.jmp (.mem (mem .r11 (8 * n)))))
    dir s!".size {f}, .-{f}"
  dir s!".globl {Tcb.kabiEndSym}"
  lbl Tcb.kabiEndSym

/-- **`--host raw`: the trampolines precede every block entry.** Every label of `its` before
`Tcb.kabiEndSym` is `scc_text_start`, `Tcb.kabiStartSym` or a trampoline's symbol: no
function or block label (no block entry of the tables) lies before the end of the
trampolines, which the tables reader's rule for them relies on (no block entry at or below
their addresses). Fails without `Tcb.kabiEndSym`. -/
def kabiFirst (its : List Item) : Except String Unit := do
  let ls := its.filterMap fun | .d (.label l) => some l | _ => none
  unless ls.contains Tcb.kabiEndSym do throw s!"--host raw: no {Tcb.kabiEndSym}"
  let ok := [StackMap.textStartSym, Tcb.kabiStartSym] ++ Tcb.kabiSlots.map (·.1)
  match (ls.takeWhile (· != Tcb.kabiEndSym)).find? (!ok.contains ·) with
  | some l => throw s!"--host raw: label {l} precedes {Tcb.kabiEndSym}"
  | none => pure ()

/-- The header. `--host linux`: `_start`, which aligns the stack and calls
`Program.start`. `--host raw`: the kernel routine trampolines (`emitKabi`);
the kernel enters `Program.start` itself. -/
def emitHead (p : IR.Program) : E Unit := do
  match p.host with
  | .linux =>
    item (.comment "Generated by scc (x86-64, AT&T syntax, Linux, no libc).")
    dir ".text"
    dir ".globl _start"
    lbl StackMap.textStartSym
    dir ".type _start, @function"
    lbl "_start"
    zero32 .rbp
    ins (i64 (.and (xr .rsp) (oi (-16))))
    callSym p.start
    ud2
  | .raw =>
    item (.comment "Generated by scc (x86-64, AT&T syntax, raw ABI, no libc).")
    dir ".text"
    lbl StackMap.textStartSym
    emitKabi

/-- After the functions: the trampoline (with `IR.Program.growth`), the
data, the stack-map table (with `IR.Program.growth`; the safepoints are
the state's). -/
def emitTail (p : IR.Program) : E Unit := do
  if let some g := p.growth then emitMorestack g
  lbl StackMap.textEndSym
  item .blank
  -- `.data` and `.bss` start 16-aligned (`Data.Secs.ofProgram`).
  dir ".data"
  dir ".balign 16"
  dir ".bss"
  dir ".balign 16"
  for d in p.data do emitData d
  if p.growth.isSome then emitMaps
  item .blank
  dir ".section .note.GNU-stack,\"\",@progbits"

/-- The items of a program's assembly file from its functions' items and
safepoints `rs`, in order, and the safepoints (`emitItemsMaps`): the
header, the functions, then the rest (`emitTail`). -/
def emitPost (p : IR.Program) (rs : List (List Item × List Map)) :
    Except String (List Item × List Map) := do
  let ms := rs.flatMap (·.2)
  let ((), h) ← (emitHead p).run {}
  let ((), t) ← (emitTail p).run { maps := ms.reverse }
  pure (h.out.reverse ++ rs.flatMap (·.1) ++ t.out.reverse, ms)

/-- The items of a program's assembly file, and the safepoints recorded
(label, stack offsets, heap offsets, in emission order): the checks
(`emitPre`), the functions (`emitFuncs`: each from a fresh state, its local
labels numbered from 0), then the rest (`emitPost`). A certificate
checks the parts separately (`emitItemsMaps_of_stages`). -/
def emitItemsMaps (p : IR.Program) : Except String (List Item × List Map) := do
  let areas ← emitPre p
  let rs ← emitFuncs p areas p.funcs 0
  emitPost p rs

/-- **`emitItemsMaps` from its stages**: the checks give the argument areas
`areas`, the functions their items and safepoints `rs` (chained with
`emitFuncs_cons`), and the rest the result. -/
theorem emitItemsMaps_of_stages {p : IR.Program} {areas : List (Sym × Nat)}
    {rs : List (List Item × List Map)} {r : List Item × List Map}
    (h1 : emitPre p = .ok areas) (h2 : emitFuncs p areas p.funcs 0 = .ok rs)
    (h3 : emitPost p rs = .ok r) : emitItemsMaps p = .ok r := by
  unfold emitItemsMaps
  rw [h1]
  show (emitFuncs p areas p.funcs 0 >>= emitPost p) = _
  rw [h2]
  exact h3

/-- The items of a program's assembly file. -/
def emitItems (p : IR.Program) : Except String (List Item) :=
  (·.1) <$> emitItemsMaps p

/-- The data sections of a program's assembly file as data images
(`Scc.Emit.Data`): what `emitData` and `emitMaps` write. -/
def dataSecs (p : IR.Program) : Except String Data.Secs := do
  let (_, ms) ← emitItemsMaps p
  pure (Data.Secs.ofProgram p.data (if p.growth.isSome then some ms else none))

/-- The assembly text of a program. -/
def emit (p : IR.Program) : Except String String := do
  render (← emitItems p)

end Scc.Emit.X64
