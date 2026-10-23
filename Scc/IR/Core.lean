/-!
# The scc intermediate representation

A small, first-order IR between WeakCore terms and assembly.  `Scc.Lower`
produces it from an accepted WeakCore program (together with the runtime:
allocator, `print` loop, `park`/`unpark`, thread start, abort routine, all
written in this IR); the emitters `Scc.Emit.X64` and `Scc.Emit.A64` turn it
into GNU assembler.  This file is the contract between the two halves: every
constructor documents what an emitter must produce for it.

The IR is not trusted (the certificates re-parse the emitted assembly),
so this file contains definitions only.

## Shape

* A `Program` is a list of `Func`s and `Data` items.
* A `Func` has named parameters and a list of `Block`s; the first block is the
  entry.  Each `Block` is a straight-line list of `Inst`s ended by one `Term`.
* Registers (`Reg`) are **named, function-local, mutable 64-bit variables**
  (the IR is not SSA).  A register may be assigned in several blocks.  The
  emitter allocates them (spilling every register to a frame slot is a valid
  allocation).  Reading a register that was never assigned on the path taken
  is a lowering bug; the emitter may give it any value.
* Every value is a 64-bit word.  Operations are on full 64-bit words with
  wrap-around; narrower WeakCore types are kept zero-extended by the lowering,
  which inserts `ext` where it needs a truncation or a sign extension.
* Labels (`Label`) are function-local; the emitter mangles them (for instance
  `.L<func>.<label>`).  Function and data names (`Sym`) are assembler symbols
  used verbatim; the lowering keeps them valid (letters, digits, `_`, `.`).

## Calling convention (both targets)

`call`/`tail`/`ret` follow a SysV-like (x64) or AAPCS64-like (AArch64)
convention chosen by the emitter; the IR only fixes the counts: at most
`maxArgs` arguments and at most `maxRets` results.  The first arguments go in
registers (x64: six, `%rdi`, `%rsi`, `%rdx`, `%rcx`, `%r8`, `%r9`; AArch64:
eight, `x0`–`x7`; every target has at least `maxRegArgs`), the rest in the
caller's **outgoing area**: argument word `k + j` (`k` the target's register
count) at `[sp + 8·j]` at the call, `sp` 16-byte aligned, so the callee finds
it at `16 + 8·j` above its frame record.  The callee copies every stack
argument into its own frame in the prologue; the outgoing words are dead after
that (so no stack map lists them past the prologue; the prologue check's map
lists the live ones in place, `Scc.IR.StackMap`).  A `tail` with stack
arguments writes them over the function's own incoming area; the emitters
size that area per `tail`-connected group of functions, and every call of
one of them reserves it (`StackMap.argAreas`), so a `tail` is always a jump
in constant stack, whatever its argument count.
`site` and `clone` take register arguments only (at most `maxRegArgs`), and
spawned blocks take at most `maxSpawnArgs` words (the TCB's argument area).
All registers are
caller-saved from the IR's point of view: the emitter must make every IR
register of the caller hold the same value after a `call` as before (other
than the result registers), for instance by keeping registers in frame slots.

Stack frames live on the thread's stack, whose lowest usable address is the
`Tcb.stackLimit` word of the current thread's TCB.  When `Func.checkStack` is
set, the prologue compares the new stack pointer with that limit.  Below it,
if the program has no `Program.growth`, the prologue calls `Program.abortFn`
with `AbortKind.stack`; otherwise it calls the grow routine, which moves the
whole stack to a larger range, and checks again (see `Scc.IR.StackMap` for
the protocol, the frame records and the stack maps it relies on).  The
lowering keeps at least `Tcb.headroom` bytes of stack below the limit, and
`Program.abortFn`, the grow routine and everything they call have
`checkStack` unset, so those paths always fit.

## Stack addresses

`Inst.slotAddr` is the only source of stack addresses.  Registers that may
hold one are listed in `Func.stackRegs`; the stack maps let the grow routine
rewrite them when the stack moves.  **Stack addresses never escape the
thread**: they are never stored to memory, passed to a system call or to
`clone`, returned, or passed in a tail call, and they flow only into
registers of `Func.stackRegs` (including the matching parameters of a
callee).  `StackMap.check` checks this on every program the emitters accept.
WeakCore programs have no stack addresses, so the term lowering produces
none; the invariant is what keeps a future lowering of frame locatives sound.
-/

namespace Scc.IR

/-- A function-local virtual register: a mutable 64-bit variable. -/
abbrev Reg := String

/-- A function-local block label. -/
abbrev Label := String

/-- An assembler symbol: the name of a `Func` or a `Data` item. -/
abbrev Sym := String

/-- At most this many arguments to a `call`, `tail` or function (the
calling convention above passes those past the target's register count on
the stack). -/
def maxArgs : Nat := 32

/-- Arguments every target passes in registers: the most a `site` or a
`clone` entry takes. -/
def maxRegArgs : Nat := 6

/-- At most this many argument words of a spawned block (they travel in the
child's TCB, whose argument area the pinned region reserves per thread). -/
def maxSpawnArgs : Nat := 6

/-- At most this many results of a `ret` or a `call`. -/
def maxRets : Nat := 6

/-- Access widths of memory operations.  Loads zero-extend to 64 bits; stores
write the low bytes.  Addresses of a width-`n` access must be `n`-aligned.

Sub-word stores are the lowering's responsibility: a WeakCore sub-word store
(`stl`/`stlw`, outside the current fragment) is only correct on a location
the thread owns, and Kraken's AArch64 lowering conditions forbid sub-word
stores to shared memory.  The lowering of the current fragment emits `w64`
stores only (every WeakCore cell is a 64-bit word); emitters need not
special-case narrower stores beyond printing them. -/
inductive Width
  | w8 | w16 | w32 | w64
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The width in bytes. -/
def Width.bytes : Width → Nat
  | .w8 => 1 | .w16 => 2 | .w32 => 4 | .w64 => 8

/-- The width in bits. -/
def Width.bits (w : Width) : Nat := 8 * w.bytes

/-- Memory order of a load or a store.  `acq` is meaningful on loads only and
`rel` on stores only (the lowering never produces the other combinations; an
emitter may reject them).  x64: every order is a plain `mov`.  AArch64:
`plain` is `ldr`/`str`, `acq` is `ldar`, `rel` is `stlr`. -/
inductive Order
  | plain | acq | rel
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Fences.  `ld`: earlier loads before later loads and stores; `st`: earlier
stores before later stores; `full`: everything.  x64: `ld`/`st` are no code,
`full` is `mfence`.  AArch64: `dmb ishld`, `dmb ishst`, `dmb ish`. -/
inductive Fence
  | ld | st | full
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Binary operations on 64-bit words, wrapping.  Division by zero is defined:
`udiv x 0 = sdiv x 0 = 0`, `urem x 0 = srem x 0 = x`; `sdiv (-2^63) (-1) = -2^63`
and `srem (-2^63) (-1) = 0` (the AArch64 results; an x64 emitter must branch
around `div`/`idiv` in those cases).  Shifts take the amount modulo 64.
`umulh` is the high word of the unsigned 128-bit product. -/
inductive BinOp
  | add | sub | mul | umulh
  | udiv | sdiv | urem | srem
  | and | or | xor
  | shl | lshr | ashr
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Unary operations on 64-bit words.  `ctz 0 = 64`. -/
inductive UnOp
  | not | neg | ctz | popcnt
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Comparisons of two 64-bit words, unsigned (`u…`) or signed (`s…`). -/
inductive Cond
  | eq | ne | ult | ule | ugt | uge | slt | sle | sgt | sge
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Atomic read-modify-write operations (`rmw`).  Both are sequentially
consistent: x64 `xchg` / `lock xadd`; AArch64 FEAT_LSE `swpal` / `ldaddal`. -/
inductive RmwOp
  | xchg | add
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The Linux system calls the runtime uses through `Inst.syscall`.  Their
numbers are per architecture (`Sys.nrX64`, `Sys.nrA64`).  `clone` and the
thread-pointer set-up are not here: they are `Inst.clone` and
`Term.switchTo`, which need code around the call. -/
inductive Sys
  | write | exit | exitGroup | futex | rtSigaction
  deriving Repr, BEq, DecidableEq, Inhabited

/-- x86-64 Linux system call numbers. -/
def Sys.nrX64 : Sys → Nat
  | .write => 1 | .exit => 60 | .exitGroup => 231 | .futex => 202 | .rtSigaction => 13

/-- AArch64 Linux system call numbers (the generic table). -/
def Sys.nrA64 : Sys → Nat
  | .write => 64 | .exit => 93 | .exitGroup => 94 | .futex => 98 | .rtSigaction => 134

/-- Flags of the `clone` system call behind `Inst.clone`:
`CLONE_VM | CLONE_FS | CLONE_FILES | CLONE_SIGHAND | CLONE_THREAD |
CLONE_SYSVSEM | CLONE_SETTLS`, and no `CLONE_*TID` flag (the kernel never
writes to user memory on the thread's behalf). -/
def cloneFlags : Nat := 0x100 ||| 0x200 ||| 0x400 ||| 0x800 ||| 0x10000 ||| 0x40000 ||| 0x80000

/-- The reasons for the distinguished abort outcome.  `Program.abortFn` takes
the `code` as its one argument; it writes a message to fd 2 and exits the
process with `abortExitCode`. -/
inductive AbortKind
  | overflow  -- a checked `Int` addition overflowed 2^64
  | heap      -- the heap arena is exhausted
  | stack     -- a frame does not fit and the stack cannot grow (no grow
              -- routine, per-thread cap reached, or stack pool exhausted)
  | write     -- `write` returned 0 or an error other than `EINTR`/`EAGAIN`
  | threads   -- a thread could not be created: the thread cap reached, no
              -- heap for its TCB, or `clone` failed
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The argument passed to `Program.abortFn`. -/
def AbortKind.code : AbortKind → Nat
  | .overflow => 1 | .heap => 2 | .stack => 3 | .write => 4 | .threads => 5

/-- The kind's name (the runtime's per-kind abort routine is
`scc_rt_abort_<name>`). -/
def AbortKind.name : AbortKind → String
  | .overflow => "overflow" | .heap => "heap" | .stack => "stack" | .write => "write"
  | .threads => "threads"

/-- The process exit status of the abort outcome. -/
def abortExitCode : Nat := 101

/-! The thread control block (TCB) layout: byte offsets of its 64-bit words.
The thread pointer (x64 `%fs` base, AArch64 `TPIDR_EL0`) holds the TCB's
address; a `ThreadId` is that address. -/
namespace Tcb
/-- The TCB's own address (lets x64 read the thread pointer as `%fs:0`). -/
def self : Nat := 0
/-- The lowest address the thread's stack may use. -/
def stackLimit : Nat := 8
/-- The `park` permit (0 or 1); also the futex word. -/
def permit : Nat := 16
/-- Set to 1 (release store) when the thread has finished. -/
def exited : Nat := 24
/-- The lowest address of the thread's current stack range (used by the grow
routine; `stackLimit` is `stackBase + headroom`). -/
def stackBase : Nat := 32
/-- One past the highest address of the thread's current stack range. -/
def stackTop : Nat := 40
/-- Reserved for the loaded-value barrier's bad-bit mask (always 0 under
`gc none`; `Scc/LAYOUT.md`). -/
def badMask : Nat := 48
/-- The thread's index (0 for the main thread, `scc_rt_thread_reserve`'s
result for a spawned one).  A `ThreadId` is the TCB's address; the index is
kept here for the runtime. -/
def index : Nat := 56
/-- The thread's depth counter: the calls of code blocks it is in (each
`let x = f(a)` adds one while `f` runs; tail calls and runtime calls none),
0 when the thread starts (the pinned region is zero-filled and never
reused).  Only the owning thread accesses it (`Lower.callBlock`). -/
def depth : Nat := 64
/-- The size of a TCB in bytes (a spawned thread's argument words follow). -/
def size : Nat := 72
/-- Bytes of stack reserved below `stackLimit` for the paths that run without
a stack check: the abort routine, and the grow routine with the pool
operations it calls (it runs on the old stack, below the frame that did not
fit). -/
def headroom : Nat := 4096
end Tcb

/-- An instruction operand: a register or a 64-bit immediate. -/
inductive Operand
  | reg (r : Reg)
  | imm (v : UInt64)
  deriving Repr, BEq, Inhabited

/-- A memory address: register plus a signed byte displacement. -/
structure Addr where
  base : Reg
  disp : Int := 0
  deriving Repr, BEq, Inhabited

/-- Straight-line instructions.  `d` is always the destination register. -/
inductive Inst
  /-- `d := s`. -/
  | mov (d : Reg) (s : Operand)
  /-- `d := a op b` (`BinOp`). -/
  | bin (op : BinOp) (d : Reg) (a b : Operand)
  /-- `d := op a` (`UnOp`). -/
  | un (op : UnOp) (d : Reg) (a : Operand)
  /-- `d := ` the low `w` bits of `a`, zero-extended (`signed = false`) or
  sign-extended (`signed = true`) to 64 bits. -/
  | ext (signed : Bool) (w : Width) (d : Reg) (a : Operand)
  /-- `d := if a c b then 1 else 0`. -/
  | setc (c : Cond) (d : Reg) (a b : Operand)
  /-- `d := if a c b then t else f`. -/
  | select (c : Cond) (d : Reg) (a b : Operand) (t f : Operand)
  /-- Checked unsigned addition: `d := a + b`; if the sum is `≥ 2^64`, call
  `Program.abortFn` with `AbortKind.overflow` instead (the abort edge). -/
  | addChk (d : Reg) (a b : Operand)
  /-- Saturating unsigned subtraction: `d := if a ≥ b then a - b else 0`. -/
  | subSat (d : Reg) (a b : Operand)
  /-- `d := ` the address of the data item or function `s`. -/
  | la (d : Reg) (s : Sym)
  /-- `d := ` the thread pointer, the current thread's TCB address. -/
  | getTp (d : Reg)
  /-- `d := ` the width-`w` value at `a`, zero-extended, with order `o`. -/
  | load (o : Order) (w : Width) (d : Reg) (a : Addr)
  /-- Store the low `w` bits of `v` at `a`, with order `o`. -/
  | store (o : Order) (w : Width) (a : Addr) (v : Operand)
  /-- Atomic 64-bit read-modify-write at `a`: `d := old`, memory gets `v`
  (`xchg`) or `old + v` (`add`). -/
  | rmw (op : RmwOp) (d : Reg) (a : Addr) (v : Operand)
  /-- A fence. -/
  | fence (f : Fence)
  /-- `ds := f(args)`: a call; `ds` receives the first `ds.length` results. -/
  | call (ds : List Reg) (f : Sym) (args : List Operand)
  /-- `d := ` the raw Linux system call `nr` with up to six arguments (the
  kernel's return value: a result, or `-errno` as a 64-bit word).  With
  `lbl = some l`, the emitters place the symbol `l` directly on the trap
  instruction itself (AArch64 `svc`, x64 `syscall`), after the argument and
  number moves; the abort routines label their `exit_group` this way. -/
  | syscall (d : Reg) (nr : Sys) (args : List Operand) (lbl : Option Sym := none)
  /-- Start a thread: `clone(cloneFlags, stack, …, tls)`.  The parent gets the
  kernel's return value (a thread id or `-errno`) in `d`.  The child starts
  with stack pointer `stack` (16-byte aligned, the top of its stack range),
  thread pointer `tls`, and calls `entry(arg)`; `entry` never returns (it ends
  in `Sys.exit`).  The child does not touch the parent's frame. -/
  | clone (d : Reg) (stack tls : Operand) (entry : Sym) (arg : Operand)
  /-- `d := ` the address of the frame slot of register `s` (a stack address;
  `d` must be in `Func.stackRegs` and `s` must not be).  Taking the address
  pins `s` to its slot: the emitter keeps `s` in that 8-byte slot for the
  whole function (every read of `s` reads it, every write writes it), so a
  64-bit `load` or `store` through `d` reads or writes `s`.  The address is
  valid until the function returns or tail-calls, and moves with the stack
  (`StackMap`). -/
  | slotAddr (d s : Reg)
  /-- A named program point: put `args` in the first argument registers (as
  for a `call`), then place the symbol `s` as a label on a `nop`.  It has no
  other effect.  A specification names the point by `s`, and finds the
  arguments in those registers when the `nop` runs; `s` must be placed once
  in the program. -/
  | site (s : Sym) (args : List Operand)
  /-- A comment carried into the assembly (no code). -/
  | comment (s : String)
  deriving Repr, BEq, Inhabited

/-- Block terminators. -/
inductive Term
  /-- Return the results `vs` (at most `maxRets`). -/
  | ret (vs : List Operand)
  /-- Jump to a block of the same function. -/
  | jmp (l : Label)
  /-- `if a c b then goto t else goto f`. -/
  | br (c : Cond) (a b : Operand) (t f : Label)
  /-- Tail call: `f(args)` replaces the current frame; its results are the
  current function's results. -/
  | tail (f : Sym) (args : List Operand)
  /-- Set the thread pointer to `tls` (x64 `arch_prctl(ARCH_SET_FS)`,
  AArch64 `msr tpidr_el0`), set the stack pointer to `stack` (16-byte
  aligned), and call `f(arg)`, which never returns.  Used once, by the
  program's start routine, to move the main thread onto its own stack. -/
  | switchTo (stack tls : Operand) (f : Sym) (arg : Operand)
  /-- Control never reaches here (after a call to a function that does not
  return).  The emitter may emit a trap or nothing. -/
  | unreachable
  deriving Repr, BEq, Inhabited

/-- A basic block. -/
structure Block where
  label : Label
  insts : List Inst
  term : Term
  deriving Repr, BEq, Inhabited

/-- A function.  The first block is the entry; `params` are assigned the
arguments on entry. -/
structure Func where
  name : Sym
  params : List Reg
  blocks : List Block
  /-- Emit the stack-limit check in the prologue (see the module docstring). -/
  checkStack : Bool := true
  /-- The registers that may hold stack addresses (`Inst.slotAddr`); the stack
  maps list their slots, which the grow routine rewrites when the stack
  moves.  See "Stack addresses" in the module docstring for the rules. -/
  stackRegs : List Reg := []
  /-- The registers that hold trace words (`Obj.traceMask`: references,
  locative bases and `ThreadId`s; addresses in the heap arena or the pinned
  region, or 0).  Recorded in the stack maps for a future moving collector;
  nothing reads them yet. -/
  heapRegs : List Reg := []
  /-- The registers the lowering knows hold scalar words (scalars and
  locative offset words).  Only checks read it: no register is in both
  lists, and every register live across a safepoint of a lowered block is in
  one of them (`Scc/Test/StackTest.lean`). -/
  scalarRegs : List Reg := []
  deriving Repr, BEq, Inhabited

/-- The contents of a data item. -/
inductive DataInit
  /-- `n` zero bytes (`.bss`). -/
  | zero (n : Nat)
  /-- The given bytes (`.data`; writable, see the decisions on static data). -/
  | bytes (bs : List UInt8)
  deriving Repr, BEq, Inhabited

/-- A data item: a symbol, its alignment in bytes (a power of two), its contents. -/
structure Data where
  name : Sym
  align : Nat := 8
  init : DataInit
  deriving Repr, BEq, Inhabited

/-- The runtime routines behind growable stacks (`StackMap` has the protocol).

* `grow(fp, need)`: called (through the emitter's trampoline
  `StackMap.morestackSym`, with `checkStack` unset, on the old stack) when a
  prologue check fails.  `fp` is the address of the trampoline's frame record,
  the lowest live word of the stack; `need` is the frame size of the function
  whose check failed.  It takes a larger range, copies `[fp, stackTop)` to
  the top of it, rewrites the stack addresses the frame records and the stack
  maps designate, updates the TCB's `stackBase`, `stackTop` and `stackLimit`,
  and returns `(delta, oldBase, oldBytes)`: the distance the stack moved
  (`new address - old address`) and the old range.  It never returns if the
  stack cannot grow (abort `AbortKind.stack`).
* `release(base, bytes)`: gives a range back to the pool.  The trampoline
  calls it after it has moved onto the new range. -/
structure Growth where
  grow : Sym
  release : Sym
  deriving Repr, BEq, Inhabited

/-- A whole program.  The emitter writes `_start`, which jumps to `start`
(with the stack pointer the kernel provides, 16-byte aligned, and no
arguments); `start` never returns. -/
structure Program where
  funcs : List Func
  data : List Data
  /-- The process entry routine (no parameters, never returns). -/
  start : Sym
  /-- The abort routine: one parameter, an `AbortKind.code`; never returns. -/
  abortFn : Sym
  /-- Growable stacks: when set, a failed prologue check grows the stack
  instead of aborting, and the emitter writes the stack-map table
  (`StackMap.tableSym`) and the trampoline (`StackMap.morestackSym`). -/
  growth : Option Growth := none
  deriving Repr, BEq, Inhabited

end Scc.IR
