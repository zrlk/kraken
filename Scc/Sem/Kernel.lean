/-
The kernel model of the canonical targets (`Scc/DESIGN.md` §3).

Linux system calls as steps of the extended machine (`Hooks`,
`Scc/Sem/Target.lean`): what the kernel does when a thread of the program
stops at `svc #0` (AArch64) or `syscall` (x64). Kraken's instruction step
halts there (`MachineData.pendingSyscall`, `Kraken/SYSCALL.md`); the
extended machine gates that thread's instruction steps (`Hooks.atSys`) and
steps it with the definitions here instead.

**Trusted.** This file is part of the trusted base (`Scc/DESIGN.md` §4):
every assumption the canonical targets make about the kernel is one of the
named definitions below, and nothing else in `Scc/Sem` gives a system call a
meaning. The ISA-specific glue (`A64.abi`, `X64.abi` in the target files)
reads and writes the registers this file names and adds no behaviour.

- Linux constants: `eintr`, `eagain`, `enomem`, `maxErrno`, `futexWaitPrivate`,
  `futexWakePrivate`, `sigpipe`, `sigsetSize`, `archSetFs`, `cloneFlags`,
  `abortStatus`, `pidMax`; the system-call numbers `Nrs.a64`, `Nrs.x64`.
- `decode` (K1): the supported calls and arguments; anything else is a
  fault (`faultAt`).
- `Abi` (K1): what the kernel reads and writes in a thread state.
- `KState`: the kernel's state (thread slots, exit record, stack pool and
  the stack ranges held, the pool's bytes, the mapped regions). The number of thread slots is a parameter
  (`KState.init n`, `hooks A n`): the canonical targets take it from the
  certificate (`CertCfg.slots`).
- `readByte` (K2, K3): how the kernel reads a byte of a `write` buffer.
- `sysStep` (K3–K5, K7–K9, K6c): every system call but a successful
  `clone`, one step at a time; `spawnStep` (K6): `clone`.
- `takeStep`, `releaseStep`, `fresh` (§2.6): at the runtime's transfer
  sites (`XferKind`), the range the thread's registers name moves from the
  pool into its private memory or back, with its bytes; `spawnStep` moves
  the child's stack range from the parent to the child; `stackRangeOf`: the
  held range a thread is on (`onStack`).
- `faultAt`: unsupported calls (K1), `clone` with every slot used (K6b),
  and threads halted off their exit path; `mapped`, `unmappedAt` (K11): a
  shared access outside the mapped regions (`SIGSEGV`) is a fault too.
- `results`, `certSuccs`, `certExec`: what each call may return to the
  calling thread, and the certification semantics built from it (the ISA's
  `exec` but at a supported system call, a choice among the states the
  kernel model may resume the thread in); `CertAfter`: the calling thread is
  certified under `certExec` after a kernel step.
- `soloExec`, `certSem` (with `solo`, `soloHeld`, `siteAt`, `svcDeps`,
  `certDeps`): certification as the solo projection of the kernel step: at
  a transfer site and at a supported system call, the states `xferStep` and
  `sysStep` of the thread run alone may leave it in, with the kernel's
  register dependencies at a system call; `clone` and `write` end a
  certifying run (no branch).
- `hooks`: the extension hooks of the canonical targets. A kernel step
  (`sys`, `spawn`) requires `CertAfter`, and certification
  (`Hooks.cexec`) is `certExec`; `ready` admits threads with outstanding
  promises.

Sanity lemmas: `fault_of_unsupported`, `fault_clone_full`, `sys_cloneErr`, `sys_exitGroup`,
`sys_writeByte`, `sys_writeRet`, `spawn_clone`, `spawn_clone_stack`,
`sysStep_ret_shape`, `sysStep_ret_mem`, `spawnStep_ret_mem` (each result a
step returns is one `certExec` allows, but the parent's stack-range erasure
at `clone`; the certification step matching a return is
`certSem_step_of_sysStep`, `Scc/Sem/CertStep.lean`; `certSem` has no step
at `clone` and `write`),
`xfer_det`, `xfer_take`, `take_bytes`, `release_bytes`,
`release_take_handoff`, `step_at_take`, `fault_of_unmapped`,
`unmappedAt_of_root`; per ISA the target files check a
`write(1, buf, 1); exit_group(0)` program end to end, `clone` (refused,
and with and without a stack range), and take, release and re-take of a
range at the transfer sites, which accesses are unmapped, and which stores
after a system call certification admits.
-/
import Scc.Sem.Target

namespace Scc.Sem.Kernel

open Kraken.Promising

/-! ## Linux constants -/

/-- `EINTR`: interrupted system call. -/
def eintr : Nat := 4

/-- `EAGAIN`: try again. -/
def eagain : Nat := 11

/-- `ENOMEM`: out of memory. -/
def enomem : Nat := 12

/-- The largest error number: a return value in `[-maxErrno, -1]` is
`-errno`. -/
def maxErrno : Nat := 4095

/-- `FUTEX_WAIT | FUTEX_PRIVATE_FLAG`. -/
def futexWaitPrivate : Nat := 128

/-- `FUTEX_WAKE | FUTEX_PRIVATE_FLAG`. -/
def futexWakePrivate : Nat := 129

/-- `SIGPIPE`. -/
def sigpipe : Nat := 13

/-- The size of the kernel's signal set, the last argument of
`rt_sigaction`. -/
def sigsetSize : Nat := 8

/-- `ARCH_SET_FS`, the `arch_prctl` code that sets the `%fs` base (x64). -/
def archSetFs : Nat := 0x1002

/-- The one `clone` flag set supported (K6): `CLONE_VM | CLONE_FS |
CLONE_FILES | CLONE_SIGHAND | CLONE_THREAD | CLONE_SYSVSEM | CLONE_SETTLS`,
no `CLONE_*TID` flag (the kernel never writes user memory for the thread,
K0). -/
def cloneFlags : Nat := 0x100 ||| 0x200 ||| 0x400 ||| 0x800 ||| 0x10000 ||| 0x40000 ||| 0x80000

/-- The exit status of the abort stubs: an `exit_group` with this status (mod
256) may be reported as an abort (`sysStep`), if `Step.sys` finds the thread
at an abort site. -/
def abortStatus : Nat := 101

/-- Thread ids are below `PID_MAX_LIMIT` (2^22). -/
def pidMax : Nat := 4194304

/-- `-e` as a 64-bit return value. -/
def neg (e : Nat) : BitVec 64 := -BitVec.ofNat 64 e

/-! ## System calls -/

/-- **System-call numbers** of one ISA, and the places of `clone`'s
`child_tid` and `tls` arguments (they differ between the ISAs). -/
structure Nrs where
  write : Nat
  exit : Nat
  exitGroup : Nat
  futex : Nat
  rtSigaction : Nat
  clone : Nat
  /-- `arch_prctl` (x64 only). -/
  archPrctl : Option Nat
  cloneCtid : Fin 6
  cloneTls : Fin 6

/-- AArch64 Linux (the generic table); `clone(flags, stack, ptid, tls,
ctid)`. -/
def Nrs.a64 : Nrs :=
  { write := 64, exit := 93, exitGroup := 94, futex := 98, rtSigaction := 134, clone := 220,
    archPrctl := none, cloneCtid := 4, cloneTls := 3 }

/-- x86-64 Linux; `clone(flags, stack, ptid, ctid, tls)`. -/
def Nrs.x64 : Nrs :=
  { write := 1, exit := 60, exitGroup := 231, futex := 202, rtSigaction := 13, clone := 56,
    archPrctl := some 158, cloneCtid := 3, cloneTls := 4 }

/-- A supported system call with its arguments. -/
inductive Call where
  /-- `write(fd, buf, n)`, `fd ∈ {1, 2}` (K3). -/
  | write (fd buf n : Nat)
  /-- `exit(code)`: the calling thread ends (K4). -/
  | exit
  /-- `exit_group(v)`: the process ends (K5). -/
  | exitGroup (v : Nat)
  /-- `futex(addr, FUTEX_WAIT_PRIVATE, val, NULL)` (K7). -/
  | futexWait
  /-- `futex(addr, FUTEX_WAKE_PRIVATE, n)` (K7). -/
  | futexWake (n : Nat)
  /-- `rt_sigaction(SIGPIPE, act, NULL, 8)` (K8). -/
  | rtSigaction
  /-- `clone(cloneFlags, stack, 0, tls, 0)` (K6). -/
  | clone (stack tls : Nat)
  /-- `arch_prctl(ARCH_SET_FS, a)` (K9, x64). -/
  | archSetFs (a : Nat)
  deriving DecidableEq, Repr

/-- **The supported calls** (K1): the call a thread asks for with number
`nr` and arguments `a`, or `none` if the call or its arguments are not
supported (a fault). A futex address must be 4-aligned. -/
def decode (N : Nrs) (nr : Nat) (a : Fin 6 → Nat) : Option Call :=
  if nr = N.write then
    if a 0 = 1 ∨ a 0 = 2 then some (.write (a 0) (a 1) (a 2)) else none
  else if nr = N.exit then some .exit
  else if nr = N.exitGroup then some (.exitGroup (a 0))
  else if nr = N.futex then
    if a 1 = futexWaitPrivate ∧ a 0 % 4 = 0 ∧ a 3 = 0 then some .futexWait
    else if a 1 = futexWakePrivate ∧ a 0 % 4 = 0 then some (.futexWake (a 2))
    else none
  else if nr = N.rtSigaction then
    if a 0 = sigpipe ∧ a 2 = 0 ∧ a 3 = sigsetSize then some .rtSigaction else none
  else if nr = N.clone then
    if a 0 = cloneFlags ∧ a 2 = 0 ∧ a N.cloneCtid = 0 then some (.clone (a 1) (a N.cloneTls)) else none
  else if N.archPrctl = some nr then
    if a 0 = archSetFs then some (.archSetFs (a 1)) else none
  else none

/-- **What the kernel reads and writes in a thread state** (K1), per ISA:
the system-call instruction, the number and argument registers, the state
after the call returns `r` (pc past the instruction, `r` in the result
register; on x64 also `rcx` and `r11` as `syscall` sets them), the
registers that return writes, the child's initial state at `clone`, the
thread pointer, and the private memory. The instances (`A64.abi`,
`X64.abi`) only access the registers and the private memory. -/
structure Abi (I : ISA) where
  nrs : Nrs
  /-- The state is at a system-call instruction. -/
  atSys : I.State → Bool
  /-- The system-call number. -/
  nr : I.State → Nat
  /-- The six argument registers. -/
  arg : I.State → Fin 6 → Nat
  /-- The state after the call returns `r`. -/
  ret : I.State → BitVec 64 → I.State
  /-- The registers `ret` writes. -/
  retRegs : List I.RegId
  /-- The child's state at `clone(…, stack, …, tls, …)`: the parent's
  registers, but result 0, stack pointer `stack`, thread pointer `tls`, the
  pc past the instruction, no private memory. -/
  child : I.State → (stack tls : Nat) → I.State
  /-- The state with thread pointer `a` (`arch_prctl(ARCH_SET_FS)`). -/
  setTp : I.State → Nat → I.State
  /-- The thread pointer. -/
  tp : I.State → BitVec 64
  /-- The private memory. -/
  dmem : I.State → _root_.Mem 64
  /-- The state with private memory `m` (a range transfer, §2.6). -/
  setDmem : I.State → _root_.Mem 64 → I.State
  /-- The stack pointer. -/
  sp : I.State → Nat
  /-- The program counter (the model's code address, as `ExtMachine.pc`). -/
  pc : I.State → Nat
  /-- The state is at a `nop` (the instruction at a transfer site). -/
  atNop : I.State → Bool
  /-- The state with the pc past the instruction at the pc (a transfer
  site's `nop`). -/
  skip : I.State → I.State
  dmem_setDmem : ∀ s m, dmem (setDmem s m) = m
  dmem_skip : ∀ s, dmem (skip s) = dmem s

/-! ## Kernel state -/

/-- A thread slot (§2.1): dormant (never used), running (with the bytes of
the current `write` transferred so far), or ended by `exit`. -/
inductive Slot where
  | dormant
  | run (wr : Nat)
  | exited
  deriving DecidableEq, Repr

/-- **The kernel's state**: one slot per thread of the configuration, the
process's exit record, and the stack ranges (§2.6): the pool they come from
(the layout's `stackPool`), the ranges now in some thread's private memory
with their owner (`held`), and the pool's contents (`pmem`: the bytes each
released range held when it was released; a range never held reads 0, the
pool being `.bss`). -/
structure KState where
  slots : Array Slot
  exited : Option Outcome := none
  pool : Range := ⟨0, 0⟩
  held : List (Nat × Range) := []
  pmem : _root_.Mem 64 := ∅
  /-- The regions mapped read-write for the whole run (K11): `.data`, the
  heap arena, the stack pool, the pinned region, the initial stack. -/
  rw : List Range := []
  /-- The regions mapped read-only (K11): the code and `.rodata`. -/
  ro : List Range := []

namespace KState

/-- At load time (K10, K11): `n` thread slots, slot 0 running, the other
`n - 1` dormant; the layout's stack pool, no range held; mapped read-write
the layout's data, heap, stack pool and pinned region and the entry state's
initial stack, read-only the layout's code and `.rodata`. -/
def init (n : Nat) (E : Entry) (Λ : Layout) : KState :=
  { slots := #[.run 0] ++ Array.replicate (n - 1) .dormant, pool := Λ.stackPool,
    rw := [Λ.data, Λ.heap, Λ.stackPool, Λ.pinned, E.stack], ro := [Λ.code, Λ.rodata] }

/-- Thread `tid` runs (an active slot that has not called `exit`). -/
def runs (x : KState) (tid : Nat) : Bool :=
  match x.slots[tid]? with
  | some (.run _) => true
  | _ => false

/-- The bytes of the current `write` of thread `tid` transferred so far. -/
def wr (x : KState) (tid : Nat) : Nat :=
  match x.slots[tid]? with
  | some (.run j) => j
  | _ => 0

/-- Set slot `tid`. -/
def set (x : KState) (tid : Nat) (s : Slot) : KState := { x with slots := x.slots.set! tid s }

/-- The dormant slots. -/
def dormants (x : KState) : List Nat :=
  (List.range x.slots.size).filter fun j => x.slots[j]? = some .dormant

end KState

/-- The ranges `r` and `[lo, lo + n)` share an address. -/
def overlaps (r : Range) (lo n : Nat) : Bool := lo < r.lo + r.size && r.lo < lo + n

/-- The bytes a memory location covers (a location of 0 bytes is taken as a
whole word, which only makes `fresh` stricter). -/
def locBytes (l : Loc) : Nat := if l.bytes = 0 then 8 else l.bytes

/-! ## Steps -/

variable {I : ISA} (K : Abi I)

/-- The call thread `t` asks for. -/
def callOf (t : Thread I) : Option Call := decode K.nrs (K.nr t.st) (K.arg t.st)

/-- The thread after the call returns `r`: `Abi.ret`, the written registers
with view 0 (a kernel result carries no dependency, which only allows more
reorderings), views and promises unchanged. -/
def retThread (t : Thread I) (r : BitVec 64) : Thread I :=
  K.retRegs.foldl (fun t reg => t.setRegView reg 0 0) { t with st := K.ret t.st r }

/-- No register dependency. -/
def iv0 : InstrViews := { addrR := 0, addrW := 0, dataR := 0, dataW := 0, condW := 0 }

/-- Byte `i` (little-endian) of a memory value. -/
def byteOf (v : Val) (i : Nat) : Fin 256 := ⟨(v.toNat / 2 ^ (8 * i)) % 256, Nat.mod_lt _ (by decide)⟩

/-- **How the kernel reads a byte of a `write` buffer** (K2, K3): from the
thread's private memory if mapped there; otherwise as a plain load by the
calling thread (Kraken's `readSuccs`, no register dependency) of the
8-byte word containing it, of which it takes the byte (memory holds 8-byte
words, `Scc/Sem/Correct.lean` `wordLoc`; Kraken has no mixed-size
accesses). `rd` picks one of the writes the thread may read. The thread
gets the views of the load. -/
def readByte (A : Arch) (t : Thread I) (mem : Memory) (a rd : Nat) : Option (Fin 256 × Thread I) :=
  match (K.dmem t.st).loadBytes (BitVec.ofNat 64 a) 1 with
  | some [b] => some (⟨b.toNat % 256, Nat.mod_lt _ (by decide)⟩, t)
  | _ =>
    match (readSuccs A iv0 { views := t.views, prom := t.prom, mem } .plain false
        ⟨BitVec.ofNat 64 (a - a % 8), 8⟩)[rd]? with
    | some (_, v, c') => some (byteOf v (a % 8), { t with views := c'.views })
    | none => none

/-- The exit status of `exit_group(v)` (K5: the kernel keeps `v mod 256`). -/
def exitCode (v : Nat) : Fin 256 := ⟨v % 256, Nat.mod_lt _ (by decide)⟩

/-- A refused `write` (K3): it returned `0` or an error other than `EINTR`
and `EAGAIN`. -/
def writeRefused (r : BitVec 64) : Bool :=
  r == 0 || (2 ^ 64 - maxErrno ≤ r.toNat && r != neg eintr && r != neg eagain)

/-- What `FUTEX_WAIT` may return (K7: spurious returns at any time). -/
def futexWaitRet (r : BitVec 64) : Bool := r == 0 || r == neg eagain || r == neg eintr

/-! ## Certification through system calls -/

/-- **What a call may return to the calling thread** in this model: every
value `sysStep` or `spawnStep` may return to it (`sysStep_ret_mem`,
`spawnStep_ret_mem`). `write(…, n)`: a count up to `n`, or any error
`-1 … -maxErrno` (`-EINTR`, `-EAGAIN` and the refusals); `exit` and
`exit_group` do not return; `futex` wait `0`, `-EAGAIN`, `-EINTR`, wake a
count up to `n`; `rt_sigaction` and `arch_prctl` `0`; `clone` (to the
parent) a thread id in `(0, pidMax)`, `-EAGAIN` or `-ENOMEM`. -/
def results : Call → List (BitVec 64)
  | .write _ _ n => (List.range (n + 1)).map (BitVec.ofNat 64) ++ (List.range maxErrno).map fun e => neg (e + 1)
  | .exit | .exitGroup _ => []
  | .futexWait => [0, neg eagain, neg eintr]
  | .futexWake n => (List.range (n + 1)).map (BitVec.ofNat 64)
  | .rtSigaction | .archSetFs _ => [0]
  | .clone _ _ => (List.range' 1 (pidMax - 1)).map (BitVec.ofNat 64) ++ [neg eagain, neg enomem]

/-- The states the calling thread may resume in after the call `call` at
state `s`: `Abi.ret` of each of `results call`, with the thread pointer set
first for `arch_prctl`. -/
def certSuccs (s : I.State) : Call → List I.State
  | .archSetFs a => [K.ret (K.setTp s a) 0]
  | call => (results call).map (K.ret s)

/-- **The certification semantics of the canonical targets**: the ISA's
`exec`, except at a supported system call, where the instruction is a
choice among the states the kernel model may resume the thread in
(`certSuccs`): no event, the result in the result registers, the pc past the
instruction; a call that does not return (`exit`, `exit_group`) is a dead
end (no branch). An unsupported call is the ISA's (a fault). This is the
sequential over-approximation of §2.2 for certification only; the thread's
own steps at a system call are the hooks' (`sysStep`, `spawnStep`). -/
def certExec (s : I.State) : Option (EvTree I.State) :=
  if K.atSys s then
    match decode K.nrs (K.nr s) (K.arg s) with
    | some call => some (.choose (certSuccs K s call).length fun i => .done (certSuccs K s call)[i])
    | none => I.exec s
  else I.exec s

/-- Off a system call, the certification semantics is the ISA's. -/
theorem certExec_of_not_atSys {s : I.State} (h : K.atSys s = false) : certExec K s = I.exec s := by
  simp [certExec, h]

/-- The nondeterministic choice of a system-call step: transfer the next
byte of a `write` reading the `rd`-th visible write, return `r`, or end the
process as an abort. -/
inductive Pick where
  | byte (rd : Nat)
  | ret (r : BitVec 64)
  | abort (k : AbortKind)

/-- Thread `tid`, in state `t`, may take a system-call step: it is at a
system call, its slot runs, and the process has not exited. Outstanding
promises are allowed: the hooks ask instead that the thread be certified
after the step (`CertAfter`), certification passing system calls with the
kernel's possible returns (`certExec`). -/
def ready (tid : Nat) (c : Config I × KState) (t : Thread I) : Bool :=
  K.atSys t.st && c.2.runs tid && c.2.exited.isNone

/-- Return `r` to thread `tid` (now `t`), with kernel state `x` and events
`es`. -/
def back (tid : Nat) (c : Config I × KState) (t : Thread I) (r : BitVec 64) (x : KState) (es : List Ev) :
    Option (List Ev × (Config I × KState)) :=
  some (es, (c.1.withThread tid (retThread K t r) c.1.mem, x))

/-- **A system-call step other than `clone`** of thread `tid` under the
memory model `A`, with the choice `p`, and the events it emits:

- `write(fd, buf, n)` (K3): while fewer than `n` bytes are out, a step
  transfers the next byte (`readByte`), emitting `out b` for `fd = 1` and
  nothing for `fd = 2`; after `k ≥ 1` bytes the call may return `k`; before
  any, it may return `-EINTR` or `-EAGAIN` with no event, or a refusal
  (`writeRefused`) with `writeErr`.
- `exit` (K4): the slot ends; no memory effect.
- `exit_group(v)` (K5): the process ends with `exit (v % 256)`, or with
  `abort k` if `v % 256 = abortStatus` (`Step.sys` admits `abort k` only at
  the abort site of kind `k`, and `exit` at none).
- `futex` (K7): `FUTEX_WAIT` returns `0`, `-EAGAIN` or `-EINTR`,
  `FUTEX_WAKE` some count up to `n`; no memory effect.
- `rt_sigaction` (K8), `arch_prctl(ARCH_SET_FS, a)` (K9, sets the thread
  pointer): return 0.
- `clone` (K6c): may be refused, returning `-EAGAIN` or `-ENOMEM` with
  `cloneErr` (Linux may refuse a thread for reasons the program cannot
  see: `RLIMIT_NPROC`, memory).

A `clone` that succeeds is `spawnStep`; with no dormant slot `clone` is a
fault (`faultAt`). Each step that returns advances the pc and writes the result (`retThread`).
`none`: no such step. -/
def sysStep (A : Arch) (tid : Nat) (c : Config I × KState) (p : Pick) :
    Option (List Ev × (Config I × KState)) :=
  match c.1.threads[tid]? with
  | none => none
  | some t =>
    if !ready K tid c t then none else
    match callOf K t, p with
    | some (.write fd buf n), .byte rd =>
      let j := c.2.wr tid
      if j < n then
        (readByte K A t c.1.mem (buf + j) rd).map fun (b, t') =>
          (if fd = 1 then [.out b] else [], (c.1.withThread tid t' c.1.mem, c.2.set tid (.run (j + 1))))
      else none
    | some (.write _ _ _), .ret r =>
      let j := c.2.wr tid
      if 0 < j then
        if r = BitVec.ofNat 64 j then back K tid c t r (c.2.set tid (.run 0)) [] else none
      else if r = neg eintr ∨ r = neg eagain then back K tid c t r c.2 []
      else if writeRefused r then back K tid c t r c.2 [.writeErr]
      else none
    | some .exit, .ret r => if r = 0 then some ([], (c.1, c.2.set tid .exited)) else none
    | some (.exitGroup v), .ret r =>
      if r = 0 then some ([.exit (exitCode v)], (c.1, { c.2 with exited := some (.exit (exitCode v)) }))
      else none
    | some (.exitGroup v), .abort k =>
      if v % 256 = abortStatus then some ([.abort k], (c.1, { c.2 with exited := some (.abort k) })) else none
    | some .futexWait, .ret r => if futexWaitRet r then back K tid c t r c.2 [] else none
    | some (.futexWake n), .ret r => if r.toNat ≤ n then back K tid c t r c.2 [] else none
    | some .rtSigaction, .ret r => if r = 0 then back K tid c t r c.2 [] else none
    | some (.archSetFs a), .ret r =>
      if r = 0 then back K tid c { t with st := K.setTp t.st a } r c.2 [] else none
    | some (.clone _ _), .ret r =>
      if r = neg eagain ∨ r = neg enomem then back K tid c t r c.2 [.cloneErr] else none
    | _, _ => none

/-- The child's thread at `clone` (K6a): `Abi.child`'s state, register views
0, no promises, and the parent's views at the call (the emitted full fence
before the call makes them post-barrier views); the parent's forwarding and
exclusive records, which concern its own accesses, are not inherited. -/
def childThread (t : Thread I) (stack tls : Nat) : Thread I :=
  { Thread.init (K.child t.st stack tls) with views := { t.views with fwdb := [], xclb := none } }

/-! ## Stack ranges (§2.6) -/

/-- A byte of a memory (0 if unmapped). -/
def byte (m : _root_.Mem 64) (a : BitVec 64) : UInt8 := (m[a]?).getD 0

/-- The addresses of a range. -/
def addrs (r : Range) : List (BitVec 64) := (List.range r.size).map fun i => BitVec.ofNat 64 (r.lo + i)

/-- `dst` with the bytes of `src` on range `r` (0 where `src` is unmapped). -/
def copyRange (src dst : _root_.Mem 64) (r : Range) : _root_.Mem 64 :=
  (addrs r).foldl (fun m a => m.insert a (byte src a)) dst

/-- `m` with range `r` unmapped. -/
def eraseRange (m : _root_.Mem 64) (r : Range) : _root_.Mem 64 :=
  (addrs r).foldl (fun m a => m.erase a) m

/-- A thread with stack pointer `sp` is on the range `r`: `sp` in
`(r.lo, r.lo + r.size]` (stacks grow down; an empty stack has `sp` at the
top). -/
def onStack (r : Range) (sp : Nat) : Bool := r.lo < sp && sp ≤ r.lo + r.size

/-- The range a thread at a transfer site names: base in the first argument
register, size in the second. -/
def siteRange (s : I.State) : Range := ⟨K.arg s 0, K.arg s 1⟩

/-- **A fresh stack range** `r` in configuration `c`: nonempty, inside the
stack pool and the address space, disjoint from every range now in some
thread's private memory (`KState.held`), and from every shared write,
initial or not (no thread accesses the pool as shared memory, `InLayout`,
so moving a range out of shared memory hides nothing any thread reads). -/
def fresh (c : Config I × KState) (r : Range) : Bool :=
  0 < r.size && c.2.pool.lo ≤ r.lo && r.lo + r.size ≤ c.2.pool.lo + c.2.pool.size && r.lo + r.size ≤ 2 ^ 64 &&
    c.2.held.all (fun h => !overlaps r h.2.lo h.2.size) &&
    c.1.mem.msgs.all (fun m => !overlaps r m.loc.addr.toNat (locBytes m.loc)) &&
    c.1.mem.init.all (fun p => !overlaps r p.1.addr.toNat (locBytes p.1))

/-- **Take** (§2.6), thread `tid` at the take site (a `nop`; `Step.xfer`
admits it only at `XferKind.take`'s label): the fresh range its registers
name (`siteRange`) moves from the pool into its private memory, with the
pool's bytes there (`pmem`: zero if never held, else what the range held at
its last release); the thread moves past the `nop`. No step if the range is
not fresh or the instruction is not a `nop`: the thread is then stuck,
which progress excludes. -/
def takeStep (tid : Nat) (c : Config I × KState) : Option (Config I × KState) :=
  match c.1.threads[tid]? with
  | none => none
  | some t =>
    let r := siteRange K t.st
    if c.2.runs tid && c.2.exited.isNone && K.atNop t.st && fresh c r then
      some (c.1.withThread tid { t with st := K.skip (K.setDmem t.st (copyRange c.2.pmem (K.dmem t.st) r)) } c.1.mem,
        { c.2 with held := (tid, r) :: c.2.held, pmem := eraseRange c.2.pmem r })
    else none

/-- **Release** (§2.6), thread `tid` at the release site (a `nop`;
`Step.xfer` admits it only at `XferKind.release`'s label): the range its
registers name, which it holds and has left (it is not on it, `onStack`),
moves from its private memory back to the pool, with its bytes
(`pmem`); the thread moves past the `nop`. No step otherwise. -/
def releaseStep (tid : Nat) (c : Config I × KState) : Option (Config I × KState) :=
  match c.1.threads[tid]? with
  | none => none
  | some t =>
    let r := siteRange K t.st
    if c.2.runs tid && c.2.exited.isNone && K.atNop t.st && c.2.held.contains (tid, r) &&
        !onStack r (K.sp t.st) then
      some (c.1.withThread tid { t with st := K.skip (K.setDmem t.st (eraseRange (K.dmem t.st) r)) } c.1.mem,
        { c.2 with held := c.2.held.erase (tid, r), pmem := copyRange (K.dmem t.st) c.2.pmem r })
    else none

/-- The transfer of kind `k`. -/
def xferStep : XferKind → Nat → Config I × KState → Option (Config I × KState)
  | .take => takeStep K
  | .release => releaseStep K

/-- **The current stack range of a thread**: the range it holds that it is
on (`onStack`). -/
def stackRangeOf (c : Config I × KState) (tid : Nat) : Option Range :=
  match c.1.threads[tid]? with
  | none => none
  | some t => (c.2.held.find? fun h => h.1 == tid && onStack h.2 (K.sp t.st)).map (·.2)

/-! ## Mapped regions (K11) -/

/-- **The regions mapped for an access** (K11): for a write, the read-write
regions and the held stack ranges (inside the pool, so already covered;
listed so that the notion does not depend on that); for a read also the
read-only code. -/
def mappedRegions (x : KState) (write : Bool) : List Range :=
  x.rw ++ x.held.map (·.2) ++ if write then [] else x.ro

/-- **A location is mapped** for a read (`write = false`) or a write: every
byte of it lies in some region mapped for that access. -/
def mapped (x : KState) (write : Bool) (l : Loc) : Bool :=
  (List.range l.bytes).all fun i => (mappedRegions x write).any fun r => decide (r.contains (l.addr.toNat + i))

/-- **Some path of an instruction's event tree reaches an access `p`
rejects**: a load (a read), a store (a write) or an RMW (a write; its read
is at the same location) at a location `l` with `p l write`, after any
choices and any values returned by earlier events of the same
instruction. Over the returned values this is an over-approximation of the
paths a run can take, so a fault defined by it only rejects more targets. -/
inductive Touches {σ : Type} (p : Loc → Bool → Prop) : EvTree σ → Prop
  | load {k x l ret} : p l false → Touches p (.load k x l ret)
  | loadRet {k x l ret} (v : Val) : Touches p (ret v) → Touches p (.load k x l ret)
  | store {k x l v ret} : p l true → Touches p (.store k x l v ret)
  | storeRet {k x l v ret} (b : Bool) : Touches p (ret b) → Touches p (.store k x l v ret)
  | rmw {k nr l op ret} : p l true → Touches p (.rmw k nr l op ret)
  | rmwRet {k nr l op ret} (v : Val) : Touches p (ret v) → Touches p (.rmw k nr l op ret)
  | choose {n k} (i : Fin n) : Touches p (k i) → Touches p (.choose n k)
  | fence {k ret} : Touches p (ret ()) → Touches p (.fence k ret)

/-- The first access of an event tree, if it is at its root: the location
and whether it is a write. -/
def rootAccess {σ : Type} : EvTree σ → Option (Loc × Bool)
  | .load _ _ l _ => some (l, false)
  | .store _ _ l _ _ => some (l, true)
  | .rmw _ _ l _ _ => some (l, true)
  | _ => none

theorem touches_of_root {σ : Type} {p : Loc → Bool → Prop} {e : EvTree σ} {l : Loc} {w : Bool}
    (h : rootAccess e = some (l, w)) (hp : p l w) : Touches p e := by
  cases e <;> simp only [rootAccess, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  · obtain ⟨rfl, rfl⟩ := h; exact .load hp
  · obtain ⟨rfl, rfl⟩ := h; exact .store hp
  · obtain ⟨rfl, rfl⟩ := h; exact .rmw hp

/-- **An access outside the mapped regions** (K11: `SIGSEGV`, a fault):
running thread `tid` of a process that has not exited, at an instruction
(not a system call) whose event tree may reach a shared access to a
location not mapped for it. Private accesses (`dmem`) need no check: a
thread's private memory is its initial stack and the stack ranges it
holds, all mapped. Writes are also confined by `InLayout` (shared writes
only in `.data`, the heap and the pinned region); this adds reads, and
writes to the pool or the code. -/
def unmappedAt (c : Config I × KState) (tid : Nat) : Prop :=
  ∃ t e, c.1.threads[tid]? = some t ∧ c.2.runs tid = true ∧ c.2.exited = none ∧ K.atSys t.st = false ∧
    I.exec t.st = some e ∧ Touches (fun l w => mapped c.2 w l = false) e

/-- The executable part of `unmappedAt`: the instruction's first access is
at its root and not mapped. -/
def rootUnmapped (c : Config I × KState) (tid : Nat) : Bool :=
  match c.1.threads[tid]? with
  | none => false
  | some t =>
    c.2.runs tid && c.2.exited.isNone && !K.atSys t.st &&
      match I.exec t.st with
      | some e =>
        match rootAccess e with
        | some (l, w) => !mapped c.2 w l
        | none => false
      | none => false

theorem unmappedAt_of_root {c : Config I × KState} {tid : Nat} (h : rootUnmapped K c tid = true) :
    unmappedAt K c tid := by
  unfold rootUnmapped at h
  split at h
  · exact absurd h (by simp)
  · rename_i t ht
    simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at h
    obtain ⟨⟨⟨hr, hx⟩, hs⟩, h⟩ := h
    split at h
    · rename_i e he
      split at h
      · rename_i l w hl
        exact ⟨t, e, ht, hr, hx, hs, he, touches_of_root hl (by simpa using h)⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)

/-! ## Thread creation -/

/-- **`clone`** (K6) of thread `tid` into the dormant slot `j`, returning the
thread id `ctid` (positive, below `pidMax`; the runtime only tests it for
an error) to the parent: the parent returns (`retThread`), the child slot
gets `childThread` and runs; memory is unchanged. The range the parent
holds that ends at the child's stack pointer `stack` (the child's stack,
which the runtime takes before the `clone`), if any, moves from the
parent's private memory to the child's, with its bytes (§2.6). -/
def spawnStep (tid : Nat) (c : Config I × KState) (j : Nat) (ctid : BitVec 64) : Option (Config I × KState) :=
  match c.1.threads[tid]? with
  | none => none
  | some t =>
    if !ready K tid c t then none else
    match callOf K t with
    | some (.clone stack tls) =>
      if c.2.slots[j]? = some .dormant ∧ j < c.1.threads.size ∧ 0 < ctid.toNat ∧ ctid.toNat < pidMax then
        let ch := childThread K t stack tls
        match c.2.held.find? (fun h => h.1 == tid && h.2.lo + h.2.size == stack) with
        | none =>
          some ((c.1.withThread tid (retThread K t ctid) c.1.mem).withThread j ch c.1.mem, c.2.set j (.run 0))
        | some (_, r) =>
          let tp := { t with st := K.setDmem t.st (eraseRange (K.dmem t.st) r) }
          let tc := { ch with st := K.setDmem ch.st (copyRange (K.dmem t.st) (K.dmem ch.st) r) }
          some ((c.1.withThread tid (retThread K tp ctid) c.1.mem).withThread j tc c.1.mem,
            { c.2.set j (.run 0) with held := (j, r) :: c.2.held.erase (tid, r) })
      else none
    | _ => none

/-- **Faults of the kernel model**: a running thread of a process that has
not exited is at an unsupported system call (K1), at `clone` with no
dormant slot left (K6b: the process has used all its thread slots; Linux
would return `-EAGAIN`, `Scc/DESIGN.md` §3.1), or has halted (run off its
code: every thread of an `scc` program ends by `exit` or `exit_group`). -/
def faultAt (c : Config I × KState) (tid : Nat) : Bool :=
  match c.1.threads[tid]? with
  | some t =>
    c.2.runs tid && c.2.exited.isNone &&
      ((K.atSys t.st &&
          match callOf K t with
          | none => true
          | some (.clone _ _) => c.2.dormants.isEmpty
          | some _ => false) ||
        t.halted)
  | none => false

/-! ## Certification as the solo projection of the kernel step

`certExec` passes a system call with every value the call may return,
whatever the kernel state, and erases nothing at `clone`; the transfer
sites are plain `nop`s to it. `soloExec` is instead the kernel's own step
of the thread run alone (`solo`): at a transfer site and at a system call
the instruction is a choice among the states the thread may resume in after
`xferStep`, `sysStep` or `spawnStep` of the configuration with only that
thread's state, the kernel state `x` of the step, and no shared write; at
`clone` and `write` there is no choice (a certifying run ends there). Its
register dependencies at a system call are the kernel's (`svcDeps`: the
result registers, no input). -/

/-- The register dependencies of the kernel's return (`retThread`): the
result registers written, with no register input. -/
def svcDeps : Kraken.InstrDeps I.RegId := { defs := K.retRegs }

/-- The dependencies of an instruction under certification: the kernel's at
a system call, the ISA's elsewhere. -/
def certDeps (s : I.State) : Kraken.InstrDeps I.RegId := if K.atSys s then svcDeps K else I.deps s

/-- The ranges held in the solo configuration of thread `tid` at state `s`:
the others' as in `x`; at a transfer site the thread's own entry for the
range its registers name is decided by its private memory (at a take, held
iff some byte of the range is mapped there, which makes the range not fresh;
at a release, held iff every byte is); elsewhere `x.held`. -/
def soloHeld (site : Option XferKind) (x : KState) (tid : Nat) (s : I.State) : List (Nat × Range) :=
  let r := siteRange K s
  let others := x.held.filter (·.1 != tid)
  match site with
  | some .take => if (addrs r).any (fun a => ((K.dmem s)[a]?).isSome) then (tid, r) :: others else others
  | some .release => if (addrs r).all (fun a => ((K.dmem s)[a]?).isSome) then (tid, r) :: others else others
  | none => x.held

/-- **The solo configuration** of thread `tid` at state `s` with kernel
state `x`: every slot holds a fresh thread at `s`, memory has no write,
`tid`'s slot runs with no byte of a `write` out, the process has not exited,
and the held ranges are `soloHeld`. -/
def solo (site : Option XferKind) (x : KState) (tid : Nat) (s : I.State) : Config I × KState :=
  ({ threads := Array.replicate x.slots.size (Thread.init s), mem := { init := [], msgs := #[] } },
   { x with slots := x.slots.set! tid (.run 0), exited := none, held := soloHeld K site x tid s })

/-- The state of thread `tid` in a configuration. -/
def stOf (tid : Nat) (c : Config I × KState) : Option I.State := (c.1.threads[tid]?).map (·.st)

/-- A choice among the states `ss`, with no event. -/
def leaves (ss : List I.State) : EvTree I.State := .choose ss.length fun i => .done ss[i]

/-- The transfer site of the code marks `μ` at state `s`, if any. -/
def siteAt (μ : Marks) (s : I.State) : Option XferKind :=
  if μ.site .take = some (K.pc s) then some .take
  else if μ.site .release = some (K.pc s) then some .release else none

/-- **The certification semantics of the canonical targets, as the solo
projection of the kernel step** of thread `tid` with code marks `μ` and
kernel state `x`:

- at a transfer site of kind `k`, the state `xferStep k` leaves the thread
  in (no branch if it takes no step);
- at a supported system call other than `clone` and `write`, the states
  `sysStep` (`.ret`) leaves it in;
- at `clone` and at `write`, no branch:
  like `exit_group`, they end a certifying run, so no promise is certified
  across them, and a thread certified at a `write` has none outstanding
  (`prom_nil_of_write`). The kernel step itself is unchanged (`spawnStep`,
  and `sysStep`'s bytes, returns and refusals, each with `CertAfter`); only
  certification stops there. This is what makes `soloExec` independent of
  the ranges the thread holds (`soloHeld none` reads them only at `clone`)
  and of a `write`'s progress record;
- elsewhere the ISA's `exec`. -/
def soloExec (A : Arch) (μ : Marks) (x : KState) (tid : Nat) (s : I.State) : Option (EvTree I.State) :=
  match siteAt K μ s with
  | some k => some (leaves ((xferStep K k tid (solo K (some k) x tid s)).bind (stOf tid)).toList)
  | none =>
  if K.atSys s then
    let c := solo K none x tid s
    let rets (rs : List (BitVec 64)) : List I.State :=
      rs.filterMap fun r => (sysStep K A tid c (.ret r)).bind fun (_, c') => stOf tid c'
    match decode K.nrs (K.nr s) (K.arg s) with
    | some (.clone _ _) => some (leaves [])
    | some (.write _ _ _) => some (leaves [])
    | some call => some (leaves (rets (results call)))
    | none => I.exec s
  else I.exec s

/-- **The certification semantics of the canonical targets**: `soloExec`
with the kernel's dependencies at a system call (`certDeps`). -/
def certSem (A : Arch) (μ : Marks) (x : KState) (tid : Nat) : CertSem I := ⟨soloExec K A μ x tid, certDeps K⟩

/-- Off the transfer sites and system calls, `soloExec` is the ISA's. -/
theorem soloExec_of_not_atSys {A : Arch} {μ : Marks} {x : KState} {tid : Nat} {s : I.State}
    (hs : siteAt K μ s = none) (h : K.atSys s = false) : soloExec K A μ x tid s = I.exec s := by
  simp [soloExec, hs, h]

/-- Off a system call, the certification dependencies are the ISA's. -/
theorem certDeps_of_not_atSys {s : I.State} (h : K.atSys s = false) : certDeps K s = I.deps s := by
  simp [certDeps, h]

/-- After a kernel step to `c'`, thread `tid` is certified under the
certification semantics of the canonical targets with the code marks `μ`
and the kernel state after the step (`certSem`). -/
def CertAfter (A : Arch) (μ : Marks) (tid : Nat) (c' : Config I × KState) : Prop :=
  ∀ t', c'.1.threads[tid]? = some t' → CertOkC A (certSem K A μ c'.2 tid) tid t' c'.1.mem

/-- A thread with no promise after the step is certified. -/
theorem certAfter_of_prom {A : Arch} {μ : Marks} {tid : Nat} {c' : Config I × KState}
    (h : ∀ t', c'.1.threads[tid]? = some t' → t'.prom = []) : CertAfter K A μ tid c' :=
  fun t' ht' => certOkC_of_prom_nil (h t' ht')

/-- **The extension hooks of the canonical targets** under the memory model
`A`, with `n` thread slots: the kernel state (`KState.init n` with the
layout's stack pool), the system-call instruction `Abi.atSys`, `sysStep`
and `spawnStep` (with every choice, each leaving the calling thread
certified: `CertAfter`), `xferStep` (deterministic: the range
is the thread's registers'), the exit records of `KState`, `faultAt`, the
current stack ranges `stackRangeOf`, the thread pointer `Abi.tp`, and
certification as the solo projection of the kernel step (`certSem`). -/
def hooks (A : Arch) (n : Nat) : Hooks I where
  X := KState
  init E Λ := KState.init n E Λ
  slots := n
  atSys := K.atSys
  sys μ tid c es c' := ∃ p, sysStep K A tid c p = some (es, c') ∧ CertAfter K A μ tid c'
  spawn μ tid c c' := ∃ j r, spawnStep K tid c j r = some c' ∧ CertAfter K A μ tid c'
  xfer k tid c c' := xferStep K k tid c = some c'
  exited x := x.exited
  threadDone x tid := x.runs tid = false
  fault c := (∃ tid, faultAt K c tid = true) ∨ ∃ tid, unmappedAt K c tid
  stackRange := stackRangeOf K
  threadPtr c tid :=
    match c.1.threads[tid]? with
    | some t => K.tp t.st
    | none => 0
  cexec := certSem K A

/-! ## Sanity -/

/-- A number that is none of the table's is not supported, whatever the
arguments. -/
theorem decode_none {N : Nrs} {nr : Nat} (a : Fin 6 → Nat) (h1 : nr ≠ N.write) (h2 : nr ≠ N.exit)
    (h3 : nr ≠ N.exitGroup) (h4 : nr ≠ N.futex) (h5 : nr ≠ N.rtSigaction) (h6 : nr ≠ N.clone)
    (h7 : N.archPrctl ≠ some nr) : decode N nr a = none := by
  simp [decode, h1, h2, h3, h4, h5, h6, h7]

variable {K} {μ : Marks}

/-! ### Promise sets across kernel steps -/

/-- Setting register views changes neither the state nor the promises. -/
theorem foldl_setRegView (regs : List I.RegId) (u : Thread I) :
    (regs.foldl (fun t reg => t.setRegView reg 0 0) u).st = u.st ∧
      (regs.foldl (fun t reg => t.setRegView reg 0 0) u).prom = u.prom := by
  induction regs generalizing u with
  | nil => exact ⟨rfl, rfl⟩
  | cons r rs ih => exact ih _

/-- A returned thread is in `Abi.ret`'s state. -/
@[simp] theorem retThread_st (t : Thread I) (r : BitVec 64) : (retThread K t r).st = K.ret t.st r :=
  (foldl_setRegView _ _).1

/-- A returned thread keeps its promises. -/
@[simp] theorem retThread_prom (t : Thread I) (r : BitVec 64) : (retThread K t r).prom = t.prom :=
  (foldl_setRegView _ _).2

/-- The kernel's byte read keeps the thread's promises. -/
theorem readByte_prom {A : Arch} {t t' : Thread I} {mem : Memory} {a rd : Nat} {b : Fin 256}
    (h : readByte K A t mem a rd = some (b, t')) : t'.prom = t.prom := by
  unfold readByte at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · cases h

/-- The child of a `clone` has no promise. -/
@[simp] theorem childThread_prom (t : Thread I) (stack tls : Nat) : (childThread K t stack tls).prom = [] := rfl

/-- A thread of `c.withThread i th mem`. -/
theorem withThread_get {c : Config I} {i k : Nat} {th : Thread I} {mem : Memory} :
    (c.withThread i th mem).threads[k]? = if i = k ∧ i < c.threads.size then some th else c.threads[k]? := by
  simp only [Config.withThread, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases h1 : i = k
  · subst h1
    by_cases h2 : i < c.threads.size
    · simp [h2]
    · simp [h2]
  · simp [h1]

/-- After replacing thread `tid` (at index `tid`) by one with no promise,
every thread at `tid` has none, given the old one had none. -/
theorem prom_withThread {c : Config I} {tid : Nat} {t th : Thread I} {mem : Memory}
    (ht : c.threads[tid]? = some t) (hp : t.prom = []) (hth : th.prom = []) :
    ∀ t', (c.withThread tid th mem).threads[tid]? = some t' → t'.prom = [] := by
  intro t' h'
  rw [withThread_get] at h'
  split at h'
  · cases h'; exact hth
  · rw [ht] at h'; cases h'; exact hp

/-- `prom_withThread` across a second replacement (a `clone`'s child). -/
theorem prom_withThread2 {c : Config I} {tid j : Nat} {t th ch : Thread I} {mem mem' : Memory}
    (ht : c.threads[tid]? = some t) (hp : t.prom = []) (hth : th.prom = []) (hch : ch.prom = []) :
    ∀ t', ((c.withThread tid th mem).withThread j ch mem').threads[tid]? = some t' → t'.prom = [] := by
  intro t' h'
  rw [withThread_get] at h'
  split at h'
  · cases h'; exact hch
  · exact prom_withThread ht hp hth t' h'

/-- **An unsupported system call is a fault**: a running thread at a system
call whose number or arguments `decode` rejects. -/
theorem fault_of_unsupported (A : Arch) (n : Nat) {c : Config I × KState} {tid : Nat} {t : Thread I}
    (ht : c.1.threads[tid]? = some t) (hr : c.2.runs tid = true) (hx : c.2.exited = none)
    (hs : K.atSys t.st = true) (hd : decode K.nrs (K.nr t.st) (K.arg t.st) = none) :
    (hooks K A n).fault c :=
  .inl ⟨tid, by simp [faultAt, ht, hr, hx, hs, callOf, hd]⟩

/-- **`exit_group(v)` ends the process** with `exit (v % 256)`. -/
theorem sys_exitGroup (A : Arch) (n : Nat) {c : Config I × KState} {tid : Nat} {t : Thread I} {v : Nat}
    (ht : c.1.threads[tid]? = some t) (hr : ready K tid c t = true) (hp : t.prom = []) (hc : callOf K t = some (.exitGroup v)) :
    (hooks K A n).sys μ tid c [.exit (exitCode v)] (c.1, { c.2 with exited := some (.exit (exitCode v)) }) :=
  ⟨.ret 0, by simp [sysStep, ht, hr, hc] <;> rfl,
    certAfter_of_prom K fun t' h' => by rw [ht] at h'; cases h'; exact hp⟩

/-- **Linux may refuse a `clone`** (`-EAGAIN`), with the event `cloneErr`;
the parent returns, no slot changes. -/
theorem sys_cloneErr (A : Arch) (n : Nat) {c : Config I × KState} {tid : Nat} {t : Thread I}
    {stack tls : Nat} (ht : c.1.threads[tid]? = some t) (hr : ready K tid c t = true) (hp : t.prom = [])
    (hc : callOf K t = some (.clone stack tls)) :
    (hooks K A n).sys μ tid c [.cloneErr] (c.1.withThread tid (retThread K t (neg eagain)) c.1.mem, c.2) :=
  ⟨.ret (neg eagain), by simp [sysStep, ht, hr, hc, back] <;> rfl,
    certAfter_of_prom K (prom_withThread ht hp (by simp [hp]))⟩

/-- **A `write` to fd 1 transfers one byte per step**: with `j < n` bytes
out, the byte at `buf + j` the thread reads (`readByte`) is the step's one
event. -/
theorem sys_writeByte (A : Arch) (n : Nat) {c : Config I × KState} {tid : Nat} {t t' : Thread I}
    {buf len rd : Nat} {b : Fin 256} (ht : c.1.threads[tid]? = some t) (hr : ready K tid c t = true) (hp : t.prom = [])
    (hc : callOf K t = some (.write 1 buf len)) (hj : c.2.wr tid < len)
    (hb : readByte K A t c.1.mem (buf + c.2.wr tid) rd = some (b, t')) :
    (hooks K A n).sys μ tid c [.out b]
      (c.1.withThread tid t' c.1.mem, c.2.set tid (.run (c.2.wr tid + 1))) :=
  ⟨.byte rd, by simp [sysStep, ht, hr, hc, hj, hb] <;> rfl,
    certAfter_of_prom K (prom_withThread ht hp ((readByte_prom hb).trans hp))⟩

/-- **After `k ≥ 1` bytes a `write` may return `k`**, with no event. -/
theorem sys_writeRet (A : Arch) (n : Nat) {c : Config I × KState} {tid : Nat} {t : Thread I}
    {fd buf len : Nat} (ht : c.1.threads[tid]? = some t) (hr : ready K tid c t = true) (hp : t.prom = [])
    (hc : callOf K t = some (.write fd buf len)) (hj : 0 < c.2.wr tid) :
    (hooks K A n).sys μ tid c []
      (c.1.withThread tid (retThread K t (BitVec.ofNat 64 (c.2.wr tid))) c.1.mem, c.2.set tid (.run 0)) :=
  ⟨.ret (BitVec.ofNat 64 (c.2.wr tid)), by simp [sysStep, ht, hr, hc, hj, back] <;> rfl,
    certAfter_of_prom K (prom_withThread ht hp (by simp [hp]))⟩

/-- **`clone` activates a dormant slot** with the child's thread at the
parent's views, and returns the child's id to the parent (here the parent
holds no range ending at the child's stack pointer). -/
theorem spawn_clone (A : Arch) (n : Nat) {c : Config I × KState} {tid j : Nat} {t : Thread I}
    {stack tls : Nat} {ctid : BitVec 64} (ht : c.1.threads[tid]? = some t) (hr : ready K tid c t = true) (hp : t.prom = [])
    (hc : callOf K t = some (.clone stack tls)) (hj : c.2.slots[j]? = some .dormant)
    (hjs : j < c.1.threads.size) (hpos : 0 < ctid.toNat) (hlt : ctid.toNat < pidMax)
    (hn : c.2.held.find? (fun h => h.1 == tid && h.2.lo + h.2.size == stack) = none) :
    (hooks K A n).spawn μ tid c
      ((c.1.withThread tid (retThread K t ctid) c.1.mem).withThread j (childThread K t stack tls) c.1.mem,
        c.2.set j (.run 0)) :=
  ⟨j, ctid, by simp [spawnStep, ht, hr, hc, hj, hjs, hpos, hlt, hn] <;> rfl,
    certAfter_of_prom K (prom_withThread2 ht hp (by simp [hp]) rfl)⟩

/-- **`clone` hands the child its stack range**: the range the parent holds
that ends at the child's stack pointer moves, with its bytes, from the
parent's private memory to the child's, and the child holds it. -/
theorem spawn_clone_stack (A : Arch) (n : Nat) {c : Config I × KState} {tid j o : Nat} {t : Thread I}
    {stack tls : Nat} {ctid : BitVec 64} {r : Range} (ht : c.1.threads[tid]? = some t)
    (hr : ready K tid c t = true) (hp : t.prom = []) (hc : callOf K t = some (.clone stack tls))
    (hj : c.2.slots[j]? = some .dormant) (hjs : j < c.1.threads.size) (hpos : 0 < ctid.toNat)
    (hlt : ctid.toNat < pidMax) (hf : c.2.held.find? (fun h => h.1 == tid && h.2.lo + h.2.size == stack) = some (o, r)) :
    (hooks K A n).spawn μ tid c
      ((c.1.withThread tid (retThread K { t with st := K.setDmem t.st (eraseRange (K.dmem t.st) r) } ctid)
          c.1.mem).withThread j
          { childThread K t stack tls with
            st := K.setDmem (childThread K t stack tls).st
              (copyRange (K.dmem t.st) (K.dmem (childThread K t stack tls).st) r) } c.1.mem,
        { c.2.set j (.run 0) with held := (j, r) :: c.2.held.erase (tid, r) }) :=
  ⟨j, ctid, by simp [spawnStep, ht, hr, hc, hj, hjs, hpos, hlt, hf] <;> rfl,
    certAfter_of_prom K (prom_withThread2 ht hp (by simp [hp]) rfl)⟩

/-! ### Certification covers the kernel's returns -/

/-- An error return (`r ≥ 2^64 - maxErrno`) is one of `results`' errors. -/
theorem mem_errs {r : BitVec 64} (h : 2 ^ 64 - maxErrno ≤ r.toNat) :
    r ∈ (List.range maxErrno).map fun e => neg (e + 1) := by
  have hr := r.isLt
  simp only [List.mem_map, List.mem_range]
  refine ⟨2 ^ 64 - r.toNat - 1, by unfold maxErrno at *; omega, ?_⟩
  apply BitVec.eq_of_toNat_eq
  simp only [neg, BitVec.toNat_neg, BitVec.toNat_ofNat]
  unfold maxErrno at h
  omega

/-- A count up to `n` is one of `results`' counts. -/
theorem mem_counts {r : BitVec 64} {n : Nat} (h : r.toNat ≤ n) : r ∈ (List.range (n + 1)).map (BitVec.ofNat 64) :=
  List.mem_map.mpr ⟨r.toNat, List.mem_range.mpr (by omega), by simp⟩

/-- **The shape of a return of `sysStep`**: the value is one of `results`,
and the thread is `retThread` of the calling thread at its own state, or at
`arch_prctl` with the thread pointer set. -/
theorem sysStep_ret_shape {A : Arch} {tid : Nat} {c c' : Config I × KState} {r : BitVec 64} {es : List Ev}
    {t : Thread I} {call : Call} (ht : c.1.threads[tid]? = some t) (hc : callOf K t = some call)
    (h : sysStep K A tid c (.ret r) = some (es, c'))
    (hwr : ∀ fd buf n, call = .write fd buf n → c.2.wr tid ≤ n) (hx : call ≠ .exit)
    (hg : ∀ v, call ≠ .exitGroup v) :
    r ∈ results call ∧ ∃ s0, c'.1.threads[tid]? = some (retThread K { t with st := s0 } r) ∧
      ((∀ a, call ≠ .archSetFs a) ∧ s0 = t.st ∨ ∃ a, call = .archSetFs a ∧ s0 = K.setTp t.st a) := by
  have hlt : tid < c.1.threads.size := (Array.getElem?_eq_some_iff.mp ht).1
  have hback : ∀ (s0 : I.State) (x : KState) (es' : List Ev),
      back K tid c { t with st := s0 } r x es' = some (es, c') →
        c'.1.threads[tid]? = some (retThread K { t with st := s0 } r) := by
    intro s0 x es' hb
    simp only [back, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨-, rfl⟩ := hb
    simp [withThread_get, hlt]
  have hb0 : ∀ (x : KState) (es' : List Ev), back K tid c t r x es' = some (es, c') →
      c'.1.threads[tid]? = some (retThread K { t with st := t.st } r) := fun x es' hb => hback t.st x es' hb
  unfold sysStep at h
  rw [ht] at h
  simp only at h
  split at h
  · cases h
  rw [hc] at h
  cases call with
  | exit => exact absurd rfl hx
  | exitGroup v => exact absurd rfl (hg v)
  | write fd buf n =>
    simp only at h
    split at h
    · split at h
      · rename_i hj hrj
        refine ⟨List.mem_append_left _ (mem_counts ?_), _, hb0 _ _ h, .inl ⟨fun _ => Call.noConfusion, rfl⟩⟩
        subst hrj
        have := hwr fd buf n rfl
        simp [BitVec.toNat_ofNat]; omega
      · cases h
    · split at h
      · rename_i hr
        refine ⟨List.mem_append_right _ (mem_errs ?_), _, hb0 _ _ h, .inl ⟨fun _ => Call.noConfusion, rfl⟩⟩
        rcases hr with rfl | rfl <;> simp [neg, eintr, eagain, maxErrno]
      · split at h
        · rename_i hr
          refine ⟨?_, _, hb0 _ _ h, .inl ⟨fun _ => Call.noConfusion, rfl⟩⟩
          simp only [writeRefused, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq,
            bne_iff_ne, ne_eq] at hr
          rcases hr with rfl | ⟨⟨hr, -⟩, -⟩
          · exact List.mem_append_left _ (mem_counts (by simp))
          · exact List.mem_append_right _ (mem_errs hr)
        · cases h
  | futexWait =>
    simp only at h
    split at h
    · rename_i hr
      refine ⟨?_, _, hb0 _ _ h, .inl ⟨fun _ => Call.noConfusion, rfl⟩⟩
      simp only [futexWaitRet, Bool.or_eq_true, beq_iff_eq] at hr
      simp only [results, List.mem_cons, List.mem_nil_iff, or_false]
      rcases hr with (h | h) | h <;> simp [h]
    · cases h
  | futexWake n =>
    simp only at h
    split at h
    · rename_i hr
      exact ⟨mem_counts hr, _, hb0 _ _ h, .inl ⟨fun _ => Call.noConfusion, rfl⟩⟩
    · cases h
  | rtSigaction =>
    simp only at h
    split at h
    · rename_i hr
      subst hr
      exact ⟨by simp [results], _, hb0 _ _ h, .inl ⟨fun _ => Call.noConfusion, rfl⟩⟩
    · cases h
  | archSetFs a =>
    simp only at h
    split at h
    · rename_i hr
      subst hr
      exact ⟨by simp [results], _, hback _ _ _ h, .inr ⟨a, rfl, rfl⟩⟩
    · cases h
  | clone stack tls =>
    simp only at h
    split at h
    · rename_i hr
      refine ⟨List.mem_append_right _ ?_, _, hb0 _ _ h, .inl ⟨fun _ => Call.noConfusion, rfl⟩⟩
      rcases hr with rfl | rfl <;> simp
    · cases h

/-- **Every return of `sysStep` is a branch of `certExec`**: a step
returning `r` to thread `tid` from a call other than `exit` and
`exit_group` leaves the thread in one of the states `certSuccs` lists
(`sysStep_ret_shape`). For `write` this needs the invariant that at most
`n` bytes are out (`wr ≤ n`), which the byte steps keep (they need
`wr < n`). The certification step itself is `certSem_step_of_sysStep`
(`Scc/Sem/CertStep.lean`), for calls other than `clone` and `write`. -/
theorem sysStep_ret_mem {A : Arch} {tid : Nat} {c c' : Config I × KState} {r : BitVec 64} {es : List Ev}
    {t : Thread I} {call : Call} (ht : c.1.threads[tid]? = some t) (hc : callOf K t = some call)
    (h : sysStep K A tid c (.ret r) = some (es, c'))
    (hwr : ∀ fd buf n, call = .write fd buf n → c.2.wr tid ≤ n) (hx : call ≠ .exit)
    (hg : ∀ v, call ≠ .exitGroup v) :
    ∃ t', c'.1.threads[tid]? = some t' ∧ t'.st ∈ certSuccs K t.st call := by
  obtain ⟨hr, s0, ht', hs0⟩ := sysStep_ret_shape ht hc h hwr hx hg
  refine ⟨_, ht', ?_⟩
  rw [retThread_st]
  rcases hs0 with ⟨hna, rfl⟩ | ⟨a, rfl, rfl⟩
  · cases call
    case archSetFs a => exact absurd rfl (hna a)
    all_goals exact List.mem_map.mpr ⟨r, hr, rfl⟩
  · simp only [results, List.mem_singleton] at hr
    subst hr; simp [certSuccs]

/-- **Every successful `clone` returns to the parent a branch of
`certExec`**, up to the parent's private memory: the parent resumes in
`Abi.ret` of a thread id that `results` lists, in its own state, or (when
it hands the child its stack range, §2.6) in its state with that range
erased from its private memory. That erasure is the one effect of a
returning call that `certExec` does not follow; `certSem` follows no
return of `clone` at all (`soloExec`). -/
theorem spawnStep_ret_mem {tid j : Nat} {c c' : Config I × KState} {ctid : BitVec 64} {t : Thread I}
    {stack tls : Nat} (ht : c.1.threads[tid]? = some t) (hc : callOf K t = some (.clone stack tls))
    (h : spawnStep K tid c j ctid = some c') :
    ctid ∈ results (.clone stack tls) ∧ ∃ t', c'.1.threads[tid]? = some t' ∧
      (t'.st ∈ certSuccs K t.st (.clone stack tls) ∨
        ∃ r, t'.st = K.ret (K.setDmem t.st (eraseRange (K.dmem t.st) r)) ctid) := by
  have hlt : tid < c.1.threads.size := (Array.getElem?_eq_some_iff.mp ht).1
  unfold spawnStep at h
  rw [ht] at h
  simp only at h
  split at h
  · cases h
  rename_i hrd
  rw [hc] at h
  simp only at h
  split at h
  · rename_i hcond
    obtain ⟨hdor, -, hpos, hpid⟩ := hcond
    have hjt : j ≠ tid := by
      rintro rfl
      simp [ready, KState.runs, hdor] at hrd
    have hres : ctid ∈ results (.clone stack tls) := by
      simp only [results, List.mem_append, List.mem_map]
      refine .inl ⟨ctid.toNat, ?_, by simp⟩
      simp only [List.mem_range'_1]
      omega
    refine ⟨hres, ?_⟩
    split at h
    · cases h
      refine ⟨retThread K t ctid, by simp [withThread_get, hjt, hlt], .inl ?_⟩
      simp only [retThread_st, certSuccs, List.mem_map]
      exact ⟨ctid, hres, rfl⟩
    · rename_i o r _
      cases h
      exact ⟨retThread K { t with st := K.setDmem t.st (eraseRange (K.dmem t.st) r) } ctid,
        by simp [withThread_get, hjt, hlt], .inr ⟨r, retThread_st _ _⟩⟩
  · cases h

/-- **`clone` with every slot used is a fault** (K6b): a running thread at a
`clone` the kernel supports, with no dormant slot left. -/
theorem fault_clone_full (A : Arch) (n : Nat) {c : Config I × KState} {tid : Nat} {t : Thread I}
    {stack tls : Nat} (ht : c.1.threads[tid]? = some t) (hr : c.2.runs tid = true) (hx : c.2.exited = none)
    (hs : K.atSys t.st = true) (hc : callOf K t = some (.clone stack tls)) (hd : c.2.dormants = []) :
    (hooks K A n).fault c :=
  .inl ⟨tid, by simp [faultAt, ht, hr, hx, hs, hc, hd]⟩

/-- **An access outside the mapped regions is a fault** (K11): a running
thread whose next instruction may reach a shared access to a location not
mapped for it. -/
theorem fault_of_unmapped (A : Arch) (n : Nat) {c : Config I × KState} {tid : Nat}
    (h : unmappedAt K c tid) : (hooks K A n).fault c :=
  .inr ⟨tid, h⟩

/-! ### Range transfers -/

/-- A lookup after inserting the bytes of `src` at the addresses `L`. -/
theorem get_foldl_insert (src : _root_.Mem 64) (L : List (BitVec 64)) (a : BitVec 64) :
    ∀ dst : _root_.Mem 64, (L.foldl (fun m b => m.insert b (byte src b)) dst)[a]? =
      if a ∈ L then some (byte src a) else dst[a]? := by
  induction L with
  | nil => intro dst; simp
  | cons x L ih =>
    intro dst
    rw [List.foldl_cons, ih, Std.ExtHashMap.getElem?_insert]
    by_cases hL : a ∈ L
    · simp [hL]
    · by_cases hx : x = a
      · subst hx
        simp
      · have hx' : (x == a) = false := by simpa using hx
        have ha : a ≠ x := fun h => hx h.symm
        simp [hL, hx', ha]

/-- A lookup after erasing the addresses `L`. -/
theorem get_foldl_erase (L : List (BitVec 64)) (a : BitVec 64) :
    ∀ m : _root_.Mem 64, (L.foldl (fun m b => m.erase b) m)[a]? = if a ∈ L then none else m[a]? := by
  induction L with
  | nil => intro m; simp
  | cons x L ih =>
    intro m
    rw [List.foldl_cons, ih, Std.ExtHashMap.getElem?_erase]
    by_cases hL : a ∈ L
    · simp [hL]
    · by_cases hx : x = a
      · subst hx
        simp
      · have hx' : (x == a) = false := by simpa using hx
        have ha : a ≠ x := fun h => hx h.symm
        simp [hL, hx', ha]

/-- **`copyRange` copies exactly the range.** -/
theorem byte_copyRange (src dst : _root_.Mem 64) (r : Range) (a : BitVec 64) :
    byte (copyRange src dst r) a = if a ∈ addrs r then byte src a else byte dst a := by
  unfold byte copyRange
  rw [get_foldl_insert]
  split <;> rfl

/-- **`eraseRange` unmaps exactly the range.** -/
theorem get_eraseRange (m : _root_.Mem 64) (r : Range) (a : BitVec 64) :
    (eraseRange m r)[a]? = if a ∈ addrs r then none else m[a]? :=
  get_foldl_erase (addrs r) a m

/-- `eraseRange` clears exactly the range (bytes). -/
theorem byte_eraseRange (m : _root_.Mem 64) (r : Range) (a : BitVec 64) :
    byte (eraseRange m r) a = if a ∈ addrs r then 0 else byte m a := by
  unfold byte
  rw [get_eraseRange]
  split <;> rfl

/-- **The transfer is deterministic**: at most one transfer of each kind
from a configuration (the range is the one the thread's registers name, not
a choice). -/
theorem xfer_det (A : Arch) (n : Nat) {k : XferKind} {tid : Nat} {c c1 c2 : Config I × KState}
    (h1 : (hooks K A n).xfer k tid c c1) (h2 : (hooks K A n).xfer k tid c c2) : c1 = c2 :=
  Option.some.inj (h1.symm.trans h2)

/-- **A thread at the take site takes the range its registers name**, if it
is fresh: the range moves into its private memory and is held by it. -/
theorem xfer_take (A : Arch) (n : Nat) {c : Config I × KState} {tid : Nat} {t : Thread I}
    (ht : c.1.threads[tid]? = some t) (hr : c.2.runs tid = true) (hx : c.2.exited = none)
    (hn : K.atNop t.st = true) (hf : fresh c (siteRange K t.st) = true) :
    (hooks K A n).xfer .take tid c
      (c.1.withThread tid
          { t with st := K.skip (K.setDmem t.st (copyRange c.2.pmem (K.dmem t.st) (siteRange K t.st))) } c.1.mem,
        { c.2 with held := (tid, siteRange K t.st) :: c.2.held, pmem := eraseRange c.2.pmem (siteRange K t.st) }) := by
  show takeStep K tid c = _
  simp [takeStep, ht, hr, hx, hn, hf] <;> rfl

/-- **What a take gives**: the taker's private memory on the range holds
the pool's bytes (`pmem`), and the pool no longer has them. -/
theorem take_bytes {c c' : Config I × KState} {tid : Nat} {t : Thread I} (ht : c.1.threads[tid]? = some t)
    (h : takeStep K tid c = some c') :
    ∃ t', c'.1.threads[tid]? = some t' ∧ (tid, siteRange K t.st) ∈ c'.2.held ∧
      ∀ a ∈ addrs (siteRange K t.st), byte (K.dmem t'.st) a = byte c.2.pmem a ∧ byte c'.2.pmem a = 0 := by
  simp only [takeStep, ht] at h
  split at h
  · cases h
    refine ⟨_, ExtMachine.withThread_self ht, by simp, fun a ha => ?_⟩
    simp [K.dmem_skip, K.dmem_setDmem, byte_copyRange, byte_eraseRange, ha]
  · cases h

/-- **What a release keeps**: the pool holds the releaser's bytes on the
range, the releaser no longer has the range mapped, and no longer holds
it. -/
theorem release_bytes {c c' : Config I × KState} {tid : Nat} {t : Thread I} (ht : c.1.threads[tid]? = some t)
    (h : releaseStep K tid c = some c') :
    ∃ t', c'.1.threads[tid]? = some t' ∧ c'.2.held = c.2.held.erase (tid, siteRange K t.st) ∧
      ∀ a ∈ addrs (siteRange K t.st), byte c'.2.pmem a = byte (K.dmem t.st) a ∧ (K.dmem t'.st)[a]? = none := by
  simp only [releaseStep, ht] at h
  split at h
  · cases h
    refine ⟨_, ExtMachine.withThread_self ht, rfl, fun a ha => ⟨?_, ?_⟩⟩
    · simp [byte_copyRange, ha]
    · simp [K.dmem_skip, K.dmem_setDmem, get_eraseRange, ha]
  · cases h

/-- **Handoff through the pool**: if thread `tid` releases a range and
thread `tid'` then takes the same range, the taker's private memory on the
range holds exactly what the releaser's held: a reused stack range is
handed over intact (on hardware, given the lock protocol, `Scc/DESIGN.md`
§2.6). -/
theorem release_take_handoff {c c1 c2 : Config I × KState} {tid tid' : Nat} {t t1 : Thread I}
    (ht : c.1.threads[tid]? = some t) (hrel : releaseStep K tid c = some c1)
    (ht1 : c1.1.threads[tid']? = some t1) (hsame : siteRange K t1.st = siteRange K t.st)
    (htake : takeStep K tid' c1 = some c2) :
    ∃ t2, c2.1.threads[tid']? = some t2 ∧
      ∀ a ∈ addrs (siteRange K t.st), byte (K.dmem t2.st) a = byte (K.dmem t.st) a := by
  obtain ⟨_, -, -, hp⟩ := release_bytes ht hrel
  obtain ⟨t2, ht2, -, hb⟩ := take_bytes ht1 htake
  refine ⟨t2, ht2, fun a ha => ?_⟩
  have ha1 : a ∈ addrs (siteRange K t1.st) := by rw [hsame]; exact ha
  rw [(hb a ha1).1, (hp a ha).1]

/-- **The transfer is forced** (the regression for `Step.xfer`): a thread
of the kernel model's machine at the take site, at no release site and not
at a system call, takes no instruction step, no spawn and no system call;
its only step is the take of the range its registers name. -/
theorem step_at_take {A : Arch} {n : Nat} {rv : I.State → I.RegId → BitVec 64}
    {pl : I.State → BitVec 64 → Option (BitVec 64)} {pcf : I.State → Nat} {μ : Marks}
    {c c' : Config I × KState} {tid : Nat} {es : List Ev} {t : Thread I}
    (ht : c.1.threads[tid]? = some t) (hsys : K.atSys t.st = false)
    (hs : (ExtMachine.ofHooks I A (hooks K A n) rv pl pcf).AtSite μ .take c tid)
    (hnr : ¬ (ExtMachine.ofHooks I A (hooks K A n) rv pl pcf).AtSite μ .release c tid)
    (h : (ExtMachine.ofHooks I A (hooks K A n) rv pl pcf).Step μ tid c es c') :
    es = [] ∧ takeStep K tid c = some c' := by
  rcases ExtMachine.Step.at_site h hs with ⟨j, r, hsp⟩ | ⟨p, hsy⟩ | ⟨hes, k', hk', hx⟩
  · simp [spawnStep, ht, ready, hsys] at hsp
  · cases p <;> simp [sysStep, ht, ready, hsys] at hsy
  · cases k' with
    | take => exact ⟨hes, hx⟩
    | release => exact absurd hk' hnr

end Scc.Sem.Kernel
