# System-call and thread-pointer instruction forms

Kraken's AArch64 and x64 models include the instruction forms a compiled
program needs to reach the kernel and to address its thread control block
through the thread pointer. This file lists the forms, their semantics, and
the extension point where a later system-call step replaces the current halt.

## Forms

| ISA | Assembly (GNU `as`) | Syntax constructor |
|---|---|---|
| AArch64 | `svc #imm16` | `Operation.SVC imm` |
| AArch64 | `mrs Xt, tpidr_el0` (also `s3_3_c13_c0_2`) | `Operation.MRS Xt .TPIDR_EL0` |
| AArch64 | `msr tpidr_el0, Xt` | `Operation.MSR .TPIDR_EL0 Xt` |
| x64 | `syscall` | `Operation.syscall` |
| x64 | `mov[bwlq] %fs:disp(base,index,scale), reg`, `mov[bwlq] %fs:disp, reg` | `Operation.movfs (.reg r) (.mem a)` |
| x64 | `mov[bwlq] reg, %fs:…`, `mov[bwlq] $imm, %fs:…` | `Operation.movfs (.mem a) src` |
| x64 | `cmp[bwlq] %fs:…, reg`, `cmp[bwlq] reg, %fs:…`, `cmp[bwlq] $imm, %fs:…` | `Operation.cmpfs a b` |
| x64 | `ud2` | `Operation.ud2` |

`Xt` is a 64-bit register or `XZR`. `SysReg` has the one constructor
`TPIDR_EL0`; other system registers are parse errors. The x64 printer
(`Kraken/X64/PrintIntel.lean`) prints `movfs` as
`mov … QWORD PTR fs:[…]` (and `cmpfs` as `cmp … fs:[…]`). Only `mov` and
`cmp` take a `%fs:` operand: other instructions with one are parse errors, and
a compiler targeting Kraken loads the thread-control-block word into a
register first. `wrfsbase`/`rdfsbase` are not modelled: Linux sets
the `%fs` base with `arch_prctl(ARCH_SET_FS)` or `clone(CLONE_SETTLS)`, both
system calls.

The new constructors come last in each `Operation`, so the derived `Hashable`
of every existing instruction (and hence `Program.fakeLayout` and every
layout derived from a hash) is unchanged.

## Semantics

**Thread pointer.** `Reg64s.TPIDR_EL0` (AArch64) and `Reg64s.fsBase` (x64) are
new fields of the register file, initially 0. They are private to the thread
like the general registers: no memory event and no view.

- `MRS Xt, TPIDR_EL0` writes the register's value to `Xt`; `MSR TPIDR_EL0, Xt`
  writes `Xt` to it (`Reg64s.getSysReg`/`setSysReg`). Both are register moves
  (`done` effects only).
- `movfs dst src` is `mov dst src` with `fsBase` added to the memory operand's
  address: the effective address at the instruction's address size,
  zero-extended to 64 bits, plus `fsBase` (`AddrExpr.interpSeg`). The access
  is then an ordinary `MachineData.load`/`store`: inside `dmem` a private
  access, outside it a plain `nonmem_load`/`nonmem_store` event, by the
  existing mappedness rule.
- `cmpfs a b` is `cmp a b` with the memory operand read as `movfs` reads its
  source; only the flags change.

**System call.** `SVC #imm` and `syscall` halt the thread with a distinguished
status, with no memory effect and the registers untouched:
`MachineData.pendingSyscall` returns the effect `Effects.syscall info ret`,
which records the call (`SyscallInfo`) and keeps the continuation `ret` after
the instruction, and which every existing consumer treats exactly as
`Effects.unimplemented` with the message `pending system call: svc #<imm>`
(AArch64) or `pending system call: syscall` (x64). Consequences:

- the sequential evaluator (`Executable.eval`) stops with that error;
- the program logics (`Effects.All`-style weakest preconditions) can prove
  nothing past it;
- the Promising adapters (`Kraken.Promising.AArch64.toEv`, `X64.toEv`) map it,
  like every `unimplemented`, to `EvTree.fault` with that message, so the
  explorers report it as a fault and no event is emitted at or after it;
- only the certification mode below uses the continuation.

The alternative of making `exec` return `none` (the existing halt at the end of
a thread) was not taken: `exec` is unfolded by many existing proofs, and a halt
there would make a thread stopped at a system call indistinguishable from one
that ran to its end, so postconditions "at the end" would silently cover it.
The fault is conservative for every existing theorem form: safety and
no-fault results do not hold for a program that reaches a system call, and no
termination result can count it as finished.

**Trap.** `ud2` faults with `Effects.unimplemented ud2Msg` before any
effect: the same outcome as the system call, with its own message.

**Dependencies** (`Kraken/AArch64/Deps.lean`, `Kraken/X64/Deps.lean`).
`TPIDR_EL0` and `fsBase` are not `RegId`s. `MRS` defines `Xt` from no tracked
register, `MSR` reads `Xt` and defines none (a dependency carried through the
thread pointer is dropped, which only weakens the memory model's ordering); a
`%fs:` move has the dependencies of `mov`, its address registers being the
operand's base and index only. `SVC`/`syscall`/`ud2` read and write no register yet.

**Lowerability.** The AArch64 forms are allowed by `Instr.WCLowerable`
(`Kraken/Promising/Lower/Lowerable.lean`) without a clause: none has a memory
event (`MRS`/`MSR` are register moves, `SVC` emits nothing before its fault).
x64 has no such predicate; there `syscall` and `ud2` are the same halt and a
`%fs:` move is an ordinary load or store.

## Extension point

The system-call step is one definition per ISA:

- `MachineData.pendingSyscall (s : MachineData) (imm : Nat) (next : MachineData → Effects)`
  in `Kraken/AArch64/Semantics.lean`;
- `MachineData.pendingSyscall (s : MachineData) (p : Std.Rco Int64) (next : MachineData → Effects)`
  in `Kraken/X64/Semantics.lean` (`p` is the instruction's address range, for
  the return address `SyscallInfo.nextPc`).

Both receive the state at the instruction and the continuation after it, so the
real step (the system-call number and arguments from `X8`/`X0`–`X5` or
`rax`/`rdi`…, a trace event for `write` and `exit_group`, `clone` with
`CLONE_SETTLS` setting the child's `TPIDR_EL0`/`fsBase`, `futex`, and on x64
`rcx`/`r11` clobbered) can replace the body without touching the instruction
semantics. Its design, and the kernel model it implements, are in
`Scc/DESIGN.md`. The register dependencies of `SVC`/`syscall` and the
`WCLowerable` argument above must be revisited with it.

## Certification mode

A Promising thread may promise a write only if it can certify it, running
alone; with the system call a fault, no write after a system call can be
promised, which under-approximates the behaviours of a program whose threads
make system calls. The certification mode lets certification continue past a
system call while every existing definition and theorem stays as it is.

**The effect.** `Effects.syscall info ret` (last constructor of `Effects` in
each ISA) carries:

- AArch64: `SyscallInfo` with the immediate `imm`, the number `num` (`X8`) and
  the arguments `args` (`X0`–`X5`); `ret : BitVec 64 → Effects` writes the
  result to `X0` and continues after the instruction;
- x64: `SyscallInfo` with the number `num` (`rax`), the arguments `args`
  (`rdi`, `rsi`, `rdx`, `r10`, `r8`, `r9`) and the return address `nextPc`;
  `ret : SyscallRet → Effects` writes `rax`, `rcx` and `r11` and continues
  after the instruction.

`Effects.All` and its variants are `False` on it, `Executable.eval` stops with
the pending-system-call error, `toEv` faults with it.

**The results.** What a system call may return is a parameter
`results : SyscallInfo → List (BitVec 64)` (AArch64) or
`results : SyscallInfo → List SyscallRet` (x64): a finite over-approximation
of the results of each call, supplied by the client (Kraken has no model of
any system call). `Kraken.Promising.AArch64.toEvCert results` and
`X64.toEvCert results` are `toEv` except that `.syscall info ret` is
`EvTree.choose` over `results info`, each branch continuing with `ret`; an
empty list is a dead end (`choose 0`), not a fault. `execCert results` is
`exec` with `toEvCert` (same halting); `AArch64.execLSE2Cert` is the same for
`isaLSE2`.

**The machine** (`Kraken/Promising/Machine.lean`, section `CertWith`).
`stepOneWith`, `certifyWith`, `certifiedPromisesWith`, `succsLWith`,
`succsRWith` and `exploreWith` are copies of `stepOne`, `certify`,
`certifiedPromises`, `succsL`, `succsR` and `explore` that take
`cexec : I.State → Option (EvTree I.State)` (e.g. `execCert results`) and use
it for certification only. The machine's own steps still use `I.exec`, so a
thread that reaches a system call still faults there; what changes is the set
of writes it may promise before. A certified trace must still end with no
outstanding promise, exactly as in `certify`. `cexec` must halt where
`I.exec` does; a certification cache is specific to the mode. No theorem is
stated about this mode, and none of the existing ones covers it.

Tests: `Kraken/Promising/SyscallCertTestsA64.lean` and
`Kraken/Promising/SyscallCertTestsX64.lean`.

**Rows** (`CellAt st d sz` the only hypothesis on the cell):
`Kraken/Promising/Lower/EventsA64Sys.lean` (`exec_svc`, `execCert_svc`,
`exec_mrs`, `exec_msr`, `exec_nop`) and
`Kraken/Promising/Lower/EventsX64Sys.lean` (`exec_syscall`,
`execCert_syscall`, `exec_ud2`, `exec_nop`, `exec_movfs_load`). The
certification rows give the choice over `results` with each branch's state
written as a kernel model's return writes it (`svcRet`, `syscallRet`);
`CellAt.directive` and `CellAt.dirSize` give the directive at the pc and the
address after it. Examples: `Kraken/AArch64/Examples/LabelSys.lean`,
`Kraken/X64/Examples/LabelSys.lean`.
