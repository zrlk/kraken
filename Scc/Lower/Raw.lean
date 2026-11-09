import Scc.Lower.Spec

/-!
# The `--host raw` lowering

`--host raw` (the raw ABI) emits a unit that a kernel loads and enters
with a thread control block installed, instead of a Linux executable. The compiled part is the
same as on Linux: the user functions, `scc_rt_main` (the unit's entry), the thread entries
`scc_rt_thr_<f>` and the morestack trampoline. The kernel provides everything that wraps a
system call or owns a shared resource: the allocators, `print`, `park` / `unpark`, the abort
routine, the stack pool and `grow`, the thread start, and thread and process exit. There is no
`_start`, no `rt_sigaction` and no `arch_prctl`, and no system call instruction anywhere.

The routines are reached through the TCB: `Tcb.kabi` holds the address of the kernel's routine
table, and the emitters write one local trampoline per routine (`Scc.Emit.X64.emitKabi`,
`Scc.Emit.A64.kabiItems`) that jumps through its slot (`slots`). Compiled code keeps calling the
routine's symbol, exactly as on Linux.

`rawIR` builds the raw program from the Linux lowering (`lowerWithMarks`, unchanged):

* it drops the runtime functions the kernel provides (`provided`), and the runtime's data;
* in the functions it keeps, the two exits become routine calls: `exit_group(c)` in
  `scc_rt_main` becomes `scc_rt_exit_process(c)`, and `exit(0)` in a thread entry becomes
  `scc_rt_exit_thread()`; any other system call is refused;
* a spawn's `clone` becomes a call of `scc_rt_spawn` (`spawnCall`). Its arguments are
  `Inst.clone`'s operands in the order of the routine's C prototype (platform §2):
  - the child's TCB (`tls`);
  - the top of its stack (`stack`);
  - the entry (the address of `scc_rt_thr_<f>`);
  - the entry's first argument (`arg`);
  - then the entry's other argument words, the operands Linux moves into the `spawnReg`
    registers right before the `clone`, in their order.
  The result is the routine's: negative when the thread could not be created, which takes the
  same `threads` abort branch as a failed `clone` on Linux.
  The full fence the Linux lowering puts right before the `clone` stays: the caller executes
  it before the argument moves and the call, and only those moves lie between the fence and
  the call (the entry's address is taken before the fence). The routine reads its arguments in the caller's thread, and the child starts from
  the caller's view at the fence; the caller does not rely on the routine for a barrier.
* the entry symbol is `scc_rt_main` (`Program.start`), with `Program.host = .raw`.

The stack budget is recomputed on the raw program (`rawBudget`, the formula of `stackBudget`):
a spawning function's frame differs from the Linux one.

Untrusted: nothing certifies a raw unit yet.
-/

open CoreLang CoreTerm
open Scc.IR

namespace Scc.Lower

namespace Names

/-- `--host raw`: the kernel's thread exit (`exited := 1` is stored before the call). -/
def exitThread : Sym := "scc_rt_exit_thread"
/-- `--host raw`: the kernel's process exit, with `main`'s status. -/
def exitProcess : Sym := "scc_rt_exit_process"
/-- `--host raw`: the kernel's thread start, the raw twin of Linux's `clone`. -/
def spawn : Sym := Tcb.spawnSym

end Names

namespace Raw

/-- **The kernel routine table's slots** (C name `enum scc_kabi_slot`): the
routine at slot `n` is called through the word at byte `8·n` of the table that the TCB's
`kabi` word points to. The order never changes. The list is `Tcb.kabiSlots` (which the
emitters read); `slots_names` checks its symbols against the runtime's names. -/
def slots : List (Sym × Nat) := Tcb.kabiSlots

/-- The slots' symbols are the runtime's routine names. -/
theorem slots_names : slots =
    [(Names.alloc, 0), (Names.allocTcb, 1), (Names.print, 2), (Names.park, 3),
     (Names.unpark, 4), (Names.abort, 5), (Names.exitThread, 6), (Names.exitProcess, 7),
     (Names.stackTake, 8), (Names.stackRelease, 9), (Names.grow, 10),
     (Names.threadReserve, 11), (Names.threadInit, 12), (Names.spawn, 13)] := rfl

/-- The spawn routine's symbol is `IR.Tcb.spawnSym`. -/
theorem spawn_name : Names.spawn = "scc_rt_spawn" := rfl

/-- The number of slots (`KABI_N`). -/
def slotCount : Nat := slots.length

/-- The runtime functions of the Linux lowering that a raw unit does not contain: the kernel
provides them (the routines of `slots`), or they have no raw counterpart (the start routine,
the per-kind abort routines, which write the message and exit the process). -/
def provided : List Sym :=
  Names.start :: slots.map (·.1) ++ Runtime.abortKinds.map Names.abortKind

/-- The register a raw spawn holds its entry's address in (`%` keeps it apart from the
lowering's registers, as `IR.spawnReg`). -/
def entryReg : Reg := "%spawnentry"

/-- **A spawn on raw** (see the module docstring): the `clone` `d := clone(stack, tls, entry,
arg)` with the argument words `ws` (the operands moved into the `spawnReg` registers before it),
and its fence, as the address of `entry`, the full fence and a call of `scc_rt_spawn`: only the
call's argument moves come between the fence and the call. -/
def spawnCall (d : Reg) (stack tls : Operand) (entry : Sym) (arg : Operand) (ws : List Operand) :
    List Inst :=
  [.la entryReg entry, .fence .full, .call [d] Names.spawn ([tls, stack, .reg entryReg, arg] ++ ws)]

/-- The index `k` of a `spawnReg k` register. -/
def spawnIdx? (r : Reg) : Option Nat :=
  (List.range maxSpawnArgs).find? fun k => k ≠ 0 && spawnReg k == r

/-- **A block's instructions on raw**: the exits as routine calls, a `clone` as a spawn call
(`spawnCall`, its argument words the `spawnReg` moves since the last `clone` of the block, which
are dropped), any other system call refused. The full fence right before a `clone` (the Linux
lowering's) is required and kept: `spawnCall` puts it after the entry's address, before the
call's argument moves.
`f` names the function in errors. -/
def rawInsts (f : Sym) (is : List Inst) : Except String (List Inst) := do
  let mut out : Array Inst := #[]
  let mut ws : List (Nat × Operand) := []
  for i in is do
    match i with
    | .mov r v =>
      match spawnIdx? r with
      | some k => ws := ws.filter (·.1 != k) ++ [(k, v)]
      | none => out := out.push i
    | .syscall _ .exitGroup [c] none => out := out.push (.call [] Names.exitProcess [c])
    | .syscall _ .exit [_] none => out := out.push (.call [] Names.exitThread [])
    | .syscall _ nr _ _ => throw s!"--host raw: {f}: system call {repr nr} has no raw routine"
    | .clone d stack tls entry arg =>
      let ks := ws.map (·.1)
      if ks != (List.range ks.length).map (· + 1) then
        throw s!"--host raw: {f}: the argument words of the spawn of {entry} are not all in its block"
      if out.back? != some (.fence .full) then
        throw s!"--host raw: {f}: the spawn of {entry} without its fence"
      out := out.pop
      out := out ++ (spawnCall d stack tls entry arg (ws.map (·.2))).toArray
      ws := []
    | _ => out := out.push i
  if !ws.isEmpty then throw s!"--host raw: {f}: a spawn argument word without its spawn"
  pure out.toList

/-- A function on raw (`rawInsts` per block). -/
def rawFunc (f : Func) : Except String Func := do
  let blocks ← f.blocks.mapM fun b => do pure { b with insts := ← rawInsts f.name b.insts }
  pure { f with blocks }

/-- Whether a function of the Linux lowering stays in a raw unit: `scc_rt_main`, a thread
entry, or a compiled code block (`Names.user`). -/
def kept (f : Func) : Bool :=
  f.name == Names.mainThread || f.name.startsWith "scc_rt_thr_" || f.name.startsWith "wc_"

/-- **The raw program of a Linux lowering** (see the module docstring). Refuses a function it
neither drops nor keeps, and a system call it cannot replace. -/
def rawIR (p : Program) : Except String Program := do
  if p.host != .linux then throw "--host raw: the program is not a Linux lowering"
  let fs := p.funcs.filter fun f => !provided.contains f.name
  if let some f := fs.find? (!kept ·) then
    throw s!"--host raw: unexpected runtime function {f.name}"
  let funcs ← fs.mapM rawFunc
  pure { p with funcs, data := [], start := Names.mainThread, host := .raw }

/-- **The stack depth limit of a raw program** (`stackBudget`'s formula on the raw program's
frames): `F` with `F · Fr + T + Fr + growExtra + headroom + growSlack ≤ cap`. -/
def rawBudget (cfg : Config) (c : Frontend.Checked) (p : Program) : Except String StackBudget := do
  let areas := StackMap.argAreas p (argRegCount cfg.arch)
  let user := c.prog.filterMap fun d =>
    if c.externs.any (·.1 == d.name) then none else some (Names.user d.name)
  let sz (f : Func) := frameBytes cfg.arch areas f
  let fr := p.funcs.foldl (fun m f => if user.contains f.name then max m (sz f) else m) 0
  let t := p.funcs.foldl (fun m f =>
    if f.checkStack && !user.contains f.name then max m (sz f) else m) 0
  let reserve := t + fr + growExtra
  let slack := Tcb.headroom + Runtime.growSlack
  let cap := cfg.layout.stackCapBytes
  if fr == 0 then throw "no code block to bound the stack depth of"
  if cap < reserve + slack + fr then
    throw s!"the stack cap of {cap} bytes holds no frame of {fr} bytes besides {reserve + slack} reserved bytes"
  pure { frames := (cap - reserve - slack) / fr, frameBytes := fr, reserve, slack, cap }

end Raw

/-- **The lowering of a checked program for `--host raw`** (`Raw.rawIR` of `lowerIR`'s
program, with the budget of the raw program). With `cfg.host = .linux` it is `lowerIR`. -/
def lowerIRHost (cfg : Config) (p : Prog) : Except String Lowered := do
  let l ← lowerIR cfg p
  match cfg.host with
  | .linux => pure l
  | .raw =>
    let ir ← Raw.rawIR l.ir
    let budget ← Raw.rawBudget cfg l.checked ir
    pure { l with ir, budget }

/-- **`--host linux` is the Linux lowering**: `lowerIRHost` is `lowerIR` there. -/
theorem lowerIRHost_linux {cfg : Config} {p : Prog} (h : cfg.host = .linux) :
    lowerIRHost cfg p = lowerIR cfg p := by
  unfold lowerIRHost
  rw [h]
  cases lowerIR cfg p <;> rfl

end Scc.Lower
