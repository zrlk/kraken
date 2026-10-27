import Scc.Lower.Runtime

/-!
# Lowering a whole program

`lowerProgram` turns a program that passed the frontend into an IR
`Program`: one function per compiled code block (externs excluded), the
runtime functions, one thread trampoline per block that is spawned, and the
runtime's data.  A deep recursion takes the stack abort in the grow
routine when a frame no longer fits under the stack cap; `stackBudget`
gives the depth up to which it never does (the certificate's `B.frames`).
-/

open CoreLang CoreTerm
open Scc.IR

namespace Scc.Lower

/-- The blocks spawned anywhere in an expression. -/
def spawnedE : Expr → List String
  | .let_ _ (.spawn f _ _ _) e => f :: spawnedE e
  | .let_ _ _ e | .split _ _ _ e | .unpack _ _ _ e | .unpackT _ _ _ e => spawnedE e
  | .ifeq _ _ e₁ e₂ => spawnedE e₁ ++ spawnedE e₂
  | _ => []

/-- Lower a checked program for configuration `cfg` (the calls of code
blocks plain calls, without a depth counter); also return the placement
traces of the compiled code blocks (`lowerDeclMarks`), by IR function name,
in the order of `c.prog`. -/
def lowerWithMarks (cfg : Config) (c : Frontend.Checked) :
    Except String (Program × List (Sym × Array (Node × Point))) := do
  -- An object never exceeds the arena, so an arena below `2^32` bytes keeps
  -- each region of every object within the 32-bit byte offsets of a
  -- locative's offset word (`Scc/LAYOUT.md` §4).
  if cfg.layout.heapBytes ≥ 2 ^ 32 then
    throw s!"the heap arena of {cfg.layout.heapBytes} bytes is 4 GiB or more: locative offsets are 32-bit byte offsets"
  let p := c.prog
  let compiled := p.filter fun d => !(c.externs.any (·.1 == d.name))
  let userMarks ← compiled.mapM fun d => lowerDeclMarks p c.externs d cfg.layout.obj
  let user := userMarks.map (·.1)
  let spawned := (p.flatMap fun d => spawnedE d.body).eraseDups
  let thr ← spawned.mapM fun f => do
    let d ← match p.find? (·.name == f) with
      | some d => pure d
      | none => throw s!"spawn of unknown block '{f}'"
    Runtime.threadF cfg.layout.obj f d.argTy
  let setupWords ← match c.entry.arg with
    | .setupTid => match p.find? (·.name == "rodata") with
      | some r => match Obj.valWords r.retTy with
        | some n => pure n
        | none => throw "rodata: no runtime layout for its result"
      | none => throw "no setup block 'rodata'"
    | _ => pure 0
  let lay := cfg.layout
  let rt ← [Runtime.startF lay, Runtime.mainThreadF c.entry setupWords, Runtime.allocF lay,
    Runtime.allocF lay Names.allocTcb Names.pinned Names.pinnedNext (Runtime.pinnedBytes lay) .threads false,
    Runtime.threadReserveF lay,
    Runtime.threadInitF lay, Runtime.stackTakeF lay, Runtime.stackReleaseF lay, Runtime.growF lay,
    Runtime.printF, Runtime.parkF, Runtime.unparkF, Runtime.abortF] ++
    Runtime.abortKinds.map Runtime.abortKindF |>.mapM id
  pure ({ funcs := rt ++ thr ++ user, data := Runtime.data lay,
          start := Names.start, abortFn := Names.abort,
          growth := some { grow := Names.grow, release := Names.stackRelease } },
        userMarks.map fun (f, ms) => (f.name, ms))

/-- Lower a checked program for configuration `cfg`: `lowerWithMarks`
without the placement traces. -/
def lowerWith (cfg : Config) (c : Frontend.Checked) : Except String Program :=
  (·.1) <$> lowerWithMarks cfg c

/-! ## The stack depth limit

A thread's stack grows by doubling up to `Layout.stackCapBytes`; a frame
that does not fit then takes the stack abort outcome (`AbortKind.stack`)
inside the grow routine, the only stack abort: there is no depth counter.
`stackBudget` is the budget number `F` (the certificate's `B.frames`),
chosen so that the cap is not reached within it: with at most `F` calls of
code blocks live, the grow routine always finds a range of at most the cap,
so a thread within `F` frames never aborts on the stack.  A deeper thread
may run past `F` frames before it aborts (smaller frames fit longer), which
the statement allows: `AbortJustified`'s `stack` case asks only that some
step leave the depth above `B.frames`, not the exact crossing.

Why `F` below suffices (`stackBudget`):

* Only functions with `Func.checkStack` grow the stack: the code blocks and
  the trampolines (`scc_rt_main`, `scc_rt_thr_*`).  The runtime functions
  run in `Tcb.headroom` below the limit without a check, so they never ask
  for more stack.
* With `c ≤ F` calls of code blocks live, the live frames are one trampoline frame
  (at most `T` bytes) and `c + 1` code block frames (at most `Fr` bytes
  each): the entry block's frame is not counted (the setup block `rodata`
  returns before the entry block is called), and a tail call replaces its
  frame.
* The grow routine is entered from the prologue of the frame that did not
  fit; the live stack it measures from `fp` includes that frame, plus at
  most `growExtra` bytes of the grow stub (x64: the six saved registers and
  `morestack`'s return address and frame pointer, 56 bytes; A64: 96 bytes).
  It wants `used + need + headroom + growSlack` bytes and doubles from the
  current size; the current size and the cap are both `stackBytes · 2^m`,
  so the doubled size is at most the cap whenever the want is.
* So `want ≤ T + (F + 1) · Fr + growExtra + headroom + growSlack`, which is
  at most the cap by the choice of `F`.

The frame sizes are the emitters' (`frameBytes`, checked against them in
`Scc/Emit/X64Test.lean` and `Scc/Emit/A64Test.lean`), measured on the
program's lowering. -/

/-- The IR registers of a function: its parameters and the registers of its
instructions and terminators, without duplicates (the emitters' slots,
`Emit.X64.frameOf` and `Emit.A64.funcRegs`). -/
def frameRegs (f : Func) : List Reg :=
  let op : Operand → List Reg := fun | .reg r => [r] | .imm _ => []
  let inst : Inst → List Reg
    | .mov d s => d :: op s
    | .bin _ d a b => d :: op a ++ op b
    | .un _ d a => d :: op a
    | .ext _ _ d a => d :: op a
    | .setc _ d a b => d :: op a ++ op b
    | .select _ d a b t e => d :: op a ++ op b ++ op t ++ op e
    | .addChk d a b => d :: op a ++ op b
    | .subSat d a b => d :: op a ++ op b
    | .la d _ => [d]
    | .getTp d => [d]
    | .load _ _ d a => [d, a.base]
    | .store _ _ a v => a.base :: op v
    | .rmw _ d a v => d :: a.base :: op v
    | .fence _ => []
    | .call ds _ args => ds ++ args.flatMap op
    | .syscall d _ args _ => d :: args.flatMap op
    | .clone d s t _ a => d :: op s ++ op t ++ op a
    | .slotAddr d s => [d, s]
    | .site _ args => args.flatMap op
    | .comment _ => []
  let term : Term → List Reg
    | .ret vs => vs.flatMap op
    | .jmp _ => []
    | .br _ a b _ _ => op a ++ op b
    | .tail _ args => args.flatMap op
    | .switchTo s t _ a => op s ++ op t ++ op a
    | .unreachable => []
  (f.params ++ f.blocks.flatMap fun b => b.insts.flatMap inst ++ term b.term).eraseDups

/-- Argument registers of an architecture. -/
def argRegCount : Arch → Nat
  | .x64 => 6
  | .arm => 8

/-- The stack bytes a frame of `f` occupies on `arch`, from the caller's
stack pointer before the call to the frame's stack pointer: x64, the return
address, the saved `%rbp`, the register slots and the outgoing area
(`Emit.X64.frameOf`); A64, the frame (`Emit.A64.fnCtx`), which holds
`x29`/`x30`.  `areas` are the argument areas (`StackMap.argAreas`). -/
def frameBytes (arch : Arch) (areas : List (Sym × Nat)) (f : Func) : Nat :=
  let k := argRegCount arch
  let n := (frameRegs f).length
  let calls := f.blocks.foldl (fun n b => b.insts.foldl (fun n i => match i with
    | .call _ g args => max n (StackMap.callWords areas k g args.length)
    | _ => n) n) 0
  let out := (calls + 1) / 2 * 2
  match arch with
  | .x64 => (8 * n + 15) / 16 * 16 + 8 * out + 16
  | .arm => 8 * out + (8 * n + 16 + 15) / 16 * 16

/-- Bytes the grow stub adds below the frame that did not fit, before the
grow routine measures the live stack (x64 56, A64 96; see above). -/
def growExtra : Nat := 96

/-- The stack depth limit of a program and the numbers it comes from. -/
structure StackBudget where
  /-- The limit: the most calls of code blocks a thread may be in. -/
  frames : Nat
  /-- The largest frame of a code block (`frameBytes`). -/
  frameBytes : Nat
  /-- The bytes besides the counted frames: the largest trampoline frame,
  the uncounted entry frame and `growExtra`. -/
  reserve : Nat
  /-- `Tcb.headroom + growSlack`. -/
  slack : Nat
  /-- `Layout.stackCapBytes`. -/
  cap : Nat
  deriving Repr, Inhabited

/-- The budget holds: at least one frame, and `frames` frames with the
reserve and the slack fit in the cap. -/
def StackBudget.ok (b : StackBudget) : Bool :=
  1 ≤ b.frames && b.frames * b.frameBytes + b.reserve + b.slack ≤ b.cap

/-- The stack depth limit for `cfg` (see above): `F` such that
`F · Fr + T + Fr + growExtra + headroom + growSlack ≤ cap`, `Fr` the
largest code block frame and `T` the largest frame of the other
stack-checked functions (the trampolines). -/
def stackBudget (cfg : Config) (c : Frontend.Checked) : Except String StackBudget := do
  let p ← lowerWith cfg c
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
  let b : StackBudget := { frames := (cap - reserve - slack) / fr, frameBytes := fr, reserve, slack, cap }
  pure b

/-- The stack depth limit's definition in a code check file
(`Scc.Cert.Blocks.code`): `{pfx}Frames`, with a `#guard` that the budget
holds (`StackBudget.ok`, its numbers as literals). -/
def StackBudget.render (b : StackBudget) (pfx : String) : String :=
  s!"/-- **The stack depth limit**: the calls of code blocks a thread can be
in without a stack abort (the statement's `B.frames`); the stack abort is the
grow routine's, when a frame no longer fits under the cap.  The frames,
the largest of {b.frameBytes} bytes, with {b.reserve} bytes of trampoline frame, entry
frame and grow stub and {b.slack} bytes of headroom and grow slack, fit in the
stack cap of {b.cap} bytes (`Scc.Lower.stackBudget`). -/
def {pfx}Frames : Nat := {b.frames}

#guard 1 ≤ {pfx}Frames && {pfx}Frames * {b.frameBytes} + {b.reserve} + {b.slack} ≤ {b.cap}
"

/-! ## The stack need of the stack-checked functions

A thread's stack check (`Func.checkStack`) compares the stack pointer after
the new frame with the TCB's `stackLimit` word `L`.  For a program without
non-tail recursion, the most stack any stack-checked function `f` uses below
its entry stack pointer until it returns is finite (`stackNeed`):

    need f = max (frameE f + max over calls g of (callCost + need g))
                 (max over tail calls g of need g)

over the calls and tail calls of stack-checked functions (`frameE` is the
frame below the entry stack pointer: A64 `Emit.A64.fnCtx`'s frame; x64
`Emit.X64.frameOf`'s size and the saved `%rbp`; `callCost` is the return
address a call pushes: x64 8, A64 0).  The functions without a stack check
(the runtime's) run in `Tcb.headroom` below the limit and are not counted.
With `sp ≥ L + need f` at `f`'s entry, no stack check on the way fails, so
the grow path is never taken; a code check file states the table and checks
it against the parsed program (`Scc.Cert.NeedA64.needOk`,
`Scc.Cert.NeedX64.needOk`, G6). -/

/-- The frame of `f` below its entry stack pointer (`frameE` above). -/
def frameE (arch : Arch) (areas : List (Sym × Nat)) (f : Func) : Nat :=
  match arch with
  | .x64 => frameBytes .x64 areas f - 8
  | .arm => frameBytes .arm areas f

/-- The bytes a call pushes below the caller's stack pointer (`callCost`). -/
def callCost : Arch → Nat
  | .x64 => 8
  | .arm => 0

/-- **The stack need** of every stack-checked function of `p` (see above):
`(name, frameE, need)`, the least solution of the equations, in the order of
`p.funcs`.  Fails when a stack-checked function reaches itself through a
call that is not a tail call (its need is unbounded). -/
def stackNeed (arch : Arch) (p : Program) : Except String (List (Sym × Nat × Nat)) := do
  let areas := StackMap.argAreas p (argRegCount arch)
  let fs := p.funcs.filter (·.checkStack)
  let names := fs.map (·.name)
  let calls (f : Func) : List Sym := f.blocks.flatMap fun b => b.insts.filterMap fun
    | .call _ g _ => if names.contains g then some g else none
    | _ => none
  let tails (f : Func) : List Sym := f.blocks.filterMap fun b => match b.term with
    | .tail g _ => if names.contains g then some g else none
    | _ => none
  let rows := fs.map fun f => (f.name, frameE arch areas f, calls f, tails f)
  let get (m : List (Sym × Nat)) (g : Sym) : Nat := ((m.find? (·.1 == g)).map (·.2)).getD 0
  let step (m : List (Sym × Nat)) : List (Sym × Nat) := rows.map fun (n, fr, cs, ts) =>
    (n, max (fr + cs.foldl (fun a g => max a (callCost arch + get m g)) 0)
            (ts.foldl (fun a g => max a (get m g)) 0))
  -- From all zeros, `k` steps give the most over call chains of `k` functions;
  -- without a cycle through a call, chains have at most `fs.length` of them.
  let m := (List.range (fs.length + 1)).foldl (fun m _ => step m) (names.map (·, 0))
  if step m != m then
    let bad := (step m).filterMap fun (n, v) => if v != get m n then some n else none
    throw s!"unbounded stack need: non-tail recursion through {bad}"
  pure (rows.map fun (n, fr, _, _) => (n, fr, get m n))

/-- The thread entries of `p`: `scc_rt_main` and the trampolines that a
spawn starts (`Inst.clone`), each on a stack range of its own. -/
def threadEntries (p : Program) : List Sym :=
  (Names.mainThread :: p.funcs.flatMap fun f => f.blocks.flatMap fun b =>
    b.insts.filterMap fun | .clone _ _ _ g _ => some g | _ => none).eraseDups

/-- The stack need table's definition in a code check file
(`Scc.Cert.Blocks.code`): `{pfx}Need` (`stackNeed`'s rows) and
`{pfx}Need_ok`, its check on the parsed program (AArch64 `{pfx}Prog`,
`Scc.Cert.NeedA64.needOk`; x64 the code cells `{pfx}Cells`,
`Scc.Cert.NeedX64.needOk`) with each thread entry's need (`entries`,
`threadEntries`) at most `budget`. -/
def renderNeed (arch : Arch) (rows : List (Sym × Nat × Nat)) (entries : List Sym) (budget : Nat)
    (pfx : String) : String :=
  let es := ", ".intercalate (entries.map fun e => s!"\"{e}\"")
  let rs := ",\n  ".intercalate (rows.map fun (n, fr, nd) => s!"(\"{n}\", {fr}, {nd})")
  let (m, code) := match arch with
    | .arm => ("Scc.Cert.NeedA64", s!"{pfx}Prog")
    | .x64 => ("Scc.Cert.NeedX64", s!"{pfx}Cells")
  s!"/-- **The stack need table** (`Scc.Lower.stackNeed`): per stack-checked
function, its label, its frame below the entry stack pointer and the most
stack it uses below it until it returns. -/
def {pfx}Need : List {m}.Row := [
  {rs}]

/-- The table holds on the program, and each thread entry's need fits in
the initial stack range less the headroom ({budget} bytes). -/
theorem {pfx}Need_ok : {m}.needOk {code} {pfx}Need {budget} [{es}] = true := by
  decide +kernel
"

/-- Lower a checked program for configuration `cfg`: `lowerWith`, where the
stack budget (`stackBudget`) holds. -/
def lowerProgram (cfg : Config) (c : Frontend.Checked) : Except String Program := do
  let _ ← stackBudget cfg c
  lowerWith cfg c

/-- The placement traces of the compiled code blocks (`lowerDeclMarks`), by
IR function name: the lowering `lowerProgram` runs, again. -/
def lowerMarks (cfg : Config) (c : Frontend.Checked) :
    Except String (List (Sym × Array (Node × Point))) := do
  let _ ← stackBudget cfg c
  (c.prog.filter fun d => !(c.externs.any (·.1 == d.name))).mapM fun d => do
    let (f, ms) ← lowerDeclMarks c.prog c.externs d cfg.layout.obj
    pure (f.name, ms)

end Scc.Lower
