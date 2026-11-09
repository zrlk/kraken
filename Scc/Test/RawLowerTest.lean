import Scc.Lower.Raw
import Scc.Test.Src

/-!
# Tests of the `--host raw` lowering (`Scc.Lower.Raw`)

On `hello1.w` (no spawn) and `hello.w` (a spawn, `park` / `unpark`), for both architectures:
the raw program keeps `scc_rt_main`, the thread entries and the user functions, in the Linux
order; it has no runtime data, no system call, no `clone` and no `switchTo`; its entry is
`scc_rt_main`; the exits are calls of `scc_rt_exit_process` / `scc_rt_exit_thread`, and the
spawn is a call of `scc_rt_spawn` with `Inst.clone`'s operands in the prototype's order. The
user functions are unchanged except for the spawn.
-/

namespace Scc.Test.RawLower

open Scc.IR

/-- The Linux and the raw IR of a WeakCore source for `arch`. -/
def irs (arch : Arch) (src : String) : Except String (Program × Program) := do
  let c ← match Frontend.run src with
    | .ok c => pure c
    | .error _ => throw "frontend error"
  let l ← Lower.lowerIRHost { arch } c.prog
  let r ← Lower.lowerIRHost { arch, host := .raw } c.prog
  pure (l.ir, r.ir)

def hello1X : Except String (Program × Program) := irs .x64 (w_src% "Scc/Test/hello1.w")
def hello1A : Except String (Program × Program) := irs .arm (w_src% "Scc/Test/hello1.w")
def helloX : Except String (Program × Program) := irs .x64 (w_src% "Scc/Test/hello.w")
def helloA : Except String (Program × Program) := irs .arm (w_src% "Scc/Test/hello.w")

/-- The function names of the raw program. -/
def names (r : Except String (Program × Program)) : List String :=
  match r with
  | .ok (_, p) => p.funcs.map (·.name)
  | .error e => [e]

/-- No system call, `clone` or `switchTo` anywhere. -/
def noSys (p : Program) : Bool :=
  p.funcs.all fun f => f.blocks.all fun b =>
    b.insts.all (fun | .syscall .. | .clone .. => false | _ => true) &&
    (match b.term with | .switchTo .. => false | _ => true)

/-- Every routine called is a compiled function of the program or a kernel routine
(`Raw.slots`). -/
def callsResolved (p : Program) : Bool :=
  p.funcs.all fun f => f.blocks.all fun b => b.insts.all fun
    | .call _ g _ => p.funcs.any (·.name == g) || Lower.Raw.slots.any (·.1 == g)
    | _ => true

/-- The shape facts of a raw program (see the module docstring). -/
def shapeOk (r : Except String (Program × Program)) : Bool :=
  match r with
  | .ok (_, p) => p.host == .raw && p.data.isEmpty && p.start == "scc_rt_main" && noSys p &&
      callsResolved p && p.growth.isSome
  | .error _ => false

/-- The user functions (`wc_*`) of the raw program are the Linux ones, except for the
instructions `f` says differ. -/
def userSame (r : Except String (Program × Program)) : Bool :=
  match r with
  | .ok (l, p) =>
    let us (q : Program) := q.funcs.filter (·.name.startsWith "wc_")
    us l == us p
  | .error _ => false

/-- info: ["scc_rt_main", "wc_rodata", "wc_main"] -/
#guard_msgs in
#eval names hello1X

/-- info: ["scc_rt_main", "wc_rodata", "wc_main"] -/
#guard_msgs in
#eval names hello1A

/-- info: ["scc_rt_main", "scc_rt_thr_worker", "wc_rodata", "wc_worker", "wc_waitLoop", "wc_main"] -/
#guard_msgs in
#eval names helloX

#guard names helloA == names helloX
#guard shapeOk hello1X && shapeOk hello1A && shapeOk helloX && shapeOk helloA
-- hello1 spawns nothing: its user functions are the Linux ones.
#guard userSame hello1X && userSame hello1A
-- hello spawns: `wc_main` differs (the spawn), the others do not.
#guard !userSame helloX

/-- The instructions of a function of the raw program. -/
def instsOf (r : Except String (Program × Program)) (f : String) : List Inst :=
  match r with
  | .ok (_, p) => ((p.funcs.find? (·.name == f)).map fun f => f.blocks.flatMap (·.insts)).getD []
  | .error _ => []

/-- The calls of a function of the raw program: callee and argument count. -/
def callsOf (r : Except String (Program × Program)) (f : String) : List (String × Nat) :=
  (instsOf r f).filterMap fun | .call _ g args => some (g, args.length) | _ => none

/-- info: [("wc_rodata", 0), ("wc_main", 5), ("scc_rt_exit_process", 1)] -/
#guard_msgs in
#eval callsOf hello1X "scc_rt_main"

/-- info: [("wc_worker", 6), ("scc_rt_exit_thread", 0)] -/
#guard_msgs in
#eval callsOf helloX "scc_rt_thr_worker"

-- hello's spawn: thread_reserve, alloc_tcb, thread_init, then scc_rt_spawn with (child TCB,
-- stack top, entry) and the six argument words of `worker`'s argument; `scc_rt_abort` is the
-- failed spawn's.
/-- info: [("scc_rt_alloc", 3), ("scc_rt_thread_reserve", 0), ("scc_rt_alloc_tcb", 2), ("scc_rt_thread_init", 1),
  ("scc_rt_spawn", 9), ("scc_rt_abort", 1)] -/
#guard_msgs in
#eval callsOf helloX "wc_main"

-- The spawn's entry is the address of the thread entry, in `Raw.entryReg`.
#guard (instsOf helloX "wc_main").any (· == .la Lower.Raw.entryReg "scc_rt_thr_worker")

-- A spawn with several argument words passes them after the first, in `spawnReg` order, and
-- drops the moves; the fence stays, after the entry's address and before the call.
#guard (Lower.Raw.rawInsts "f"
    [.mov (spawnReg 1) (.imm 7), .mov (spawnReg 2) (.reg "y"), .fence .full,
     .clone "r" (.reg "top") (.reg "tcb") "scc_rt_thr_g" (.reg "x")]).toOption ==
  some [.la Lower.Raw.entryReg "scc_rt_thr_g", .fence .full,
    .call ["r"] "scc_rt_spawn" [.reg "tcb", .reg "top", .reg Lower.Raw.entryReg, .reg "x",
      .imm 7, .reg "y"]]
-- A gap in the argument words, an unknown system call, or an argument word without its spawn
-- is refused.
#guard (Lower.Raw.rawInsts "f"
    [.mov (spawnReg 2) (.imm 7), .clone "r" (.reg "top") (.reg "tcb") "e" (.reg "x")]).toOption.isNone
#guard (Lower.Raw.rawInsts "f" [.syscall "r" .write [.imm 1]]).toOption.isNone
#guard (Lower.Raw.rawInsts "f" [.mov (spawnReg 1) (.imm 7)]).toOption.isNone
-- A spawn without the fence right before it is refused.
#guard (Lower.Raw.rawInsts "f"
    [.fence .full, .mov (spawnReg 1) (.imm 7),
     .clone "r" (.reg "top") (.reg "tcb") "e" (.reg "x")]).toOption.isSome
#guard (Lower.Raw.rawInsts "f"
    [.mov (spawnReg 1) (.imm 7), .clone "r" (.reg "top") (.reg "tcb") "e" (.reg "x")]).toOption.isNone
-- hello's raw `wc_main`: exactly one full fence, after the entry's address and directly before
-- the call of `scc_rt_spawn`; and its instructions are the Linux ones but for the `clone` (and the
-- `spawnReg` moves feeding it), which is the entry address and the call.
/-- The Linux and the raw instructions of `wc_main`, without the spawn's own: the `spawnReg`
moves and the `clone` (Linux), the entry address and the spawn call (raw). -/
def spawnFree (r : Except String (Program × Program)) : Option (List Inst × List Inst) :=
  match r with
  | .ok (l, p) =>
    let of (q : Program) := ((q.funcs.find? (·.name == "wc_main")).map fun f =>
      f.blocks.flatMap (·.insts)).getD []
    some ((of l).filter (fun
        | .mov r _ => (Lower.Raw.spawnIdx? r).isNone
        | .clone .. => false
        | _ => true),
      (of p).filter (fun
        | .la r _ => r != Lower.Raw.entryReg
        | .call _ g _ => g != Tcb.spawnSym
        | _ => true))
  | .error _ => none
/-- The full fences of raw `wc_main` with the instruction before and the one after each. -/
def fencesAfter (r : Except String (Program × Program)) : List (List Inst) :=
  let is := instsOf r "wc_main"
  (is.zipIdx.filter (·.1 == .fence .full)).map fun (_, k) => (is.drop (k - 1)).take 1 ++ (is.drop (k + 1)).take 1
#guard (spawnFree helloX).map (fun (l, r) => l == r) == some true
#guard (spawnFree helloA).map (fun (l, r) => l == r) == some true
#guard match fencesAfter helloX with
  | [[.la e "scc_rt_thr_worker", .call _ g _]] => e == Lower.Raw.entryReg && g == Tcb.spawnSym
  | _ => false
#guard match fencesAfter helloA with
  | [[.la e "scc_rt_thr_worker", .call _ g _]] => e == Lower.Raw.entryReg && g == Tcb.spawnSym
  | _ => false
-- A WeakCore block cannot take a runtime symbol (the emitters fence every call of
-- `IR.Tcb.spawnSym`): its function and every call of it are `Names.user`'s `wc_` symbols, and
-- every other call the lowering emits is of a fixed `Names` routine. A Linux program whose
-- block is named `scc_rt_spawn`, and calls it, has `wc_scc_rt_spawn` and no call of
-- `scc_rt_spawn`, so no fence besides its own `spawn`s.
def spawnNamed : String := "def scc_rt_spawn(n : Int) : Int =
  ret n

def rodata(u : Unit) : Int =
  ret 0

def main(a : Int * Ptr pub Void) : Int =
  let (n, me) = a
  let r = scc_rt_spawn(n)
  ret r
"
/-- The callees of a program. -/
def callees (p : Program) : List String :=
  p.funcs.flatMap fun f => f.blocks.flatMap fun b => b.insts.filterMap fun
    | .call _ g _ => some g
    | _ => none
#guard match irs .x64 spawnNamed with
  | .ok (l, _) => l.funcs.any (·.name == "wc_scc_rt_spawn") &&
      (callees l).contains "wc_scc_rt_spawn" && !(callees l).contains Tcb.spawnSym &&
      !l.funcs.any (·.name == Tcb.spawnSym)
  | .error _ => false
#guard match irs .arm spawnNamed with
  | .ok (l, _) => (callees l).contains "wc_scc_rt_spawn" && !(callees l).contains Tcb.spawnSym
  | .error _ => false
-- A raw program is not lowered again.
#guard (do let (_, p) ← hello1X; Lower.Raw.rawIR p).toOption.isNone

-- The slot table: 14 routines, numbered 0 … 13 in order, all distinct.
#guard Lower.Raw.slotCount == 14
#guard Lower.Raw.slots.map (·.2) == List.range 14
#guard (Lower.Raw.slots.map (·.1)).eraseDups.length == 14

-- The budget is recomputed on the raw program and holds.
#guard (do
    let c ← match Frontend.run (w_src% "Scc/Test/hello.w") with
      | .ok c => pure c
      | .error _ => throw "frontend error"
    let l ← Lower.lowerIRHost { arch := .x64, host := .raw } c.prog
    pure l.budget.ok).toOption == some true

end Scc.Test.RawLower
