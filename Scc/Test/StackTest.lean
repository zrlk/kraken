import Scc.Lower.Program

/-!
# Tests of growable stacks at the IR level

WeakCore programs have no stack addresses, so the `.w` tests exercise only
the frame records.  `relocIR` creates stack addresses with `Inst.slotAddr`
and keeps them live across calls and across prologue checks, so a run that
grows the stack exercises the stack-map rewriting of both kinds of
safepoint.  It uses the real runtime (`Scc.Lower.Runtime`): start-up, pool,
grow routine and abort.

`rec(p, n)` (with `p` the address of its caller's slot `w`):

* `w := n; q := &w; *p := *p + 1` (`p` may come from the grow stub's save
  area, when the prologue check of this call grew the stack);
* if `n > 0`: `rec(q, n - 1)` (`q` and `p` are live across the call), then
  check that `*q` and `w` both equal `n + 1001` (the callee added 1 and
  1000 to `w` through its `p`);
* `*p := *p + 1000`.

A stale stack address (one that the move did not rewrite) reads or writes
the abandoned old range, so the two checks disagree; a check that fails
exits with status 77.  `main` runs `rec(&w0, 20000)` (several doublings of
the 16 KiB initial stack), checks `w0 = 1001`, prints `reloc ok` and exits
with 0.

`Scc/Test/run.sh` writes the program for its architecture (`writeReloc`),
assembles, links and runs it.
-/

namespace Scc.Test.Stack
open Scc.IR

def r (s : String) : Operand := .reg s
def k (n : Nat) : Operand := .imm (UInt64.ofNat n)

/-- The recursion depth of `relocIR`. -/
def depth : Nat := 20000

/-- `rec(p, n)` (see the module docstring). -/
def recFunc : Func :=
  { name := "wc_rec", params := ["p", "n"], stackRegs := ["p", "q"], blocks := [
    { label := "entry", insts := [
        .mov "w" (r "n"), .slotAddr "q" "w",
        .load .plain .w64 "t" ⟨"p", 0⟩, .bin .add "t" (r "t") (k 1),
        .store .plain .w64 ⟨"p", 0⟩ (r "t")],
      term := .br .eq (r "n") (k 0) "post" "step" },
    { label := "step", insts := [
        .bin .sub "n1" (r "n") (k 1),
        .call ["z"] "wc_rec" [r "q", r "n1"],
        .bin .add "want" (r "n") (k 1001),
        .load .plain .w64 "v" ⟨"q", 0⟩],
      term := .br .ne (r "v") (r "want") "bad" "step2" },
    { label := "step2", insts := [.mov "wr" (r "w")],
      term := .br .ne (r "wr") (r "want") "bad" "post" },
    { label := "post", insts := [
        .load .plain .w64 "u" ⟨"p", 0⟩, .bin .add "u" (r "u") (k 1000),
        .store .plain .w64 ⟨"p", 0⟩ (r "u")],
      term := .ret [k 0] },
    { label := "bad", insts := [.syscall "x" .exitGroup [k 77]], term := .unreachable }] }

/-- `main`: `rec(&w0, depth)`, then check `w0`. -/
def mainFunc : Func :=
  { name := "wc_main", params := [], stackRegs := ["q0"], blocks := [
    { label := "entry", insts := [
        .mov "w0" (k 0), .slotAddr "q0" "w0",
        .call ["z"] "wc_rec" [r "q0", k depth],
        .load .plain .w64 "v" ⟨"q0", 0⟩],
      term := .br .ne (r "v") (k 1001) "bad" "chk2" },
    { label := "chk2", insts := [], term := .br .ne (r "w0") (k 1001) "bad" "ok" },
    { label := "ok", insts := [
        .la "m" "t_reloc_ok", .syscall "x" .write [k 1, r "m", k 9]],
      term := .ret [k 0] },
    { label := "bad", insts := [.syscall "x" .exitGroup [k 77]], term := .unreachable }] }

open Scc.Lower in
/-- The relocation test program, with the real runtime. -/
def relocIR : Except String IR.Program := do
  let lay : Layout := {}
  let rt ← [Runtime.startF lay, Runtime.mainThreadF { arg := .unit, retInt := true } 0,
    Runtime.allocF lay,
    Runtime.allocF lay Names.allocTcb Names.pinned Names.pinnedNext (Runtime.pinnedBytes lay) .threads false,
    Runtime.threadInitF lay,
    Runtime.stackTakeF lay, Runtime.stackReleaseF lay, Runtime.growF lay, Runtime.abortF] ++
    Runtime.abortKinds.map Runtime.abortKindF |>.mapM id
  pure { funcs := rt ++ [recFunc, mainFunc],
         data := Runtime.data lay ++
           [{ name := "t_reloc_ok", align := 1, init := .bytes "reloc ok\n".toUTF8.toList }],
         start := Names.start, abortFn := Names.abort,
         growth := some { grow := Names.grow, release := Names.stackRelease } }

/-! ## The maps of `rec` -/

-- The call in `step` lists `p` and `q` (both live after it); no heap slots.
/--
info: [[none, none, none, none, none],
 [none, some { stack := ["p", "q"], heap := [] }, none, none],
 [none],
 [none, none, none],
 [none]]
-/
#guard_msgs in #eval StackMap.callMaps recFunc

-- The prologue check lists `p` (live on entry); `n` is not a stack register.
/-- info: { stack := ["p"], heap := [] } -/
#guard_msgs in #eval StackMap.checkMap recFunc

-- A dead stack register is not listed: after `main`'s call only `q0` is live.
/-- info: [[none, none, some { stack := ["q0"], heap := [] }, none], [], [none, none], [none]] -/
#guard_msgs in #eval StackMap.callMaps mainFunc

-- The program satisfies the no-escape rules (both emitters accept it:
-- `Scc/Test/StackX64.lean`, `Scc/Test/StackArm.lean`).
#guard (relocIR.bind StackMap.check).toOption.isSome

/-! ## The no-escape check rejects escapes -/

def oneFunc (f : Func) : IR.Program := { funcs := [f], data := [], start := f.name, abortFn := f.name }

/-- The check's verdict on a one-block function with instructions `body` and
terminator `t`, parameters `ps`, stack registers `["q"]`. -/
def verdict (body : List Inst) (t : Term := .ret []) (ps : List Reg := []) : String :=
  let b : Block := { label := "entry", insts := .slotAddr "q" "w" :: body, term := t }
  let f : Func := { name := "f", params := ps, stackRegs := ["q"], blocks := [b] }
  match StackMap.check (oneFunc f) with
  | .ok () => "ok"
  | .error e => e

/-- info: "f: a stack address is stored to memory" -/
#guard_msgs in #eval verdict [.store .plain .w64 ⟨"q", 0⟩ (r "q")]
/-- info: "f: a stack address flows into register x, which is not in stackRegs" -/
#guard_msgs in #eval verdict [.bin .add "x" (r "q") (k 8)]
/-- info: "f: a stack address is returned" -/
#guard_msgs in #eval verdict [] (.ret [r "q"])
/-- info: "f: a stack address is passed in a tail call" -/
#guard_msgs in #eval verdict [] (.tail "f" [r "q"]) ["a"]
/-- info: "f: a stack address is passed to a system call" -/
#guard_msgs in #eval verdict [.syscall "x" .write [k 1, r "q", k 8]]
/-- info: "f: a stack address is passed to f in parameter a, which is not in its stackRegs" -/
#guard_msgs in #eval verdict [.call [] "f" [r "q"]] (.ret []) ["a"]
/-- info: "f: slotAddr of q, a stack register" -/
#guard_msgs in #eval verdict [.slotAddr "q" "q"]
/-- info: "ok" -/
#guard_msgs in #eval verdict [.bin .add "q" (r "q") (k 8), .load .plain .w64 "x" ⟨"q", 0⟩,
  .store .plain .w64 ⟨"q", 0⟩ (k 5)]

/-! ## Heap references recorded by the term lowering

The lowering marks the registers that hold locations (`Func.heapRegs`), so
the maps of WeakCore programs list them (for a future moving collector).  In
`handoff.w`'s `wait`, the two cell pointers (the parameters) are live across
the call of `park` and are the heap slots of its map; the prologue check
lists them too. -/

/-- The call maps and the check map of block `f` of a WeakCore file, lowered
for x64. -/
def mapsOfW (path f : String) : IO String := do
  let src ← IO.FS.readFile path
  match Frontend.run src with
  | .error _ => return "frontend error"
  | .ok c =>
    match Lower.lowerProgram {} c with
    | .error e => return e
    | .ok p =>
      match p.funcs.find? (·.name == Lower.Names.user f) with
      | none => return "no such function"
      | some g =>
        let calls := (StackMap.callMaps g).flatten.filterMap id
        return s!"heapRegs {g.heapRegs}; calls {repr calls}; check {repr (StackMap.checkMap g)}"

/--
info: "heapRegs [a.0, a.1]; calls [{ stack := [], heap := [\"a.0\", \"a.1\"] }]; check { stack := [], heap := [\"a.0\", \"a.1\"] }"
-/
#guard_msgs in #eval mapsOfW "Scc/Test/handoff.w" "wait"

/-! ## Thread creation aborts as `threads`

A spawn allocates the TCB with `scc_rt_alloc_tcb` in the pinned region (whose
exhaustion is the `threads` abort; its header: kind `pinned`, the TCB's 9
words and the argument's 3 trace words) and a failed `clone` aborts with the `threads` code; each
abort kind has its own routine, the only `exit_group(101)` sites. -/

/-- The callees and their immediate arguments in block `f` of a WeakCore file. -/
def callsOfW (path f : String) : IO (List (String × List Nat)) := do
  let src ← IO.FS.readFile path
  match Frontend.run src with
  | .error _ => return []
  | .ok c =>
    match Lower.lowerProgram {} c with
    | .error _ => return []
    | .ok p =>
      let g := (p.funcs.find? (·.name == Lower.Names.user f)).getD default
      return g.blocks.flatMap fun b => b.insts.filterMap fun
        | .call _ h args => some (h, args.filterMap fun | .imm v => some v.toNat | .reg _ => none)
        | _ => none

/--
info: [("scc_rt_alloc", [256, 1, 2]),
 ("scc_rt_alloc", [256, 1, 2]),
 ("scc_rt_thread_reserve", []),
 ("scc_rt_alloc_tcb", [12585219, 1]),
 ("scc_rt_thread_init", []),
 ("scc_rt_abort", [5])]
-/
#guard_msgs in #eval callsOfW "Scc/Test/handoff.w" "main"

end Scc.Test.Stack
