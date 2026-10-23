import Scc.Frontend
import Scc.Lower.Program
import Scc.Test.Src

/-!
# Exact heap lists in the stack maps

The lowering records the kind of every register that holds a word of a typed
value (`Lower.markWords`, from `Obj.traceMask`): trace words (references,
locative bases, `ThreadId`s) in `Func.heapRegs`, scalar words (scalars,
locative offset words) in `Func.scalarRegs`; the runtime marks its own
registers that live across a call.  The stack maps' heap lists are the
`heapRegs` live at each safepoint (`StackMap.entryOf`).

`mapIssues` checks, for every function of a lowered program (blocks,
trampolines and runtime):

* no register is in both lists, so every heap-list entry holds a trace word
  of its value's type and never a scalar or an offset word;
* every register live across a safepoint (a call, or the prologue check for
  the parameters live on entry) is in one of the lists, so no trace word that
  a safepoint must preserve is missing from its heap list.

`areaIssues` checks the argument areas (`StackMap.argAreas`) for a register
count `k` (x64 6, AArch64 8), which keep every `tail` a jump: each tail call
fits in its caller's area and caller and callee share it, each function's own
stack parameters fit, every call reserves at least the callee's area, and
the functions entered without a caller (`start`, `clone` and `switchTo`
targets) need none.  Stack parameters are listed by the prologue check's map
in place (`16 + 8·j` from the frame record, `StackMap.checkMap`), so the
heap-list rules above cover them too.
-/

namespace Scc.Test.Maps
open Scc.IR

/-- Frontend and lowering (the default configuration). -/
def lowerW (src : String) : Except String Program := do
  let c ← match Frontend.run src with
    | .ok c => pure c
    | .error ds => throw (String.intercalate "\n" (ds.map (·.render "input")))
  Lower.lowerProgram {} c

/-- The registers live across the safepoints of `f`: its calls, and its
prologue check (when it has one). -/
def safepointLive (f : Func) : List Reg :=
  let calls := ((StackMap.callLives f).flatten.filterMap id).flatten
  (calls ++ (if f.checkStack then StackMap.entryLive f else [])).eraseDups

/-- The violations of the two rules in `f`. -/
def mapIssues (f : Func) : List String :=
  let both := (f.heapRegs.filter f.scalarRegs.contains).map fun r =>
    s!"{f.name}: {r} is marked both trace and scalar"
  let untyped := (safepointLive f).filter (fun r =>
    !(f.heapRegs.contains r || f.scalarRegs.contains r)) |>.map fun r =>
    s!"{f.name}: {r} is live across a safepoint with no kind"
  both ++ untyped

/-- The violations of the argument-area rules in `p` for `k` registers. -/
def areaIssues (p : Program) (k : Nat) : List String :=
  let areas := StackMap.argAreas p k
  let area (g : Sym) : Option Nat := (areas.find? (·.1 == g)).map (·.2)
  p.funcs.flatMap fun f =>
    let a := (area f.name).getD 0
    let own := if StackMap.stackWords k f.params.length > a then
      [s!"{f.name}: parameters exceed its area {a}"] else []
    let tails := (StackMap.tailCalls f).flatMap fun (g, n) =>
      (if StackMap.stackWords k n > a then [s!"{f.name}: tail call of {g} exceeds its area {a}"]
       else []) ++
      (match area g with
       | some b => if b != a then [s!"{f.name} → {g}: areas {a} and {b} differ"] else []
       | none => [])
    let calls := f.blocks.flatMap fun b => b.insts.flatMap fun
      | .call _ g args =>
        if StackMap.callWords areas k g args.length < (area g).getD 0 then
          [s!"{f.name}: call of {g} reserves less than its area"] else []
      | _ => []
    let entered := f.blocks.flatMap fun b =>
      (b.insts.filterMap fun | .clone _ _ _ g _ => some g | _ => none) ++
      (match b.term with | .switchTo _ _ g _ => [g] | _ => [])
    let entries := (if f.name == p.start then [f.name] else []) ++ entered |>.filter fun g =>
      (area g).getD 0 > 0
    own ++ tails ++ calls ++ entries.map (s!"{·}: entered without a caller but has an area")

/-- The violations in a program, and the number of heap-list entries over
all its safepoints (calls and prologue checks). -/
def report (p : Except String Program) : String :=
  match p with
  | .error e => s!"error: {e}"
  | .ok p =>
    let issues := p.funcs.flatMap mapIssues ++ areaIssues p 6 ++ areaIssues p 8
    let entries := p.funcs.foldl (fun n f =>
      let calls := ((StackMap.callMaps f).flatten.filterMap id).foldl (· + ·.heap.length) 0
      n + calls + (if f.checkStack then (StackMap.checkMap f).heap.length else 0)) 0
    if issues.isEmpty then s!"ok: {p.funcs.length} functions, {entries} heap-list entries"
    else String.intercalate "\n" issues

/-- info: ok: 26 functions, 27 heap-list entries -/
#guard_msgs in #eval IO.println (report (lowerW (w_src% "Scc/Test/hello.w")))

/-- info: ok: 22 functions, 25 heap-list entries -/
#guard_msgs in #eval IO.println (report (lowerW (w_src% "Scc/Test/handoff.w")))

/-- info: ok: 22 functions, 14 heap-list entries -/
#guard_msgs in #eval IO.println (report (lowerW (w_src% "Scc/Test/spill.w")))

/-- info: ok: 20 functions, 13 heap-list entries -/
#guard_msgs in #eval IO.println (report (lowerW (w_src% "Scc/Test/layout.w")))

/-- info: ok: 22 functions, 7 heap-list entries -/
#guard_msgs in #eval IO.println (report (lowerW (w_src% "Scc/Test/tailwide.w")))

-- `tailwide.w`'s three blocks form one tail component: on x64 its area is
-- the six stack words of `wv`'s twelve, on AArch64 four.
#guard match lowerW (w_src% "Scc/Test/tailwide.w") with
  | .ok p =>
    let area (k : Nat) (g : Sym) : Option Nat := ((StackMap.argAreas p k).find? (·.1 == g)).map (·.2)
    ["wc_wl", "wc_ww", "wc_wv", "wc_main"].map (fun g => (area 6 g, area 8 g)) ==
    [(some 6, some 4), (some 6, some 4), (some 6, some 4), (some 0, some 0)]
  | .error _ => false

-- The check finds both kinds of violation: `p` holds a trace word but is
-- marked scalar too, and `q`, live across the call, has no kind.
#guard mapIssues
  { name := "f", params := ["p", "q"], heapRegs := ["p"], scalarRegs := ["p"],
    blocks := [{ label := "entry", insts := [.call [] "g" [.reg "p"]],
                 term := .ret [.reg "p", .reg "q"] }] } ==
  ["f: p is marked both trace and scalar", "f: q is live across a safepoint with no kind"]

-- A start routine that tail-calls a nine-word function shares its area,
-- but nothing above it holds one: the check reports it (and so do the
-- emitters).
#guard areaIssues
  { funcs := [
      { name := "s", params := [],
        blocks := [{ label := "entry", insts := [], term := .tail "w" (List.replicate 9 (.imm 0)) }] },
      { name := "w", params := (List.range 9).map toString,
        blocks := [{ label := "entry", insts := [], term := .ret [] }] }],
    data := [], start := "s", abortFn := "s" } 6 ==
  ["s: entered without a caller but has an area"]

end Scc.Test.Maps
