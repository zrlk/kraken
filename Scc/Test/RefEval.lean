import WeakCore.TermRun
import Scc.Frontend
import Std.Data.HashMap

/-!
# A reference evaluator for differential testing

Runs a source program's main thread with WeakCore's own executable machine,
`TermRun` (WeakCore/TermRun.lean): a configuration with one thread entering
`main`, stepped by `TermRun.threadSteps` (`tstep`, §4) with promises off,
until the thread is done (`TermRun.isDone`), stuck (no step) or out of fuel.
Every construct of the accepted fragment steps by `tstep`'s rule for it: calls
push a `TermRun.Frame` (`callFrame`/`enter`), `tail` re-enters, `ifeq`
compares numbers, operations go through `TermRun.evalOp` (`addW`/`subW` for
`Int` `+`/`-`, `fopN`/`fcmpN`/`cvtN`/… for fixed-width words, `alloc`/
`allocBuf` and `Promises.stepLoad`/`stepStore` for the heap).

The single departure is scc's source semantics for `Int` `+`: WeakCore's
`Int` is unbounded (`addW` is `Nat` addition), while scc aborts when a sum
reaches `2^64` (exit status 101, see `Scc/Frontend.lean`).  Before a
`let x = a + b` steps, the evaluator computes the sum and reports the
overflow abort if it does not fit in 64 bits.  `Int` `-` is already `Nat`
subtraction in `subW`, the saturating semantics scc implements.

With one thread and no promises every successor list has at most one element
that matters: loads see the thread's own latest write.  The evaluator takes
the first successor.

**Speed.**  `Promises.stepLoad` extends the thread's coherence view
`VState.coh` (a function `Address → Ts`) by one closure per load, so a lookup
walks every earlier load's closure and a run of `n` loads costs `O(n²)`.
Every `compactEvery` steps the evaluator replaces the function by an equal
one, a table over the locations in memory (`compact`); this changes no value
the machine can observe, only how it is computed.  The quadratic cost is in
WeakCore, which this file does not edit.

The outcome is the exit status scc's binary must produce: `main`'s `Int`
result modulo 256 (`0` for a `Unit` main), or the overflow abort.  The other
abort kinds of the binary (heap, stack, threads) are resource limits the
source semantics does not have; `Scc/Test/diff.sh` accepts a binary's 101
against a reference result only when the reference reports the overflow.
-/

open CoreLang CoreTerm

namespace Scc.Test.RefEval

/-- What a reference run of `main` ends in. -/
inductive Outcome where
  /-- `main` returned; `val` is its `Int` result (`0` for `Unit`). -/
  | ret (val : Nat)
  /-- An `Int` `+` whose sum is `2^64` or more, in block `fn`. -/
  | overflow (fn : String)
  /-- No step applies (a program the machine cannot run). -/
  | stuck (why : String)
  /-- The fuel ran out after `steps` steps. -/
  | fuel (steps : Nat)
  /-- The work budget (`workBudget`) ran out after `steps` steps. -/
  | work (steps : Nat)
  deriving Repr, BEq, Inhabited

/-- The exit status a binary must produce for an outcome (`none`: no
verdict, i.e. stuck or out of fuel). -/
def Outcome.code : Outcome → Option Nat
  | .ret v => some (v % 256)
  | .overflow _ => some 101
  | _ => none

def Outcome.render : Outcome → String
  | .ret v => s!"ret {v} exit {v % 256}"
  | .overflow fn => s!"abort overflow in {fn} exit 101"
  | .stuck why => s!"stuck {why}"
  | .fuel n => s!"fuel {n}"
  | .work n => s!"work budget out after {n} steps"

/-- The initial configuration: thread 0 about to enter `main` with `()`.
Memory is empty and labels start at 0 (`TermRun.MP.init` reserves label 0
for its flag; nothing is preallocated here). -/
def init : TermRun.Cfg where
  mem := #[]
  ths := #[{ term := .tail "main" [] .unit, env := [] }]

/-- The knobs: promises off (a single thread has nothing to promise to). -/
def knobs : Promises.Knobs := { promises := false }

/-- The numeric value of an atom in a thread's environment. -/
def numAt (th : TermRun.TTh) (a : At) : Option Nat :=
  match TermRun.evalAt th.env a with
  | some (_, [w]) => match w.val with | .num n => some n | _ => none
  | _ => none

/-- Steps between two `compact`s. -/
def compactEvery : Nat := 1024

/-- `th` with its coherence view `vs.coh` replaced by an equal function: a
table of its values at the locations of `mem`'s messages, falling back to
the old function elsewhere.  The table is built once (Lean is strict), so a
lookup at a location in memory no longer walks the closures `stepLoad` has
stacked (see "Speed" above). -/
def compact (mem : WeakMem.Memory) (th : TermRun.TTh) : TermRun.TTh :=
  let old := th.vs.coh
  let tab : Std.HashMap (Nat × Nat) WeakMem.Ts := mem.foldl (fun m msg =>
    let k := (msg.loc.label, msg.loc.offset)
    if m.contains k then m else m.insert k (old msg.loc)) {}
  { th with vs := { th.vs with coh := fun b => (tab.get? (b.label, b.offset)).getD (old b) } }

/-- The default work budget of a run: the sum, over its steps, of the
memory's size (plus one) before the step.  A step's cost grows with the
memory (the machine looks messages up in it), so a run that allocates in a
long loop costs about `steps × messages`, quadratic in its length; the
budget stops such a run without a verdict (`.work`), where the step fuel
alone would let it run for hours (seed 25's program 256 of `Gen.batch`, a
count-down that allocates 14889 times).  At about `5·10^6` units a second,
this is about six seconds. -/
def workBudget : Nat := 30_000_000

/-- Run thread 0 for at most `fuel` steps and `work` units of work (see
`workBudget`); `n` counts the steps taken.  `fn` is the block last entered by
a call or `tail` (for messages only). -/
def runFrom (p : Prog) (arch : WeakMem.Arch) (fn : String) (work : Nat) :
    Nat → Nat → TermRun.Cfg → Outcome
  | 0, n, _ => .fuel n
  | fuel + 1, n, c =>
    match c.ths[0]? with
    | none => .stuck "no thread"
    | some th =>
      if TermRun.isDone th then
        match th.term with
        | .ret a =>
            match TermRun.evalAt th.env a with
            | some (_, []) => .ret 0
            | some (_, [w]) => match w.val with
              | .num v => .ret v
              | v => .stuck s!"main returned a non-number {repr v}"
            | _ => .stuck "main returned a multi-word value"
        | _ => .stuck "done without ret"
      else if work < c.mem.size + 1 then .work n
      else
        -- scc's checked `Int` addition: the abort outcome on a sum ≥ 2^64.
        let ovf : Bool := match th.term with
          | .let_ _ (.add a b) _ =>
              match numAt th a, numAt th b with
              | some x, some y => x + y ≥ 2 ^ 64
              | _, _ => false
          | _ => false
        if ovf then .overflow fn
        else
          -- Track the current block for messages: a call or tail enters `f`.
          let fn' := match th.term with
            | .let_ _ (.call f _ _ _) _ => f
            | .tail f _ _ _ => f
            | _ => fn
          match TermRun.threadSteps p knobs arch c 0 with
          | c' :: _ =>
              let c' := if (n + 1) % compactEvery == 0 then
                  { c' with ths := c'.ths.modify 0 (compact c'.mem) }
                else c'
              runFrom p arch fn' (work - (c.mem.size + 1)) fuel (n + 1) c'
          | [] => .stuck s!"no step (in or after {fn'}) at {repr th.term |>.pretty 80 |>.take 200}"

/-- Run a checked program's `main` with at most `fuel` steps and `work`
units of work. -/
def runProg (p : Prog) (arch : WeakMem.Arch := .arm) (fuel : Nat := 10_000_000)
    (work : Nat := workBudget) : Outcome :=
  runFrom p arch "main" work fuel 0 init

/-- Run a source text: the frontend's checks first (a rejected text has no
reference outcome), then the machine. -/
def runSrc (src : String) (arch : WeakMem.Arch := .arm) (fuel : Nat := 10_000_000) :
    Except String Outcome :=
  match Frontend.run src with
  | .error ds => .error ("; ".intercalate (ds.map (·.render "t.w")))
  | .ok c =>
      if c.entry.arg != .unit then .error "the reference runs only main(a : Unit)"
      else .ok (runProg c.prog arch fuel)

/-- Print `FILE: OUTCOME` for each file (from `#eval`: WeakCore's `WeakMem`
already defines the root `main`, so a driver cannot be run with
`lean --run`). -/
def runFiles (fs : List String) : IO Unit := do
  for f in fs do
    let src ← IO.FS.readFile f
    match runSrc src with
    | .ok o => IO.println s!"{f}: {o.render}"
    | .error e => IO.println s!"{f}: rejected {e}"

end Scc.Test.RefEval

/-! ## Tests -/

namespace Scc.Test.RefEval

/-- The outcome of a source text, as text. -/
def outcomeOf (src : String) : String :=
  match runSrc src with
  | .ok o => o.render
  | .error e => s!"rejected {e}"

/-- info: "ret 300 exit 44" -/
#guard_msgs in
#eval outcomeOf "
def h(a : Int * Int) : Int =
  let (x, y) = a
  let s = x + y
  ret s

def main(u : Unit) : Int =
  let zi = zero[Int]
  let c = new zi
  let s0 = store c 100
  let v = load c
  let p = (v, 200)
  let r = h(p)
  ret r
"

/-- info: "abort overflow in main exit 101" -/
#guard_msgs in
#eval outcomeOf "
def main(u : Unit) : Int =
  let big = 18446744073709551615
  let s = big + 1
  ret s
"

-- A wrapping `bits wadd` does not abort; `fop div` by zero is 0.
/-- info: "ret 0 exit 0" -/
#guard_msgs in
#eval outcomeOf "
def main(u : Unit) : Int =
  let big = 18446744073709551615
  let s = bits wadd big 1
  let z = cvt U64 0
  let seven = cvt U64 7
  let q = fop div seven z
  let qi = toInt q
  let r = s + qi
  ret r
"

end Scc.Test.RefEval
