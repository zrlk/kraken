import WeakCore.EM0
import WeakCore.TermLiveXE

/-! # LostWakeDemo — the faithful permit makes a lost wakeup visible

EM0's `worker` release-stores 1 to `c` and then `unpark`s `main`; `main` joins in `waitLoop`, which `park`s until it
reads 1.  With the faithful permit (the permit semantics) a `park` returns as a THREAD move only with a permit, so:

* EM0 as written: the explorer (spawn machine, capacity 2, no promises) finds no stuck configuration and no fair
  livelock — the permit set by `unpark` is never lost, whichever order the two threads run in;
* EM0 with the worker's `unpark` deleted (`em0Lost`): a run where `waitLoop` reads 0 and parks before the store is
  stuck — the permit never comes (the spurious-wake environment edges are unforced, as promises are, so they do not
  count as a move of the parked thread).

Under the old prelude (`park`/`unpark` = `ret ()` bodies) both programs had no stuck configuration: the lost wakeup was
invisible.  Search reports only (not theorems): `analyseX` on `exploreGX`. -/

namespace LostWakeDemo
open CoreLang CoreTerm TermRun TermLive TermLiveXE TermStartW EM0Prelude EM0

/-- EM0 with the worker's `let w = unpark j` deleted (everything else verbatim). -/
def progSrcLost : String := progSrc.replace "  let w = unpark j\n" ""

def em0Lost : Prog := P (preludeSrc ++ helloSrc ++ progSrcLost)

-- the deletion is exactly one line, and the result still parses and checks
#guard progSrcLost.length + "  let w = unpark j\n".length == progSrc.length
#guard em0Lost.length == em0.length
#guard accepts (checkProg em0Lost)

/-- The search graph from the wrapper start (spawn machine, capacity 2, no promises). -/
def graphOf (p : Prog) : Graph :=
  exploreGX p kOff .arm { maxP := 0 } 2 600 (startW p 2)

/-- The threads of `c` at a `park` call holding no permit (they have no thread move under the permit semantics). -/
def parkedNoPermit (c : Cfg) : List Nat :=
  (List.range c.ths.size).filter fun i =>
    match c.ths[i]? with
    | some th => match th.term with
      | .let_ _ (.ext .park _) _ => th.permit.isNone
      | _ => false
    | none => false

/-- The reason for each stuck node: every expanded non-final node with no thread edge, with its parked threads. -/
def stuckWhy (g : Graph) : List (Nat × List Nat) :=
  (List.range g.nodes.size).filterMap fun v =>
    if g.expanded[v]! && !(g.nodes[v]!).final && (g.edges[v]!).all (fun (_, t, _) => !t) then
      some (v, parkedNoPermit g.nodes[v]!)
    else none

-- EM0 as written: complete search, nothing stuck, no fair livelock.
#guard let l := analyseX (graphOf em0) 2; !l.cut && l.stuck == 0 && l.livelocks.isEmpty
#guard (stuckWhy (graphOf em0)).isEmpty
-- The lost wakeup: complete search, at least one stuck configuration, and at EVERY node with no thread move some
-- thread is parked without a permit (the reason).
#guard let l := analyseX (graphOf em0Lost) 2; !l.cut && l.stuck ≥ 1
#guard let w := stuckWhy (graphOf em0Lost); !w.isEmpty && w.all fun (_, ts) => !ts.isEmpty

/-- The report: the first stuck node of `em0Lost` and its reason. -/
def report : String :=
  match stuckWhy (graphOf em0Lost) with
  | (v, ts) :: rest =>
      s!"em0Lost: STUCK at node {v} ({rest.length + 1} stuck node(s)): thread(s) {ts} parked at `park` with no permit " ++
      "(no thread move; the spurious wake is an unforced environment move)"
  | [] => "em0Lost: no stuck node"

#eval IO.println report

end LostWakeDemo
