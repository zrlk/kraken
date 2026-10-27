/-
# Liveness under fairness: the configuration graph, and its terminal classes

`TermRun.exploreM` finds the *final* configurations of a program.  This module
keeps the graph it walks --- every configuration it visits and every move
between them --- and asks the other question: can a run go on forever?

## The criterion

A **fair livelock** is a strongly connected class `C` of configurations that
is *closed under thread steps*: it has a move inside it (so a run can stay),
and no thread step leaves it.  Promise steps and crash steps are not counted
as exits (a run need not speculate, and need not crash).  Liveness holds when
every such terminal class is a single final configuration.

Why closure is the right notion of fairness here, rather than "every enabled
thread takes a step in `C`":

* **Memory is constant inside `C`.**  A configuration's key contains the
  memory, and memory only grows, so a cycle cannot add a message.  Likewise
  every thread's views and promise list are constant on the cycle.
* **Thread fairness.**  A thread enabled somewhere in `C` with no step inside
  `C` never moves on a run that stays in `C`; such a run is unfair.  So every
  enabled thread must have an edge inside `C`.
* **Memory fairness.**  Suppose thread `j` at some `s ∈ C` has one step inside
  `C` and another leaving it.  Memory and `j`'s views are the same on both
  sides of the inside step, so that step read a message no newer than `j`'s
  view; the exit read a newer one (the only other nondeterminism in a thread
  step is the message read).  A run that takes the inside edge forever reads a
  stale value forever while a newer write stands in memory --- which the
  hardware does not do: writes become visible.  So that run is unfair too.
* Hence a fair infinite run exists in `C` iff no thread step leaves `C`.

The spin of a waiter on a lock whose holder is still running is therefore
*not* a livelock: the holder's release leaves the class.  The same spin after
the holder has crashed (`crash=`) is one, and is reported as such --- which is
what makes "a crashed waiter deadlocks the queue" a checked sentence rather
than a remark.

A **stuck** configuration is a non-final one with no thread step at all.  The
core language has no blocking primitive, so there should be none; the count
is reported so that a change would show.

## What the partial-order reduction does to this

`successors` offers only the first available silent step when there is one.
A class consisting of silent steps of one thread alone is a pure loop of that
thread, a real non-termination, and is reported.  Otherwise the class
contains a configuration at which every thread's steps were offered, and a
step of thread `j` at a reduced configuration commutes with the silent steps
before that one, so it leaves the class iff `j`'s step there does.  The
criterion is therefore unaffected by the reduction.

## Promises

Inside a class a thread's promise list is constant, so a thread with a
promise outstanding never fulfils it on a run that stays.  Such a class is
reported with `promised = true`; the same spin without the promise is its own
class and is reported on its own merits.
-/

import WeakCore.TermRun
import WeakCore.TermSmoke
import Std.Data.HashMap

open CoreLang CoreTerm TermRun TermSmoke
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

namespace TermLive

instance : Inhabited Cfg := ⟨{ mem := #[], ths := #[] }⟩

/-- `successors`, with each move labelled by its thread and whether it is a
thread step (`true`) or a promise (`false`).  The same partial-order
reduction, the same bounds. -/
def successorsL (p : Prog) (k : Promises.Knobs) (arch : Arch) (b : Bounds) (c : Cfg) :
    List (Nat × Bool × Cfg) :=
  let silent := (List.range c.ths.size).find? fun i =>
    match c.ths[i]? with
    | some th => !isDone th && !touchesMem th && !(threadSteps p k arch c i).isEmpty
    | none => false
  match silent with
  | some i => (threadSteps p k arch c i).map fun c' => (i, true, c')
  | none =>
    (List.range c.ths.size).flatMap fun i =>
      let ts := ((threadSteps p k arch c i).filter fun c' => certB p k arch b.solo c' i).map
        fun c' => (i, true, c')
      let ps :=
        match c.ths[i]? with
        | some th =>
            if th.promises.length < b.maxP && !isDone th then
              (((soloWrites p k arch i b.solo c).eraseDups.flatMap fun (a, v) =>
                (List.range c.mem.size).map fun w => promise c i a v w).filter
                  fun c' => certB p k arch b.solo c' i).map fun c' => (i, false, c')
            else []
        | none => []
      -- (F2) the extern moves (`successorsAll`'s `extSuccs`), labelled as thread moves
      let es := (extSuccs p k arch b c i).map fun c' => (i, true, c')
      -- (D4) the spurious wakes (`successorsAll`'s `wakeSuccs`), environment moves: unforced, like promises
      let ws := (wakeSuccs p k arch b c i).map fun c' => (i, false, c')
      ts ++ ps ++ es ++ ws

/-- `successorsL`, with the truncations its bounds caused (as `TermRun.successorsAllT`), and the
node's (`nodeTrunc`; spawn sites count iff `spawnOff`). -/
def successorsLT (p : Prog) (k : Promises.Knobs) (arch : Arch) (b : Bounds) (spawnOff : Bool)
    (c : Cfg) : List (Nat × Bool × Cfg) × Trunc :=
  let silent := (List.range c.ths.size).find? fun i =>
    match c.ths[i]? with
    | some th => !isDone th && !touchesMem th && !(threadSteps p k arch c i).isEmpty
    | none => false
  let nt := nodeTrunc true spawnOff b c
  match silent with
  | some i => ((threadSteps p k arch c i).map fun c' => (i, true, c'), nt)
  | none =>
    let rs := (List.range c.ths.size).map fun i =>
      let ts := (threadSteps p k arch c i).partition fun c' => certB p k arch b.solo c' i
      let ps : List Cfg × List Cfg × Bool :=
        match c.ths[i]? with
        | some th =>
            if th.promises.length < b.maxP && !isDone th then
              let q := ((soloWrites p k arch i b.solo c).eraseDups.flatMap fun (a, v) =>
                (List.range c.mem.size).map fun w => promise c i a v w).partition
                  fun c' => certB p k arch b.solo c' i
              (q.1, q.2, candCut p k arch i b.solo c)
            else ([], [], false)
        | none => ([], [], false)
      ((ts.1.map fun c' => (i, true, c')) ++ (ps.1.map fun c' => (i, false, c')) ++
          ((extSuccs p k arch b c i).map fun c' => (i, true, c')) ++
          (wakeSuccs p k arch b c i).map fun c' => (i, false, c'),
        ({ cert := (ts.2 ++ ps.2.1).any (fun c' => certCut p k arch b.solo c' i) ||
              extCut p k arch b c i ||
              wakeCut p k arch b c i
           cand := ps.2.2 } : Trunc))
    (rs.flatMap (·.1), rs.foldl (fun t r => t.or r.2) nt)

/-- The flags change nothing else: `successorsLT` offers exactly `successorsL`'s moves. -/
theorem successorsLT_fst (p : Prog) (k : Promises.Knobs) (arch : Arch) (b : Bounds) (s : Bool)
    (c : Cfg) : (successorsLT p k arch b s c).1 = successorsL p k arch b c := by
  simp only [successorsLT, successorsL]
  split
  · rfl
  · simp only [List.flatMap_map]
    congr 1
    funext i
    simp only [List.partition_eq_filter_filter]
    split <;> (try split) <;> simp_all

/-- Thread `i` stops here: its term becomes a `ret` of nothing, which `resWs`
reads as no result (`-` in the table).  Not while it has a promise out: a
stopped thread cannot keep one, and the model has no take-back. -/
def crashCfg (c : Cfg) (i : Nat) : Option Cfg :=
  match c.ths[i]? with
  | some th =>
      if isDone th || !th.promises.isEmpty then none
      else some { c with ths := c.ths.set! i { th with term := .ret (.var "crashed"), stack := [] } }
  | none => none

/-- The explored graph.  `edges[v]` lists `(thread, isThreadStep, target)`;
an `extra` move (a crash) is labelled with the thread count and `false`.
`expanded[v]` is false only for a node the depth bound left unexpanded.
`why` is every truncation the search hit; `cut` is `why.isCut`. -/
structure Graph where
  nodes    : Array Cfg
  edges    : Array (List (Nat × Bool × Nat))
  expanded : Array Bool
  cut      : Bool
  why      : Trunc := {}

/-- `exploreM`, keeping the graph, for a successor function `succ` (labelled
moves) and the label `xl d` of `extra` moves at `d`.  Breadth-first over
configuration keys, `fuel` layers deep. -/
def exploreGP (succ : Cfg → List (Nat × Bool × Cfg) × Trunc) (xl : Cfg → Nat) (fuel : Nat) (c : Cfg)
    (extra : Cfg → List Cfg := fun _ => []) : Graph := Id.run do
  let mut tr : Trunc := {}
  let mut ids : Std.HashMap CfgKey Nat := Std.HashMap.emptyWithCapacity.insert (cfgKey c) 0
  let mut nodes : Array Cfg := #[c]
  let mut edges : Array (List (Nat × Bool × Nat)) := #[[]]
  let mut expanded : Array Bool := #[false]
  let mut frontier : List Nat := [0]
  for _ in [0:fuel] do
    if frontier.isEmpty then break
    let mut next : List Nat := []
    for v in frontier do
      let d := nodes[v]!
      expanded := expanded.set! v true
      if d.final then continue
      let (sm, t) := succ d
      tr := tr.or t
      let moves := sm ++ (extra d).map fun e => (xl d, false, e)
      let mut es : List (Nat × Bool × Nat) := []
      for (i, t, e) in moves do
        let key := cfgKey e
        let mut w := 0
        match ids.get? key with
        | some u => w := u
        | none =>
          w := nodes.size
          ids := ids.insert key w
          nodes := nodes.push e
          edges := edges.push []
          expanded := expanded.push false
          next := w :: next
        es := (i, t, w) :: es
      edges := edges.set! v es
    frontier := next
  let all := { tr with depth := !frontier.isEmpty }
  return ⟨nodes, edges, expanded, all.isCut, all⟩

/-- `exploreM`, keeping the graph: `exploreGP` on `successorsL` (`successorsLT`; this explorer
has no spawn moves, so a spawn site is a truncation), an `extra` move (a crash) labelled with the
thread count. -/
def exploreG (p : Prog) (k : Promises.Knobs) (arch : Arch) (b : Bounds) (fuel : Nat) (c : Cfg)
    (extra : Cfg → List Cfg := fun _ => []) : Graph :=
  exploreGP (successorsLT p k arch b true) (fun d => d.ths.size) fuel c extra

/-- The `Explored` view of a graph: what `exploreM` would have returned. -/
def Graph.toExplored (g : Graph) : Explored :=
  let finals := (List.range g.nodes.size).filterMap fun v =>
    if g.expanded[v]! && (g.nodes[v]!).final then some g.nodes[v]! else none
  ⟨finals, g.nodes.size, g.cut⟩

/-- Strongly connected components (Tarjan, iterative).  Returns each node's
component number. -/
def sccs (succ : Array (List Nat)) : Array Nat := Id.run do
  let n := succ.size
  let mut index : Array (Option Nat) := Array.replicate n none
  let mut low : Array Nat := Array.replicate n 0
  let mut onStack : Array Bool := Array.replicate n false
  let mut comp : Array Nat := Array.replicate n 0
  let mut stack : Array Nat := #[]
  let mut counter := 0
  let mut ncomp := 0
  for root in [0:n] do
    if (index[root]!).isSome then continue
    let mut call : Array (Nat × List Nat) := #[(root, succ[root]!)]
    index := index.set! root (some counter); low := low.set! root counter; counter := counter + 1
    stack := stack.push root; onStack := onStack.set! root true
    while !call.isEmpty do
      let (v, rest) := call.back!
      match rest with
      | w :: rest' =>
        call := call.set! (call.size - 1) (v, rest')
        match index[w]! with
        | none =>
          index := index.set! w (some counter); low := low.set! w counter; counter := counter + 1
          stack := stack.push w; onStack := onStack.set! w true
          call := call.push (w, succ[w]!)
        | some iw => if onStack[w]! then low := low.set! v (min low[v]! iw)
      | [] =>
        call := call.pop
        if low[v]! == (index[v]!).getD 0 then
          let mut go := true
          while go do
            let w := stack.back!
            stack := stack.pop
            onStack := onStack.set! w false
            comp := comp.set! w ncomp
            if w == v then go := false
          ncomp := ncomp + 1
        if !call.isEmpty then
          let (u, _) := call.back!
          low := low.set! u (min low[u]! low[v]!)
  return comp

/-- One fair livelock: a class closed under thread steps with a move inside. -/
structure Livelock where
  /-- configurations in the class -/
  size     : Nat
  /-- threads with a step inside the class (they spin) -/
  stepping : List Nat
  /-- threads that have finished (or stopped) -/
  done     : List Nat
  /-- threads neither finished nor stepping -/
  blocked  : List Nat
  /-- some thread has a promise outstanding in the class -/
  promised : Bool
  deriving Repr, BEq

structure Live where
  livelocks : List Livelock
  /-- non-final configurations with no thread step -/
  stuck     : Nat
  nodes     : Nat
  cut       : Bool
  /-- every truncation the search hit (`cut` is `why.isCut`) -/
  why       : Trunc := {}
  deriving Repr

/-- The terminal classes of the thread-step graph. -/
def analyse (g : Graph) : Live := Id.run do
  let n := g.nodes.size
  let comp := sccs (g.edges.map fun es => es.filterMap fun (_, t, d) => if t then some d else none)
  let ncomp := comp.foldl max 0 + 1
  let mut closed : Array Bool := Array.replicate ncomp true
  let mut inside : Array (List Nat) := Array.replicate ncomp []
  let mut members : Array (List Nat) := Array.replicate ncomp []
  for v in [0:n] do
    let c := comp[v]!
    members := members.set! c (v :: members[c]!)
    for (i, t, d) in g.edges[v]! do
      if t then
        if comp[d]! == c then inside := inside.set! c (i :: inside[c]!)
        else closed := closed.set! c false
  let mut lls : List Livelock := []
  let mut stuck := 0
  for c in [0:ncomp] do
    if !closed[c]! then continue
    match members[c]!, inside[c]! with
    | [], _ => pure ()
    | v :: _, [] =>
        if g.expanded[v]! && !(g.nodes[v]!).final then stuck := stuck + 1
    | v :: _, ins =>
        let cfg := g.nodes[v]!
        let ths := List.range cfg.ths.size
        let stepping := (ths.filter ins.contains)
        let done := ths.filter fun i => (cfg.ths[i]?.map isDone).getD false
        let blocked := ths.filter fun i => !stepping.contains i && !done.contains i
        let promised := cfg.ths.any fun th => !th.promises.isEmpty
        lls := ⟨(members[c]!).length, stepping, done, blocked, promised⟩ :: lls
  return ⟨lls.reverse, stuck, n, g.cut, g.why⟩

/-- The livelocks grouped by kind (who spins, who finished, who is blocked,
whether a promise is out), each with its count and class sizes. -/
def Live.kinds (l : Live) : List (Livelock × Nat × List Nat) :=
  let key (ll : Livelock) : Livelock := { ll with size := 0 }
  (l.livelocks.map key).eraseDups.map fun k =>
    let same := l.livelocks.filter fun ll => key ll == k
    (k, same.length, (same.map (·.size)).eraseDups)

/-- `fair runs` sentence for a report (plain text, LaTeX-safe). -/
def Live.describe (l : Live) : String :=
  let ths (xs : List Nat) := (if xs.length == 1 then "thread " else "threads ") ++
    ", ".intercalate (xs.map toString)
  let plural (n : Nat) (w : String) := s!"{n} {w}" ++ (if n == 1 then "" else "s")
  let one : Livelock × Nat × List Nat → String
    | (ll, n, sizes) =>
      (if n == 1 then "" else s!"{n} of ") ++
      "{" ++ ", ".intercalate (
        (if ll.stepping.isEmpty then [] else [ths ll.stepping ++ " spin"]) ++
        (if ll.done.isEmpty then [] else [ths ll.done ++ " finished"]) ++
        (if ll.blocked.isEmpty then [] else [ths ll.blocked ++ " blocked"]) ++
        (if ll.promised then ["a promise outstanding"] else [])) ++ "}" ++
      (match sizes with
       | [k] => s!" of {plural k "configuration"}"
       | ks => s!" of {ks.foldl min (ks.headD 0)} to {ks.foldl max 0} configurations")
  match l.livelocks, l.stuck with
  | [], 0 => "no fair livelock found"
  | lls, s =>
    (if lls.isEmpty then "" else
      plural lls.length "fair livelock" ++ ": " ++ "; ".intercalate (l.kinds.map one)) ++
    (if s == 0 then "" else (if lls.isEmpty then "" else "; ") ++ s!"{s} stuck configuration" ++
      (if s == 1 then "" else "s"))

/-! ## Pinned: the mutex, with and without a crash

Two threads increment under `mutexLib`'s mutex: no fair livelock found.
If thread 0 may stop anywhere, the classes in which it stopped while holding
the lock are fair livelocks of thread 1's spin --- and nothing else is. -/

def mutexGraph (crash : Option Nat) : Option Graph :=
  mSetup.map fun s =>
    exploreG mutexLib Promises.Knobs.all .arm { maxP := 0 } 300 (spawn s (mThr s))
      (fun d => match crash with | some i => (crashCfg d i).toList | none => [])

#guard match mutexGraph none with
  | some g => let l := analyse g; l.livelocks.isEmpty && l.stuck == 0 && !l.cut
  | none => false

#guard match mutexGraph (some 0) with
  | some g =>
      let l := analyse g
      !l.livelocks.isEmpty && l.stuck == 0 && !l.cut &&
      l.livelocks.all fun ll => ll.stepping == [1] && ll.done == [0] && ll.blocked == [] && !ll.promised
  | none => false

-- The graph's finals agree with `exploreM`'s.
#guard match mutexGraph none, runE mutexLib mSetup mThr 0 with
  | some g, some ex => g.toExplored.finals.length == ex.finals.length && g.toExplored.seen == ex.seen
  | _, _ => false

end TermLive
