/-
 tool, not a theorem file: a complete certification
search beside the existing one, to check whether the `certify` incompleteness
found by an earlier prototype changes any verdict of the real test corpus.

Nothing here is used by the library or by a theorem; the root module does not
import it (the `Kraken.*` glob builds it). The drivers are the executables
`checkercompare_aarch64` / `checkercompare_x64` (`CheckerCompare{AArch64,X64}.lean`
at the repository root; not default targets). Their output has the format of
the main litmus drivers, so a comparison script can parse both.

Part 1 is that prototype (`CertifyC.lean`, namespace renamed),
verbatim:

- `certifyB`: breadth-first search with the plain `(thread, memory)` visited
  set (variant β). Each state is first expanded at its BFS depth, i.e. its
  distance from the start, so `certified` is exactly "some prom-empty state is
  within `fuel` steps" (`CertOkN`), given that `hasDeadPromise` is exact.
  `writes` are recorded as in `certify.go` (per path); they are not used by
  `certifiedPromisesB`.
- `candidatesB`: every message written on some step within `fuel` of the
  pre-promise state (any `ν`, certified or not): a superset of what a
  `PromSem` promise can be (projection, Q3).
- `certifiedPromisesB`: the paper's rule: a candidate `w` is promised iff the
  *post*-promise thread certifies (`certifyB`) against `mem ++ w`.
- `succsLB`/`succsB`/`exploreB`: the machine step and an unreduced BFS over it;
  `exploreS`: the same BFS over the main `succs`.

Part 2 is what the drivers run: `exploreRB`, a copy of the main `explore`
(`Machine.lean`) in which only the successor function changes: `succsRB` is
`succsR` (local-step reduction, `overlapFault` filter, `maxPromises` cap,
symmetry key in `exploreRB`) over `succsLBC`, which is `succsLB` with a
memo table for `certifyB` and for the promise rule (both are functions of
`(thread, tid, memory)` at a fixed fuel, so the table changes no result).
Witness traces are not recorded. So a difference between `explore` and
`exploreRB` at the same options is due to the certifier and promise rule
alone.
-/
import Kraken.Promising.Machine

namespace Kraken.Promising.CheckerCompare

open Kraken.Promising

/-! ## Part 1: the prototype (verbatim) -/

variable (A : Arch) {I : ISA}

abbrev Entry (I : ISA) := Thread I × Memory × List (Msg × View) × Bool

/-- One BFS level: expand every entry of `frontier` (each state at most once
overall), returning the visited set, the accumulator and the next level. -/
def levelB (tid : Nat) (n : Nat) (visited : Std.HashSet (Thread I × Memory)) (acc : CertResult I)
    (frontier : List (Entry I)) : Std.HashSet (Thread I × Memory) × CertResult I × List (Entry I) :=
  frontier.foldl (init := (visited, acc, [])) fun (visited, acc, next) (t, mem, ws, done) =>
    if visited.contains (t, mem) then (visited, acc, next) else
    let visited := visited.insert (t, mem)
    if t.hasDeadPromise mem then (visited, acc, next) else
    let (acc, done) :=
      if !done && t.prom.isEmpty then ({ acc with certified := true, writes := acc.writes ++ ws }, true)
      else (acc, done)
    if t.halted then (visited, acc, next)
    else
      match n with
      | 0 => (visited, { acc with boundHit := true }, next)
      | _ + 1 =>
        match stepOne A t tid mem with
        | none => (visited, acc, next)
        | some outs =>
          outs.foldl (init := (visited, acc, next)) fun (visited, acc, next) o =>
            match o with
            | .error m => (visited, { acc with faults := acc.faults ++ [m] }, next)
            | .ok o =>
              if done then (visited, { acc with writes := acc.writes ++ o.promisedNow }, (o.thread, o.mem, [], true) :: next)
              else (visited, acc, (o.thread, o.mem, ws ++ o.promisedNow, false) :: next)

/-- BFS certification: level `fuel - n` of the search has `n` instructions
left. Structural on `n`. -/
def goB (tid : Nat) : Nat → Std.HashSet (Thread I × Memory) → CertResult I → List (Entry I) → CertResult I
  | n, visited, acc, frontier =>
    let (visited, acc, next) := levelB A tid n visited acc frontier
    match n, next with
    | _, [] => acc
    | 0, _ => acc
    | n + 1, next => goB tid n visited acc next.reverse

def certifyB (t : Thread I) (tid : Nat) (mem : Memory) (fuel : Nat) : CertResult I :=
  goB A tid fuel {} {} [(t, mem, [], false)]

/-- Every message written by some step within `fuel` instructions of `(t, mem)`
(BFS, plain visited set, no certification): the promise candidates. -/
def candidatesB (t : Thread I) (tid : Nat) (mem : Memory) (fuel : Nat) : List Msg :=
  let rec go : Nat → Std.HashSet (Thread I × Memory) → List Msg → List (Thread I × Memory) → List Msg
    | n, visited, acc, frontier =>
      let (visited, acc, next) := frontier.foldl (init := (visited, acc, ([] : List (Thread I × Memory))))
        fun (visited, acc, next) (t, mem) =>
          if visited.contains (t, mem) then (visited, acc, next) else
          let visited := visited.insert (t, mem)
          if t.hasDeadPromise mem then (visited, acc, next) else
          match n with
          | 0 => (visited, acc, next)
          | _ + 1 =>
            match stepOne A t tid mem with
            | none => (visited, acc, next)
            | some outs => outs.foldl (init := (visited, acc, next)) fun (visited, acc, next) o =>
              match o with
              | .error _ => (visited, acc, next)
              | .ok o => (visited, acc ++ o.promisedNow.map (·.1), (o.thread, o.mem) :: next)
      match n, next with
      | _, [] => acc
      | 0, _ => acc
      | n + 1, next => go n visited acc next.reverse
  (go fuel {} [] [(t, mem)]).eraseDups

/-- The paper's promise rule over `certifyB`: candidate messages whose
post-promise thread certifies within `fuel`. -/
def certifiedPromisesB (c : Config I) (tid : Nat) (fuel : Nat) : List (Config I × TraceEv) × CertResult I :=
  match c.threads[tid]? with
  | none => ([], {})
  | some t =>
    let ws := candidatesB A t tid c.mem fuel
    let cs := ws.filterMap fun w =>
      let (mem', tnew) := c.mem.append { w with tid }
      let t' := { t with prom := t.prom ++ [tnew] }
      if (certifyB A t' tid mem' fuel).certified then
        some (c.withThread tid t' mem', TraceEv.promise tid w.loc w.val tnew)
      else none
    (cs, {})

/-- `succsL` over `certifyB` and `certifiedPromisesB` (no cache, no cap). -/
def succsLB (c : Config I) (fuel : Nat) : List (Config I × List TraceEv) × Bool × List String :=
  (List.range c.threads.size).foldl (init := ([], false, [])) fun (next, bound, faults) tid =>
    let (next, bound, faults) : List (Config I × List TraceEv) × Bool × List String :=
      match stepThread A c tid with
      | none => (next, bound, faults)
      | some outs => outs.foldl (init := (next, bound, faults)) fun (next, bound, faults) o =>
        match o with
        | .error m => (next, bound, faults ++ [m])
        | .ok o =>
          let c' := c.withThread tid o.thread o.mem
          if o.thread.prom.isEmpty then ((c', o.log) :: next, bound, faults)
          else
            let r := certifyB A o.thread tid o.mem fuel
            if r.certified then ((c', o.log) :: next, bound || r.boundHit, faults)
            else (next, bound || r.boundHit, faults)
    let (ps, _) := certifiedPromisesB A c tid fuel
    (next.reverse ++ (ps.map fun (c', e) => (c', [e])), bound, faults)

def succsB (c : Config I) (fuel : Nat) : List (Config I) := (succsLB A c fuel).1.map (·.1)

/-- Exhaustive BFS exploration over `succsLB` (no reductions), collecting
final projections. -/
partial def exploreB {α : Type} [BEq α] [Hashable α] (c0 : Config I) (proj : Config I → α) (fuel : Nat) :
    List α × Nat :=
  let rec go (visited : Std.HashSet (Config I)) (finals : Std.HashSet α) (front back : List (Config I)) (n : Nat) :
      List α × Nat :=
    match front with
    | [] => if back.isEmpty then (finals.toList, n) else go visited finals back.reverse [] n
    | c :: rest =>
      if visited.contains c then go visited finals rest back n else
      let visited := visited.insert c
      if c.final then go visited (finals.insert (proj c)) rest back (n + 1)
      else
        let next := succsB A c fuel
        go visited finals rest (next.foldl (fun b c' => c' :: b) back) (n + 1)
  go {} {} [c0] [] 0

/-- The same exploration over the main `succs` (no reductions), for a
like-for-like comparison. -/
partial def exploreS {α : Type} [BEq α] [Hashable α] (c0 : Config I) (proj : Config I → α) (fuel : Nat) :
    List α × Nat :=
  let rec go (visited : Std.HashSet (Config I)) (finals : Std.HashSet α) (front back : List (Config I)) (n : Nat) :
      List α × Nat :=
    match front with
    | [] => if back.isEmpty then (finals.toList, n) else go visited finals back.reverse [] n
    | c :: rest =>
      if visited.contains c then go visited finals rest back n else
      let visited := visited.insert c
      if c.final then go visited (finals.insert (proj c)) rest back (n + 1)
      else
        let next := (succs A c fuel).1
        go visited finals rest (next.foldl (fun b c' => c' :: b) back) (n + 1)
  go {} {} [c0] [] 0

/-! ## Part 2: the driver's explorer (`explore` with the prototype's step) -/

/-- Memo tables for the prototype at one fuel: `certifyB` results and the
messages the promise rule accepts, both keyed on `(thread, tid, memory)`. -/
structure CacheB (I : ISA) where
  cert : Std.HashMap (Thread I × Nat × Memory) (CertResult I) := {}
  prom : Std.HashMap (Thread I × Nat × Memory) (List Msg) := {}

/-- `certifyB`, memoised. -/
def certifyBC (cache : CacheB I) (t : Thread I) (tid : Nat) (mem : Memory) (fuel : Nat) :
    CertResult I × CacheB I :=
  match cache.cert[(t, tid, mem)]? with
  | some r => (r, cache)
  | none =>
    let r := certifyB A t tid mem fuel
    (r, { cache with cert := cache.cert.insert (t, tid, mem) r })

/-- `certifiedPromisesB`, memoised: the same configurations, in the same
order (the accepted candidates depend on `(t, tid, c.mem)` only). -/
def certifiedPromisesBC (cache : CacheB I) (c : Config I) (tid : Nat) (fuel : Nat) :
    List (Config I × TraceEv) × CacheB I :=
  match c.threads[tid]? with
  | none => ([], cache)
  | some t =>
    let (ws, cache) : List Msg × CacheB I := match cache.prom[(t, tid, c.mem)]? with
      | some ws => (ws, cache)
      | none =>
        let ws := (candidatesB A t tid c.mem fuel).filter fun (w : Msg) =>
          let (mem', tnew) := c.mem.append { w with tid }
          (certifyB A { t with prom := t.prom ++ [tnew] } tid mem' fuel).certified
        (ws, { cache with prom := cache.prom.insert (t, tid, c.mem) ws })
    let cs := ws.map fun w =>
      let (mem', tnew) := c.mem.append { w with tid }
      (c.withThread tid { t with prom := t.prom ++ [tnew] } mem', TraceEv.promise tid w.loc w.val tnew)
    (cs, cache)

/-- `succsLB` with the memo tables and the standard `maxPromises` cap. -/
def succsLBC (cache : CacheB I) (c : Config I) (fuel : Nat) (maxPromises : Option Nat := none) :
    List (Config I × List TraceEv) × Bool × List String × CacheB I :=
  (List.range c.threads.size).foldl (init := ([], false, [], cache)) fun (next, bound, faults, cache) tid =>
    let (next, bound, faults, cache) : List (Config I × List TraceEv) × Bool × List String × CacheB I :=
      match stepThread A c tid with
      | none => (next, bound, faults, cache)
      | some outs => outs.foldl (init := (next, bound, faults, cache)) fun (next, bound, faults, cache) o =>
        match o with
        | .error m => (next, bound, faults ++ [m], cache)
        | .ok o =>
          let c' := c.withThread tid o.thread o.mem
          if o.thread.prom.isEmpty then ((c', o.log) :: next, bound, faults, cache)
          else
            let (r, cache) := certifyBC A cache o.thread tid o.mem fuel
            if r.certified then ((c', o.log) :: next, bound || r.boundHit, faults, cache)
            else (next, bound || r.boundHit, faults, cache)
    let (ps, cache) := certifiedPromisesBC A cache c tid fuel
    let ps := match maxPromises, c.threads[tid]? with
      | some k, some t => if t.prom.length < k then ps else []
      | _, _ => ps
    (next.reverse ++ (ps.map fun (c', e) => (c', [e])), bound, faults, cache)

/-- `succsR` over `succsLBC`. -/
def succsRB (cache : CacheB I) (c : Config I) (o : ExploreOpts) :
    List (Config I × List TraceEv) × Bool × List String × CacheB I :=
  match localStep A c with
  | some next => (next, false, [], cache)
  | none =>
    let (next, bound, faults, cache) := succsLBC A cache c o.fuel o.maxPromises
    let (next, faults) := next.foldr (init := ([], faults)) fun (c', ev) (next, faults) =>
      match overlapFault c'.mem ev with
      | some m => (next, m :: faults)
      | none => ((c', ev) :: next, faults)
    (next, bound, faults, cache)

/-- `explore` over `succsRB`, without witness traces (`witnesses` is empty). -/
partial def exploreRB {α : Type} [BEq α] [Hashable α] (c0 : Config I) (proj : Config I → α)
    (o : ExploreOpts := {}) : ExploreResult α :=
  let key (c : Config I) : Config I := if o.symmetric then c.canonical else c
  let rec go (visited : Std.HashSet (Config I)) (finals : Std.HashSet α) (cache : CacheB I)
      (front back : List (Config I)) (acc : ExploreResult α) : ExploreResult α :=
    match front with
    | [] =>
      if back.isEmpty then { acc with finals := finals.toList }
      else go visited finals cache back.reverse [] acc
    | c :: rest =>
      if visited.contains (key c) then go visited finals cache rest back acc else
      let visited := visited.insert (key c)
      let acc := { acc with configs := acc.configs + 1 }
      if c.final then go visited (finals.insert (proj c)) cache rest back acc
      else
      let (next, bound, faults, cache) := succsRB A cache c o
      go visited finals cache rest (next.foldl (fun b (c', _) => c' :: b) back)
        { acc with boundHit := acc.boundHit || bound, faults := acc.faults ++ faults }
  go {} {} {} [c0] [] {}

end Kraken.Promising.CheckerCompare
