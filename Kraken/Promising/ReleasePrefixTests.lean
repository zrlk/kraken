/-
Explorer checks for `Kraken.Promising.ReleasePrefix`: the strict form of (S1)
(`Config.AdvanceableStrict`) fails on
an instruction that performs a release store and then a fresh store; (S1′)
(`Config.Advanceable`, proved as `Config.advanceable_of_path`) and the
variant-(ii) virtual advance hold. Every reachable configuration, promises
included. The harness is ISA-generic; the programs are in
`ReleasePrefixTestsX64` and `ReleasePrefixTestsAArch64` (the two litmus
front ends cannot be imported together).
-/
import Kraken.Promising.ReleasePrefix

namespace Kraken.Promising.ReleasePrefixTests


variable {I : ISA}

/-- The thread states reachable from `t` by memory-silent instruction steps
of thread `i` alone against `mem` (breadth-first, at most `cap` states). -/
partial def silentStates (A : Arch) (i : Nat) (mem : Memory) (t : Thread I) (cap : Nat) : List (Thread I) :=
  let rec go (vis : Std.HashSet (Thread I)) (front : Array (Thread I)) (k : Nat) : List (Thread I) :=
    if h : k < front.size then
      if front.size > cap then front.toList else
      let nexts := match stepOne A front[k] i mem with
        | none => []
        | some outs => outs.filterMap fun (r : Except String (Outcome I)) => match r with
          | .ok o => if o.mem.last == mem.last then some o.thread else none
          | .error _ => none
      let (vis, front) := nexts.foldl (init := (vis, front)) fun (vis, front) t' =>
        if vis.contains t' then (vis, front) else (vis.insert t', front.push t')
      go vis front (k + 1)
    else front.toList
  go (({} : Std.HashSet (Thread I)).insert t) #[t] 0

def okOuts (A : Arch) (i : Nat) (mem : Memory) (t : Thread I) : List (Outcome I) :=
  match stepOne A t i mem with
  | none => []
  | some outs => outs.filterMap fun | .ok o => some o | .error _ => none

/-- `(#configurations, #(configuration, thread) pairs with an outstanding
promise, #outstanding promises, #violating AdvanceableStrict, #violating
(S1′), #pairs with no single variant-(ii) advance)`. (S1′) for `ts`: a
memory-silent run to a state that still has `ts` and whose next instruction
fulfils it (on TSO every store is a release). Variant (ii): one memory-silent
run after which the thread's next instruction fulfils all its remaining
outstanding promises. -/
partial def advanceCheck (A : Arch) (c0 : Config I) (d : Nat := 4000) : Nat × Nat × Nat × Nat × Nat × Nat :=
  let rec go (vis : Std.HashSet (Config I)) (cache : CertCache I) (acc : Nat × Nat × Nat × Nat × Nat × Nat)
      (front : List (Config I)) : Nat × Nat × Nat × Nat × Nat × Nat :=
    match front with
    | [] => acc
    | c :: rest =>
      if vis.contains c then go vis cache acc rest else
      let (next, _, _, cache) := succsL A cache c 300 none
      let (n, thr, proms, strict, s1p, joint) := acc
      let acc := (List.range c.threads.size).foldl (init := (n + 1, thr, proms, strict, s1p, joint))
        fun (n, thr, proms, strict, s1p, joint) i =>
          match c.threads[i]? with
          | none => (n, thr, proms, strict, s1p, joint)
          | some t =>
            if t.prom.isEmpty then (n, thr, proms, strict, s1p, joint) else
            let sts := silentStates A i c.mem t d
            let (strict, s1p) := t.prom.foldl (init := (strict, s1p)) fun (strict, s1p) ts =>
              (if sts.any (fun t' => !t'.prom.contains ts) then strict else strict + 1,
               if sts.any (fun t' => t'.prom.contains ts &&
                   (okOuts A i c.mem t').any fun o => !o.thread.prom.contains ts) then s1p else s1p + 1)
            let ok := sts.any fun t' =>
              let rem := t.prom.filter t'.prom.contains
              rem.isEmpty || (okOuts A i c.mem t').any fun o => rem.all fun ts => !o.thread.prom.contains ts
            (n, thr + 1, proms + t.prom.length, strict, s1p, if ok then joint else joint + 1)
      go (vis.insert c) cache acc (next.map (·.1) ++ rest)
  go {} {} (0, 0, 0, 0, 0, 0) [c0]

/-- The states `(t', M')` reachable from `(t, mem)` by instruction steps of
thread `i` alone, which may append its own messages (`ThreadNP`;
breadth-first, at most `cap` states). -/
partial def npStates (A : Arch) (i : Nat) (mem : Memory) (t : Thread I) (cap : Nat) : List (Thread I × Memory) :=
  let rec go (vis : Std.HashSet (Thread I × Memory)) (front : Array (Thread I × Memory)) (k : Nat) :
      List (Thread I × Memory) :=
    if h : k < front.size then
      if front.size > cap then front.toList else
      let nexts := (okOuts A i front[k].2 front[k].1).map fun o => (o.thread, o.mem)
      let (vis, front) := nexts.foldl (init := (vis, front)) fun (vis, front) q =>
        if vis.contains q then (vis, front) else (vis.insert q, front.push q)
      go vis front (k + 1)
    else front.toList
  go (({} : Std.HashSet (Thread I × Memory)).insert (t, mem)) #[(t, mem)] 0

/-- `(#configurations, #outstanding promises, #violating (S1′),
#violating (S1′) with pending non-temporal stores)`. The last is
`Config.AdvanceableNT` (proved as `Config.advanceableNT_of_path`,
`ReleasePrefixNT`): a run of the thread alone that may append its own
messages, to a state that still has `ts` and whose next instruction, against
the run's memory, fulfils it. -/
partial def advanceCheckNT (A : Arch) (c0 : Config I) (d : Nat := 4000) : Nat × Nat × Nat × Nat :=
  let rec go (vis : Std.HashSet (Config I)) (cache : CertCache I) (acc : Nat × Nat × Nat × Nat)
      (front : List (Config I)) : Nat × Nat × Nat × Nat :=
    match front with
    | [] => acc
    | c :: rest =>
      if vis.contains c then go vis cache acc rest else
      let (next, _, _, cache) := succsL A cache c 300 none
      let (n, proms, s1p, s1pNT) := acc
      let acc := (List.range c.threads.size).foldl (init := (n + 1, proms, s1p, s1pNT))
        fun (n, proms, s1p, s1pNT) i =>
          match c.threads[i]? with
          | none => (n, proms, s1p, s1pNT)
          | some t =>
            if t.prom.isEmpty then (n, proms, s1p, s1pNT) else
            let sts := silentStates A i c.mem t d
            let nps := npStates A i c.mem t d
            let (s1p, s1pNT) := t.prom.foldl (init := (s1p, s1pNT)) fun (s1p, s1pNT) ts =>
              (if sts.any (fun t' => t'.prom.contains ts &&
                   (okOuts A i c.mem t').any fun o => !o.thread.prom.contains ts) then s1p else s1p + 1,
               if nps.any (fun (t', M') => t'.prom.contains ts &&
                   (okOuts A i M' t').any fun o => !o.thread.prom.contains ts) then s1pNT else s1pNT + 1)
            (n, proms + t.prom.length, s1p, s1pNT)
      go (vis.insert c) cache acc (next.map (·.1) ++ rest)
  go {} {} (0, 0, 0, 0) [c0]

end Kraken.Promising.ReleasePrefixTests
