/-
Promising-ARM/RISC-V for Kraken: the machine.

A configuration is a pool of threads and the memory. A machine step picks a
thread and either runs its next instruction (`Thread` rules) or takes a
*certified* promise (§4.3 and §7 of the paper): a write the thread would
perform when run alone from here, promise-free, on a trace that ends with
no outstanding promises, and whose pre-view and coherence view do not exceed
the current memory. `explore` enumerates every reachable final state.
-/
import Kraken.Promising.Thread
import Std.Data.HashSet

namespace Kraken.Promising

/-! ## Configurations -/

structure Config (I : ISA) where
  threads : Array (Thread I)
  mem : Memory

namespace Config

variable {I : ISA}

instance : BEq (Config I) := ⟨fun a b => a.threads == b.threads && a.mem == b.mem⟩
instance : Hashable (Config I) := ⟨fun c => mixHash (Hashable.hash c.threads) (Hashable.hash c.mem)⟩

def init (states : List I.State) (initMem : List (Loc × Val)) : Config I :=
  { threads := (states.map Thread.init).toArray, mem := { init := initMem, msgs := #[] } }

/-- Every thread has halted with no outstanding promise. -/
def final (c : Config I) : Bool :=
  c.threads.all fun t => t.halted && t.prom.isEmpty

end Config

/-! ## One instruction of one thread -/

section Step

variable (A : Arch) {I : ISA}

/-- The views an instruction's register dependencies give it. With per-store
data registers (`STP`), each store gets its own data views (`dataPer`) and
the instruction-wide data views are `0`: the data feeds the stores only, not
a written-back base (herd's `stp_wback` writes the base without reading the
data registers). -/
def instrViews (t : Thread I) (d : InstrDeps I.RegId) : InstrViews :=
  let (addrR, addrW) := t.joinViews d.addrRegs
  let dv := if d.dataRegsPer.isEmpty then t.joinViews d.dataRegs else (0, 0)
  let dataR := dv.1
  let dataW := dv.2
  let (_, condW) := t.joinViews d.condRegs
  { addrR, addrW, dataR, dataW, condW, dataPer := d.dataRegsPer.map t.joinViews }

/-- Register views after the instruction: loads' destinations get the loads'
post-views (one per destination, in order; the join when counts differ), the
success register of a store exclusive its success view, every other
destination the join of the instruction's input views — for a pick, the
condition joins the write-ordering view only; a branch folds its condition
view into `vCAP`.

A successful compare-and-swap (`casLike` with the write performed) is herd's
`aarch64_cas_ok`: the comparand register's new value is data-dependent
*either* on the old register value (with a control dependency on the memory
read, i.e. a pick dependency) *or* on the memory read; both executions are
legal, so both threads are returned. -/
def finishInstr (t : Thread I) (d : InstrDeps I.RegId) (iv : InstrViews) (st : I.State) (c : Ctx) :
    List (Thread I) :=
  let inR := max iv.addrR iv.dataR
  let inW := max (max iv.addrW iv.dataW) iv.condW
  let inR := if d.isPick then inR else max inR iv.condW
  let t := { t with st, views := c.views, prom := c.prom }
  let t := d.defs.foldl (fun t r => t.setRegView r inR inW) t
  let t := d.statusDefs.foldl (fun t r => t.setRegView r c.succView c.succView) t
  let branch (t : Thread I) : Thread I :=
    if d.isBranch then { t with views := { t.views with vCAP := max t.views.vCAP iv.condW } } else t
  let fromLoads (t : Thread I) : Thread I :=
    if d.loadDefs.length == c.loadViews.length then
      (d.loadDefs.zip c.loadViews).foldl (fun t (r, v) => t.setRegView r v v) t
    else
      let v := c.loadViews.foldl max 0
      d.loadDefs.foldl (fun t r => t.setRegView r v v) t
  if d.casLike && c.rmwWrote then
    let readView := c.loadViews.foldl max 0
    let fromRs := d.loadDefs.foldl (fun t r => t.setRegView r (t.rviewOf r) (max (t.wviewOf r) readView)) t
    [branch fromRs, branch (fromLoads t)]
  else
    [branch (fromLoads t)]

/-- An outcome of running one instruction: the new thread and memory, with
the writes it promised-now and their constraining views (for certification). -/
structure Outcome (I : ISA) where
  thread : Thread I
  mem : Memory
  promisedNow : List (Msg × View)
  log : List TraceEv

/-- Run the next instruction of thread `t`, whose id is `tid`, against `mem`.
`none` if the thread has halted; a fault is reported as an error. -/
def stepOne (t : Thread I) (tid : Nat) (mem : Memory) : Option (List (Except String (Outcome I))) := do
  let tree ← I.exec t.st
  let d := I.deps t.st
  let iv := instrViews t d
  let ctx : Ctx := { views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] }
  return (runTree A tid iv ctx tree).flatMap fun
    | .error m => [.error m]
    | .ok (st, c') => (finishInstr t d iv st c').map fun th =>
        .ok { thread := th, mem := c'.mem, promisedNow := c'.promisedNow, log := c'.log }

/-- Run the next instruction of thread `tid` of a configuration. -/
def stepThread (c : Config I) (tid : Nat) : Option (List (Except String (Outcome I))) := do
  let t ← c.threads[tid]?
  stepOne A t tid c.mem

def Config.withThread (c : Config I) (tid : Nat) (t : Thread I) (mem : Memory) : Config I :=
  { threads := c.threads.set! tid t, mem }

end Step

/-! ## Certification and promises -/

section Certify

variable (A : Arch) {I : ISA}

/-- The result of running a thread alone from a configuration. -/
structure CertResult (I : ISA) where
  /-- Some trace reaches a state with no outstanding promises (the thread
  need not halt: a thread blocked on another thread, e.g. a producer waiting
  for the consumer, can still promise the writes it performs before
  blocking). -/
  certified : Bool := false
  /-- Writes performed on certified traces, with the `pre ⊔ coh` view each
  was constrained by, in the memory at the time. -/
  writes : List (Msg × View) := []
  /-- The instruction budget was exhausted on some trace. -/
  boundHit : Bool := false
  /-- A fault was reached on some trace. -/
  faults : List String := []

/-- Certification results, memoised on the thread, its id and the memory: the
same triple recurs across interleavings of the other threads.

The id is part of the key because `certify` depends on it: fulfilling a
promise needs the message's `tid` to match, and `Memory.atomic` lets a store
exclusive succeed over writes of its own thread only. On the configurations
`explore` visits it happens not to matter (two threads with equal state
against the same memory have no messages of their own: every timestamp in a
thread's `prom` and `fwdb` is one of its own messages, so equal lists are
empty), but that is an invariant of reachable configurations, not of
`certify`, and keying on the id costs nothing measurable. -/
abbrev CertCache (I : ISA) := Std.HashMap (Thread I × Nat × Memory) (CertResult I)

/-- Run thread `tid` alone, promise-free, exploring every trace up to `fuel`
instructions each. A trace certifies once its promise set is empty; the
writes before that point are recorded then, the writes after it as they
happen (promising any of them keeps the thread certifiable by that trace).

The search is depth first, with a visited set on `(thread, memory)` shared
by all traces. `go n (visited, acc) (t, mem, ws, done)` explores from the
state `(t, mem)` with `n` instructions left: `ws` are the writes of the
trace so far (until it certifies), `done` says it has certified. The
recursion is structural on `n` (each successor has one instruction less),
so `certify` is total and its specification is provable
(`PromiseSafe.lean`, `certify_sound`). It visits states in exactly the order
of the former worklist loop (which pushed successors in front of the
worklist, i.e. was a depth-first search too). -/
def certify (cache : CertCache I) (t : Thread I) (tid : Nat) (mem : Memory) (fuel : Nat) :
    CertResult I × CertCache I :=
  match cache[(t, tid, mem)]? with
  | some r => (r, cache)
  | none =>
    let r := (go tid fuel ({}, {}) (t, mem, [], false)).2
    (r, cache.insert (t, tid, mem) r)
where
  go (tid : Nat) : Nat → Std.HashSet (Thread I × Memory) × CertResult I →
      Thread I × Memory × List (Msg × View) × Bool → Std.HashSet (Thread I × Memory) × CertResult I
    | n, (visited, acc), (t, mem, ws, done) =>
      if visited.contains (t, mem) then (visited, acc) else
      let visited := visited.insert (t, mem)
      -- a promise that can no longer be fulfilled: dead branch
      if t.hasDeadPromise mem then (visited, acc) else
      let (acc, done) :=
        if !done && t.prom.isEmpty then ({ acc with certified := true, writes := acc.writes ++ ws }, true)
        else (acc, done)
      if t.halted then (visited, acc)
      else
        match n with
        | 0 => (visited, { acc with boundHit := true })
        | n + 1 =>
          match stepOne A t tid mem with
          | none => (visited, acc)
          | some outs =>
            let (next, acc) := outs.foldl (init := ([], acc)) fun (next, acc) o =>
              match o with
              | .error m => (next, { acc with faults := acc.faults ++ [m] })
              | .ok o =>
                if done then ((o.thread, o.mem, [], true) :: next, { acc with writes := acc.writes ++ o.promisedNow })
                else ((o.thread, o.mem, ws ++ o.promisedNow, false) :: next, acc)
            next.foldl (go tid n) (visited, acc)

/-- The promises thread `tid` may make now: the writes of certified traces
whose constraining view is at most `|M|`, each as a configuration with the
message appended and promised. Duplicate messages are promised once. -/
def certifiedPromises (cache : CertCache I) (c : Config I) (tid : Nat) (fuel : Nat) :
    List (Config I × TraceEv) × CertResult I × CertCache I :=
  match c.threads[tid]? with
  | none => ([], {}, cache)
  | some t =>
    let (r, cache) := certify A cache t tid c.mem fuel
    let ws := (r.writes.filter fun (_, ν) => ν ≤ c.mem.last).map (·.1) |>.eraseDups
    let cs := ws.map fun w =>
      let (mem', tnew) := c.mem.append { w with tid }
      (c.withThread tid { t with prom := t.prom ++ [tnew] } mem', TraceEv.promise tid w.loc w.val tnew)
    (cs, r, cache)

end Certify

/-! ## The machine step and exhaustive exploration -/

/-- Exploration options. -/
structure ExploreOpts where
  /-- Certification budget: instructions per thread when run alone. -/
  fuel : Nat := 64
  /-- Cap on outstanding promises per thread; `none` is complete, a cap is
  an under-approximation (fewer behaviours explored). -/
  maxPromises : Option Nat := none
  /-- Symmetry reduction: identical threads are interchangeable. Only sound
  for properties invariant under renaming threads. -/
  symmetric : Bool := false
  deriving Repr, Inhabited

section Explore

variable (A : Arch) {I : ISA}

/-- Canonical representative under thread renaming: threads sorted by a
thread-id-independent key, message thread ids renamed accordingly. -/
def Config.canonical (c : Config I) : Config I :=
  let keyed := (c.threads.toList.zipIdx).map fun (t, i) => (hash t, i)
  let order := keyed.mergeSort (fun a b => a.1 ≤ b.1) |>.map (·.2)   -- new position ↦ old tid
  let rename (tid : Nat) : Nat := (order.idxOf? tid).getD tid        -- old tid ↦ new position
  { threads := (order.filterMap fun i => c.threads[i]?).toArray,
    mem := { c.mem with msgs := c.mem.msgs.map fun w => { w with tid := rename w.tid } } }

/-- Every machine successor of a configuration, each with the trace events
that produced it: for each thread, its instruction steps (kept only if the
thread can still fulfil its promises when run alone) and its certified
promises. Faults and budget exhaustion are reported alongside; the
certification cache is threaded through. -/
def succsL (cache : CertCache I) (c : Config I) (fuel : Nat) (maxPromises : Option Nat := none) :
    List (Config I × List TraceEv) × Bool × List String × CertCache I :=
  (List.range c.threads.size).foldl (init := ([], false, [], cache)) fun (next, bound, faults, cache) tid =>
    let (next, bound, faults, cache) : List (Config I × List TraceEv) × Bool × List String × CertCache I :=
      match stepThread A c tid with
      | none => (next, bound, faults, cache)
      | some outs => outs.foldl (init := (next, bound, faults, cache)) fun (next, bound, faults, cache) (o : Except String (Outcome I)) =>
        match o with
        | .error m => (next, bound, faults ++ [m], cache)
        | .ok o =>
          let c' := c.withThread tid o.thread o.mem
          if o.thread.prom.isEmpty then ((c', o.log) :: next, bound, faults, cache)
          else
            let (r, cache) := certify A cache o.thread tid o.mem fuel
            if r.certified then ((c', o.log) :: next, bound || r.boundHit, faults, cache)
            else (next, bound || r.boundHit, faults, cache)
    let (ps, r, cache) := certifiedPromises A cache c tid fuel
    let ps := match maxPromises, c.threads[tid]? with
      | some k, some t => if t.prom.length < k then ps else []
      | _, _ => ps
    -- In thread order, ordinary steps before promises: this decides which of
    -- several shortest runs the breadth-first `explore` records as a witness.
    (next.reverse ++ (ps.map fun (c', e) => (c', [e])), bound || r.boundHit, faults ++ r.faults, cache)

/-- An outcome that touched no shared memory: a register-only instruction or
a branch. Such a step commutes with every step of every other thread. -/
def Outcome.isLocal (o : Outcome I) : Bool :=
  o.log.all fun | .instr .. => true | _ => false

/-- Partial-order reduction: if some thread's next instruction is local for
all its outcomes, step that thread alone. Sound for reachability of final
configurations because local steps commute with all other steps and do not
affect certification of other threads. Returns `none` when no thread
qualifies. -/
def localStep (c : Config I) : Option (List (Config I × List TraceEv)) :=
  (List.range c.threads.size).findSome? fun tid =>
    match stepThread A c tid with
    | none => none
    | some outs =>
      let oks := outs.filterMap fun | .ok o => some o | .error _ => none
      if oks.length == outs.length && !oks.isEmpty && oks.all Outcome.isLocal then
        some (oks.map fun o => (c.withThread tid o.thread o.mem, o.log))
      else none

/-- A mixed-size report for a step: an access or promise of the step (`log`)
to a sized footprint that overlaps, without being equal to, a sized footprint
of the memory after the step (`Decls.resolve`'s message). `resolve` already
reports an access overlapping a sized declaration; this catches two
*undeclared* footprints (strict mode), which
`resolve` cannot see, since it does not know the memory.

It is complete for what a mixed-size access could observe: a load whose
value a mixed-size semantics would build from an overlapping write can only
read once that write is in memory, and a store's footprint is in memory for
every later access. Unsized locations (`bytes = 0`, legacy mode) are never
checked, so legacy runs are unaffected. -/
def overlapFault (mem : Memory) (log : List TraceEv) : Option String :=
  let here (b : BitVec 64) : String := s!"0x{b.toHex}"
  let check (l : Loc) : Option String :=
    if l.bytes == 0 then none
    else
      let clash (l' : Loc) : Bool := l' != l && l'.bytes != 0 && Decls.overlaps l.addr l.bytes l'.addr l'.bytes
      match (mem.init.map (·.1)).find? clash <|> (mem.msgs.find? (clash ·.loc)).map (·.loc) with
      | some l' => some s!"mixed-size access: {l.bytes} bytes at {here l.addr} overlaps the location of {l'.bytes} bytes at {here l'.addr}"
      | none => none
  log.findSome? fun
    | .read l .. | .write l .. | .promise _ l .. => check l
    | _ => none

/-- `succsL` with the local-step reduction; a successor whose step makes a
mixed-size access (`overlapFault`) is dropped and reported as a fault. -/
def succsR (cache : CertCache I) (c : Config I) (o : ExploreOpts) :
    List (Config I × List TraceEv) × Bool × List String × CertCache I :=
  match localStep A c with
  | some next => (next, false, [], cache)
  | none =>
    let (next, bound, faults, cache) := succsL A cache c o.fuel o.maxPromises
    let (next, faults) := next.foldr (init := ([], faults)) fun (c', ev) (next, faults) =>
      match overlapFault c'.mem ev with
      | some m => (next, m :: faults)
      | none => ((c', ev) :: next, faults)
    (next, bound, faults, cache)

/-- The successors alone (unreduced). -/
def succs (c : Config I) (fuel : Nat) : List (Config I) × Bool × List String :=
  let (cs, b, f, _) := succsL A {} c fuel
  (cs.map (·.1), b, f)

/-- The machine step as a relation in the shape `Eventually` consumes:
every successor satisfies `post`, and there is one. `Eventually (Step A fuel)`
is then "under every schedule, a configuration satisfying `post` is reached". -/
def Step (fuel : Nat) (c : Config I) (post : Config I → Prop) : Prop :=
  (succs A c fuel).1 ≠ [] ∧ ∀ c' ∈ (succs A c fuel).1, post c'

/-- Reachability along machine steps. -/
inductive Reachable (fuel : Nat) : Config I → Config I → Prop
  | refl (c : Config I) : Reachable fuel c c
  | step {c c' c'' : Config I} : c' ∈ (succs A c fuel).1 → Reachable fuel c' c'' → Reachable fuel c c''

structure ExploreResult (α : Type) where
  finals : List α := []
  /-- For each final projection, the trace of the first run that reached it.
  The exploration is breadth first, so this is a shortest run of the reduced
  machine. (A promise costs a step: for loop-free threads, a witness contains
  a promise only if no promise-free run reaches the state.) -/
  witnesses : List (α × List TraceEv) := []
  boundHit : Bool := false
  faults : List String := []
  configs : Nat := 0

/-- Exhaustive exploration of `Reachable`, collecting the projections of the
final configurations and a witness trace for each. Memoised on
configurations; parent links give the traces. Uses the local-step
reduction (`succsR`), which preserves the set of reachable final
configurations. -/
partial def explore {α : Type} [BEq α] [Hashable α] (c0 : Config I) (proj : Config I → α)
    (o : ExploreOpts := {}) : ExploreResult α :=
  let key (c : Config I) : Config I := if o.symmetric then c.canonical else c
  -- Breadth first, so that the recorded witness of a final state is a shortest
  -- run. The frontier is a queue kept as two lists: `front` is popped, `back`
  -- (newest first) is pushed, and reversed into `front` when `front` runs out.
  let rec go (visited : Std.HashSet (Config I)) (parent : Std.HashMap (Config I) (Config I × List TraceEv))
      (finals : Std.HashMap α (List TraceEv)) (cache : CertCache I) (front back : List (Config I))
      (acc : ExploreResult α) : ExploreResult α :=
    match front with
    | [] =>
      if back.isEmpty then { acc with finals := finals.toList.map (·.1), witnesses := finals.toList }
      else go visited parent finals cache back.reverse [] acc
    | c :: rest =>
      if visited.contains (key c) then go visited parent finals cache rest back acc else
      let visited := visited.insert (key c)
      let acc := { acc with configs := acc.configs + 1 }
      if c.final then
        let x := proj c
        let finals := if finals.contains x then finals else finals.insert x (pathTo parent c)
        go visited parent finals cache rest back acc
      else
      let (next, bound, faults, cache) := succsR A cache c o
      let parent := next.foldl (fun p (c', ev) => if visited.contains (key c') || p.contains c' then p else p.insert c' (c, ev)) parent
      go visited parent finals cache rest (next.foldl (fun b (c', _) => c' :: b) back)
        { acc with boundHit := acc.boundHit || bound, faults := acc.faults ++ faults }
  go {} {} {} {} [c0] [] {}
where
  /-- The trace from the initial configuration to `c`, through the parent links. -/
  pathTo (parent : Std.HashMap (Config I) (Config I × List TraceEv)) (c : Config I) : List TraceEv :=
    let rec walk (c : Config I) (acc : List TraceEv) (n : Nat) : List TraceEv :=
      match n, parent[c]? with
      | 0, _ | _, none => acc
      | n + 1, some (p, ev) => walk p (ev ++ acc) n
    walk c [] 100000

end Explore

/-! ## Certification with a different instruction semantics

The machine above certifies promises with the ISA's own `exec`, under which a
system call faults: no promise can be certified past one. The functions below
are copies of `stepOne`, `certify`, `certifiedPromises`, `succsL`, `succsR`
and `explore` that certify with another semantics `cexec` (an ISA's
`execCert`, which branches over the possible results of a system call) and
run the machine's own steps with `I.exec` as before, so that a thread still
faults when it reaches a system call; only what it may promise changes.
Certification is otherwise the same: a trace certifies once it has no
outstanding promise.

`cexec` must halt exactly where `I.exec` does (`Thread.halted` is computed
with `I.exec`). A `CertCache` filled in this mode must not be used by the
plain functions, nor the converse. No theorem is stated about this mode. -/

section CertWith

variable (A : Arch) {I : ISA} (cexec : I.State → Option (EvTree I.State))

/-- `stepOne` with `cexec` in place of `I.exec`. -/
def stepOneWith (t : Thread I) (tid : Nat) (mem : Memory) : Option (List (Except String (Outcome I))) := do
  let tree ← cexec t.st
  let d := I.deps t.st
  let iv := instrViews t d
  let ctx : Ctx := { views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] }
  return (runTree A tid iv ctx tree).flatMap fun
    | .error m => [.error m]
    | .ok (st, c') => (finishInstr t d iv st c').map fun th =>
        .ok { thread := th, mem := c'.mem, promisedNow := c'.promisedNow, log := c'.log }

/-- `certify`, running the thread with `stepOneWith cexec`. -/
def certifyWith (cache : CertCache I) (t : Thread I) (tid : Nat) (mem : Memory) (fuel : Nat) :
    CertResult I × CertCache I :=
  match cache[(t, tid, mem)]? with
  | some r => (r, cache)
  | none =>
    let r := (go tid fuel ({}, {}) (t, mem, [], false)).2
    (r, cache.insert (t, tid, mem) r)
where
  go (tid : Nat) : Nat → Std.HashSet (Thread I × Memory) × CertResult I →
      Thread I × Memory × List (Msg × View) × Bool → Std.HashSet (Thread I × Memory) × CertResult I
    | n, (visited, acc), (t, mem, ws, done) =>
      if visited.contains (t, mem) then (visited, acc) else
      let visited := visited.insert (t, mem)
      -- a promise that can no longer be fulfilled: dead branch
      if t.hasDeadPromise mem then (visited, acc) else
      let (acc, done) :=
        if !done && t.prom.isEmpty then ({ acc with certified := true, writes := acc.writes ++ ws }, true)
        else (acc, done)
      if t.halted then (visited, acc)
      else
        match n with
        | 0 => (visited, { acc with boundHit := true })
        | n + 1 =>
          match stepOneWith A cexec t tid mem with
          | none => (visited, acc)
          | some outs =>
            let (next, acc) := outs.foldl (init := ([], acc)) fun (next, acc) o =>
              match o with
              | .error m => (next, { acc with faults := acc.faults ++ [m] })
              | .ok o =>
                if done then ((o.thread, o.mem, [], true) :: next, { acc with writes := acc.writes ++ o.promisedNow })
                else ((o.thread, o.mem, ws ++ o.promisedNow, false) :: next, acc)
            next.foldl (go tid n) (visited, acc)

/-- `certifiedPromises` with `certifyWith cexec`. -/
def certifiedPromisesWith (cache : CertCache I) (c : Config I) (tid : Nat) (fuel : Nat) :
    List (Config I × TraceEv) × CertResult I × CertCache I :=
  match c.threads[tid]? with
  | none => ([], {}, cache)
  | some t =>
    let (r, cache) := certifyWith A cexec cache t tid c.mem fuel
    let ws := (r.writes.filter fun (_, ν) => ν ≤ c.mem.last).map (·.1) |>.eraseDups
    let cs := ws.map fun w =>
      let (mem', tnew) := c.mem.append { w with tid }
      (c.withThread tid { t with prom := t.prom ++ [tnew] } mem', TraceEv.promise tid w.loc w.val tnew)
    (cs, r, cache)

/-- `succsL` with certification by `certifyWith cexec`; the instruction steps
are `stepThread`'s, with `I.exec`. -/
def succsLWith (cache : CertCache I) (c : Config I) (fuel : Nat) (maxPromises : Option Nat := none) :
    List (Config I × List TraceEv) × Bool × List String × CertCache I :=
  (List.range c.threads.size).foldl (init := ([], false, [], cache)) fun (next, bound, faults, cache) tid =>
    let (next, bound, faults, cache) : List (Config I × List TraceEv) × Bool × List String × CertCache I :=
      match stepThread A c tid with
      | none => (next, bound, faults, cache)
      | some outs => outs.foldl (init := (next, bound, faults, cache)) fun (next, bound, faults, cache) (o : Except String (Outcome I)) =>
        match o with
        | .error m => (next, bound, faults ++ [m], cache)
        | .ok o =>
          let c' := c.withThread tid o.thread o.mem
          if o.thread.prom.isEmpty then ((c', o.log) :: next, bound, faults, cache)
          else
            let (r, cache) := certifyWith A cexec cache o.thread tid o.mem fuel
            if r.certified then ((c', o.log) :: next, bound || r.boundHit, faults, cache)
            else (next, bound || r.boundHit, faults, cache)
    let (ps, r, cache) := certifiedPromisesWith A cexec cache c tid fuel
    let ps := match maxPromises, c.threads[tid]? with
      | some k, some t => if t.prom.length < k then ps else []
      | _, _ => ps
    (next.reverse ++ (ps.map fun (c', e) => (c', [e])), bound || r.boundHit, faults ++ r.faults, cache)

/-- `succsR` with `succsLWith cexec`. -/
def succsRWith (cache : CertCache I) (c : Config I) (o : ExploreOpts) :
    List (Config I × List TraceEv) × Bool × List String × CertCache I :=
  match localStep A c with
  | some next => (next, false, [], cache)
  | none =>
    let (next, bound, faults, cache) := succsLWith A cexec cache c o.fuel o.maxPromises
    let (next, faults) := next.foldr (init := ([], faults)) fun (c', ev) (next, faults) =>
      match overlapFault c'.mem ev with
      | some m => (next, m :: faults)
      | none => ((c', ev) :: next, faults)
    (next, bound, faults, cache)

/-- `explore` with `succsRWith cexec`. -/
partial def exploreWith {α : Type} [BEq α] [Hashable α] (c0 : Config I) (proj : Config I → α)
    (o : ExploreOpts := {}) : ExploreResult α :=
  let key (c : Config I) : Config I := if o.symmetric then c.canonical else c
  let rec go (visited : Std.HashSet (Config I)) (parent : Std.HashMap (Config I) (Config I × List TraceEv))
      (finals : Std.HashMap α (List TraceEv)) (cache : CertCache I) (front back : List (Config I))
      (acc : ExploreResult α) : ExploreResult α :=
    match front with
    | [] =>
      if back.isEmpty then { acc with finals := finals.toList.map (·.1), witnesses := finals.toList }
      else go visited parent finals cache back.reverse [] acc
    | c :: rest =>
      if visited.contains (key c) then go visited parent finals cache rest back acc else
      let visited := visited.insert (key c)
      let acc := { acc with configs := acc.configs + 1 }
      if c.final then
        let x := proj c
        let finals := if finals.contains x then finals else finals.insert x (explore.pathTo parent c)
        go visited parent finals cache rest back acc
      else
      let (next, bound, faults, cache) := succsRWith A cexec cache c o
      let parent := next.foldl (fun p (c', ev) => if visited.contains (key c') || p.contains c' then p else p.insert c' (c, ev)) parent
      go visited parent finals cache rest (next.foldl (fun b (c', _) => c' :: b) back)
        { acc with boundHit := acc.boundHit || bound, faults := acc.faults ++ faults }
  go {} {} {} {} [c0] [] {}

end CertWith

/-! ## Printing traces -/

/-- One line per event; `locName` names locations, `A` is the profile (so
that a plain access under TSO prints its effective kind). -/
def TraceEv.format (locName : Loc → String) : TraceEv → String
  | .instr tid text => s!"P{tid}: {text}"
  | .read l t v ν => s!"    read {locName l} = {v.toNat} @{t}  (post-view {ν})"
  | .write l t v fulfilled =>
    s!"    write {locName l} := {v.toNat} @{t}{if fulfilled then "  (fulfils promise)" else ""}"
  | .xclFail l => s!"    store-exclusive to {locName l} fails"
  | .fence k => s!"    fence {match k with | .sy => "sy" | .ld => "ld" | .st => "st" | .stAll => "st (dsb)" | .isb => "isb"}"
  | .promise tid l v t => s!"P{tid} promises {locName l} := {v.toNat} @{t}"

def formatTrace (locName : Loc → String) (tr : List TraceEv) : String :=
  "\n".intercalate (tr.map (TraceEv.format locName))

end Kraken.Promising
