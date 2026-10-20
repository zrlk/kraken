/-
Explorer experiments for `Kraken.Promising.PFCompleteDRF` on the Toy ISA
(second prototype): the hypotheses of
`pf_complete_drf_steps` (`RunOrderedOff`, `DataRaceFreeSteps`) and its
conclusion (every promise-free configuration reachable with promises is `≈`
to one reachable without), checked by enumerating every reachable
configuration of both machines, not only the final ones.
-/
import Kraken.Promising.PFCompleteDRF
import Kraken.Promising.PFCompleteTests

namespace Kraken.Promising.Toy

open Instr

/-! ## Enumeration and checks -/

/-- Every configuration reachable from `c0` (no partial-order reduction, so
that intermediate configurations are compared exactly); `pf`: the
promise-free machine (`maxPromises := some 0`). -/
partial def reachAll (A : Arch) (c0 : Config isa) (pf : Bool) : Array (Config isa) :=
  let rec go (vis : Std.HashSet (Config isa)) (cache : CertCache isa) (acc : Array (Config isa))
      (front : List (Config isa)) : Array (Config isa) :=
    match front with
    | [] => acc
    | c :: rest =>
      if vis.contains c then go vis cache acc rest else
      let (next, _, _, cache) := succsL A cache c 64 (if pf then some 0 else none)
      go (vis.insert c) cache (acc.push c) (next.map (·.1) ++ rest)
  go {} {} #[] [c0]

def initOf (progs : List (List Instr)) : Config isa :=
  Config.init (progs.map fun p => ({ prog := p.toArray } : State)) []

def isData (data : List Nat) (l : Loc) : Bool := data.any fun n => loc n == l

/-- `DataRaceFreeSteps` at one configuration. -/
def drfStepsAt (A : Arch) (data : List Nat) (c : Config isa) : Bool :=
  c.threads.toList.zipIdx.all fun (t, tid) =>
    match stepThread A c tid with
    | none => true
    | some outs => outs.all fun
      | .error _ => true
      | .ok o => o.log.all fun
        | .read l ts _ _ => !isData data l || ts == c.mem.lastWrite l
        | .write l _ _ _ => !isData data l || decide (c.mem.lastWrite l ≤ max (t.views.getCoh l) t.views.vrNew)
        | _ => true

/-- `RunOrderedOff` at one configuration. -/
def orderedOffAt (A : Arch) (data : List Nat) (c : Config isa) : Bool :=
  c.threads.toList.zipIdx.all fun (t, tid) =>
    match stepThread A c tid with
    | none => true
    | some outs => outs.all fun
      | .error _ => true
      | .ok o => o.log.all fun
        | .write l ts _ _ => isData data l || decide (t.frontier < ts)
        | _ => true

/-- The promise-free reading of `RunOrderedOff` (rejected): every write to a
non-data location by a promise-free run has its constraining view `≥` the
frontier. -/
def orderedOffPFAt (A : Arch) (data : List Nat) (c : Config isa) : Bool :=
  c.threads.toList.zipIdx.all fun (t, tid) =>
    match stepThread A c tid with
    | none => true
    | some outs => outs.all fun
      | .error _ => true
      | .ok o => o.promisedNow.all fun (m, ν) => isData data m.loc || decide (t.frontier ≤ ν)

/-- The `≈` key: thread states (pc and registers) and per-location histories. -/
def equivKeyC (c : Config isa) : List (Nat × List Nat) × List (List Msg) :=
  (c.threads.toList.map fun t => (t.st.pc, t.st.regs.toList.map (·.toNat)),
   (List.range 4).map fun n => c.mem.msgs.toList.filter (·.loc == loc n))

def promFreeB (c : Config isa) : Bool := c.threads.all (·.prom.isEmpty)

/-- `(RunOrderedOff, DataRaceFreeSteps, #promise-free configurations reachable
with promises that have no ≈ promise-free counterpart, #final ones among them)`. -/
def drfCheck (A : Arch) (progs : List (List Instr)) (data : List Nat) : Bool × Bool × Nat × Nat :=
  let c0 := initOf progs
  let all := reachAll A c0 false
  let pf := reachAll A c0 true
  let keys : Std.HashSet _ := pf.foldl (fun s c => s.insert (equivKeyC c)) {}
  let bad := all.filter fun c => promFreeB c && !keys.contains (equivKeyC c)
  (all.all (orderedOffAt A data), pf.all (drfStepsAt A data), bad.size, (bad.filter (·.final)).size)

/-! ## Programs -/

/-- The `LDAXR/STXR` spinlock with an acquire-only `CASA` acquisition (the
`SWPA`/`LDADDA` shape: an acquire RMW, no release on its write). -/
def spinCas : List Instr :=
  [rmw .acq 0 0 (.i 1) (cmp := some (.i 0)), beq 0 1 0,
   ld .plain false 2 1, add 2 (.r 2) (.i 1), st .plain false 1 (.r 2), st .rel false 0 (.i 0)]

/-- The ticket shape with an unconditional back edge (`r3` is always 0):
thread `my` waits for `owner = my`. -/
def ticketFix (my : Nat) : List Instr := (ticket my .acq .acq).set 3 (beq 3 0 1)

/-- A write-only critical section (`data := v` without reading it first). -/
def spinWO (v : Nat) : List Instr :=
  [ld .acq true 0 0, beq 0 1 0, st .plain true 0 (.i 1) (status := some 1), beq 1 1 0,
   st .plain false 1 (.i v), st .rel false 0 (.i 0)]

/-- Write-after-read through a flag (`d` = 0, `s` = 2): `A` reads `d`, then
releases `s`; `B` reads `s` and writes `d`. -/
def war (bRead : Instr) (guard : List Instr) (aStore : StoreKind := .rel) : List (List Instr) :=
  [[ld .plain false 0 0, st aStore false 2 (.i 1)], [bRead] ++ guard ++ [st .plain false 0 (.i 1)]]

/-- Message passing through a flag with an early-promised data store, and a
third thread's synchronisation write the reader may see stale. -/
def viewGap : List (List Instr) :=
  [[st .plain false 0 (.i 1), st .rel false 2 (.i 1)],
   [st .rel false 3 (.i 1)],
   [ld .acq false 0 2, beq 0 0 99, ld .plain false 1 0, ld .plain false 2 3]]

/-- 2+2W on two data locations: no reads at all. -/
def twoPlusTwoW : List (List Instr) :=
  [[st .plain false 0 (.i 1), st .plain false 1 (.i 1)], [st .plain false 1 (.i 2), st .plain false 0 (.i 2)]]

/-! ## Results

Hypotheses hold ⇒ conclusion holds (no counterexample); each hypothesis is
needed (a racy or unordered variant breaks the conclusion). -/

-- Lock shapes as written: acquire-only acquisitions, plain critical sections.
/-- info: (true, true, 0, 0) -/
#guard_msgs in #eval drfCheck .armv8 [spinCas, spinCas] [1]
/-- info: (true, true, 0, 0) -/
#guard_msgs in #eval drfCheck .armv8 [ticketFix 0, ticketFix 1] [2]
/-- info: (true, true, 0, 0) -/
#guard_msgs in #eval drfCheck .armv8 [spinWO 1, spinWO 2] [1]
-- Write-after-read synchronised by an acquire, or only by a control
-- dependency (racy in the happens-before sense, race-free in the
-- configuration sense, and `≈`): the hypothesis need not be happens-before DRF.
/-- info: (true, true, 0, 0) -/
#guard_msgs in #eval drfCheck .armv8 (war (ld .acq false 1 2) [beq 1 0 99]) [0]
/-- info: (true, true, 0, 0) -/
#guard_msgs in #eval drfCheck .armv8 (war (ld .plain false 1 2) [beq 1 0 99]) [0]
/-- info: (true, true, 0, 0) -/
#guard_msgs in #eval drfCheck .armv8 viewGap [0]
-- Racy: the write-after-read with no guard is load buffering.
/-- info: (true, false, 1, 1) -/
#guard_msgs in #eval drfCheck .armv8 (war (ld .plain false 1 2) []) [0]
-- Unordered: the flag written by a plain store.
/-- info: (false, true, 1, 1) -/
#guard_msgs in #eval drfCheck .armv8 (war (ld .acq false 1 2) [beq 1 0 99] .plain) [0]
-- `RunOrderedOff` cannot be weakened to promise-free runs: there the flag
-- store is always ordered (the read of `d` only ever sees the initial write),
-- yet with promises it is not, and `≈` fails.
/-- info: true -/
#guard_msgs in #eval (reachAll .armv8 (initOf (war (ld .acq false 1 2) [beq 1 0 99] .plain)) true).all
  (orderedOffPFAt .armv8 [0])
-- The write clause is needed: 2+2W has no reads.
/-- info: (true, false, 6, 6) -/
#guard_msgs in #eval drfCheck .armv8 twoPlusTwoW [0, 1]
/-- info: (true, false, 1, 1) -/
#guard_msgs in #eval drfCheck .armv8 mpRacy [0, 1]

/-! ## Mutual exclusion is a property of promise-free configurations

With promises, both threads can be inside the critical section (the holder's
release `STLR` is promised, and the next acquirer reads it, before the holder
executes it), even with an acquire-release acquisition and under TSO; no such
configuration is promise-free. `(#configurations with both threads in the
critical section, #promise-free ones)`. -/

def bothIn (A : Arch) (progs : List (List Instr)) (lo hi : Nat) : Nat × Nat :=
  let cs := (reachAll A (initOf progs) false).filter fun c =>
    c.threads.all fun t => lo ≤ t.st.pc && t.st.pc ≤ hi
  (cs.size, (cs.filter promFreeB).size)

/-- info: (88, 0) -/
#guard_msgs in #eval bothIn .armv8 [spinAcqRel, spinAcqRel] 2 5
/-- info: (88, 0) -/
#guard_msgs in #eval bothIn .tso [spin, spin] 4 7

end Kraken.Promising.Toy
