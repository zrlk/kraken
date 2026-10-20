/-
Explorer checks for `Kraken.Promising.PromiseSafe` on the Toy ISA. Every
candidate rule of the n-thread logic must
hold in **every** `Reachable` configuration, promises included, of racy
programs too: each check below enumerates all of them (`reachAll ... false`,
no partial-order reduction), not only final ones and not only promise-free
ones.
-/
import Kraken.Promising.PromiseSafe
import Kraken.Promising.PFCompleteDRFTests

namespace Kraken.Promising.Toy

open Instr

/-! ## Checks at one configuration -/

/-- The Toy location index of a location (`4` if none). -/
def locIdx (l : Loc) : Nat := ((List.range 4).find? fun n => loc n == l).getD 4

/-- The successful outcomes of thread `tid`'s next instruction. -/
def outcomes (A : Arch) (c : Config isa) (tid : Nat) : List (Outcome isa) :=
  match stepThread A c tid with
  | none => []
  | some outs => outs.filterMap fun | .ok o => some o | .error _ => none

/-- **Reads-from-Write**: every value any thread can read is the initial
value or the value of a message to that location. -/
def readsFromWriteAt (A : Arch) (c : Config isa) : Bool :=
  (List.range c.threads.size).all fun tid => (outcomes A c tid).all fun o => o.log.all fun
    | .read l _ v _ => v == c.mem.initVal l || c.mem.msgs.any fun w => w.loc == l && w.val == v
    | _ => true

/-- The timestamp of thread `tid`'s last *performed* write to `l` (a message
of `tid` to `l` that is not an outstanding promise of `tid`), else `0`. -/
def lastOwnWrite (c : Config isa) (tid : Nat) (l : Loc) : Time :=
  let prom := (c.threads[tid]?.map (·.prom)).getD []
  (List.range (c.mem.last + 1)).foldl (init := 0) fun acc i =>
    match c.mem.get? i with
    | some w => if w.loc == l && w.tid == tid && !prom.contains i then i else acc
    | none => acc

/-- **Exclusive writer** (SLR's `r-rlx*`, its Lemma 1): if `tid` is the only
writer of location `n`, every read of `n` by `tid` reads its own last
performed write, whatever its outstanding promises. -/
def exclusiveReadAt (A : Arch) (n tid : Nat) (c : Config isa) : Bool :=
  (outcomes A c tid).all fun o => o.log.all fun
    | .read l ts _ _ => l != loc n || ts == lastOwnWrite c tid l
    | _ => true

/-- `MemInv G` of `PromiseSafe` on the four Toy locations (initial values and
every message, outstanding promises included). -/
def memInvAt (G : Nat → Nat → Bool) (c : Config isa) : Bool :=
  (List.range 4).all (fun n => G n (c.mem.initVal (loc n)).toNat) &&
    c.mem.msgs.all fun w => G (locIdx w.loc) w.val.toNat

/-- The write obligation `WritesPreserve` at one configuration, on
promise-free runs of each thread alone up to `depth` instructions: every
"promise now" write of every step satisfies `G` (from memories satisfying
`MemInv G`). -/
partial def obligationAt (A : Arch) (G : Nat → Nat → Bool) (depth : Nat) (c : Config isa) : Bool :=
  (List.range c.threads.size).all fun tid =>
    match c.threads[tid]? with
    | none => true
    | some t =>
      let rec go (t : Thread isa) (mem : Memory) (d : Nat) : Bool :=
        if d == 0 || !memInvAt G { c with mem } then true else
        match stepOne A t tid mem with
        | none => true
        | some outs => outs.all fun
          | .error _ => true
          | .ok o => o.promisedNow.all (fun (w, _) => G (locIdx w.loc) w.val.toNat) && go o.thread o.mem (d - 1)
      go t c.mem depth

/-- `(#configurations, #with an outstanding promise, Reads-from-Write in all,
exclusive-writer rule in all (for each `(n, tid)` given), MemInv G in all,
the write obligation in all)`. -/
def sp3Check (A : Arch) (progs : List (List Instr)) (excl : List (Nat × Nat)) (G : Nat → Nat → Bool)
    (depth : Nat := 4) : Nat × Nat × Bool × Bool × Bool × Bool :=
  let all := reachAll A (initOf progs) false
  (all.size, (all.filter (!promFreeB ·)).size, all.all (readsFromWriteAt A),
   excl.all (fun (n, tid) => all.all (exclusiveReadAt A n tid)), all.all (memInvAt G),
   all.all (obligationAt A G depth))

/-! ## Programs (locations `x = 0`, `y = 1`, unless noted) -/

/-- LB with plain stores of constants (`r0 := x; y := 1 ∥ r0 := y; x := 1`). -/
def lbConst : List (List Instr) := LB [] []

/-- LB+data+fakedep: `r0 := x; y := r0 ∥ r0 := y; x := r0 + 1 - r0`
(the second store's value does not depend on the read). -/
def lbDataFake : List (List Instr) :=
  [[ld .plain false 0 0, st .plain false 1 (.r 0)],
   [ld .plain false 0 1, add 1 (.r 0) (.i 1), st .plain false 0 (.r 1)]]

/-- LB+data+fakedep with Toy's arithmetic (no subtraction): the second thread
writes `1` through a register that is `1` whatever it read. -/
def lbDataFake' : List (List Instr) :=
  [[ld .plain false 0 0, st .plain false 1 (.r 0)],
   [ld .plain false 0 1, mov 1 (.i 1), st .plain false 0 (.r 1)]]

/-- RNG (SLR's introduction): `r0 := x; y := r0 + 1 ∥ r0 := y; x := r0`. -/
def rng : List (List Instr) :=
  [[ld .plain false 0 0, add 1 (.r 0) (.i 1), st .plain false 1 (.r 1)],
   [ld .plain false 0 1, st .plain false 0 (.r 0)]]

/-- CoRR2: two writers of `x`, two readers reading it twice. -/
def corr2 : List (List Instr) :=
  [[st .plain false 0 (.i 1)], [st .plain false 0 (.i 2)],
   [ld .plain false 0 0, ld .plain false 1 0], [ld .plain false 0 0, ld .plain false 1 0]]

/-- An exclusive writer of `x` reading it back, against a racy reader:
`x := 1; x := 2; r0 := x ∥ r0 := x`. -/
def exclRead : List (List Instr) :=
  [[st .plain false 0 (.i 1), st .plain false 0 (.i 2), ld .plain false 0 0], [ld .plain false 0 0]]

/-- MP with plain data (`x`) and a release flag (`y`): `x := 1; y :=rel 1 ∥
r0 :=acq y; r1 := x`. `rel := false`: the flag store is plain (racy). -/
def mpRel (rel : Bool) : List (List Instr) :=
  [[st .plain false 0 (.i 1), st (if rel then .rel else .plain) false 1 (.i 1)],
   [ld .acq false 0 1, ld .plain false 1 0]]

/-! ## Results: the cheap rules hold everywhere, promises included -/

-- Write invariants: "every value is 0 or 1", and for RNG the invariant
-- SLR shows a value logic cannot establish thread-modularly ("x ≤ 1, y ≤ 1");
-- with the obligation quantified over reachable configurations it is
-- dischargeable here, and every message (promises included) satisfies it.
def le1 (_ : Nat) (v : Nat) : Bool := v ≤ 1
def le2 (_ : Nat) (v : Nat) : Bool := v ≤ 2

/-- info: (72, 54, true, true, true, true) -/
#guard_msgs in #eval sp3Check .armv8 lbConst [] le1
/-- info: (96, 76, true, true, true, true) -/
#guard_msgs in #eval sp3Check .armv8 lbDataFake' [] le1
-- RNG: "x ≤ 1, y ≤ 1" holds of every message of every reachable
-- configuration, but it is not a write invariant: run alone from a reachable
-- configuration (a promise of `y = 1` outstanding, `x = 1` in memory), the
-- first thread reads `x = 1` and writes `y = 2`, on a run that will never
-- fulfil its promise. As SLR says, a value logic cannot bound RNG; it needs
-- the end-of-run confrontation of `O` and `W¹`. "x ≤ 1, y ≤ 2" is one.
/-- info: (78, 60, true, true, true, false) -/
#guard_msgs in #eval sp3Check .armv8 rng [] le1
/-- info: (78, 60, true, true, true, true) -/
#guard_msgs in #eval sp3Check .armv8 rng [] (fun n v => v ≤ if n == 0 then 1 else 2)
/-- info: (24, 11, true, true, true, true) -/
#guard_msgs in #eval sp3Check .armv8 exclRead [(0, 0)] le2
/-- info: (29, 16, true, true, true, true) -/
#guard_msgs in #eval sp3Check .armv8 (mpRel true) [(0, 0)] le1
/-- info: (55, 35, true, true, true, true) -/
#guard_msgs in #eval sp3Check .armv8 (mpRel false) [(0, 0)] le1

-- `G` that is not invariant: the explorer finds both the message and the
-- failing obligation (LB with constant 1 stores, `G` = "only 0").
/-- info: (72, 54, true, true, false, false) -/
#guard_msgs in #eval sp3Check .armv8 lbConst [] (fun _ v => v == 0)

/-! ## Ownership transfer for MP

Candidate rule (SLR's `r-acq` with `W¹(x)` in the flag's predicate): once the
reader's acquire read returns `y = 1`, every message of `x` it can read has
value `1`, in every reachable configuration, promises included. It must hold
with the release flag and fail with the plain (racy) one. -/

def mpTransferAt (A : Arch) (c : Config isa) : Bool :=
  match c.threads[1]? with
  | some t =>
    if t.st.pc == 1 && t.st.regs[0]! == 1 then
      (outcomes A c 1).all fun o => o.log.all fun
        | .read _ _ v _ => v == 1
        | _ => true
    else true
  | none => true

/-- info: (true, false) -/
#guard_msgs in #eval ((reachAll .armv8 (initOf (mpRel true)) false).all (mpTransferAt .armv8),
  (reachAll .armv8 (initOf (mpRel false)) false).all (mpTransferAt .armv8))

/-! ## Promised release stores ("prepaid release")

Kraken promises release stores (PS 1.0 does not; SLR's proof uses that). In
the `LDAXR/STXR` spinlock (`spin`: lock `0`, counter `1`; the critical
section's store is instruction 6, the `STLR` release instruction 7), an
outstanding promise of the release by a thread that has not yet performed its
critical-section store always comes with an outstanding promise of that store:
the release's pre-view covers the store's timestamp. So everything the
release will transfer is already in memory when the release is promised: the
law `promisedRelease` needs. `(#configurations with
a promised release before the critical-section store, #those whose thread
has no outstanding promise to the counter)`. -/

def prepaidRelease (A : Arch) (progs : List (List Instr)) (lockLoc dataLoc storePc : Nat) : Nat × Nat :=
  let all := reachAll A (initOf progs) false
  let hits := all.toList.flatMap fun c => c.threads.toList.filter fun t =>
    t.st.pc ≤ storePc && t.prom.any fun ts =>
      match c.mem.get? ts with
      | some w => w.loc == loc lockLoc && w.val == 0
      | none => false
  let bad := all.toList.flatMap fun c => c.threads.toList.filter fun t =>
    t.st.pc ≤ storePc &&
    (t.prom.any fun ts => match c.mem.get? ts with
      | some w => w.loc == loc lockLoc && w.val == 0
      | none => false) &&
    !(t.prom.any fun ts => match c.mem.get? ts with
      | some w => w.loc == loc dataLoc
      | none => false)
  (hits.length, bad.length)

/-- info: (11548, 0) -/
#guard_msgs in #eval prepaidRelease .armv8 [spin, spin] 0 1 6
/-- info: (466, 0) -/
#guard_msgs in #eval prepaidRelease .armv8 [spinAcqRel, spinAcqRel] 0 1 4

/-! ## The side condition of `ResModel.PromisedRelease`

Design (V) accounts a promised release in a *virtual* configuration where
the promising thread has run ahead, along a memory-silent promise-free run
of its own, to the release's fulfilment (`Config.VirtualOf`). That needs two
machine facts, checked here on every reachable configuration:

- (S1) every outstanding release promise has such a run
  (`Config.AdvanceableStrict`: it holds here because every Toy store
  instruction performs one store; in general only (S1′), a run up to the
  fulfilling instruction, holds: `Config.Advanceable`, `ReleasePrefixTests`);
- (S2) every reachable instruction step of a thread that leaves one of its
  release promises outstanding appends no message and reads no message above
  it, so the thread's real steps up to the fulfilment are stutter steps of
  the virtual configuration.

Neither is a hypothesis about programs: both follow from the release
pre-view (`writeSuccs`: `vrOld ⊔ vrOldNR ⊔ vwOld`), without certification
(proved in `Kraken/Promising/ReleasePrefix.lean`). The plain-store variants (`spinAcqRelRelaxed`,
`spinRelaxed`) are the negative control: their `lock := 0` is not a release,
so (V) does not apply, and (S1) and (S2) indeed fail. `(#configurations with an outstanding release
promise, #reachable steps checked for (S2), #violating (S2), #violating (S2)
among the uncertified outcomes, #(configuration, thread) pairs violating
(S1))`. -/

/-- Outstanding promises of thread `i` of `lock := 0` (the release store). -/
def relOut (lockLoc : Nat) (c : Config isa) (i : Nat) : List Time :=
  ((c.threads[i]?.map (·.prom)).getD []).filter fun ts => match c.mem.get? ts with
    | some w => w.loc == loc lockLoc && w.val == 0
    | none => false

/-- (S2) for one step of thread `i` to `(prom', mem')` with trace `log`. -/
def relPrefixViolates (lockLoc : Nat) (c : Config isa) (i : Nat) (prom' : List Time) (mem' : Memory)
    (log : List TraceEv) : Bool :=
  (relOut lockLoc c i).any fun p => prom'.contains p &&
    (mem'.last > c.mem.last || log.any fun | .read _ t _ _ => t > p | _ => false)

/-- (S1): a memory-silent promise-free run of thread `i` alone, of at most `d`
instructions, after which no promise in `targets` is outstanding. -/
partial def silentAdvance (A : Arch) (i : Nat) (mem : Memory) (targets : List Time) (t : Thread isa)
    (d : Nat) : Bool :=
  targets.all (fun p => !t.prom.contains p) ||
  (d != 0 && match stepOne A t i mem with
    | none => false
    | some outs => outs.any fun
      | .ok o => o.mem.last == mem.last && silentAdvance A i mem targets o.thread (d - 1)
      | .error _ => false)

partial def releasePrefixCheck (A : Arch) (progs : List (List Instr)) (lockLoc : Nat) : Nat × Nat × Nat × Nat × Nat :=
  let rec go (vis : Std.HashSet (Config isa)) (cache : CertCache isa) (acc : Nat × Nat × Nat × Nat × Nat)
      (front : List (Config isa)) : Nat × Nat × Nat × Nat × Nat :=
    match front with
    | [] => acc
    | c :: rest =>
      if vis.contains c then go vis cache acc rest else
      let (next, _, _, cache) := succsL A cache c 64 none
      let n := c.threads.size
      let ahead := (List.range n).filter fun i => !(relOut lockLoc c i).isEmpty
      let (hits, checked, bad, raw, noAdv) := acc
      let hits := if ahead.isEmpty then hits else hits + 1
      let (raw, noAdv) := ahead.foldl (init := (raw, noAdv)) fun (raw, noAdv) i =>
        let outs := (outcomes A c i).filter fun o => relPrefixViolates lockLoc c i o.thread.prom o.mem o.log
        let adv := match c.threads[i]? with
          | some t => silentAdvance A i c.mem (relOut lockLoc c i) t 12
          | none => true
        (raw + outs.length, if adv then noAdv else noAdv + 1)
      let (checked, bad) := next.foldl (init := (checked, bad)) fun (checked, bad) (c', log) =>
        match log with
        | [.promise ..] => (checked, bad)
        | _ =>
          match (List.range n).find? (fun i => !(c'.threads[i]? == c.threads[i]?)) with
          | none => (checked, bad)
          | some j =>
            if (relOut lockLoc c j).isEmpty then (checked, bad) else
            (checked + 1, if relPrefixViolates lockLoc c j ((c'.threads[j]?.map (·.prom)).getD []) c'.mem log
              then bad + 1 else bad)
      go (vis.insert c) cache (hits, checked, bad, raw, noAdv) (next.map (·.1) ++ rest)
  go {} {} (0, 0, 0, 0, 0) [initOf progs]

/-- info: (9864, 14896, 0, 4608, 0) -/
#guard_msgs in #eval releasePrefixCheck .armv8 [spin, spin] 0
/-- info: (428, 576, 0, 324, 0) -/
#guard_msgs in #eval releasePrefixCheck .armv8 [spinAcqRel, spinAcqRel] 0
-- Negative control: the unlock is a plain store, not a release; (S1) and
-- (S2) fail, so (V) does not apply and the lock's predicate must be pure at
-- the plain store's value (a weaker specification, no transfer). The same
-- holds for `spinRelaxed`: (50342, 92260, 1960, 27612, 10078), not run here
-- (2 min).
/-- info: (4824, 8322, 444, 4520, 1318) -/
#guard_msgs in #eval releasePrefixCheck .armv8 [spinAcqRelRelaxed, spinAcqRelRelaxed] 0

/-! ## The `DSB ST` leak: a racy read must be allowed to be stale

`T0: LDR z; STR d; DSB ST; LDR y ∥ T1: STLR y; STLR z` (`d = 0`, `z = 1`,
`y = 2`): `z = 1, y = 0` is reachable (only with promises), so no rule may
conclude from `DSB ST` that a later read of `y` sees `T1`'s write once `z`'s
has been seen; SLR's `r-rlx` (`O(y, _, t)`, any message at or after the
reader's own observation) is the right strength. `(#final configurations with
r0 = 1, r1 = 0, with promises; without)`. -/

def dsbLeakProg : List (List Instr) :=
  [[ld .plain false 0 1, st .plain false 0 (.i 1), fence .stAll, ld .plain false 1 2],
   [st .rel false 2 (.i 1), st .rel false 1 (.i 1)]]

def staleFinals (A : Arch) (progs : List (List Instr)) (pf : Bool) : Nat :=
  ((reachAll A (initOf progs) pf).filter fun c =>
    c.final && match c.threads[0]? with
      | some t => t.st.regs[0]! == 1 && t.st.regs[1]! == 0
      | none => false).size

/-- info: (1, 0) -/
#guard_msgs in #eval (staleFinals .armv8 dsbLeakProg false, staleFinals .armv8 dsbLeakProg true)

end Kraken.Promising.Toy
