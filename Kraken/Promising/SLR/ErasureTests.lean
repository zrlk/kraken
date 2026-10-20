/-
Explorer sanity checks for the SLR-adapted erasure (`Kraken.Promising.SLR.Erase`) on the Toy ISA.

For a program and a hand-written proof outline (which thread holds which
resource, which slots hang off which release message, as a function of the
thread states), the checks below evaluate a Boolean *shadow* of every clause
of `Erase` at **every** reachable configuration, promises included
(`reachAll ... false`):

- at the real configuration `c`, with the promises that the virtual advance
  fulfils marked pending (design (V) variant (ii), `Erase.ofVirtualOf`);
- at the virtual configuration `v` itself (`Config.VirtualOf`: every thread
  with an outstanding release promise has run ahead, memory-silently and
  without promising, until none of its release promises is outstanding), with
  nothing pending (`Erase.virtualOf`). This runs through the fulfilling
  instruction (`Config.AdvanceableStrict`, true on Toy); `Config.VirtualOf`
  stops just before it with the release pending, and erasure there is,
  by `Erase.unfulfil`/`Erase.fulfil`, the first check;
- at `c` with nothing pending: this must fail when a release is promised, or
  the pending-release clause would be unnecessary.

## The shadow

Resources are finite: write-permission fractions in sixths per Toy location
and a list of held acquire ids. Write sets are not represented: when a
location is tracked, erasure fixes the total write set to `Fulf`, which
contains the initial message, so the write-set clause amounts to "a tracked
location has a positive total fraction"; a predicate that inspects a write
set does so only for a full permission, whose holder's write set *is* the
total one (every other part has fraction `0`, hence an empty write set).
Predicates are Boolean functions of `Fulf`, the value and the resource; the
entailment `relAcq` is checked over a finite domain of resources and the
values `0..2`; `Pure` is evaluated at the configuration's own memory. So a
`true` here is evidence, not proof, that `Erase` is satisfiable with these
resources; a `false` pinpoints the clause that fails.

The RMW extension (`SLR/Rmw.lean`)
is shadowed too: update ids per location (`SSpec.upd`), release-mode initial
messages (`SSpec.initRel`), and claims, computed from memory: every settled
message the outline marks as an RMW write (`SSpec.rmwMsg`) claims the latest
message to its location below it (`claimsOf`; by `Memory.atomic` the
messages in between can only be the RMW thread's own, and the spinlocks below
have none). Update slots exist exactly on unclaimed release messages and are
acquirable by every thread. The spinlock section checks a CAS spinlock with
two acquirers of `lock = 0`, with negative controls and a racing plain-store
"unlock".
-/
import Kraken.Promising.SLR.Virtual
import Kraken.Promising.PromiseSafeTests

namespace Kraken.Promising.Toy

open Instr

/-! ## Shadow resources and predicates -/

/-- A shadow resource: write fractions in halves (index = Toy location) and
held acquire permissions `(location, id)`. -/
structure SRes where
  wr : List Nat := [0, 0, 0, 0]
  acq : List (Nat × Nat) := []
  deriving BEq, Repr, Inhabited

namespace SRes

def unit : SRes := {}

/-- The full fraction, in sixths (halves and thirds are representable). -/
def one : Nat := 6

def op (a b : SRes) : SRes :=
  { wr := (List.range 4).map fun x => a.wr.getD x 0 + b.wr.getD x 0, acq := a.acq ++ b.acq }

def q (r : SRes) (x : Nat) : Nat := r.wr.getD x 0

def acqCount (r : SRes) (x ι : Nat) : Nat := (r.acq.filter (· == (x, ι))).length

/-- Equality up to the order of acquire permissions. -/
def same (a b : SRes) : Bool :=
  a.wr == b.wr && a.acq.all (fun p => a.acqCount p.1 p.2 == b.acqCount p.1 p.2) &&
    b.acq.all (fun p => a.acqCount p.1 p.2 == b.acqCount p.1 p.2)

/-- The full write permission for `x`. -/
def full (x : Nat) : SRes := { wr := (List.range 4).map fun y => if y == x then one else 0 }

/-- A fraction `k / one` of the write permission for `x`. -/
def frac (x k : Nat) : SRes := { wr := (List.range 4).map fun y => if y == x then k else 0 }

end SRes

/-- `Fulf` of each location: `(value, timestamp)` pairs. -/
abbrev SFulf := Nat → List (Nat × Nat)

/-- A shadow predicate: of `Fulf`, the value and the resource. -/
abbrev SPred := SFulf → Nat → SRes → Bool

/-- `Pred.SepList` over a finite domain of resources. -/
def sepList (dom : List SRes) (f : SFulf) : List SPred → Nat → SRes → Bool
  | [], _, r => r.same SRes.unit
  | φ :: φs, v, r => dom.any fun r₁ => dom.any fun r₂ =>
      (r₁.op r₂).same r && φ f v r₁ && sepList dom f φs v r₂

/-- A slot: `(location, timestamp, id, resource)`. -/
abbrev SSlot := Nat × Nat × Nat × SRes

/-- A proof outline: the ghost state and thread resources at a configuration
(computed from the virtual configuration's thread states). -/
structure SSpec where
  rel : Nat → SPred
  acqTab : List SPred
  /-- Which messages are in release mode (`Ghost.relMsgs`). -/
  relMode : Msg → Bool
  /-- Thread resources and slots. -/
  assign : Config isa → List SRes × List SSlot
  /-- The domain of the `relAcq` entailment check. -/
  dom : List SRes
  /-- Initial messages in release mode (`(x, 0) ∈ Ghost.relMsgs`). -/
  initRel : Nat → Bool := fun _ => false
  /-- The update ids of each location (`Ghost.upd`). -/
  upd : Nat → List Nat := fun _ => []
  /-- The messages written by RMWs (each claims the message it read). -/
  rmwMsg : Msg → Bool := fun _ => false

/-! ## The clauses of `Erase` (with `T = ∅`) -/

def outstandingB (c : Config isa) (ts : Nat) : Bool := c.threads.any (·.prom.contains ts)

/-- The outstanding promises of thread `i`. -/
def promsOf (c : Config isa) (i : Nat) : List Time := (c.threads[i]?.map (·.prom)).getD []

def msgs (c : Config isa) : List (Nat × Msg) :=
  (List.range (c.mem.last + 1)).filterMap fun ts => (c.mem.get? ts).map (ts, ·)

def settledB (c : Config isa) (pend : List Nat) (ts : Nat) : Bool := !outstandingB c ts || pend.contains ts

def fulfOf (c : Config isa) (pend : List Nat) : SFulf := fun x =>
  ((c.mem.initVal (loc x)).toNat, 0) ::
    ((msgs c).filter (fun (ts, w) => ts != 0 && locIdx w.loc == x && settledB c pend ts)).map
      fun (ts, w) => (w.val.toNat, ts)

/-- `CanAcq` by saturation: the `(key, id)` of the slots reachable from `A`;
update slots (`upd`) are acquirable by everyone. -/
def canAcqB (slots : List SSlot) (A : List (Nat × Nat)) (upd : Nat → List Nat := fun _ => []) : List SSlot :=
  let step (acc : List SSlot) : List SSlot :=
    slots.filter fun s@(x, _, ι, _) =>
      acc.contains s || A.contains (x, ι) || (upd x).contains ι || acc.any fun (_, _, _, r) => r.acq.contains (x, ι)
  (List.range (slots.length + 1)).foldl (fun acc _ => step acc) []

def mayWriteB (slots : List SSlot) (r : SRes) (x : Nat) (upd : Nat → List Nat := fun _ => []) : Bool :=
  r.q x > 0 || (canAcqB slots r.acq upd).any fun (_, _, _, res) => res.q x > 0

/-- The claims (`Ghost.claims`): every settled RMW write claims the latest
message to its location below it (`0`: the initial message). -/
def claimsWith (rmwMsg : Msg → Bool) (c : Config isa) (pend : List Nat) : List ((Nat × Nat) × Nat) :=
  let ms := msgs c
  (ms.filter fun (ts, w) => ts != 0 && rmwMsg w && settledB c pend ts).map fun (ts, w) =>
    let tr := (ms.filter fun (ts', w') => ts' < ts && w'.loc == w.loc).foldl (fun a (ts', _) => max a ts') 0
    ((locIdx w.loc, tr), ts)

def claimsOf (S : SSpec) (c : Config isa) (pend : List Nat) : List ((Nat × Nat) × Nat) := claimsWith S.rmwMsg c pend

/-- The clauses of `Erase rF g ∅ c` that fail (empty: all hold). -/
def eraseFails (S : SSpec) (c : Config isa) (assignAt : Config isa) (pend : List Nat) : List String :=
  let (rF, slots) := S.assign assignAt
  let tot := (rF ++ slots.map (·.2.2.2)).foldl SRes.op SRes.unit
  let f := fulfOf c pend
  let ms := msgs c
  let initMsgs := (List.range 4).map fun x => (x, 0, (c.mem.initVal (loc x)).toNat)
  let relKeys := ((List.range 4).filter S.initRel).map (·, 0) ++
    (ms.filter fun (ts, w) => ts != 0 && S.relMode w).map fun (ts, w) => (locIdx w.loc, ts)
  let claims := claimsOf S c pend
  let claimed (k : Nat × Nat) : Bool := claims.any (·.1 == k)
  let valAt (x ts : Nat) : Option Nat :=
    if ts == 0 then some (c.mem.initVal (loc x)).toNat else (ms.find? (·.1 == ts)).map (·.2.val.toNat)
  let check (name : String) (b : Bool) : List String := if b then [] else [name]
  check "valid" ((List.range 4).all (tot.q · ≤ SRes.one) && tot.acq.all fun (x, ι) => tot.acqCount x ι ≤ 1) ++
  check "slotIds" (slots.all fun (_, _, ι, _) => ι < S.acqTab.length) ++
  check "acqIds" (tot.acq.all fun (_, ι) => ι < S.acqTab.length) ++
  check "relAcq" ((List.range 4).all fun x => (List.range 3).all fun v => S.dom.all fun r =>
    !S.rel x f v r ||
      sepList S.dom f (((tot.acq.filter (·.1 == x)).map (·.2) ++ S.upd x).map fun ι =>
        S.acqTab.getD ι fun _ _ _ => false) v r) ++
  check "writes" ((List.range 4).all fun x =>
    let tracked := tot.q x > 0 || ms.any fun (ts, w) => ts != 0 && locIdx w.loc == x && settledB c pend ts
    !tracked || tot.q x > 0) ++
  let nonInit : List (Nat × Nat × Nat) :=
    (ms.filter fun (p : Nat × Msg) => p.1 != 0).map fun (ts, w) => (locIdx w.loc, ts, w.val.toNat)
  check "pure" ((initMsgs ++ nonInit).all fun (x, ts, v) => relKeys.contains (x, ts) || S.rel x f v SRes.unit) ++
  check "slotsNodup" ((slots.map fun (x, ts, ι, _) => (x, ts, ι)).eraseDups.length == slots.length) ++
  check "slotsDom" ((slots.all fun (x, ts, ι, _) => relKeys.contains (x, ts) &&
      (tot.acqCount x ι == 1 || ((S.upd x).contains ι && !claimed (x, ts)))) &&
    relKeys.all fun (x, ts) =>
      let ids := (tot.acq.filter (·.1 == x)).map (·.2) ++ (if claimed (x, ts) then [] else S.upd x)
      ids.all fun ι => slots.any fun (x', ts', ι', _) => x' == x && ts' == ts && ι' == ι) ++
  check "slotsPred" (slots.all fun (x, ts, ι, r) =>
    match valAt x ts with
    | some v => (S.acqTab.getD ι fun _ _ _ => false) f v r
    | none => false) ++
  check "promWf" ((List.range c.threads.size).all fun i => (promsOf c i).all fun ts =>
    match c.mem.get? ts with
    | some w => w.tid == i
    | none => false) ++
  check "promValid" ((List.range c.threads.size).all fun i => (promsOf c i).all fun ts =>
    pend.contains ts || match c.mem.get? ts with
    | some w => mayWriteB slots (rF.getD i SRes.unit) (locIdx w.loc) S.upd
    | none => true) ++
  check "pend" (pend.all fun ts => outstandingB c ts && (c.mem.get? ts).isSome) ++
  check "updIds" ((List.range 4).all fun x => (S.upd x).all fun ι => ι < S.acqTab.length && tot.acqCount x ι == 0) ++
  check "relSettled" (relKeys.all fun (_, ts) => ts == 0 || settledB c pend ts) ++
  check "claimsNodup" ((claims.map (·.1)).eraseDups.length == claims.length) ++
  check "claimsAt" (claims.all fun ((x, tr), tw) => match c.mem.get? tw with
    | some w => tr < tw && (ms.all fun (ts, w') => !(tr < ts && ts < tw && locIdx w'.loc == x) || w'.tid == w.tid)
    | none => false)

/-! ## Virtual configurations -/

/-- A memory-silent promise-free run of thread `i` alone, of at most `d`
instructions, after which no promise in `targets` is outstanding: its final
thread. -/
partial def advanceTo (A : Arch) (i : Nat) (mem : Memory) (targets : List Time) (t : Thread isa) (d : Nat) :
    Option (Thread isa) :=
  if targets.all (fun p => !t.prom.contains p) then some t
  else if d == 0 then none
  else match stepOne A t i mem with
    | none => none
    | some outs => outs.findSome? fun
      | .ok o => if o.mem.last == mem.last then advanceTo A i mem targets o.thread (d - 1) else none
      | .error _ => none

/-- The virtual configuration of `c` (`none`: some release promise has no
memory-silent advance; the explorer reports it). -/
def virtualOf (A : Arch) (S : SSpec) (c : Config isa) : Option (Config isa) :=
  (List.range c.threads.size).foldlM (init := c) fun v i =>
    match c.threads[i]? with
    | none => some v
    | some t =>
      let targets := t.prom.filter fun ts => match c.mem.get? ts with
        | some w => S.relMode w
        | none => false
      if targets.isEmpty then some v else
      (advanceTo A i c.mem targets t 12).map fun t' => { v with threads := v.threads.set! i t' }

/-- `(#configurations, #with an outstanding release promise, #without a
virtual advance, #failing erasure at c with pending releases, #failing at the
virtual configuration, #failing at c with nothing pending, the clauses failing
at c with pending releases, and at c with nothing pending, deduplicated)`. -/
def erasureCheck (A : Arch) (progs : List (List Instr)) (S : SSpec) :
    Nat × Nat × Nat × Nat × Nat × Nat × List String × List String :=
  let all := reachAll A (initOf progs) false
  all.foldl (init := (all.size, 0, 0, 0, 0, 0, [], [])) fun (n, rp, noAdv, fc, fv, f0, why, why0) c =>
    let hasRel := (msgs c).any fun (ts, w) => S.relMode w && outstandingB c ts
    let rp := if hasRel then rp + 1 else rp
    match virtualOf A S c with
    | none => (n, rp, noAdv + 1, fc, fv, f0, why, why0)
    | some v =>
      let pend := (List.range (c.mem.last + 1)).filter fun ts => outstandingB c ts && !outstandingB v ts
      let ec := eraseFails S c v pend
      let ev := eraseFails S v v []
      let e0 := eraseFails S c v []
      (n, rp, noAdv, if ec.isEmpty then fc else fc + 1, if ev.isEmpty then fv else fv + 1,
        if e0.isEmpty then f0 else f0 + 1, (why ++ ec).eraseDups, (why0 ++ e0).eraseDups)

/-! ## LB with constant stores: relaxed, nothing transferred

`r0 := x; y := 1 ∥ r0 := y; x := 1`. Thread 0 owns `W¹(y)`, thread 1
`W¹(x)`; every release predicate is the exact empty resource (no acquirers,
so `relAcq` forces it). Every promise is valid: its thread owns its
location. Negative control: with the permissions swapped, `promValid` fails
exactly where a thread has promised. -/

def unitPred : SPred := fun _ _ r => r.same SRes.unit

def lbSpec (swap : Bool) : SSpec where
  rel _ := unitPred
  acqTab := []
  relMode _ := false
  assign _ := (if swap then [SRes.full 0, SRes.full 1] else [SRes.full 1, SRes.full 0], [])
  dom := [SRes.unit, SRes.full 0, SRes.full 1]

/-- info: (72, 0, 0, 0, 0, 0, [], []) -/
#guard_msgs in #eval erasureCheck .armv8 lbConst (lbSpec false)
/-- info: (72, 0, 0, 54, 54, 54, ["promValid"], ["promValid"]) -/
#guard_msgs in #eval erasureCheck .armv8 lbConst (lbSpec true)

/-! ## MP with a release flag: ownership transfer through a promised release

`x := 1; y :=rel 1 ∥ r0 :=acq y; r1 := x` (`mpRel true`). Thread 0 starts
with `W¹(x)` and `W¹(y)`, thread 1 with the acquire permission `ι₀` of `y`:
`W.acq ι₀ = W.rel y = λ v r. if v = 1 then r = W¹(x) with 1 ∈ Fulf(x) else
r = emp`. The release message `y = 1` carries the slot `(ι₀, W¹(x))`; once
thread 1 has acquired it (`r0 = 1`), it holds `W¹(x)` and the renamed
permission `ι₁ = ι₀[1 := ⊤]` (SLR's one-shot acquire), whose slot is empty.

The release is promised (with `x := 1`, its pre-view covers it) in most
configurations; erasure must hold there with both promises pending, and
fail without the pending-release clause (`slotsPred`: `x := 1` is not yet
written). Negative control `mpRel false`: the flag is a plain store, so the
`y = 1` message must satisfy `W.rel y` purely, which it does not. -/

def mpAcq : SPred := fun f v r =>
  if v == 1 then r.same (SRes.full 0) && (f 0).any (·.1 == 1) else r.same SRes.unit

def mpAcq' : SPred := fun _ v r => v == 1 || r.same SRes.unit

def mpSpec (rel : Bool) : SSpec where
  rel y := if y == 1 then mpAcq else unitPred
  acqTab := [mpAcq, mpAcq']
  relMode w := rel && locIdx w.loc == 1 && w.val.toNat == 1
  assign v :=
    match v.threads[0]?, v.threads[1]? with
    | some t0, some t1 =>
      let flag := (msgs v).find? fun (ts, w) => ts != 0 && locIdx w.loc == 1 && w.val.toNat == 1
      let r0 : SRes := if t0.st.pc ≤ 1 then (SRes.full 0).op (SRes.full 1) else SRes.full 1
      let acquired := t1.st.pc ≥ 1 && t1.st.regs[0]! == 1
      (match flag with
      | none => ([r0, { acq := [(1, 0)] }], [])
      | some (ts, _) =>
        if !rel then
          ([r0, if acquired then (SRes.full 0).op { acq := [(1, 1)] } else { acq := [(1, 0)] }], [])
        else if acquired then ([r0, (SRes.full 0).op { acq := [(1, 1)] }], [(1, ts, 1, SRes.unit)])
        else ([r0, { acq := [(1, 0)] }], [(1, ts, 0, SRes.full 0)]))
    | _, _ => ([], [])
  dom := [SRes.unit, SRes.full 0, SRes.full 1, (SRes.full 0).op (SRes.full 1)]

-- 12 configurations have the release promised, all of them advance; erasure
-- holds everywhere with the advanced-over promises pending and at every
-- virtual configuration. Without the pending-release clause it fails in all
-- 12: an outstanding release-mode message must be pending (`relSettled`,
-- RMW extension); in the 6 where `x := 1` is promised too, also the slot's
-- predicate needs `x = 1` written (`slotsPred`), and the `x := 1` promise is
-- no longer one thread 0 may write, its `W¹(x)` being in the slot
-- (`promValid`).
/-- info: (29, 12, 0, 0, 0, 12, [], ["slotsPred", "promValid", "relSettled"]) -/
#guard_msgs in #eval erasureCheck .armv8 (mpRel true) (mpSpec true)
-- Plain flag: `y = 1` is not pure (`pure`); with no slot to carry it,
-- `W¹(x)` is either lost when thread 0 is done (`writes`) or duplicated when
-- thread 1 reads the flag early (`valid`).
/-- info: (55, 0, 0, 44, 44, 44, ["pure", "writes", "valid"], ["pure", "writes", "valid"]) -/
#guard_msgs in #eval erasureCheck .armv8 (mpRel false) (mpSpec false)

/-! ## A CAS spinlock: two acquirers of `lock = 0` (RMW extension)

`spinAcqRel` (`CAS.acqRel lock 0 → 1; retry if it read 1; counter :=
counter + 1; lock :=rel 0`) and `spinCas` (the same with `CAS.acq`), two
threads. Location `0` is the lock, `1` the counter. The lock's release
predicate is `φ(0) = W¹(counter)`, `φ(1) = emp`, and its only acquire
predicate is the **update id** `0` (`U(lock, φ)`, held by nobody): every
release message `lock = 0` (the initial one included) carries an update slot
with `W¹(counter)` until a successful CAS claims it. Each thread holds half
of `W(lock)` and, in its critical section, `W¹(counter)`. Two threads
acquire `lock = 0`, but each such message is claimed by at most one CAS, so
`W¹(counter)` is never duplicated: `valid` is the mutual-exclusion check. A
failed CAS (read `1`) writes nothing and claims nothing.

`promValid` may fail where a thread has promised its counter store while the
lock was free (valid then: the update slot is acquirable by everyone) and
the other thread has since claimed it (R3). Such a
promise can never be fulfilled (the thread will read the other thread's
counter write), so the configuration is not live. The check reports the
failures and how many of them are in live configurations (`liveSet`:
backward reachability from final configurations): Theorem 1′ quantifies over
live configurations only. -/

/-- The live configurations among `all` (a final configuration is reachable). -/
partial def liveSet (A : Arch) (all : Array (Config isa)) : Std.HashSet (Config isa) :=
  let edges : Array (Config isa × List (Config isa)) := all.map fun c =>
    let (next, _, _, _) := succsL A {} c 64 none
    (c, next.map (·.1))
  let rec go (live : Std.HashSet (Config isa)) : Std.HashSet (Config isa) :=
    let live' := edges.foldl (init := live) fun acc (c, ns) =>
      if acc.contains c then acc
      else if c.final || ns.any acc.contains then acc.insert c else acc
    if live'.size == live.size then live else go live'
  go {}

/-- `erasureCheck`, restricted to live configurations: `(#configurations,
#live, #failing at c with pending releases, #of those live, the clauses
failing in live configurations)`. -/
def erasureCheckLive (A : Arch) (progs : List (List Instr)) (S : SSpec) :
    Nat × Nat × Nat × Nat × List String :=
  let all := reachAll A (initOf progs) false
  let live := liveSet A all
  all.foldl (init := (all.size, live.size, 0, 0, [])) fun (n, nl, fc, fl, why) c =>
    match virtualOf A S c with
    | none => (n, nl, fc + 1, if live.contains c then fl + 1 else fl, (why ++ ["noAdvance"]).eraseDups)
    | some v =>
      let pend := (List.range (c.mem.last + 1)).filter fun ts => outstandingB c ts && !outstandingB v ts
      let ec := eraseFails S c v pend
      if ec.isEmpty then (n, nl, fc, fl, why)
      else (n, nl, fc + 1, if live.contains c then fl + 1 else fl,
        if live.contains c then (why ++ ec).eraseDups else why)

def lockPred : SPred := fun _ v r => if v == 0 then r.same (SRes.full 1) else r.same SRes.unit

/-- In the critical section: after a successful CAS (`r0 = 0`), before the
release has run. -/
def inCS (t : Thread isa) : Bool := (t.st.pc == 1 && t.st.regs[0]! == 0) || (2 ≤ t.st.pc && t.st.pc ≤ 5)

def lockRmw (w : Msg) : Bool := locIdx w.loc == 0 && w.val.toNat == 1

/-- The spinlock outline. `rel`: the unlock is a release store (else a plain
store: negative control); `nLock`: threads `< nLock` run the lock protocol
(others are racing threads whose stores are relaxed); `lockShare`: each
thread's fraction of `W(lock)`, in sixths. -/
def spinSpec (rel : Bool) (nLock : Nat := 2) (lockShare : Nat := 3) : SSpec where
  rel x := if x == 0 then lockPred else unitPred
  acqTab := [lockPred]
  relMode w := rel && locIdx w.loc == 0 && w.val.toNat == 0 && w.tid < nLock
  initRel x := x == 0
  upd x := if x == 0 then [0] else []
  rmwMsg := lockRmw
  assign v :=
    let rF := (List.range v.threads.size).map fun i =>
      let cs := match v.threads[i]? with
        | some t => i < nLock && inCS t
        | none => false
      (SRes.frac 0 lockShare).op (if cs then SRes.full 1 else SRes.unit)
    let cl := claimsWith lockRmw v []
    let relKeys := (0 :: ((msgs v).filter fun (ts, w) => ts != 0 && rel && locIdx w.loc == 0 &&
      w.val.toNat == 0 && w.tid < nLock).map (·.1))
    (rF, (relKeys.filter fun ts => !cl.any (·.1 == (0, ts))).map fun ts => (0, ts, 0, SRes.full 1))
  dom := [SRes.unit, SRes.full 1]

-- Two acquirers of `lock = 0`: erasure holds at every configuration, with
-- the promised releases pending, at the virtual configurations, and fails
-- without the pending clause only where an unlock is promised.
/-- info: (565, 428, 0, 0, 0, 428, [], ["slotsDom", "relSettled", "promValid"]) -/
#guard_msgs in #eval erasureCheck .armv8 [spinAcqRel, spinAcqRel] (spinSpec true)
/-- info: (565, 565, 0, 0, []) -/
#guard_msgs in #eval erasureCheckLive .armv8 [spinAcqRel, spinAcqRel] (spinSpec true)

-- `CAS.acq` lock (`spinCas`): same result shape; the `promValid` failures
-- (a counter store promised while the lock was free, then the other thread
-- claims the slot, R3) are all in configurations that are not live: 72
-- failing configurations (with pending releases and at the virtual
-- configuration), 0 of them live.
/-- info: (1965, 1568, 0, 72, 72, 1640, ["promValid"], ["slotsDom", "relSettled", "promValid"]) -/
#guard_msgs in #eval erasureCheck .armv8 [spinCas, spinCas] (spinSpec true)
/-- info: (1965, 1791, 72, 0, []) -/
#guard_msgs in #eval erasureCheckLive .armv8 [spinCas, spinCas] (spinSpec true)

/-- The Theorem 1′ split: validity-free
erasure (`T` = every thread, what `NPSafe` maintains) at *every* reachable
configuration, live or not, with the promised releases pending, and full
erasure (`T = ∅`, `promValid` included: what condition (3) restores) at the
live ones: `(#configurations, #live, #failing validity-free erasure, its
clauses, #live failing full erasure, #non-live failing full erasure)`. -/
def erasureCheckSplit (A : Arch) (progs : List (List Instr)) (S : SSpec) :
    Nat × Nat × Nat × List String × Nat × Nat :=
  let all := reachAll A (initOf progs) false
  let live := liveSet A all
  all.foldl (init := (all.size, live.size, 0, [], 0, 0)) fun (n, nl, ft, why, fl, fd) c =>
    match virtualOf A S c with
    | none => (n, nl, ft + 1, (why ++ ["noAdvance"]).eraseDups, fl, fd)
    | some v =>
      let pend := (List.range (c.mem.last + 1)).filter fun ts => outstandingB c ts && !outstandingB v ts
      let ec := eraseFails S c v pend
      let et := ec.filter (· != "promValid")
      let (ft, why) := if et.isEmpty then (ft, why) else (ft + 1, (why ++ et).eraseDups)
      let (fl, fd) := if ec.isEmpty then (fl, fd) else if live.contains c then (fl + 1, fd) else (fl, fd + 1)
      (n, nl, ft, why, fl, fd)

-- Validity-free erasure holds at every reachable configuration (doomed ones
-- included); full erasure fails only at non-live configurations (R3).
/-- info: (565, 565, 0, [], 0, 0) -/
#guard_msgs in #eval erasureCheckSplit .armv8 [spinAcqRel, spinAcqRel] (spinSpec true)
/-- info: (1965, 1791, 0, [], 0, 72) -/
#guard_msgs in #eval erasureCheckSplit .armv8 [spinCas, spinCas] (spinSpec true)

-- Negative control: relaxed (plain-store) unlock. The `lock = 0` messages
-- are relaxed, so they must be pure for `φ`, which `φ(0) = W¹(counter)` is
-- not: the outline fails in live configurations.
/-- info: (5139, 5139, 5050, 5050, ["pure", "writes", "promValid", "valid"]) -/
#guard_msgs in #eval erasureCheckLive .armv8 [spinAcqRelRelaxed, spinAcqRelRelaxed] (spinSpec false)

/-- A racing thread that "unlocks" with a plain store, never having locked. -/
def racer : List Instr := [st .plain false 0 (.i 0)]

-- A plain-store "unlock" racing a CAS: the lock protocol outline fails (the
-- racer's `lock = 0` is relaxed and not pure for `φ`: it would hand out a
-- `W¹(counter)` nobody gave up)...
/-- info: (133, 133, 114, 114, ["pure", "valid"]) -/
#guard_msgs in #eval erasureCheckLive .armv8 [spinAcqRel, racer] (spinSpec true (nLock := 1))

/-- ... but the program is not excluded: it gets a weaker outline in which
the lock transfers nothing (`φ = emp`, no update ids) and the only counter
writer keeps `W¹(counter)` throughout. Conclusion: no mutual exclusion
claim, but the counter is still exclusively written. -/
def spinWeakSpec : SSpec where
  rel _ := unitPred
  acqTab := []
  relMode _ := false
  assign v := ((List.range v.threads.size).map fun i =>
      (SRes.frac 0 3).op (if i == 0 then SRes.full 1 else SRes.unit), [])
  dom := [SRes.unit, SRes.full 1]

/-- info: (133, 133, 0, 0, []) -/
#guard_msgs in #eval erasureCheckLive .armv8 [spinAcqRel, racer] spinWeakSpec

/-! ## Instruction steps: the shadow of the lifted lemma

The per-instruction form (`EvTree.eraseWP_store`/`eraseWP_rmw` through the
frame `runTree_eraseWP` to `Erase.npStep`, `SLR/Lift*.lean`) carries erasure
across one instruction of thread `i`, from `Config.MachInv` (proved for every
reachable configuration, `Config.MachInv.reachable`) and the rules'
preconditions. `stepCheck` shadows it on every instruction step `c → c'`
between reachable configurations (every `stepOne` outcome of every thread):

- `machInvFails`: `Config.MachInv` at `c` (`promWf`, `promNodup`, `ownCoh`);
  a theorem, so it must never fail;
- for an RMW write at `tw` reading `tr` (the latest message to its location
  below `tw`, as `claimsWith`): the facts `eraseWP_rmw` discharges or assumes,
  `atomic` (discharged, `WriteEv.tr`), `tw` not pending (`WriteAt`), `(l, tr)`
  unclaimed (`claimed_store`), and `hnp` (no promise of `i` pending: an
  assumption of `ErAt.rmw`);
- erasure transfer: where erasure holds at `c` (with the pending set of
  `virtualOf c`), it holds at `c'` (with that of `virtualOf c'`). Failures are
  expected only where the rules' `hval` (R3) fails, i.e. `promValid`, and
  never in a live configuration. -/

/-- The clauses of `Config.MachInv` that fail at `c`. -/
def machInvFails (c : Config isa) : List String :=
  let check (name : String) (b : Bool) : List String := if b then [] else [name]
  let n := c.threads.size
  check "promWf" ((List.range n).all fun i => (promsOf c i).all fun ts =>
    match c.mem.get? ts with
    | some w => w.tid == i
    | none => false) ++
  check "promNodup" ((List.range n).all fun i => (promsOf c i).eraseDups.length == (promsOf c i).length) ++
  check "ownCoh" ((List.range n).all fun i => match c.threads[i]? with
    | none => true
    | some t => (msgs c).all fun (ts, w) => w.tid != i || t.prom.contains ts || decide (ts ≤ t.views.getCoh w.loc))

/-- The pending set of `c` (`virtualOf`), if `c` has a virtual configuration,
with the latter. -/
def pendOf (A : Arch) (S : SSpec) (c : Config isa) : Option (Config isa × List Nat) :=
  (virtualOf A S c).map fun v =>
    (v, (List.range (c.mem.last + 1)).filter fun ts => outstandingB c ts && !outstandingB v ts)

/-- `(#instruction steps between reachable configurations, #writes, #RMW
writes, #configurations failing MachInv, #RMW steps (not fulfilling a pending
promise) failing a fact (atomic, (l, tr) unclaimed, hnp), #RMW steps
fulfilling a pending promise, #steps with erasure before and not after, #of
those into a live configuration, the clauses failing after, deduplicated, and
the failing RMW facts)`. -/
def stepCheck (A : Arch) (progs : List (List Instr)) (S : SSpec) :
    Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × List String × List String :=
  let all := reachAll A (initOf progs) false
  let allSet : Std.HashSet (Config isa) := all.foldl (·.insert ·) {}
  let live := liveSet A all
  all.foldl (init := (0, 0, 0, 0, 0, 0, 0, 0, [], [])) fun (ns, nw, nr, fmi, frf, fnp, fer, fel, why, rwhy) c =>
    let fmi := if (machInvFails c).isEmpty then fmi else fmi + 1
    match pendOf A S c with
    | none => (ns, nw, nr, fmi, frf, fnp, fer, fel, why, rwhy)
    | some (v, pend) =>
      let pre := (eraseFails S c v pend).isEmpty
      (List.range c.threads.size).foldl (init := (ns, nw, nr, fmi, frf, fnp, fer, fel, why, rwhy))
        fun acc@(ns, nw, nr, fmi, frf, fnp, fer, fel, why, rwhy) i =>
        match c.threads[i]? with
        | none => acc
        | some t =>
          let outs := ((stepOne A t i c.mem).getD []).filterMap fun
            | .ok o => some o
            | .error _ => none
          outs.foldl (init := (ns, nw, nr, fmi, frf, fnp, fer, fel, why, rwhy))
            fun acc@(ns, nw, nr, fmi, frf, fnp, fer, fel, why, rwhy) o =>
            let c' := c.withThread i o.thread o.mem
            if !allSet.contains c' then acc else
            let tw? : Option Time :=
              if o.mem.last > c.mem.last then some o.mem.last
              else t.prom.find? fun p => !o.thread.prom.contains p
            let (nw, nr, frf, fnp, rwhy) := match tw? with
              | none => (nw, nr, frf, fnp, rwhy)
              | some tw =>
                match o.mem.get? tw with
                | none => (nw + 1, nr, frf, fnp, rwhy)
                | some w =>
                  if !S.rmwMsg w then (nw + 1, nr, frf, fnp, rwhy) else
                  let tr := (msgs { c with mem := o.mem }).foldl
                    (fun a (ts, w') => if ts < tw && w'.loc == w.loc then max a ts else a) 0
                  if pend.contains tw then (nw + 1, nr + 1, frf, fnp + 1, rwhy) else
                  let facts := (if o.mem.atomic w.loc i tr tw then [] else ["atomic"]) ++
                    (if (claimsOf S c pend).any (·.1 == (locIdx w.loc, tr)) then ["claimed"] else []) ++
                    (if t.prom.all (fun p => !pend.contains p) then [] else ["hnp"])
                  (nw + 1, nr + 1, if facts.isEmpty then frf else frf + 1, fnp, (rwhy ++ facts).eraseDups)
            let post := match pendOf A S c' with
              | none => ["noAdvance"]
              | some (v', pend') => eraseFails S c' v' pend'
            if pre && !post.isEmpty then
              (ns + 1, nw, nr, fmi, frf, fnp, fer + 1, if live.contains c' then fel + 1 else fel,
                (why ++ post).eraseDups, rwhy)
            else (ns + 1, nw, nr, fmi, frf, fnp, fer, fel, why, rwhy)

-- `MachInv` holds everywhere. Every RMW write that does not fulfil a pending
-- promise satisfies `atomic`, reads an unclaimed message and has no pending
-- promise of its thread (`hnp`); the others (96 and 360) fulfil a promise the
-- virtual configuration has already advanced over (the write is pending, so
-- it is not a write rule's step but `Erase.fulfil`'s, S2b), and erasure
-- carries across them too. `spinAcqRel`: erasure carries across every step.
/-- info: (1160, 428, 198, 0, 0, 96, 0, 0, [], []) -/
#guard_msgs in #eval stepCheck .armv8 [spinAcqRel, spinAcqRel] (spinSpec true)
-- `spinCas`: 24 steps lose erasure, all `promValid` (a claim invalidates the
-- other thread's promised counter store: the rules' `hval`, R3), none into a
-- live configuration.
/-- info: (3850, 1508, 692, 0, 0, 360, 24, 0, ["promValid"], []) -/
#guard_msgs in #eval stepCheck .armv8 [spinCas, spinCas] (spinSpec true)

end Kraken.Promising.Toy
