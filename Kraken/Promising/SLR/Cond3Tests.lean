/-
Explorer shadow of condition (3)'s argument (`SLR/Cond3.lean`) on the Toy CAS spinlocks of
`SLR/ErasureTests.lean`, with the same outline (`spinSpec`): the ghost state
and thread resources at a configuration are the outline's at its virtual
configuration (`virtualOf`), slots as in `SSpec.assign`.

Checked on **every machine edge** `c → c'` between reachable configurations
(instruction steps and promises, `succsL`), with `b` ranging over
`0..c.mem.last`:

- **K2** (`ReachFrame`): for every thread's resource at `c`, and the empty
  one, bounded reach (`reachBB`: `mayWriteB` over the slots at or below `b`)
  at `c'` implies bounded reach at `c`, for every location;
- **K1** (`ReachOwn`): for an instruction step of thread `i` whose write floor
  after the step (`Views.wfloor`) is at most `b`, `i`'s bounded reach after
  implies its bounded reach before (for a promise step: the promising thread's
  bounded reach does not grow at all).

And **the conclusion of `cond3_of_run`** at every live configuration: every
outstanding promise `ts` that is not pending (not fulfilled by the virtual
advance) is in its thread's bounded reach at `b = ts - 1`, i.e. through
messages below `ts` only (stronger than `promValid`).

As in `ErasureTests`, a `true` is evidence, not proof.
-/
import Kraken.Promising.SLR.ErasureTests
import Kraken.Promising.AcqFloor

namespace Kraken.Promising.Toy

open Instr

/-- Bounded reach: `mayWriteB` through the slots of messages at or below
`b` only (equivalent to `SLR.CanAcqB`: every slot of a chain is at most `b`). -/
def reachBB (slots : List SSlot) (r : SRes) (x b : Nat) (upd : Nat → List Nat) : Bool :=
  mayWriteB (slots.filter fun (_, ts, _, _) => ts ≤ b) r x upd

/-- The outline's resources and slots at `c` (at its virtual configuration),
with the pending set. -/
def ghostAt (A : Arch) (S : SSpec) (c : Config isa) : Option (List SRes × List SSlot × List Nat) :=
  (pendOf A S c).map fun (v, pend) => let (rF, sl) := S.assign v; (rF, sl, pend)

/-- `(#edges, #K2 failures, #K1 failures, #K1 failures into a live
configuration, #live configurations, #live configurations with a
non-pending promise, #bounded-reach failures at live configurations)`. -/
def cond3Check (A : Arch) (progs : List (List Instr)) (S : SSpec) (noFloor : Bool := false) :
    Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  let all := reachAll A (initOf progs) false
  let live := liveSet A all
  let locs := List.range 4
  let res (rF : List SRes) (i : Nat) := rF.getD i SRes.unit
  let edges := all.foldl (init := (0, 0, 0, 0)) fun acc c =>
    match ghostAt A S c with
    | none => acc
    | some (rF, sl, _) =>
      let (next, _, _, _) := succsL A {} c 64 none
      next.foldl (init := acc) fun (ne, f2, f1, f1l) (c', log) =>
        match ghostAt A S c' with
        | none => (ne + 1, f2, f1, f1l)
        | some (rF', sl', _) =>
          let bs := List.range (c.mem.last + 1)
          let ρs := SRes.unit :: rF
          let k2 := bs.all fun b => ρs.all fun ρ => locs.all fun x =>
            !reachBB sl' ρ x b S.upd || reachBB sl ρ x b S.upd
          let actor := (List.range c.threads.size).find? fun i => !(c.threads[i]? == c'.threads[i]?)
          let isPromise := log.any fun | .promise .. => true | _ => false
          let k1 := match actor with
            | none => true
            | some i => bs.all fun b =>
                let floorOk := match c'.threads[i]? with
                  | some t' => isPromise || noFloor || decide (t'.views.wfloor ≤ b)
                  | none => true
                !floorOk || locs.all fun x =>
                  !reachBB sl' (res rF' i) x b S.upd || reachBB sl (res rF i) x b S.upd
          (ne + 1, if k2 then f2 else f2 + 1, if k1 then f1 else f1 + 1,
            if !k1 && live.contains c' then f1l + 1 else f1l)
  let (ne, f2, f1, f1l) := edges
  let (nl, np, fb) := all.foldl (init := (0, 0, 0)) fun (nl, np, fb) c =>
    if !live.contains c then (nl, np, fb) else
    match ghostAt A S c with
    | none => (nl + 1, np, fb + 1)
    | some (rF, sl, pend) =>
      let ps := (List.range c.threads.size).flatMap fun i =>
        (promsOf c i).filterMap fun ts => if pend.contains ts then none else some (i, ts)
      let ok := ps.all fun (i, ts) => match c.mem.get? ts with
        | some w => reachBB sl (res rF i) (locIdx w.loc) (ts - 1) S.upd
        | none => true
      (nl + 1, if ps.isEmpty then np else np + 1, if ok then fb else fb + 1)
  (ne, f2, f1, f1l, nl, np, fb)

-- `spinAcqRel` ×2: K1 and K2 hold on every edge; at every live configuration
-- (230 of them with a non-pending promise) every non-pending promise is in
-- bounded reach below its timestamp.
/-- info: (1572, 0, 0, 0, 565, 230, 0) -/
#guard_msgs in #eval cond3Check .armv8 [spinAcqRel, spinAcqRel] (spinSpec true)

-- `spinCas` ×2: the same, including the 72 non-live R3 configurations'
-- edges (the claim there removes a slot: K2 allows it; the doomed promise
-- is simply not in reach any more, and the configuration is not live).
/-- info: (5246, 0, 0, 0, 1791, 818, 0) -/
#guard_msgs in #eval cond3Check .armv8 [spinCas, spinCas] (spinSpec true)

-- Negative control: dropping K1's write-floor hypothesis (checking K1 for
-- every bound `b`, not only `b ≥ wfloor`) makes 84 edges fail, all into
-- live configurations; so the floor hypothesis is what makes K1 hold.
/-- info: (1572, 0, 84, 84, 565, 230, 0) -/
#guard_msgs in #eval cond3Check .armv8 [spinAcqRel, spinAcqRel] (spinSpec true) (noFloor := true)

end Kraken.Promising.Toy
