import Kraken.Promising.Toy

/-!
# Evidence for `LiveBridge`: where the executable machine is incomplete

Concrete witnesses (AArch64 toy ISA) for the claims made in
`Kraken/Promising/LiveBridge.lean`:

* `cex1`: `succs` is not monotone in fuel, and `certify` rejects at fuel 4 a
  thread state that it accepts at fuel 3 (so `certify` at a fixed fuel is not
  complete for `CertOkN`, and `MemSuccsOfStepSem` fails);
* `cex4`: a loop-free certification that the depth-first `certify` misses at
  fuels 11–16, because the visited set is shared across paths and the failing
  store-exclusive branch reaches the join state first;
* `cex3`: a write lost by pruning (`DeadPromiseExact`/Q3(d)): after the
  promise of `z`, the plain store of `y` is never offered as a promise, since
  its path is pruned at a state already visited by the release-store path.

Each block shows only the existing functions (`succs`, `certify`,
`certifiedPromises`); the matching semantic witnesses (a breadth-first
certifier with the post-state promise rule) were run in a separate prototype.
-/

namespace Kraken.Promising.LiveBridgeTests

open Kraken.Promising Kraken.Promising.Toy Instr

/-- Location index of the newest message of `c` (`99` for empty memory). -/
def lastLoc (c : Config isa) : Nat :=
  (c.mem.msgs.toList.map fun w => (w.loc.addr.toNat - 0x1000) / 8).getLastD 99

/-- Locations of the messages added by the promise successors of thread 0. -/
def promLocs (c : Config isa) (f : Nat) : List Nat :=
  (certifiedPromises .armv8 {} c 0 f).1.map fun (c', _) => lastLoc c'

namespace Cex1

/-- x = loc 0, z = loc 1.
  0: r0 := ldxr x
  1: stxr x := 1, status r1
  2: if r1 = 1 goto 0
  3: z := 1 -/
def prog : List Instr :=
  [ld .plain true 0 0, st .plain true 0 (.i 1) [] (some 1), beq 1 1 0, st .plain false 1 (.i 1)]

def c0 : Config isa := Config.init [({ prog := prog.toArray } : State)] []

/-- Is `z := 1` offered as a promise successor at fuel `f`? -/
def offersZ (f : Nat) : Bool := (succs .armv8 c0 f).1.any fun c => lastLoc c == 1

-- The promise of `z` is offered at fuel 4, not at 5 or 6, again at 7.
/-- info: [(0, false), (1, false), (2, false), (3, false), (4, true), (5, false), (6, false), (7, true), (8, true)] -/
#guard_msgs in
#eval (List.range 9).map fun f => (f, offersZ f)

/-- The configuration with `z` promised (taken at fuel 4). -/
def c1 : Config isa := ((succs .armv8 c0 4).1).getD 2 c0

/-- Number of successors of `c1`, and whether each step result of thread 0
certifies, per fuel. -/
def certAfterStep (f : Nat) : List Bool :=
  match c1.threads[0]? with
  | none => []
  | some t => match stepOne .armv8 t 0 c1.mem with
    | some outs => outs.filterMap fun
      | .ok o => some (certify .armv8 {} o.thread 0 o.mem f).1.certified
      | .error _ => none
    | none => []

-- The load result certifies at fuel 3 but not at 4 or 5.
/--
info: [(0, 1, 0, [false]),
 (1, 1, 0, [false]),
 (2, 1, 0, [false]),
 (3, 1, 1, [true]),
 (4, 1, 1, [false]),
 (5, 1, 0, [false]),
 (6, 1, 1, [true]),
 (7, 1, 2, [true]),
 (8, 1, 2, [true])]
-/
#guard_msgs in
#eval (List.range 9).map fun f => (f, lastLoc c1, (succs .armv8 c1 f).1.length, certAfterStep f)

end Cex1

namespace Cex4

/-- LB with a loop-free certification that DFS misses (x = 0, z = 1).
T1: 0: r0 := ldxr x; 1: r2 := r0; 2: stxr x := 1 -> r1; 3: if r1 = 0 goto 10
    4-6: r3 := 0 (x3); 7: r0 := ldxr x; 8: stxr x := 1 -> r1; 9: if r1 = 1 goto 20 (halt)
    10: r1 := 0; 11-15: r3 := 0 (x5); 16: z := 1
T2: r0 := z; x := r0. -/
def t1 : List Instr :=
  [ld .plain true 0 0, mov 2 (.r 0), st .plain true 0 (.i 1) [] (some 1), beq 1 0 10,
   mov 3 (.i 0), mov 3 (.i 0), mov 3 (.i 0), ld .plain true 0 0, st .plain true 0 (.i 1) [] (some 1),
   beq 1 1 20,
   mov 1 (.i 0), mov 3 (.i 0), mov 3 (.i 0), mov 3 (.i 0), mov 3 (.i 0), mov 3 (.i 0),
   st .plain false 1 (.i 1)]
def t2 : List Instr := [ld .plain false 0 1, st .plain false 0 (.r 0)]
def c0 : Config isa :=
  Config.init [({ prog := t1.toArray } : State), ({ prog := t2.toArray } : State)] []

-- `z` (loc 1) is promised by thread 0 only from fuel 17 on (a breadth-first
-- certifier offers it from fuel 11; the LB outcome `T1.r2 = T2.r0 = 1` is
-- then reachable at fuels 11–16 on the semantic machine only).
/-- info: [(10, [0]), (11, [0]), (16, [0]), (17, [0, 1])] -/
#guard_msgs in
#eval [10, 11, 16, 17].map fun f => (f, promLocs c0 f)

end Cex4

namespace Cex3

/-- Q3(d) (x = 0, a = 1, y = 2, z = 3).
  0: ldxr x; 1: stxr x := 1 -> r1; 2: if r1 = 0 goto 8
  3: ldxr x; 4: stxr x := 1 -> r1; 5: stlr a := 1; 6: stlr y := 1; 7: goto 10
  8: stlr a := 1; 9: str y := 1
  10: stlr a := 2; 11: str z := 1 -/
def t : List Instr :=
  [ld .plain true 0 0, st .plain true 0 (.i 1) [] (some 1), beq 1 0 8,
   ld .plain true 0 0, st .plain true 0 (.i 1) [] (some 1), st .rel false 1 (.i 1),
   st .rel false 2 (.i 1), beq 3 0 10,
   st .rel false 1 (.i 1), st .plain false 2 (.i 1),
   st .rel false 1 (.i 2), st .plain false 3 (.i 1)]
def c0 : Config isa := Config.init [({ prog := t.toArray } : State)] []

/-- Promises available after first promising `z` (loc 3). -/
def afterZ (f : Nat) : List Nat :=
  match ((certifiedPromises .armv8 {} c0 0 f).1.map (·.1)).find? (fun c => lastLoc c == 3) with
  | none => [99]
  | some cz => promLocs cz f

-- `y` (loc 2) is never offered after `z`, although the path through the
-- plain store `9: str y := 1` certifies it (a breadth-first certifier offers
-- `[0, 1, 2]`).
/-- info: [(10, [0, 1, 3, 2], [1, 0]), (12, [0, 1, 3, 2], [1, 0])] -/
#guard_msgs in
#eval [10, 12].map fun f => (f, promLocs c0 f, afterZ f)

end Cex3

end Kraken.Promising.LiveBridgeTests
