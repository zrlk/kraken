import Kraken.Promising.Toy

/-!
# Evidence for `LiveBridge`: `StepSemOfSuccs` needs `ISA.LawfulState`

`stepSemOfSuccs` (`StepSemOfSuccs.lean`) assumes `[I.LawfulState]`. It
cannot be dropped: `succs` shares one certification cache (a hash map keyed
on `(thread, tid, memory)`) across all threads and steps, so with a `BEq`
on thread states that identifies distinct states, `certify` answers for one
thread state with the cached result of another.

`BadKey`: the toy AArch64 ISA with `beqState := fun _ _ => true` (and a
constant hash). Program (x = loc 0, y = loc 1):
`0: r0 := 0; 1: y := 1; 2: x := 1`. From `c1`, the configuration with
`x := 1` promised by thread 0, promising `y := 1` needs a certifying run of
three instructions (`mov`, the fulfilment of `y`, the fulfilment of `x`), so
the semantic machine has no such promise step at fuel 2 (`PromSem` needs
`CertOkN … 2`; `promReplay`/`promProjection` make this the executable
`CertWriteN` condition). With the lawful ISA `succs` agrees (the promise of
`y` appears from fuel 3); with the unlawful one it is offered at fuel 2: a
`succs` successor that is not a `StepSem` step, i.e. `StepSemOfSuccs` fails.
-/

namespace Kraken.Promising.LiveBridgeTestsLawful

open Kraken.Promising Kraken.Promising.Toy Instr

/-- The toy ISA with an unlawful state comparison: all states are equal. -/
def isaBad : ISA := { isa with beqState := fun _ _ => true, hashState := fun _ => 0 }

/-- Location index of the newest message of `c` (`99` for empty memory). -/
def lastLoc {I : ISA} (c : Config I) : Nat :=
  (c.mem.msgs.toList.map fun w => (w.loc.addr.toNat - 0x1000) / 8).getLastD 99

/-- x = loc 0, y = loc 1.
  0: r0 := 0
  1: y := 1
  2: x := 1 -/
def prog : List Instr := [mov 0 (.i 0), st .plain false 1 (.i 1), st .plain false 0 (.i 1)]

def c0 : Config isa := Config.init [({ prog := prog.toArray } : State)] []

/-- `c1`: `x := 1` promised by thread 0 (taken at a large fuel). -/
def c1 : Config isa := ((succs .armv8 c0 10).1.filter fun c => lastLoc c == 0).headD c0

/-- The same configuration over `isaBad` (the thread states are the same
values; `Config isa` and `Config isaBad` are different types). -/
def conv (c : Config isa) : Config isaBad :=
  { threads := c.threads.map fun t =>
      ({ st := t.st, rview := t.rview, wview := t.wview, views := t.views, prom := t.prom } : Thread isaBad),
    mem := c.mem }

def c1Bad : Config isaBad := conv c1

-- `c1` has one message (x), promised by thread 0, in both forms.
/-- info: (1, #[[1]], 1, #[[1]]) -/
#guard_msgs in
#eval (c1.mem.msgs.size, c1.threads.map (·.prom), c1Bad.mem.msgs.size, c1Bad.threads.map (·.prom))

-- Is a promise of `y` among the successors of `c1`, per fuel: lawful ISA
-- from fuel 3 (as the semantic machine), unlawful ISA already at fuel 2.
/-- info: [(0, false, false), (1, false, false), (2, false, true), (3, true, true), (4, true, true)] -/
#guard_msgs in
#eval (List.range 5).map fun f => (f, (succs .armv8 c1 f).1.any (fun c => lastLoc c == 1),
  (succs .armv8 c1Bad f).1.any (fun c => lastLoc c == 1))

end Kraken.Promising.LiveBridgeTestsLawful
