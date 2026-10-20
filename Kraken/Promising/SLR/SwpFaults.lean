/-
Faults and wild halts for the N = 2 SWP spinlock instance
(`SLR/SwpConcrete.lean`): an explorer check, not a theorem.

The explorer (`explore`, local-step reduction and thread symmetry) visits
the reachable configurations of `Config.init states2 initMem2` under
`Arch.armv8`, collects every fault message of a step (`succsR` reports the
`.error` outcomes `Config.FaultStep` names, and mixed-size accesses), and
projects every final configuration to its counter and to whether every
thread halted at its end address (`Thread.cleanHalted` with `atEnd`). A
halted thread stays halted, so a wild halt on any explored run would show
in a final configuration reached from it. **Flagged**: this is `#eval`
evidence about the reduced, fuel-bounded exploration, not a proof of
`Config.FaultFree` or `Config.WildFree`.
-/
import Kraken.Promising.Faults
import Kraken.Promising.SLR.SwpConcrete

namespace Kraken.Promising.SLR.SwpFaults

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.SwpConcrete

/-- The AArch64 "pc = endPc" test, the `atEnd` of `Thread.cleanHalted`. -/
def atEnd (s : State) : Bool := s.st.2 == s.endPc

/-- Final counters with clean-halting flags, whether the exploration hit its
bound, and the fault messages. -/
def exploreClean : List (Nat × Bool) × Bool × List String :=
  let r := explore Arch.armv8 (Config.init states2 initMem2 : Config isa)
    (fun c => ((c.mem.finalVal P2.C).toNat, c.threads.all fun t => atEnd t.st))
    { fuel := 64, symmetric := true }
  (r.finals, r.boundHit, r.faults)

/-- info: ([(2, true)], false, []) -/
#guard_msgs in
#eval exploreClean

end Kraken.Promising.SLR.SwpFaults
