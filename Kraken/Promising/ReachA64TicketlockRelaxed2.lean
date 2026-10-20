/-
**`ticketlock_relaxed2.kl` is `Sometimes`: a lost update is reachable**.

The spin on `owner` is a plain `LDR`; the control dependency out of the
loop does not order the counter load after it, so the second holder can
read a stale counter.
`ticketlock_relaxed2_reachable`: from the runner's exact initial configuration (`c0`, checked by
`reachA64RunnerMatches`), under `Arch.armv8`, some final configuration has
`[counter] = 1`, violating the `.kl`'s `forall [counter]=2`.
-/
import Kraken.Promising.ReachA64Core
import Kraken.AArch64.Parser

namespace Kraken.Promising.Reach.TicketlockRelaxed2

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- The `code` block of `ticketlock_relaxed2.kl`, verbatim. -/
def code : Program := parseAArch64("
worker:
  MOV W6,#1
  LDADDA W6,W3,[X0]
spin:
  LDR W4,[X1]
  CMP W4,W3
  B.NE spin
  LDR W5,[X2]
  ADD W5,W5,#1
  STR W5,[X2]
  ADD W4,W3,#1
  STLR W4,[X1]
  B done
done:
")

/-- The runner's declarations for the untyped header: unsized. -/
def decls : Decls := { locs := [⟨0x1000, 0⟩, ⟨0x1100, 0⟩, ⟨0x1200, 0⟩], unsizedDefault := true }

/-- The initial memory: every location `0` (unsized). -/
def initMem : List (Loc × Val) := [(⟨0x1000, 0⟩, 0), (⟨0x1100, 0⟩, 0), (⟨0x1200, 0⟩, 0)]

/-- The runner's initial configuration: both threads from `worker` to
`done`, `X0 = next`, `X1 = owner`, `X2 = counter`. -/
def c0 : Config isa := Config.init
  [reachA64Thread (reachA64Exe code) decls [(.X0, 0x1000), (.X1, 0x1100), (.X2, 0x1200)] 0x100000 0x10002c,
   reachA64Thread (reachA64Exe code) decls [(.X0, 0x1000), (.X1, 0x1100), (.X2, 0x1200)] 0x100000 0x10002c] initMem

/-- The `.kl` source. -/
def kl : String := include_str "../Examples/LockFree/AArch64/ticketlock_relaxed2.kl"

/-- info: true -/
#guard_msgs in
#eval reachA64RunnerMatches kl c0

/-- The explorer's witness (`reach_trace.py`, 22 steps). -/
def trace : List (Nat × List Nat) :=
  [(0, []), (1, []), (0, [0, 1]), (0, [0]), (0, []), (0, []),
   (0, [0]), (0, []), (0, [2]), (0, []), (0, [3]), (0, []),
   (1, [1, 4]), (1, [3]), (1, []), (1, []), (1, [0]), (1, []),
   (1, [5]), (1, []), (1, [6]), (1, [])]

/-- **`ticketlock_relaxed2.kl`'s lost update is reachable** from the runner's
configuration. -/
theorem ticketlock_relaxed2_reachable (fuel : Nat) :
    ∃ c, Reachable Arch.armv8 fuel c0 c ∧ c.final = true ∧ c.mem.finalVal ⟨0x1200, 0⟩ = 1 :=
  reach_witness_prop Arch.armv8 fuel reachA64ExecK_eq reachA64Deps_eq (tr := trace) (by decide +kernel)

end Kraken.Promising.Reach.TicketlockRelaxed2

#print axioms Kraken.Promising.Reach.TicketlockRelaxed2.ticketlock_relaxed2_reachable
