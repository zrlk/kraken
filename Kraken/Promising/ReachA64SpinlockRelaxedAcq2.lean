/-
**`spinlock_relaxed_acq2.kl` is `Sometimes`: a lost update is reachable**.

The lock is taken with `LDXR` (no acquire), so the counter read of the
second holder may be satisfied before its lock read and miss the first
holder's increment.
`spinlock_relaxed_acq2_reachable`: from the runner's exact initial configuration (`c0`, checked by
`reachA64RunnerMatches`), under `Arch.armv8`, some final configuration has
`[counter] = 1`, violating the `.kl`'s `forall [counter]=2`.
-/
import Kraken.Promising.ReachA64Core
import Kraken.AArch64.Parser

namespace Kraken.Promising.Reach.SpinlockRelaxedAcq2

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- The `code` block of `spinlock_relaxed_acq2.kl`, verbatim. -/
def code : Program := parseAArch64("
worker:
  LDXR W2,[X0]
  CBNZ W2,worker
  MOV W3,#1
  STXR W4,W3,[X0]
  CBNZ W4,worker
  LDR W5,[X1]
  ADD W5,W5,#1
  STR W5,[X1]
  STLR WZR,[X0]
  B done
done:
")

/-- The runner's declarations for the untyped header: unsized. -/
def decls : Decls := { locs := [⟨0x1000, 0⟩, ⟨0x1100, 0⟩], unsizedDefault := true }

/-- The initial memory: every location `0` (unsized). -/
def initMem : List (Loc × Val) := [(⟨0x1000, 0⟩, 0), (⟨0x1100, 0⟩, 0)]

/-- The runner's initial configuration: both threads from `worker` to
`done`, `X0 = lock`, `X1 = counter`. -/
def c0 : Config isa := Config.init
  [reachA64Thread (reachA64Exe code) decls [(.X0, 0x1000), (.X1, 0x1100)] 0x100000 0x100028,
   reachA64Thread (reachA64Exe code) decls [(.X0, 0x1000), (.X1, 0x1100)] 0x100000 0x100028] initMem

/-- The `.kl` source. -/
def kl : String := include_str "../Examples/LockFree/AArch64/spinlock_relaxed_acq2.kl"

/-- info: true -/
#guard_msgs in
#eval reachA64RunnerMatches kl c0

/-- The explorer's witness (`reach_trace.py`, 20 steps). -/
def trace : List (Nat × List Nat) :=
  [(0, [0]), (0, []), (0, []), (0, [1]), (0, []), (0, [0]),
   (0, []), (0, [2]), (0, [3]), (0, []), (1, [3]), (1, []),
   (1, []), (1, [4]), (1, []), (1, [0]), (1, []), (1, [5]),
   (1, [6]), (1, [])]

/-- **`spinlock_relaxed_acq2.kl`'s lost update is reachable** from the runner's
configuration. -/
theorem spinlock_relaxed_acq2_reachable (fuel : Nat) :
    ∃ c, Reachable Arch.armv8 fuel c0 c ∧ c.final = true ∧ c.mem.finalVal ⟨0x1100, 0⟩ = 1 :=
  reach_witness_prop Arch.armv8 fuel reachA64ExecK_eq reachA64Deps_eq (tr := trace) (by decide +kernel)

end Kraken.Promising.Reach.SpinlockRelaxedAcq2

#print axioms Kraken.Promising.Reach.SpinlockRelaxedAcq2.spinlock_relaxed_acq2_reachable
