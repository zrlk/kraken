/-
**`spinlock_relaxed2.kl` is `Sometimes`: a lost update is reachable**
.

The lock is released with a plain `STR` (no release), so the first holder
may promise the unlock before its counter write; the second holder then
takes the lock and reads the stale counter.
`spinlock_relaxed2_reachable`: from the runner's exact initial configuration
(`c0`, checked by `reachA64RunnerMatches`), under `Arch.armv8` at the
runner's certification fuel `300`, some final configuration has
`[counter] = 1`, violating the `.kl`'s `forall [counter]=2`. The witness has
one promise step (`ReachCertCore`).
-/
import Kraken.Promising.ReachA64Core
import Kraken.Promising.ReachCertCore
import Kraken.Promising.CertifyAArch64
import Kraken.AArch64.Parser

namespace Kraken.Promising.Reach.SpinlockRelaxed2

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- The `code` block of `spinlock_relaxed2.kl`, verbatim. -/
def code : Program := parseAArch64("
worker:
  LDAXR W2,[X0]
  CBNZ W2,worker
  MOV W3,#1
  STXR W4,W3,[X0]
  CBNZ W4,worker
  LDR W5,[X1]
  ADD W5,W5,#1
  STR W5,[X1]
  STR WZR,[X0]
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
def kl : String := include_str "../Examples/LockFree/AArch64/spinlock_relaxed2.kl"

/-- info: true -/
#guard_msgs in
#eval reachA64RunnerMatches kl c0

/-- The explorer's witness (`reach_trace.py --promises`, 21 steps, 1 promise). -/
def trace : List ReachPStep :=
  [.instr 0 [0], .instr 0 [], .instr 0 [], .instr 0 [1], .instr 0 [],
   .promise 0 0x1000 0, .instr 0 [0], .instr 0 [], .instr 0 [3], .instr 0 [2],
   .instr 0 [], .instr 1 [2], .instr 1 [], .instr 1 [], .instr 1 [4],
   .instr 1 [], .instr 1 [0], .instr 1 [], .instr 1 [5], .instr 1 [6],
   .instr 1 []]

/-- **`spinlock_relaxed2.kl`'s lost update is reachable** from the runner's
configuration, at certification fuel `300`. -/
theorem spinlock_relaxed2_reachable :
    ∃ c, Reachable Arch.armv8 300 c0 c ∧ c.final = true ∧ c.mem.finalVal ⟨0x1100, 0⟩ = 1 :=
  reach_witness_promise Arch.armv8 300 reachA64ExecK_eq reachA64Deps_eq (tr := trace) (by decide +kernel)

end Kraken.Promising.Reach.SpinlockRelaxed2

#print axioms Kraken.Promising.Reach.SpinlockRelaxed2.spinlock_relaxed2_reachable
