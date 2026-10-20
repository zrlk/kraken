/-
**`spsc_queue_relaxed2.kl` is `Sometimes`: the consumer can read a slot
before its data lands**.

The producer publishes `tail` with a plain `STR` (no release), so it may
promise a `tail` update before the slot's data store; the consumer then
reads a stale `0`.
`spsc_queue_relaxed2_reachable`: from the runner's exact initial
configuration (`c0`, checked by `reachA64RunnerMatches`), under
`Arch.armv8` at the runner's certification fuel `300`, some final
configuration violates the `.kl`'s `forall (1:X10=1 /\ 1:X11=2)`. The
witness has one promise step (`ReachCertCore`).
-/
import Kraken.Promising.ReachA64Core
import Kraken.Promising.ReachCertCore
import Kraken.Promising.CertifyAArch64
import Kraken.AArch64.Parser

namespace Kraken.Promising.Reach.SpscQueueRelaxed2

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- The `code` block of `spsc_queue_relaxed2.kl`, verbatim. -/
def code : Program := parseAArch64("
prod:
  MOV W3,#1
  MOV X4,#0
  MOV X7,X0
prod_loop:
  LDAR X5,[X1]
  SUB X6,X4,X5
  CMP X6,#2
  B.EQ prod_loop
  STR W3,[X7]
  EOR X7,X7,#8
  ADD X4,X4,#1
  STR X4,[X2]
  ADD W3,W3,#1
  CMP W3,#3
  B.NE prod_loop
  B pdone
pdone:
  NOP
cons:
  MOV X4,#0
  MOV X7,X0
c1:
  LDAR X5,[X2]
  CMP X5,X4
  B.EQ c1
  LDR W10,[X7]
  EOR X7,X7,#8
  ADD X4,X4,#1
  STLR X4,[X1]
c2:
  LDAR X5,[X2]
  CMP X5,X4
  B.EQ c2
  LDR W11,[X7]
  EOR X7,X7,#8
  ADD X4,X4,#1
  STLR X4,[X1]
  B cdone
cdone:
")

/-- The runner's declarations for the untyped header: unsized. -/
def decls : Decls := { locs := [⟨0x1000, 0⟩, ⟨0x1100, 0⟩, ⟨0x1200, 0⟩], unsizedDefault := true }

/-- The runner's initial memory (unsized locations). -/
def initMem : List (Loc × Val) := [(⟨0x1000, 0⟩, 0x0), (⟨0x1100, 0⟩, 0x0), (⟨0x1200, 0⟩, 0x0)]

/-- The runner's initial configuration: the producer from `prod` to `pdone`, the consumer from
`cons` to `cdone`, both with `X0 = buf`, `X1 = head`, `X2 = tail`. -/
def c0 : Config isa := Config.init
  [reachA64Thread (reachA64Exe code) decls [(.X0, 0x1000), (.X1, 0x1100), (.X2, 0x1200)] 0x100000 0x10003c,
   reachA64Thread (reachA64Exe code) decls [(.X0, 0x1000), (.X1, 0x1100), (.X2, 0x1200)] 0x100040 0x100084] initMem

/-- The `.kl` source. -/
def kl : String := include_str "../Examples/LockFree/AArch64/spsc_queue_relaxed2.kl"

/-- info: true -/
#guard_msgs in
#eval reachA64RunnerMatches kl c0

/-- The explorer's witness (`reach_trace.py --promises`, 44 steps, 1 promise). -/
def trace : List ReachPStep :=
  [.instr 0 [], .instr 0 [], .instr 0 [], .instr 1 [], .instr 1 [],
   .instr 0 [0], .instr 0 [], .instr 0 [], .instr 0 [], .instr 0 [1],
   .instr 0 [], .instr 0 [], .instr 0 [2], .instr 0 [], .instr 0 [],
   .instr 0 [], .promise 0 0x1200 2, .instr 0 [0], .instr 0 [], .instr 0 [],
   .instr 0 [], .instr 1 [2], .instr 1 [], .instr 1 [], .instr 1 [1],
   .instr 1 [], .instr 1 [], .instr 1 [4], .instr 0 [5], .instr 0 [],
   .instr 0 [], .instr 0 [3], .instr 0 [], .instr 0 [], .instr 0 [],
   .instr 0 [], .instr 1 [3], .instr 1 [], .instr 1 [], .instr 1 [0],
   .instr 1 [], .instr 1 [], .instr 1 [6], .instr 1 []]

/-- **`spsc_queue_relaxed2.kl`'s stale read is reachable** from the runner's configuration, at certification
fuel `300` (the runner's `-fuel`). -/
theorem spsc_queue_relaxed2_reachable :
    ∃ c, Reachable Arch.armv8 300 c0 c ∧ c.final = true ∧
      ¬ (reachXReg c 1 .X10 = some 1 ∧ reachXReg c 1 .X11 = some 2) :=
  reach_witness_promise Arch.armv8 300 reachA64ExecK_eq reachA64Deps_eq (tr := trace) (by decide +kernel)

end Kraken.Promising.Reach.SpscQueueRelaxed2

#print axioms Kraken.Promising.Reach.SpscQueueRelaxed2.spsc_queue_relaxed2_reachable
