/-
**`treiber_pp_relaxed.kl` is `Sometimes`: the popper can read the node's
stale data**.

The pusher's `STR` of the node's data and its `CAS` of `top` are unordered
(plain `LDR`/`CAS`, no release), so the pusher may promise the new `top`
first; the popper then pops `n1` and reads its data `0`.
`treiber_pp_relaxed_reachable`: from the runner's exact initial
configuration (`c0`, checked by `reachA64RunnerMatches`), under
`Arch.armv8` at the runner's certification fuel `300`, some final
configuration violates the `.kl`'s `forall (1:X10=n1 /\ 1:X11=1)`.
The witness has one promise step (`ReachCertCore`).
-/
import Kraken.Promising.ReachA64Core
import Kraken.Promising.ReachCertCore
import Kraken.Promising.CertifyAArch64
import Kraken.AArch64.Parser

namespace Kraken.Promising.Reach.TreiberPpRelaxed

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- The `code` block of `treiber_pp_relaxed.kl`, verbatim. -/
def code : Program := parseAArch64("
pusher:
  STR W9,[X1]
push:
  LDR X2,[X0]
  STR X2,[X1,#8]
  MOV X3,X2
  CAS X3,X1,[X0]
  CMP X3,X2
  B.NE push
  B pdone
pdone:
  NOP
popper:
  LDR X2,[X0]
  CBZ X2,popper
  LDR X4,[X2,#8]
  MOV X3,X2
  CAS X3,X4,[X0]
  CMP X3,X2
  B.NE popper
  MOV X10,X2
  LDR W11,[X2]
  B qdone
qdone:
")

/-- The runner's declarations for the untyped header: unsized. -/
def decls : Decls := { locs := [⟨0x1000, 0⟩, ⟨0x1100, 0⟩], unsizedDefault := true }

/-- The initial memory: every location `0` (unsized). -/
def initMem : List (Loc × Val) := [(⟨0x1000, 0⟩, 0), (⟨0x1100, 0⟩, 0)]

/-- The runner's initial configuration: the pusher from `pusher` to `pdone`
(`X0 = top`, `X1 = n1`, `X9 = 1`), the popper from `popper` to `qdone`
(`X0 = top`). -/
def c0 : Config isa := Config.init
  [reachA64Thread (reachA64Exe code) decls [(.X0, 0x1000), (.X1, 0x1100), (.X9, 1)] 0x100000 0x100020,
   reachA64Thread (reachA64Exe code) decls [(.X0, 0x1000)] 0x100024 0x10004c] initMem

/-- The `.kl` source. -/
def kl : String := include_str "../Examples/LockFree/AArch64/treiber_pp_relaxed.kl"

/-- info: true -/
#guard_msgs in
#eval reachA64RunnerMatches kl c0

/-- The explorer's witness (`reach_trace.py --promises`, 19 steps, 1 promise). -/
def trace : List ReachPStep :=
  [.promise 0 0x1000 4352, .instr 0 [2], .instr 0 [0], .instr 0 [3], .instr 0 [],
   .instr 0 [0, 1], .instr 0 [], .instr 0 [], .instr 0 [], .instr 1 [1],
   .instr 1 [], .instr 1 [0], .instr 1 [], .instr 1 [1, 4], .instr 1 [],
   .instr 1 [], .instr 1 [], .instr 1 [0], .instr 1 []]

/-- **`treiber_pp_relaxed.kl`'s stale pop is reachable** from the runner's
configuration, at certification fuel `300`. -/
theorem treiber_pp_relaxed_reachable :
    ∃ c, Reachable Arch.armv8 300 c0 c ∧ c.final = true ∧
      ¬ (reachXReg c 1 .X10 = some 0x1100 ∧ reachWReg c 1 .X11 = some 1) :=
  reach_witness_promise Arch.armv8 300 reachA64ExecK_eq reachA64Deps_eq (tr := trace) (by decide +kernel)

end Kraken.Promising.Reach.TreiberPpRelaxed

#print axioms Kraken.Promising.Reach.TreiberPpRelaxed.treiber_pp_relaxed_reachable
