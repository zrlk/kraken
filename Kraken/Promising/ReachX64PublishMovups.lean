/-
**`publish_movups.kl` is `Sometimes`: a torn 16-byte read is reachable**
.

`movups` is not single-copy atomic (two 8-byte pieces), so the
reader can see the low half of the second store and the high half of the
first. `publish_movups_reachable`: from the runner's exact initial
configuration (`c0`, checked by `reachX64RunnerMatches`), under `Arch.tso`,
some final configuration has the reader's `xmm2 = 0x1_0000000000000002`,
none of `0`, `0x1_0000000000000001`, `0x2_0000000000000002` (the `.kl`'s
`exists (not (1:xmm2=0 \/ …))`).
-/
import Kraken.Promising.ReachX64Core
import Kraken.X64.Parser

namespace Kraken.Promising.Reach.PublishMovups

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.X64.Parser

/-- The `code` block of `publish_movups.kl`, verbatim. -/
def code : Program := parse("
writer:
  movups %xmm0,(rec)
  movups %xmm1,(rec)
  jmp done
reader:
  movups (rec),%xmm2
  jmp done
done:
")

/-- The runner's image: the code, then `rec`. -/
def exe : _root_.Executable := reachX64Exe code [("rec", 0x1000000)]

/-- The runner's declarations for the typed `uint64_t rec[2]`: two sized
8-byte cells (strict). -/
def decls : Decls := { locs := [⟨0x1000000, 8⟩, ⟨0x1000008, 8⟩], unsizedDefault := false }

/-- The runner's initial configuration: the writer from `writer` with
`xmm0 = 0x1_0000000000000001`, `xmm1 = 0x2_0000000000000002`; the reader
from `reader`; both to `done`; no initial memory entries (every cell reads
`0`). -/
def c0 : Config isa := Config.init
  [reachX64Thread exe decls [] 0x100000 0x100005
     [(.mm0, 0x10000000000000001), (.mm1, 0x20000000000000002)],
   reachX64Thread exe decls [] 0x100003 0x100005] []

/-- The `.kl` source. -/
def kl : String := include_str "../Examples/LockFree/X64/publish_movups.kl"

/-- info: true -/
#guard_msgs in
#eval reachX64RunnerMatches kl c0

/-- The explorer's witness (`reach_trace.py`, 5 steps). -/
def trace : List (Nat × List Nat) :=
  [(0, [1, 2]), (0, [3, 4]), (0, []), (1, [3, 2]), (1, [])]

/-- **`publish_movups.kl`'s torn read is reachable** from the runner's
configuration. -/
theorem publish_movups_reachable (fuel : Nat) :
    ∃ c, Reachable Arch.tso fuel c0 c ∧ c.final = true ∧
      reachXmm128 c 1 .mm2 = some 0x10000000000000002 :=
  reach_witness_prop Arch.tso fuel reachExecK_eq reachDeps_eq (tr := trace) (by decide +kernel)

/-- The value read is none of the three the property allows. -/
theorem publish_movups_torn :
    (0x10000000000000002 : BitVec 128) ≠ 0 ∧ (0x10000000000000002 : BitVec 128) ≠ 0x10000000000000001 ∧
      (0x10000000000000002 : BitVec 128) ≠ 0x20000000000000002 := by decide

end Kraken.Promising.Reach.PublishMovups

#print axioms Kraken.Promising.Reach.PublishMovups.publish_movups_reachable
