/-
**`treiber_aba_untagged.kl` is `Sometimes`: the ABA problem is reachable**
.

Thread 0 starts popping `A` (reads `head = A`, `A.next = B`); thread 1 pops
`A` and `B` and pushes `A` back; thread 0's untagged `lock cmpxchgq` then
succeeds and installs the stale `B`. `treiber_aba_untagged_reachable`: from
the runner's exact initial configuration (`c0`, checked by
`reachX64RunnerMatches`), under `Arch.tso`, some final configuration has
thread 0's `r12 = A`, `r13 = B` and thread 1's `r13 = B` (the `.kl`'s
`exists (0:r12=A /\ 0:r13=B /\ 1:r13=B)`).
-/
import Kraken.Promising.ReachX64Core
import Kraken.X64.Parser

namespace Kraken.Promising.Reach.TreiberAbaUntagged

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.X64.Parser

/-- The `code` block of `treiber_aba_untagged.kl`, verbatim. -/
def code : Program := parse("
p0:
  movq (head),%rax
  testq %rax,%rax
  je p0
  movq (%rax),%rbx
  lock cmpxchgq %rbx,(head)
  jne p0
  movq %rax,%r12
  movq %rbx,%r13
  jmp done
p1:
p1pop1:
  movq (head),%rax
  movq $0,%r12
  testq %rax,%rax
  je p1pop2
  movq (%rax),%rbx
  lock cmpxchgq %rbx,(head)
  jne p1pop1
  movq %rax,%r12
p1pop2:
  movq (head),%rax
  movq $0,%r13
  testq %rax,%rax
  je p1push
  movq (%rax),%rbx
  lock cmpxchgq %rbx,(head)
  jne p1pop2
  movq %rax,%r13
p1push:
  testq %r12,%r12
  je done
p1push1:
  movq (head),%rax
  movq %rax,(%r12)
  lock cmpxchgq %r12,(head)
  jne p1push1
  jmp done
done:
")

/-- The runner's image: the code, then `head`, `A`, `B`. -/
def exe : _root_.Executable := reachX64Exe code [("head", 0x1000000), ("A", 0x1000100), ("B", 0x1000200)]

/-- The runner's declarations for the untyped header: unsized. -/
def decls : Decls :=
  { locs := [⟨0x1000000, 0⟩, ⟨0x1000100, 0⟩, ⟨0x1000200, 0⟩], unsizedDefault := true }

/-- The initial memory: `head = A`, `A = B` (the next pointer), `B = 0`
(unsized). -/
def initMem : List (Loc × Val) :=
  [(⟨0x1000000, 0⟩, 0x1000100), (⟨0x1000100, 0⟩, 0x1000200), (⟨0x1000200, 0⟩, 0)]

/-- The runner's initial configuration: thread 0 from `p0`, thread 1 from
`p1`, both to `done`. -/
def c0 : Config isa := Config.init
  [reachX64Thread exe decls [] 0x100000 0x100020, reachX64Thread exe decls [] 0x100009 0x100020] initMem

/-- The `.kl` source. -/
def kl : String := include_str "../Examples/LockFree/X64/treiber_aba_untagged.kl"

/-- info: true -/
#guard_msgs in
#eval reachX64RunnerMatches kl c0

/-- The explorer's witness (`reach_trace.py`, 32 steps). -/
def trace : List (Nat × List Nat) :=
  [(0, [0]), (0, []), (0, []), (0, [0]), (1, [0]), (1, []),
   (1, []), (1, []), (1, [0]), (1, [0, 1]), (1, []), (1, []),
   (1, [1]), (1, []), (1, []), (1, []), (1, [0]), (1, [1, 2]),
   (1, []), (1, []), (1, []), (1, []), (1, [2]), (1, [3]),
   (1, [2, 4]), (1, []), (1, []), (0, [4, 5]), (0, []), (0, []),
   (0, []), (0, [])]

/-- **`treiber_aba_untagged.kl`'s ABA outcome is reachable** from the
runner's configuration. -/
theorem treiber_aba_untagged_reachable (fuel : Nat) :
    ∃ c, Reachable Arch.tso fuel c0 c ∧ c.final = true ∧
      reachReg64 c 0 .r12 = some 0x1000100 ∧ reachReg64 c 0 .r13 = some 0x1000200 ∧
      reachReg64 c 1 .r13 = some 0x1000200 :=
  reach_witness_prop Arch.tso fuel reachExecK_eq reachDeps_eq (tr := trace) (by decide +kernel)

end Kraken.Promising.Reach.TreiberAbaUntagged

#print axioms Kraken.Promising.Reach.TreiberAbaUntagged.treiber_aba_untagged_reachable
