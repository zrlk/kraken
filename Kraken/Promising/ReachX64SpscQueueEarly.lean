/-
**`spsc_queue_early.kl` is `Sometimes`: the consumer can read a slot
before the producer fills it**.

`spsc_queue_early_reachable`: from the runner's exact initial configuration
(`c0`, checked by `reachX64RunnerMatches`), under `Arch.tso`, some final
configuration violates the `.kl`'s `forall (1:r12=1 /\ 1:r13=2 /\ 1:r14=3)`.
-/
import Kraken.Promising.ReachX64Core
import Kraken.X64.Parser

namespace Kraken.Promising.Reach.SpscQueueEarly

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.X64.Parser

/-- The `code` block of `spsc_queue_early.kl`, verbatim. -/
def code : Program := parse("
producer:
  movl $1,%r8d
produce:
  movl (tail),%eax
  movl %eax,%ecx
  addl $1,%ecx
  andl $1,%ecx
pfull:
  movl (head),%edx
  cmpl %ecx,%edx
  je pfull
  movl %eax,%edx
  shll $8,%edx
  movl %r8d,(%rbx,%rdx,1)
  movl %ecx,(tail)
  addl $1,%r8d
  cmpl $4,%r8d
  jne produce
  jmp pdone
pdone:

consumer:
  movl (head),%eax
  movl %eax,%edx
  shll $8,%edx
cempty0:
  movl (%rbx,%rdx,1),%r12d
  movl (tail),%ecx
  cmpl %eax,%ecx
  je cempty0
  addl $1,%eax
  andl $1,%eax
  movl %eax,(head)
  movl %eax,%edx
  shll $8,%edx
cempty1:
  movl (%rbx,%rdx,1),%r13d
  movl (tail),%ecx
  cmpl %eax,%ecx
  je cempty1
  addl $1,%eax
  andl $1,%eax
  movl %eax,(head)
  movl %eax,%edx
  shll $8,%edx
cempty2:
  movl (%rbx,%rdx,1),%r14d
  movl (tail),%ecx
  cmpl %eax,%ecx
  je cempty2
  addl $1,%eax
  andl $1,%eax
  movl %eax,(head)
  jmp cdone
cdone:
")

/-- The runner's image: the code, then `buf0`, `buf1`, `head`, `tail`. -/
def exe : _root_.Executable :=
  reachX64Exe code [("buf0", 0x1000000), ("buf1", 0x1000100), ("head", 0x1000200), ("tail", 0x1000300)]

/-- The runner's declarations for the untyped header: unsized. -/
def decls : Decls :=
  { locs := [⟨0x1000000, 0⟩, ⟨0x1000100, 0⟩, ⟨0x1000200, 0⟩, ⟨0x1000300, 0⟩], unsizedDefault := true }

/-- The initial memory: every location `0` (unsized). -/
def initMem : List (Loc × Val) :=
  [(⟨0x1000000, 0⟩, 0), (⟨0x1000100, 0⟩, 0), (⟨0x1000200, 0⟩, 0), (⟨0x1000300, 0⟩, 0)]

/-- The runner's initial configuration: the producer from `producer` to
`pdone`, the consumer from `consumer` to `cdone`, both with `%rbx = buf0`. -/
def c0 : Config isa := Config.init
  [reachX64Thread exe decls [(.rbx, 0x1000000)] 0x100000 0x100010,
   reachX64Thread exe decls [(.rbx, 0x1000000)] 0x100010 0x10002d] initMem

/-- The `.kl` source. -/
def kl : String := include_str "../Examples/LockFree/X64/spsc_queue_early.kl"

/-- info: true -/
#guard_msgs in
#eval reachX64RunnerMatches kl c0

/-- The explorer's witness (`reach_trace.py`, 73 steps). -/
def trace : List (Nat × List Nat) :=
  [(0, []), (0, [0]), (0, []), (0, []), (0, []), (0, [0]),
   (0, []), (0, []), (0, []), (0, []), (0, [1]), (0, [2]),
   (0, []), (0, []), (0, []), (0, [2]), (0, []), (0, []),
   (0, []), (1, [0]), (1, []), (1, []), (1, [1]), (1, [2]),
   (1, []), (1, []), (1, []), (1, []), (1, [3]), (1, []),
   (1, []), (0, [3]), (0, []), (0, []), (0, []), (0, []),
   (0, [4]), (0, [5]), (0, []), (0, []), (0, []), (0, [5]),
   (0, []), (0, []), (0, []), (1, [0]), (1, [5]), (1, []),
   (1, []), (1, []), (1, []), (1, [6]), (1, []), (1, []),
   (0, [6]), (0, []), (0, []), (0, []), (0, []), (0, [7]),
   (0, [8]), (0, []), (0, []), (0, []), (0, []), (1, [1]),
   (1, [8]), (1, []), (1, []), (1, []), (1, []), (1, [9]),
   (1, [])]

/-- **`spsc_queue_early.kl`'s violation is reachable** from the runner's
configuration. -/
theorem spsc_queue_early_reachable (fuel : Nat) :
    ∃ c, Reachable Arch.tso fuel c0 c ∧ c.final = true ∧
      ¬ (reachReg64 c 1 .r12 = some 1 ∧ reachReg64 c 1 .r13 = some 2 ∧ reachReg64 c 1 .r14 = some 3) :=
  reach_witness_prop Arch.tso fuel reachExecK_eq reachDeps_eq (tr := trace) (by decide +kernel)

end Kraken.Promising.Reach.SpscQueueEarly

#print axioms Kraken.Promising.Reach.SpscQueueEarly.spsc_queue_early_reachable
