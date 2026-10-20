/-
**`dekker_broken.kl` is `Sometimes`: the lost update is reachable**
.

Both threads raise their flag with a plain store and read the other's flag;
under TSO each store may sit in its store buffer while the load reads the
initial `0`, so both enter the critical section and one increment of
`counter` is lost. `dekker_broken_reachable`: from the runner's exact
initial configuration (`c0`, checked by `reachX64RunnerMatches`), under
`Arch.tso`, some final configuration has both `edx = 1` and `[counter] = 1`
(the `.kl`'s `~exists (0:edx=1 /\ 1:edx=1 /\ [counter]=1)` is violated).
-/
import Kraken.Promising.ReachX64Core
import Kraken.X64.Parser

namespace Kraken.Promising.Reach.DekkerBroken

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.X64.Parser

/-- The `code` block of `dekker_broken.kl`, verbatim. -/
def code : Program := parse("
worker:
  xorl %edx,%edx
  movl $1,(%rsi)
  movl (%rdi),%eax
  testl %eax,%eax
  jne done
  movl $1,%edx
  movl (counter),%ecx
  addl $1,%ecx
  movl %ecx,(counter)
  movl $0,(%rsi)
  jmp done
done:
")

/-- The runner's image: the code, then `flag0`, `flag1`, `counter`. -/
def exe : _root_.Executable :=
  reachX64Exe code [("flag0", 0x1000000), ("flag1", 0x1000100), ("counter", 0x1000200)]

/-- The runner's declarations for the untyped header: unsized. -/
def decls : Decls :=
  { locs := [⟨0x1000000, 0⟩, ⟨0x1000100, 0⟩, ⟨0x1000200, 0⟩], unsizedDefault := true }

/-- The initial memory: every location `0` (unsized). -/
def initMem : List (Loc × Val) := [(⟨0x1000000, 0⟩, 0), (⟨0x1000100, 0⟩, 0), (⟨0x1000200, 0⟩, 0)]

/-- The runner's initial configuration: both threads from `worker` to
`done`, `%rsi` their own flag and `%rdi` the other's. -/
def c0 : Config isa := Config.init
  [reachX64Thread exe decls [(.rsi, 0x1000000), (.rdi, 0x1000100)] 0x100000 0x10000b,
   reachX64Thread exe decls [(.rsi, 0x1000100), (.rdi, 0x1000000)] 0x100000 0x10000b] initMem

/-- The `.kl` source. -/
def kl : String := include_str "../Examples/LockFree/X64/dekker_broken.kl"

/-- info: true -/
#guard_msgs in
#eval reachX64RunnerMatches kl c0

/-- The explorer's witness (`reach_trace.py`, 22 steps). -/
def trace : List (Nat × List Nat) :=
  [(0, []), (1, []), (0, [1]), (0, [0]), (0, []), (0, []),
   (0, []), (0, [0]), (0, []), (0, [2]), (0, [3]), (0, []),
   (1, [4]), (1, [0]), (1, []), (1, []), (1, []), (1, [0]),
   (1, []), (1, [5]), (1, [6]), (1, [])]

/-- **`dekker_broken.kl`'s lost update is reachable** from the runner's
configuration: a final configuration where both threads entered and
`[counter] = 1`. -/
theorem dekker_broken_reachable (fuel : Nat) :
    ∃ c, Reachable Arch.tso fuel c0 c ∧ c.final = true ∧
      reachReg32 c 0 .rdx = some 1 ∧ reachReg32 c 1 .rdx = some 1 ∧
      c.mem.finalVal ⟨0x1000200, 0⟩ = 1 :=
  reach_witness_prop Arch.tso fuel reachExecK_eq reachDeps_eq (tr := trace) (by decide +kernel)

end Kraken.Promising.Reach.DekkerBroken

#print axioms Kraken.Promising.Reach.DekkerBroken.dekker_broken_reachable
