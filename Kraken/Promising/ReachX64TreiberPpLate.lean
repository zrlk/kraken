/-
**`treiber_pp_late.kl` is `Sometimes`: the pop can miss the node's
contents**.

The pusher publishes `n1` with `lock cmpxchgq` before writing its payload,
so the popper can pop `n1` and read the payload before it is written.
`treiber_pp_late_reachable`: from the runner's exact initial configuration
(`c0`, checked by `reachX64RunnerMatches`), under `Arch.tso`, some final
configuration violates the `.kl`'s `forall (1:r10=n1 /\ 1:r11=1)`.
-/
import Kraken.Promising.ReachX64Core
import Kraken.X64.Parser

namespace Kraken.Promising.Reach.TreiberPpLate

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.X64.Parser

/-- The `code` block of `treiber_pp_late.kl`, verbatim. -/
def code : Program := parse("
pusher:
push:
  movq (%rdi),%rax
  movq %rax,8(%rbx)
  lock cmpxchgq %rbx,(%rdi)
  jne push
  movl $1,(%rbx)
  jmp pdone
pdone:
  nop
popper:
  movq (%rdi),%rax
  testq %rax,%rax
  je popper
  movq 8(%rax),%rcx
  lock cmpxchgq %rcx,(%rdi)
  jne popper
  movq %rax,%r10
  movl (%rax),%r11d
  jmp qdone
qdone:
")

/-- The runner's image: the code, then `top` and `n1`. -/
def exe : _root_.Executable := reachX64Exe code [("top", 0x1000000), ("n1", 0x1000100)]

/-- The runner's declarations for the untyped header: unsized. -/
def decls : Decls := { locs := [⟨0x1000000, 0⟩, ⟨0x1000100, 0⟩], unsizedDefault := true }

/-- The initial memory: `top = 0`, `n1 = 0` (unsized). -/
def initMem : List (Loc × Val) := [(⟨0x1000000, 0⟩, 0), (⟨0x1000100, 0⟩, 0)]

/-- The runner's initial configuration: the pusher from `pusher` to `pdone`
with `%rdi = top`, `%rbx = n1`; the popper from `popper` to `qdone` with
`%rdi = top`. -/
def c0 : Config isa := Config.init
  [reachX64Thread exe decls [(.rdi, 0x1000000), (.rbx, 0x1000100)] 0x100000 0x100006,
   reachX64Thread exe decls [(.rdi, 0x1000000)] 0x100007 0x100010] initMem

/-- The `.kl` source. -/
def kl : String := include_str "../Examples/LockFree/X64/treiber_pp_late.kl"

/-- info: true -/
#guard_msgs in
#eval reachX64RunnerMatches kl c0

/-- The explorer's witness (`reach_trace.py`, 15 steps). -/
def trace : List (Nat × List Nat) :=
  [(0, [0]), (0, [1]), (0, [0, 2]), (0, []), (1, [2]), (1, []),
   (1, []), (1, [1]), (1, [2, 3]), (1, []), (1, []), (0, [4]),
   (0, []), (1, [0]), (1, [])]

/-- **`treiber_pp_late.kl`'s violation is reachable** from the runner's
configuration: a final configuration where the popper did not get `n1`
with payload `1`. -/
theorem treiber_pp_late_reachable (fuel : Nat) :
    ∃ c, Reachable Arch.tso fuel c0 c ∧ c.final = true ∧
      ¬ (reachReg64 c 1 .r10 = some 0x1000100 ∧ reachReg32 c 1 .r11 = some 1) :=
  reach_witness_prop Arch.tso fuel reachExecK_eq reachDeps_eq (tr := trace) (by decide +kernel)

end Kraken.Promising.Reach.TreiberPpLate

#print axioms Kraken.Promising.Reach.TreiberPpLate.treiber_pp_late_reachable
