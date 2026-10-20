/-
**`mp_incl_early.kl` is `Sometimes`: the weak outcome is reachable**
.

The writer increments the flag `f` before storing the data `d`, so the
reader can see the flag set and still read `d = 0`. `mp_incl_early_reachable`:
from the runner's exact initial configuration (`c0`: declarations and
initial memory included, checked against `Litmus.X64.prepareProgram` by
`reachX64RunnerMatches`), under `Arch.tso`, some final configuration has the
reader's `ebx = 0` (the `.kl`'s `exists (1:ebx=0)`).

The proof replays the explorer's witness (`Kraken/Litmus/reach_trace.py`)
with `reachCheck`, evaluated by the kernel (`decide +kernel`).
-/
import Kraken.Promising.ReachX64Core
import Kraken.X64.Parser

namespace Kraken.Promising.Reach.MpInclEarly

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.X64.Parser

/-- The `code` block of `mp_incl_early.kl`, verbatim. -/
def code : Program := parse("
writer:
  incl (%rdi)
  movl $42,(%rsi)
  jmp wdone
wdone:
  nop
reader:
  movl (%rdi),%eax
  cmpl $0,%eax
  je reader
  movl (%rsi),%ebx
  jmp rdone
rdone:
")

/-- The runner's image: the code, then `d` and `f` in 256-byte slots. -/
def exe : _root_.Executable := reachX64Exe code [("d", 0x1000000), ("f", 0x1000100)]

/-- The runner's declarations for the untyped header: unsized. -/
def decls : Decls := { locs := [⟨0x1000000, 0⟩, ⟨0x1000100, 0⟩], unsizedDefault := true }

/-- A thread as the runner prepares it: `%rdi = f`, `%rsi = d`. -/
def thread (pc endPc : Int64) : X64.State where
  exe := exe
  endPc := endPc
  st := ({ ({} : MachineData) with
    regs := ((({} : MachineData).regs.set64 .rdi 0x1000100).set64 .rsi 0x1000000) }, pc)
  decls := decls

/-- The initial memory: `d = 0`, `f = 0` (unsized). -/
def initMem : List (Loc × Val) := [(⟨0x1000000, 0⟩, 0), (⟨0x1000100, 0⟩, 0)]

/-- The runner's initial configuration: the writer from `writer` to `wdone`,
the reader from `reader` to `rdone`. -/
def c0 : Config isa := Config.init [thread 0x100000 0x100003, thread 0x100004 0x100009] initMem

/-- The `.kl` source. -/
def kl : String := include_str "../Examples/LockFree/X64/mp_incl_early.kl"

/-- info: true -/
#guard_msgs in
#eval reachX64RunnerMatches kl c0

/-- The explorer's witness (8 steps). -/
def trace : List (Nat × List Nat) :=
  [(0, [0, 1]), (0, [2]), (0, []), (1, [1]), (1, []), (1, []), (1, [0]), (1, [])]

/-- **`mp_incl_early.kl`'s weak outcome is reachable** from the runner's
configuration: a final configuration with the reader's `ebx = 0`. -/
theorem mp_incl_early_reachable (fuel : Nat) :
    ∃ c, Reachable Arch.tso fuel c0 c ∧ c.final = true ∧
      ∃ t, c.threads[1]? = some t ∧ (t.st.st.1.regs.get64 .rbx).setWidth 32 = 0 :=
  reach_witness_prop Arch.tso fuel reachExecK_eq reachDeps_eq (tr := trace) (by decide +kernel)

end Kraken.Promising.Reach.MpInclEarly

#print axioms Kraken.Promising.Reach.MpInclEarly.mp_incl_early_reachable
