import Kraken.X64.Parser
import Kraken.Promising.X64
import Kraken.Promising.Rel

/-!
# Store buffering on x86-TSO

Two threads, two shared locations `x` and `y`, both initially 0. Each thread
writes 1 to one location and then reads the other:

    P0: movl $1,(x)        P1: movl $1,(y)
        movl (y),%eax          movl (x),%eax

Under sequential consistency one of the reads must see a 1. x86 does not
guarantee that: a store may sit in the core's store buffer while the later
load goes to memory, so both threads can read 0 (`SB`, the one weak
behaviour of TSO). An `mfence` between the store and the load restores the
SC outcomes (`SB+mfences`).

This file runs both programs on Kraken's Promising machine under the TSO
profile (`Arch.tso`: every load is an RCpc acquire, every store a release,
`mfence` is the full fence `dmb.sy`). The configurations are built directly
from the parsed programs, not through the litmus front-end. `finals` lists
the reachable final states (four without fences, three with);
`sb_weak_reachable` and `sb_mfence_sc` are the two verdicts as theorems,
decided by running the explorer (`native_decide`); `sb_weak_witness` shows a
shortest run that produces the weak outcome.

The model has no store buffer. Memory is a list of messages, each write
appended at a fresh timestamp, and a thread may read any message its views
allow. In the weak run P0 writes `x := 1` at timestamp 1 and reads `y` from
the initial write; P1 then writes `y := 1` at timestamp 2 and still reads
`x` from the initial write, although `x := 1` is already in memory. Nothing
forbids it: a release store does not raise the thread's read view
(`vrNew`), and P1 has not accessed `x` before. `mfence` raises `vrNew` to
the thread's own write, after which a load cannot read a message that was
overwritten at or before that timestamp.
-/

open Kraken Kraken.Promising
open Kraken.X64.Parser

namespace Kraken.X64.Examples.WeakMemory

/-- Addresses of the two shared locations, above the threads' code (which
`mkState` lays out at `0x100000 * (tid + 1)`). -/
def xAddr : BitVec 64 := 0x1000000
def yAddr : BitVec 64 := 0x1000100
def syms : List (String × BitVec 64) := [("x", xAddr), ("y", yAddr)]

/-- A thread's code: its instructions as source lines (which the traces
print) and parsed. -/
structure ThreadCode where
  src : List String
  prog : Program
  deriving Inhabited

/-- Parse one thread's code, one instruction per line. -/
def thread (code : String) : ThreadCode :=
  match parse code with
  | .ok prog => { src := ((code.splitOn "\n").map (·.trimAscii.copy)).filter (· ≠ ""), prog }
  | .error e => panic! s!"parse error: {e}"

/-! ## The programs -/

/-- `SB`, thread 0: write `x`, then read `y`. -/
def sb_p0 : ThreadCode := thread "
    movl $1,(x)
    movl (y),%eax"

/-- `SB`, thread 1: write `y`, then read `x`. -/
def sb_p1 : ThreadCode := thread "
    movl $1,(y)
    movl (x),%eax"

/-- `SB+mfences`, thread 0: a full fence between the store and the load. -/
def sbf_p0 : ThreadCode := thread "
    movl $1,(x)
    mfence
    movl (y),%eax"

/-- `SB+mfences`, thread 1. -/
def sbf_p1 : ThreadCode := thread "
    movl $1,(y)
    mfence
    movl (x),%eax"

/-! ## Running them -/

/-- The initial configuration of two threads; shared memory is unmapped in
both threads' `dmem`, so every access reaches the memory model. -/
def config (p0 p1 : ThreadCode) : Config Promising.X64.isa :=
  Config.init [Promising.X64.mkState 0 p0.prog {} syms (texts := p0.src),
               Promising.X64.mkState 1 p1.prog {} syms (texts := p1.src)] []

/-- `eax` of thread `tid` in a final configuration. -/
def eax (c : Config Promising.X64.isa) (tid : Nat) : Nat :=
  match c.threads[tid]? with
  | some t => (t.st.st.1.regs.get64 .rax).setWidth 32 |>.toNat
  | none => 0

/-- Every run of the two threads, observing each thread's `eax` at the end. -/
def explored (p0 p1 : ThreadCode) := explore (I := Promising.X64.isa) Arch.tso (config p0 p1) fun c => (eax c 0, eax c 1)

/-- The reachable final `(P0's eax, P1's eax)`, sorted. -/
def finals (p0 p1 : ThreadCode) : List (Nat × Nat) :=
  (explored p0 p1).finals.mergeSort (fun a b => decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)))

-- Every interleaving, and the weak one: both reads see 0.
/-- info: [(0, 0), (0, 1), (1, 0), (1, 1)] -/
#guard_msgs in
#eval finals sb_p0 sb_p1

-- With fences, only the SC outcomes.
/-- info: [(0, 1), (1, 0), (1, 1)] -/
#guard_msgs in
#eval finals sbf_p0 sbf_p1

/-- The weak outcome of `SB` is reachable on TSO. -/
theorem sb_weak_reachable : (0, 0) ∈ finals sb_p0 sb_p1 := by native_decide

/-- With `mfence`s it is not. -/
theorem sb_mfence_sc : (0, 0) ∉ finals sbf_p0 sbf_p1 := by native_decide

/-! ## The weak run -/

/-- A shortest run that ends with both `eax` 0. Each thread's store is a
message at a fresh timestamp; each thread's load is still free to read
timestamp 0, because a (release) store does not raise the thread's read
view. P1's read of `x` is the store-buffering behaviour: `x := 1` is in
memory at timestamp 1, and P1 reads the older value. -/
def sb_weak_witness : String :=
  let locName (l : Loc) : String := if l.addr == xAddr then "x" else if l.addr == yAddr then "y" else "?"
  match (explored sb_p0 sb_p1).witnesses.find? (·.1 == (0, 0)) with
  | some (_, tr) => formatTrace locName tr
  | none => "unreachable"

/--
info: P0: movl $1,(x)
    write x := 1 @1
P0: movl (y),%eax
    read y = 0 @0  (post-view 0)
P1: movl $1,(y)
    write y := 1 @2
P1: movl (x),%eax
    read x = 0 @0  (post-view 0)
-/
#guard_msgs in
#eval IO.println sb_weak_witness

end Kraken.X64.Examples.WeakMemory
