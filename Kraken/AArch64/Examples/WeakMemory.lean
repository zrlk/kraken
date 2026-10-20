import Kraken.AArch64.Parser
import Kraken.Promising.AArch64
import Kraken.Promising.Rel

/-!
# Message passing and load buffering on AArch64

Two threads and two shared locations `x`, `y`, initially 0; `X1` holds the
address of `x` and `X3` that of `y` in both threads.

Message passing (`MP`): P0 writes the data `x := 1` and then the flag
`y := 1`; P1 reads the flag and then the data.

    P0: MOV W0,#1          P1: LDR W0,[X3]
        STR W0,[X1]            LDR W2,[X1]
        MOV W2,#1
        STR W2,[X3]

On Arm the two loads of P1 may be satisfied out of order, so P1 can see the
flag and still the old data (`1:X0=1, 1:X2=0`). Making the flag store a
release (`STLR`) and the flag load an acquire (`LDAR`) forbids it; so does
`DMB SY` on P0 together with an address dependency on P1.

Load buffering (`LB`): each thread reads one location and writes the other.

    P0: LDR W0,[X1]        P1: LDR W0,[X3]
        MOV W2,#1              MOV W2,#1
        STR W2,[X3]            STR W2,[X1]

Both reads may return 1, each store having become visible before the
load that precedes it in program order. This is the behaviour the
Promising machine explains with *promises*: a thread may append a write it
has not executed yet, provided it can certify it will perform it; the
witness below shows P0 promising `y := 1` before executing its load. A
data dependency from the load to the store forbids the outcome.

Each program is parsed by Kraken's AArch64 parser; the configurations are
built directly on the Promising machine under `Arch.armv8`, not through the
litmus front-end. The `#guard_msgs` show the reachable final states and
shortest witness runs; the theorems are the verdicts, decided by running
the explorer (`native_decide`).
-/

open Kraken Kraken.Promising
open Kraken.AArch64.Parser

namespace Kraken.AArch64.Examples.WeakMemory

/-- Addresses of the two shared locations, above the threads' code (which
`mkState` lays out at `0x100000 * (tid + 1)`). -/
def xAddr : BitVec 64 := 0x1000000
def yAddr : BitVec 64 := 0x1000100

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

/-! ## Message passing -/

/-- `MP`, the writer: data, then flag. -/
def mp_p0 : ThreadCode := thread "
    MOV W0,#1
    STR W0,[X1]
    MOV W2,#1
    STR W2,[X3]"

/-- `MP`, the reader: flag, then data. -/
def mp_p1 : ThreadCode := thread "
    LDR W0,[X3]
    LDR W2,[X1]"

/-- `MP+rel+acq`, the writer: the flag store is a release. -/
def mpra_p0 : ThreadCode := thread "
    MOV W0,#1
    STR W0,[X1]
    MOV W2,#1
    STLR W2,[X3]"

/-- `MP+rel+acq`, the reader: the flag load is an acquire. -/
def mpra_p1 : ThreadCode := thread "
    LDAR W0,[X3]
    LDR W2,[X1]"

/-- `MP+dmb+addr`, the writer: a full barrier between the two stores. -/
def mpdep_p0 : ThreadCode := thread "
    MOV W0,#1
    STR W0,[X1]
    DMB SY
    MOV W2,#1
    STR W2,[X3]"

/-- `MP+dmb+addr`, the reader: the data address depends on the flag
(`EOR W4,W0,W0` is 0 but depends on `W0`). -/
def mpdep_p1 : ThreadCode := thread "
    LDR W0,[X3]
    EOR W4,W0,W0
    LDR W2,[X1,W4,SXTW]"

/-! ## Running them -/

/-- `X1 = &x`, `X3 = &y` in every thread. -/
def regs : Reg64s := { X1 := UInt64.ofBitVec xAddr, X3 := UInt64.ofBitVec yAddr }

/-- The initial configuration of two threads; shared memory is unmapped in
both threads' `dmem`, so every access reaches the memory model. -/
def config (p0 p1 : ThreadCode) : Config Promising.AArch64.isa :=
  Config.init [Promising.AArch64.mkState 0 p0.prog regs (texts := p0.src),
               Promising.AArch64.mkState 1 p1.prog regs (texts := p1.src)] []

/-- Register `r` of thread `tid` in a final configuration, as a `W` value. -/
def wreg (c : Config Promising.AArch64.isa) (tid : Nat) (r : XReg) : Nat :=
  match c.threads[tid]? with
  | some t => (t.st.st.1.regs.getXReg r).toBitVec.setWidth 32 |>.toNat
  | none => 0

def locName (l : Loc) : String := if l.addr == xAddr then "x" else if l.addr == yAddr then "y" else "?"

def sorted (l : List (Nat × Nat)) : List (Nat × Nat) :=
  l.mergeSort (fun a b => decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)))

/-- Every run of `MP`, observing P1's `(flag, data)` at the end. -/
def mpExplored (p0 p1 : ThreadCode) :=
  explore (I := Promising.AArch64.isa) Arch.armv8 (config p0 p1) fun c => (wreg c 1 .X0, wreg c 1 .X2)
def mpFinals (p0 p1 : ThreadCode) : List (Nat × Nat) := sorted (mpExplored p0 p1).finals

-- Plain accesses: the flag may be seen without the data.
/-- info: [(0, 0), (0, 1), (1, 0), (1, 1)] -/
#guard_msgs in #eval mpFinals mp_p0 mp_p1

-- Release/acquire: not any more.
/-- info: [(0, 0), (0, 1), (1, 1)] -/
#guard_msgs in #eval mpFinals mpra_p0 mpra_p1

-- Barrier plus address dependency: the same.
/-- info: [(0, 0), (0, 1), (1, 1)] -/
#guard_msgs in #eval mpFinals mpdep_p0 mpdep_p1

/-- On Arm, plain `MP` may see the flag without the data. -/
theorem mp_weak_reachable : (1, 0) ∈ mpFinals mp_p0 mp_p1 := by native_decide
/-- A release store and an acquire load forbid it. -/
theorem mp_rel_acq_forbids : (1, 0) ∉ mpFinals mpra_p0 mpra_p1 := by native_decide
/-- So do a full barrier and an address dependency. -/
theorem mp_dmb_addr_forbids : (1, 0) ∉ mpFinals mpdep_p0 mpdep_p1 := by native_decide

/-- A shortest weak run: P1 reads the flag at timestamp 2 and the data at
timestamp 0. A plain load raises the thread's `vrOld` but not `vrNew`, the
view that constrains later loads, so the stale `x` stays readable. No
promise is needed. -/
def mp_weak_witness : String :=
  match (mpExplored mp_p0 mp_p1).witnesses.find? (·.1 == (1, 0)) with
  | some (_, tr) => formatTrace locName tr
  | none => "unreachable"

/--
info: P0: MOV W0,#1
P0: STR W0,[X1]
    write x := 1 @1
P0: MOV W2,#1
P0: STR W2,[X3]
    write y := 1 @2
P1: LDR W0,[X3]
    read y = 1 @2  (post-view 2)
P1: LDR W2,[X1]
    read x = 0 @0  (post-view 0)
-/
#guard_msgs in #eval IO.println mp_weak_witness

/-! ## Load buffering -/

/-- `LB`, thread 0: read `x`, write `y`. -/
def lb_p0 : ThreadCode := thread "
    LDR W0,[X1]
    MOV W2,#1
    STR W2,[X3]"

/-- `LB`, thread 1: read `y`, write `x`. -/
def lb_p1 : ThreadCode := thread "
    LDR W0,[X3]
    MOV W2,#1
    STR W2,[X1]"

/-- `LB+datas`, thread 0: the stored value depends on the loaded one
(`EOR W2,W0,W0` then `ADD`), which forbids the out-of-order store. -/
def lbdep_p0 : ThreadCode := thread "
    LDR W0,[X1]
    EOR W2,W0,W0
    ADD W2,W2,#1
    STR W2,[X3]"

/-- `LB+datas`, thread 1. -/
def lbdep_p1 : ThreadCode := thread "
    LDR W0,[X3]
    EOR W2,W0,W0
    ADD W2,W2,#1
    STR W2,[X1]"

/-- Every run of `LB`, observing each thread's `W0` at the end. -/
def lbExplored (p0 p1 : ThreadCode) :=
  explore (I := Promising.AArch64.isa) Arch.armv8 (config p0 p1) fun c => (wreg c 0 .X0, wreg c 1 .X0)
def lbFinals (p0 p1 : ThreadCode) : List (Nat × Nat) := sorted (lbExplored p0 p1).finals

/-- info: [(0, 0), (0, 1), (1, 0), (1, 1)] -/
#guard_msgs in #eval lbFinals lb_p0 lb_p1

/-- info: [(0, 0), (0, 1), (1, 0)] -/
#guard_msgs in #eval lbFinals lbdep_p0 lbdep_p1

/-- Both loads of `LB` may read the other thread's store. -/
theorem lb_weak_reachable : (1, 1) ∈ lbFinals lb_p0 lb_p1 := by native_decide
/-- Not with data dependencies. -/
theorem lb_data_forbids : (1, 1) ∉ lbFinals lbdep_p0 lbdep_p1 := by native_decide

/-- The run behind both reads seeing 1: P0 *promises* `y := 1` at timestamp 1
before it has executed anything, P1 reads that promise and writes `x := 1`
at timestamp 2, P0 reads it, and P0's store finally fulfils its promise. The
fulfilment is allowed because the store's data (`W2 := 1`) does not depend
on the load; in `lbdep` it does, the store's pre-view would exceed timestamp
1, and no such run exists. -/
def lb_weak_witness : String :=
  match (lbExplored lb_p0 lb_p1).witnesses.find? (·.1 == (1, 1)) with
  | some (_, tr) => formatTrace locName tr
  | none => "unreachable"

/--
info: P0 promises y := 1 @1
P1: LDR W0,[X3]
    read y = 1 @1  (post-view 1)
P1: MOV W2,#1
P1: STR W2,[X1]
    write x := 1 @2
P0: LDR W0,[X1]
    read x = 1 @2  (post-view 2)
P0: MOV W2,#1
P0: STR W2,[X3]
    write y := 1 @1  (fulfils promise)
-/
#guard_msgs in #eval IO.println lb_weak_witness

end Kraken.AArch64.Examples.WeakMemory
