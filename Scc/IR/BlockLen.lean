import Scc.IR.Core

/-!
# Block lengths

The length of a straight-line block in **weight units**: a measure of the
code an emitter writes for it that does not depend on the ISA, the frame or
the layout.  An emitter writes at most `bytesPerWeight` bytes per weight unit
(checked per instruction shape on both ISAs in `Spike/Test/BlockLenX64.lean`
and `Spike/Test/BlockLenA64.lean`), so a block of at most `maxBlockLen` units
is at most `bytesPerWeight · maxBlockLen` bytes of straight-line code.

Why a bound at all: the scheduler drives a thread to a safe point (a block
entry) with hardware breakpoints, so the time a thread takes to reach one is
bounded by the longest straight-line block it can be in.  The lowering keeps
every block of the user functions and thread trampolines within the bound
(`Scc.Lower.Split`); the runtime routines are checked on the emitted bytes
instead (see `Scc/Lower/Split.lean`).

The weights:

* an instruction is 1, except a call, a system call, a `site` or a `clone`
  (1 plus its operands: arguments and results, each a register move), and
  `popcnt`, `select` (four operands) and byte and halfword stores (a
  read-modify-write of the doubleword on AArch64), which are 2;
* a terminator is 1, except `ret` (1 plus its results) and `tail` and
  `switchTo` (1 plus their arguments);
* the first block also carries the prologue's parameter moves, one unit per
  parameter (`blocksOk`); the prologue's fixed part is `prologueWeight`,
  outside the bound.

This file contains definitions only (the IR is not trusted).
-/

namespace Scc.IR

/-- The most weight units a block may have (the first block including its
function's parameters, `blocksOk`). -/
def maxBlockLen : Nat := 512

/-- The most bytes an emitter writes per weight unit, on either ISA. -/
def bytesPerWeight : Nat := 72

/-- The fixed part of a function's prologue (frame allocation, stack-limit
check, frame record), in weight units: not counted by `blocksOk`, so the
first block of a `blocksOk` function is at most
`bytesPerWeight · (maxBlockLen + prologueWeight)` bytes with its prologue. -/
def prologueWeight : Nat := 2

/-- The weight of an instruction. -/
def instWeight : Inst → Nat
  | .call ds _ args => 1 + args.length + ds.length
  | .syscall _ _ args _ => 1 + args.length + 1
  | .clone .. => 1 + 3 + 1
  | .site _ args => 1 + args.length
  | .un .popcnt _ _ => 2
  | .select .. => 2
  | .store _ .w8 _ _ | .store _ .w16 _ _ => 2
  | _ => 1

/-- The weight of a terminator. -/
def termWeight : Term → Nat
  | .ret vs => 1 + vs.length
  | .tail _ args => 1 + args.length
  | .switchTo .. => 1 + 3
  | .jmp _ | .br .. | .unreachable => 1

/-- The weight of a list of instructions. -/
def instsWeight (is : List Inst) : Nat := (is.map instWeight).sum

/-- The weight of a block: its instructions and its terminator. -/
def blockWeight (b : Block) : Nat := instsWeight b.insts + termWeight b.term

/-- **Every block of `f` is within `maxBlockLen`**, the first one with one
unit per parameter (the prologue's moves). -/
def blocksOk (f : Func) : Bool :=
  match f.blocks with
  | [] => true
  | b :: bs => decide (f.params.length + blockWeight b ≤ maxBlockLen) &&
      bs.all fun b => decide (blockWeight b ≤ maxBlockLen)

theorem termWeight_pos (t : Term) : 0 < termWeight t := by
  cases t <;> simp [termWeight] <;> omega

theorem instWeight_pos (i : Inst) : 0 < instWeight i := by
  unfold instWeight; split <;> omega

end Scc.IR
