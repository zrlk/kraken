import Scc.IR.Core
import WeakCore.CoreTerm

/-!
# A builder for IR functions

A small state monad that appends instructions to a current block, opens and
closes blocks, and makes fresh register and label names.  Used by the term
lowering and by the runtime.  Not trusted.

The builder also keeps the term lowering's *placement trace* (`BState.marks`,
read by `buildFuncMarks`): at the start of a block and at the return point of
a call, the source point there (`Point`: the lowering's variables and the
term that remains), for the certificates' node invariants
(`Scc/Cert/Place.lean`). The runtime's functions have none.
-/

namespace Scc.Lower
open Scc.IR

/-- A source point: the lowering's variables (each with its shape type and
one IR operand per word, innermost first, as `Scc.Lower.Env`) and the term
that remains. -/
abbrev Point := List (String × CoreLang.Ty × List Operand) × CoreTerm.Expr

/-- A node of a function the placement trace annotates: the start of block
`l`, or the return point of the call that is instruction `i` of block `l`. -/
inductive Node where
  | block (l : Label)
  | ret (l : Label) (i : Nat)
  deriving BEq, Repr, Inhabited

/-- The state of one function under construction. -/
structure BState where
  /-- Finished blocks, in order. -/
  blocks : Array Block := #[]
  /-- The open block's label and instructions (`none`: after a terminator). -/
  cur : Option (Label × Array Inst) := some ("entry", #[])
  /-- Fresh-name counter. -/
  next : Nat := 0
  /-- Registers that hold trace words (`Func.heapRegs`). -/
  heapRegs : Array Reg := #[]
  /-- Registers that hold scalar words (`Func.scalarRegs`). -/
  scalarRegs : Array Reg := #[]
  /-- The source point being lowered (`none`: no trace, as in the runtime). -/
  here : Option Point := none
  /-- The placement trace: the source point at each node, in order. -/
  marks : Array (Node × Point) := #[]

/-- The builder monad: errors are messages. -/
abbrev B := StateT BState (Except String)

/-- Record source point `p` at node `n` (replacing an earlier record of `n`).
The filter runs on the underlying list: `Array.filter` indexes the array, which
the kernel (deciding the certificates' lowering) does in linear time per index. -/
def markAt (n : Node) (p : Point) : B Unit :=
  modify fun s => { s with marks := (s.marks.toList.filter (·.1 != n)).toArray.push (n, p) }

/-- Set the source point being lowered. -/
def setHere (p : Point) : B Unit :=
  modify fun s => { s with here := some p }

/-- Append an instruction to the open block (opening an unreachable one if
needed); a call's return point gets the source point being lowered. -/
def emit (i : Inst) : B Unit := do
  modify fun s =>
    match s.cur with
    | some (l, is) => { s with cur := some (l, is.push i) }
    | none => { s with cur := some (s!"dead{s.next}", #[i]), next := s.next + 1 }
  if i matches .call .. then
    let s ← get
    if let (some p, some (l, is)) := (s.here, s.cur) then markAt (.ret l (is.size - 1)) p

/-- A fresh register named after `hint`. -/
def fresh (hint : String := "t") : B Reg := do
  let s ← get
  set { s with next := s.next + 1 }
  pure s!"{hint}%{s.next}"

/-- A fresh label named after `hint`. -/
def freshLabel (hint : String := "L") : B Label := do
  let s ← get
  set { s with next := s.next + 1 }
  pure s!"{hint}{s.next}"

/-- Close the open block with `t`. -/
def terminate (t : Term) : B Unit :=
  modify fun s =>
    match s.cur with
    | some (l, is) => { s with blocks := s.blocks.push ⟨l, is.toList, t⟩, cur := none }
    | none => s

/-- Open block `l` (closing the open one, if any, with a jump to `l`). -/
def startBlock (l : Label) : B Unit := do
  if (← get).cur.isSome then terminate (.jmp l)
  modify fun s => { s with cur := some (l, #[]) }
  if let some p := (← get).here then markAt (.block l) p

/-- Whether `r` is in `rs`: `Array.contains` (`hasReg_eq`), tested on the
underlying list, which the kernel (deciding the certificates' lowering) walks in
linear time where `Array.contains` takes quadratic time.  Irreducible so that
elaboration does not evaluate it either: a structural list walk would let `whnf`
run a whole lowering while unifying (the kernel ignores the attribute). -/
@[irreducible] def hasReg (rs : Array Reg) (r : Reg) : Bool := rs.toList.contains r

theorem hasReg_eq (rs : Array Reg) (r : Reg) : hasReg rs r = rs.contains r := by
  unfold hasReg; simp

/-- Record that register `r` holds a trace word. -/
def markHeap (r : Reg) : B Unit :=
  modify fun s => if hasReg s.heapRegs r then s else { s with heapRegs := s.heapRegs.push r }

/-- Record that register `r` holds a scalar word. -/
def markScalar (r : Reg) : B Unit :=
  modify fun s => if hasReg s.scalarRegs r then s else { s with scalarRegs := s.scalarRegs.push r }

/-- Run a builder to a function, with its placement trace. -/
def buildFuncMarks (name : Sym) (params : List Reg) (checkStack : Bool) (body : B Unit) :
    Except String (Func × Array (Node × Point)) := do
  let ((), s) ← body.run {}
  let blocks := match s.cur with
    | some (l, is) => s.blocks.push ⟨l, is.toList, .unreachable⟩
    | none => s.blocks
  pure ({ name, params, blocks := blocks.toList, checkStack, heapRegs := s.heapRegs.toList,
          scalarRegs := s.scalarRegs.toList }, s.marks)

/-- Run a builder to a function. -/
def buildFunc (name : Sym) (params : List Reg) (checkStack : Bool) (body : B Unit) :
    Except String Func :=
  (·.1) <$> buildFuncMarks name params checkStack body

/-- `d := op a b` into a fresh register. -/
def binR (op : BinOp) (a b : Operand) (hint : String := "t") : B Operand := do
  let d ← fresh hint
  emit (.bin op d a b)
  pure (.reg d)

/-- An immediate operand. -/
def imm (n : Nat) : Operand := .imm (UInt64.ofNat n)

/-- The 64-bit pattern of a negative number `-n`. -/
def immNeg (n : Nat) : Operand := .imm (0 - UInt64.ofNat n)

end Scc.Lower
