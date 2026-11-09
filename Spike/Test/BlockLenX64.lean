import Scc.Emit.X64
import Scc.Emit.X64Size
import Spike.Test.BlockLenShapes

/-!
# The block-length byte bound on x86-64

Every instruction and terminator shape (`Spike/Test/BlockLenShapes.lean`),
emitted by `Scc.Emit.X64` in a frame whose slots are all beyond `disp8` of
`%rbp` (the longest slot operands), is at most `bytesPerWeight` bytes per
weight unit, every branch counted rel32 (`Scc.Emit.X64.Size.sizeOf`).  So is
the prologue: its fixed part fits `prologueWeight` units and each parameter's move one
more.  Untrusted.
-/

namespace Scc.Test.BlockLen.X64

open Scc.IR Scc.Emit.X64

/-- A frame with 32 filler slots first, so every shape register's slot is
at `-8(k+1)(%rbp)` with `k ≥ 32` (a 32-bit displacement), and the growth
labels on. -/
def frame : Frame :=
  let fill := (List.range 32).map (s!"z{·}")
  { fn := "f", slots := (fill ++ regs).zipIdx, size := 8 * 64, inArea := maxArgs, maps := true }

/-- The bytes of emitted items, branches rel32; `none` if an item has no
modelled size (a raw line, an alignment). -/
def itemBytes (items : List Item) : Option Nat :=
  items.foldlM (init := 0) fun n it => match it with
    | .d d => (Scc.Emit.X64.Size.sizeOf d true).map (n + ·)
    | .comment _ | .blank => some n
    | .dir _ | .raw _ => none

def emitted (m : E Unit) : Option Nat :=
  match m.run {} with
  | .ok ((), s) => itemBytes s.out
  | .error _ => none

def instBytes (i : Inst) : Option Nat := emitted (emitInst frame none i)
def termBytes (t : Term) : Option Nat := emitted (emitTerm frame t)

/-- The shapes over the bound (or not emitted). -/
def badInsts : List Inst := insts.filter fun i =>
  match instBytes i with
  | some b => bytesPerWeight * instWeight i < b
  | none => true

def badTerms : List Term := terms.filter fun t =>
  match termBytes t with
  | some b => bytesPerWeight * termWeight t < b
  | none => true

#guard badInsts.isEmpty
#guard badTerms.isEmpty

/-- The prologue of a function with `n` parameters (stack check and grow
label included): everything `emitFunc` writes before the first block's label. -/
def prologueBytes (n : Nat) : Option Nat :=
  let ps := (List.range n).map (s!"p{·}")
  let f : Func := { name := "f", params := ps, blocks := [⟨"entry", [], .unreachable⟩] }
  match (emitFunc "abort" (some ⟨"grow", "rel"⟩) [("f", maxArgs)] f).run {} with
  | .ok ((), s) =>
    let items := s.out.reverse
    let pre := items.takeWhile fun | .d (.label l) => l != labelOf "f" "entry" | _ => true
    -- `.globl`/`.type` lines are no code
    itemBytes (pre.filter fun | .dir _ => false | _ => true)
  | .error _ => none

#guard (List.range (maxArgs + 1)).all fun n =>
  match prologueBytes n with
  | some b => b ≤ bytesPerWeight * (prologueWeight + n)
  | none => false

/-- The largest bytes per weight unit over all shapes, in hundredths. -/
def worst : Nat :=
  let i := insts.foldl (fun m i => max m ((instBytes i).getD 0 * 100 / instWeight i)) 0
  terms.foldl (fun m t => max m ((termBytes t).getD 0 * 100 / termWeight t)) i

/-- info: (6600, some 30, some 353, some 35) -/
#guard_msgs in
#eval (worst, prologueBytes 0, prologueBytes 32, prologueBytes 1)

end Scc.Test.BlockLen.X64
