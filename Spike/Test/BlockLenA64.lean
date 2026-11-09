import Scc.Emit.A64
import Spike.Test.BlockLenShapes

/-!
# The block-length byte bound on AArch64

Every instruction and terminator shape (`Spike/Test/BlockLenShapes.lean`),
emitted by `Scc.Emit.A64` in a frame whose slots are all beyond the scaled
`ldr`/`str` offsets of `sp` and beyond 16 bits (each slot access a `movz`,
a `movk` and a register-offset access, the longest), takes at most
`bytesPerWeight` bytes (4 per instruction) per weight unit.  So does the
prologue: its fixed part `prologueWeight` units, each parameter's move one more.
Untrusted.
-/

namespace Scc.Test.BlockLen.A64

open Scc.IR Scc.Emit.A64

/-- Filler slots before the shape registers: their offsets are past
`8 · 8200 > 65535`. -/
def fill : List Reg := (List.range 8200).map (s!"z{·}")

def ctx : FnCtx :=
  { fi := 0, name := "f", slots := fill ++ regs, blocks := labels,
    frame := align16 (8 * (fill.length + regs.length) + 16), inArea := maxArgs,
    abortFn := "abort", maps := true }

/-- The bytes of emitted items: 4 per instruction. -/
def itemBytes (items : List Item) : Nat :=
  4 * (items.filter fun | .d (.instr _) => true | _ => false).length

def instBytes (i : Inst) : Option Nat := (ctx.inst 0 i).toOption.map itemBytes
def termBytes (t : Term) : Option Nat := (ctx.term 0 t).toOption.map itemBytes

/-- The shapes over the bound, or not emitted.  Exceptions the emitter
rejects by design: an acquire store, a release load. -/
def badInsts : List Inst := insts.filter fun i =>
  match instBytes i, i with
  | some b, _ => bytesPerWeight * instWeight i < b
  | none, .store .acq .. | none, .load .rel .. => false
  | none, _ => true

def badTerms : List Term := terms.filter fun t =>
  match termBytes t with
  | some b => bytesPerWeight * termWeight t < b
  | none => true

#guard badInsts.isEmpty
#guard badTerms.isEmpty

/-- The prologue of a function with `n` parameters and the frame of `ctx`:
everything `emitFunc` writes before the first block's label. -/
def prologueBytes (n : Nat) : Option Nat :=
  let ps := (List.range n).map (s!"p{·}")
  let body : List Inst := fill.map fun r => Inst.mov r (.imm 0)
  let f : Func := { name := "f", params := ps, blocks := [⟨"entry", body, .unreachable⟩] }
  match emitFunc "abort" (some ⟨"grow", "rel"⟩) [("f", maxArgs)] 0 f with
  | .ok (items, _) =>
    let pre := items.takeWhile fun | .d (.label l) => !l.endsWith "0_entry" | _ => true
    some (itemBytes pre)
  | .error _ => none

/-- The parameter counts the prologue is checked at: none, the eight register
parameters, one stack parameter, the most (`emitFunc`'s slot list is
quadratic in the function's registers, so each run takes seconds). -/
def paramCounts : List Nat := [0, 8, 9, maxArgs]

#guard paramCounts.all fun n =>
  match prologueBytes n with
  | some b => b ≤ bytesPerWeight * (prologueWeight + n)
  | none => false

/-- The largest bytes per weight unit over all shapes, in hundredths. -/
def worst : Nat :=
  let i := insts.foldl (fun m i => max m ((instBytes i).getD 0 * 100 / instWeight i)) 0
  terms.foldl (fun m t => max m ((termBytes t).getD 0 * 100 / termWeight t)) i

/-- info: (5200, [some 76, some 108, some 124, some 492]) -/
#guard_msgs in
#eval (worst, paramCounts.map prologueBytes)

end Scc.Test.BlockLen.A64
