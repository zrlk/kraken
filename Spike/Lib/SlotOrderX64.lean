/-
**The slot order of an `Accepted1` code block's function on x86-64**:
`Emit.X64.frameOf`'s register list is `Spike/Lib/SlotOrderC1.lean`'s
`slots_func1`.

- `instRegs_eq`, `termRegs_eq`: `Emit.X64.instRegs i` is
  `instDefs i ++ instUsesR i`, `termRegs` is `termUses`;
- `frameRegs_eq`: the first occurrences `frameOf` numbers, by `StackMap`'s
  definitions and uses;
- `frameRegs_func1`: for `func1` of a closed form `lowerC`, the parameter
  registers, then the definitions in order.
-/
import Spike.Lib.SlotOrderC1
import Scc.Emit.X64

namespace Spike.Lib.SlotOrder

open Scc.IR
open Scc.Lower
open Scc.Lower.Inv
open Scc.IR.StackMap (opRegs instDefs instUses termUses)

/-- **`instRegs` is definitions then uses** (`instUsesR`). -/
theorem instRegs_eq (i : Inst) : Scc.Emit.X64.instRegs i = instDefs i ++ instUsesR i := by
  cases i <;> simp [Scc.Emit.X64.instRegs, instDefs, instUsesR, instUses, Scc.Emit.X64.opRegs, opRegs] <;> rfl

/-- **`termRegs` is `termUses`.** -/
theorem termRegs_eq (t : Term) : Scc.Emit.X64.termRegs t = termUses t := by
  cases t <;> rfl

/-- **`frameOf`'s registers by `StackMap`'s definitions and uses.** -/
theorem frameRegs_eq (f : Func) :
    (f.params ++ f.blocks.flatMap fun b => b.insts.flatMap Scc.Emit.X64.instRegs ++
        Scc.Emit.X64.termRegs b.term).eraseDups =
      (f.params ++ f.blocks.flatMap fun b => b.insts.flatMap (fun i => instDefs i ++ instUsesR i) ++
        termUses b.term).eraseDups := by
  have : Scc.Emit.X64.instRegs = fun i => instDefs i ++ instUsesR i := funext instRegs_eq
  simp only [this, termRegs_eq]

/-- **The x86-64 slots of an `Accepted1` code block's function**: for
`func1` of a body's closed form `lowerC` (`accepted1_lowerC`), the registers
`frameOf` numbers are its parameter registers, then its definitions
(`StackMap.instDefs`) in order. -/
theorem frameRegs_func1 (cx : Scc.Lower.Ctx) {d : CoreTerm.Decl} {r : Res1}
    (hr : lowerC cx (env1 d) 0 "entry" 0 d.body = some r) (name : Sym) :
    ((func1 name (params1R d) r).params ++ (func1 name (params1R d) r).blocks.flatMap fun b =>
        b.insts.flatMap Scc.Emit.X64.instRegs ++ Scc.Emit.X64.termRegs b.term).eraseDups =
      (func1 name (params1R d) r).params ++ defsOf instDefs (func1 name (params1R d) r) := by
  rw [frameRegs_eq]
  exact slots_func1 shape_instUsesR _ (fun _ => rfl) cx hr name

/-- **`frameOf`'s slots** for `func1` of a closed form: the parameter
registers, then the definitions, numbered in order. -/
theorem frameOf_slots_func1 (areas : List (Sym × Nat)) (cx : Scc.Lower.Ctx) {d : CoreTerm.Decl} {r : Res1}
    (hr : lowerC cx (env1 d) 0 "entry" 0 d.body = some r) (name : Sym) :
    (Scc.Emit.X64.frameOf areas (func1 name (params1R d) r)).slots =
      ((func1 name (params1R d) r).params ++ defsOf instDefs (func1 name (params1R d) r)).zipIdx := by
  simp only [Scc.Emit.X64.frameOf]
  rw [frameRegs_func1 cx hr name]

end Spike.Lib.SlotOrder
