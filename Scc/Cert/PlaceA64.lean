import Scc.Emit.A64
import Scc.Cert.Place

/-!
# Placement data: the AArch64 emitter's frames and labels

`places p`: for each function of `p`, what `Scc.Emit.A64.emitFunc` fixes of
it (`Scc.Cert.Place.FnPlace`): the assembler label of each block
(`FnCtx.blockLabel`) and of each call's return point (its safepoint label
`sp<k>`, `k` the instruction's index in the function, terminators counted),
and the slot of each IR register (`fnCtx`, as `emitFunc`) as an offset from the base of the
function's stack region in the block data (`Scc.Cert.Blocks`: the stack
pointer on entry, offset 0). The frame is allocated first (`sub sp, sp,
#frame`, or through `x9` under the stack check), so the slot at `sp + o`
(`FnCtx.slotOff`) is at offset `o - frame`.
-/

namespace Scc.Cert.Place.A64

open Scc.Emit.A64 Scc.Lower

/-- The placement of each function of `p` (see the module docstring). -/
def places (p : IR.Program) : Except String (List FnPlace) := do
  let areas := IR.StackMap.argAreas p argRegs.length
  p.funcs.zipIdx.mapM fun (f, fi) => do
    let c := fnCtx p.abortFn p.growth areas fi f
    let rs ← c.slots.mapM fun r => do return (r, (← c.slotOff r) - (c.frame : Int))
    let mut labels : List (Node × String) := []
    let mut k := 0
    for b in f.blocks do
      labels := labels ++ [(.block b.label, ← c.blockLabel b.label)]
      for (ins, i) in b.insts.zipIdx do
        if c.maps && ins matches .call .. then
          labels := labels ++ [(.ret b.label i, c.local s!"sp{k}")]
        k := k + 1
      k := k + 1
    return { name := f.name, slots := rs, labels }

end Scc.Cert.Place.A64
