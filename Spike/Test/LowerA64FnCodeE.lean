import Scc.Cert.PlaceDataA64
import Scc.Cert.PlaceOKA64
import Spike.Lib.Ret0Src

/-!
# `fnCodeOk` on scc's own AArch64 output

`Spike.Lib.LowerA64.fnCodeOk` (A9's code part, `Scc/Cert/PlaceOKA64.lean`)
evaluated on `Out.ofEmitted (lowerAll cfg ret0Src)`: the instruction list and
the IR both computed by scc's pipeline, no fixture. Since the P5 labels, the
body is read across the labels `bodyIn` steps over (each `addChk`'s
return label `x{n}`, the result's), at `bodyIn … entry 0 0`.
-/

namespace Spike.Test.LowerA64FnCodeE

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64

/-- scc's AArch64 output for `ret0.w` as `PlaceOK` reads it. -/
def ret0O : Out := Out.ofEmitted (Scc.Lower.A64.lowerAll { arch := .arm } Spike.Lib.Ret0Src.ret0Src)

/-- info: true -/
#guard_msgs in -- `wc_main`'s prologue, body (across its return labels) and overflow block in the output
#eval match ret0O.place.ir with
  | some ir => Spike.Lib.LowerA64.fnCodeOk ret0O.prog ir
  | none => false

/-- `wc_main`'s index, its one `addChk` and its result: `fnCodeOk` checks it
(not vacuous). -/
def wcMain? : Option (Nat × Scc.IR.Func × List Scc.IR.Inst × Scc.IR.Operand) := do
  let ir ← ret0O.place.ir
  let (f, i) ← ir.funcs.zipIdx.find? fun (f, _) => f.name == "wc_main"
  match f.params, f.checkStack, f.blocks with
  | [], true, [⟨"entry", is, .ret [w]⟩] => if is.all Spike.Lib.LowerA64.isAddChk then some (i, f, is, w) else none
  | _, _, _ => none

/-- info: some (18, 1) -/
#guard_msgs in -- `wc_main` is function 18 (after the runtime's), one `addChk` in its body
#eval wcMain?.map fun (i, _, is, _) => (i, is.length)

/-- info: true -/
#guard_msgs in -- the body alone, at `wc_main`'s context: the `addChk`, its return label `x0`, the result's `x1`
#eval match ret0O.place.ir, wcMain? with
  | some ir, some (i, f, is, w) =>
    let c := Scc.Emit.A64.fnCtx ir.abortFn ir.growth (Scc.IR.StackMap.argAreas ir Scc.Emit.A64.argRegs.length) i f
    Spike.Lib.LowerA64.bodyIn ret0O.prog c (c.prefix ++ "0_entry") 0 0 is [w]
  | _, _ => false

/-- info: true -/
#guard_msgs in -- A9 whole (with the phase part) on the output
#eval a9 ret0O (tablesOf Config.canonical ret0O)

end Spike.Test.LowerA64FnCodeE
