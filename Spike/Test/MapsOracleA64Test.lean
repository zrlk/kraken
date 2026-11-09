import Spike.Test.MapsOracle
import Scc.Cert.MapsA64
import Scc.Emit.A64
import Scc.Frontend
import Scc.Lower.Program
import Scc.Test.Src

/-!
# `Scc.Cert.Maps.compute` against its `List.mergeSort` form on AArch64 texts (untrusted test)

The AArch64 twin of `Spike/Test/MapsOracleX64Test.lean`: the tables of the AArch64 texts of
`hello.w`, `hello1.w`, `ret0.w`, `call1.w` and `wake.w` (frontend, `Scc.Lower.lowerProgram`,
`Scc.Emit.A64.emitItems`) are the same under `compute` (structural `sortStable`) and under
`Scc.Cert.MapsOracle.computeOracle` (the old form, on `List.mergeSort`).
-/

namespace Scc.Cert.MapsOracleA64Test
open Scc.Cert.Maps Scc.Cert.MapsA64 Scc.Cert.MapsOracle

/-- The AArch64 IR and items of a WeakCore source. -/
def compileW (src : String) : Except String (IR.Program × List Scc.Emit.A64.Item) := do
  let c ← match Frontend.run src with
    | .ok c => pure c
    | .error ds => throw (String.intercalate "\n" (ds.map (·.render "input")))
  let ir ← Lower.lowerProgram { arch := .arm } c
  pure (ir, ← Scc.Emit.A64.emitItems ir)

/-- Whether the tables compute on the text, and whether both computations agree on it. -/
def agreesW (src : String) : Except String (Bool × Bool) := do
  let (p, its) ← compileW src
  let areas ← Scc.Emit.A64.emitPre p
  let items ← itemsOf its
  let tbl ← stackTable its items
  let fns ← p.funcs.zipIdx.mapM (tagsOf p areas items tbl)
  pure ((compute fns items).toOption.isSome, agrees fns items)

/-- Both computations succeed on the text and agree. -/
def okW (src : String) : Bool :=
  match agreesW src with
  | .ok (c, a) => c && a
  | .error _ => false

#guard okW (w_src% "Scc/Test/hello.w")
#guard okW (w_src% "Scc/Test/hello1.w")
#guard okW (w_src% "Scc/Test/ret0.w")
#guard okW (w_src% "Scc/Test/call1.w")
#guard okW (w_src% "Scc/Test/wake.w")

/-- How many old leaders the label-keyed rules drop on a text (`droppedCount`). -/
def droppedW (src : String) : Nat :=
  match (do
    let (p, its) ← compileW src
    let areas ← Scc.Emit.A64.emitPre p
    let items ← itemsOf its
    let tbl ← stackTable its items
    let fns ← p.funcs.zipIdx.mapM (tagsOf p areas items tbl)
    pure (droppedCount fns items) : Except String Nat) with
  | .ok n => n
  | .error _ => 0

-- The dropped-leader rules are exercised.
#guard droppedW (w_src% "Scc/Test/hello1.w") + droppedW (w_src% "Scc/Test/wake.w") > 0

end Scc.Cert.MapsOracleA64Test
