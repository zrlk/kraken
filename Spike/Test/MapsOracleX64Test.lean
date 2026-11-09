import Spike.Test.MapsOracle
import Scc.Cert.MapsX64
import Scc.Emit.X64
import Scc.Frontend
import Scc.Lower.Program
import Scc.Test.Src

/-!
# `Scc.Cert.Maps.compute` against its `List.mergeSort` form on x64 texts (untrusted test)

The tables of the x86-64 texts of `hello.w`, `hello1.w`, `ret0.w`, `call1.w` and `wake.w`
(frontend, `Scc.Lower.lowerProgram`, `Scc.Emit.X64.emitItems`) are the same under `compute`
(structural `sortStable`) and under `Scc.Cert.MapsOracle.computeOracle` (the old form, on
`List.mergeSort`). The instruction sizes are all 1: only the addresses depend on them, and the
comparison is the same for any sizes (the real sizes of `hello1.w` are compared in
`Spike/Test/MapsX64Test.lean`).
-/

namespace Scc.Cert.MapsOracleX64Test
open Scc.Cert.Maps Scc.Cert.MapsX64 Scc.Cert.MapsOracle

/-- The x64 IR and items of a WeakCore source. -/
def compileW (src : String) : Except String (IR.Program × List Scc.Emit.X64.Item) := do
  let c ← match Frontend.run src with
    | .ok c => pure c
    | .error ds => throw (String.intercalate "\n" (ds.map (·.render "input")))
  let ir ← Lower.lowerProgram { arch := .x64 } c
  pure (ir, ← Scc.Emit.X64.emitItems ir)

/-- The number of instructions of the text (up to the first section switch). -/
def insCount : List Scc.Emit.X64.Item → Nat
  | [] => 0
  | .dir s :: rest => if endsText s then 0 else insCount rest
  | .d (.label _) :: rest => insCount rest
  | .d _ :: rest => insCount rest + 1
  | _ :: rest => insCount rest

/-- The tagged functions and items of a text (sizes all 1), and whether both computations agree
on them; also whether the tables compute at all. -/
def agreesW (src : String) : Except String (Bool × Bool) := do
  let (p, its) ← compileW src
  let sizes := List.replicate (insCount its) 1
  let items ← itemsOf its sizes
  let tbl ← stackTable its items
  let fns ← p.funcs.mapM (tagsOf p items tbl)
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
    let sizes := List.replicate (insCount its) 1
    let items ← itemsOf its sizes
    let tbl ← stackTable its items
    let fns ← p.funcs.mapM (tagsOf p items tbl)
    pure (droppedCount fns items) : Except String Nat) with
  | .ok n => n
  | .error _ => 0

-- The dropped-leader rules are exercised.
#guard droppedW (w_src% "Scc/Test/hello1.w") + droppedW (w_src% "Scc/Test/wake.w") > 0

end Scc.Cert.MapsOracleX64Test
