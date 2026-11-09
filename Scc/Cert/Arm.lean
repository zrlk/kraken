import Scc.Frontend
import Scc.Lower.Program
import Scc.Lower.Spec1
import Scc.Lower.SpecA64
import Scc.Emit.A64
import Kraken.Promising.Lower.Lowerable

/-!
# Certificate support for AArch64

What an AArch64 certificate (`Scc.Cert.Gen`) uses: `compile`, the pipeline
`scc` runs (frontend, lowering, AArch64 emitter), for the reproducibility
check; and `Scc.Emit.A64.reparse`, Kraken's AArch64 parser after
`stripDirectives`, with the elaborator `scc_arm_reparse%` that runs it at
elaboration time and returns the parsed `Program` as a literal, so that
`decide +kernel` can check Kraken's `Program.WCLowerable` of it. Every
instruction the emitter writes, `svc` and `mrs`/`msr` of `TPIDR_EL0`
included, is a Kraken instruction and part of the parsed program; only
assembler directive lines are dropped.
-/

namespace Scc.Cert.Arm

open Scc

/-- The pipeline of `scc --arch arm` on a source text: the lowering (`Lower.lowerIR`), the
emission at the configuration's GC witness (`Lower.A64.emitAll`) and its text with the GC
tables' items (`Lower.A64.Emitted.listing`, which refuses where the tables' stage fails). -/
def compile (cfg : Config) (src : String) : Except String String := do
  let c ← match Frontend.run src with
    | .ok c => pure c
    | .error ds => throw (String.intercalate "\n" (ds.map (·.render "input")))
  let l ← Lower.lowerIR cfg c.prog
  let e ← Lower.A64.emitAll l cfg.gcWit
  return (← e.listing).text

/-- **The GC tables' ranked witness scc computes** for a source text: `Scc.Cert.MapsA64.gcWitness`
on the lowering and the emitter's items at `cfg` (whose own witness it does not read). The
witness a certificate puts in its configuration (untrusted: `emitTablesW` refuses it unless
every function's entry is its least fixpoint). -/
def gcWitOf (cfg : Config) (src : String) : Except String Scc.Cert.Maps.GcWit := do
  let c ← match Frontend.run src with
    | .ok c => pure c
    | .error ds => throw (String.intercalate "\n" (ds.map (·.render "input")))
  let l ← Lower.lowerIR cfg c.prog
  let (its, _) ← Emit.A64.emitItemsMaps l.ir
  Scc.Cert.MapsA64.gcWitness l.ir its

/-- The reproducibility check: `src` compiles to exactly `asm`. -/
def reproduces (cfg : Config) (src asm : String) : Bool :=
  match compile cfg src with
  | .ok t => t == asm
  | .error _ => false

open Lean Elab Term Meta in
/-- `scc_arm_reparse% c`, `c` a string constant: run Kraken's AArch64 parser
(after `stripDirectives`) on its value at elaboration time and return the
parsed `Program` as a literal. -/
elab "scc_arm_reparse% " id:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let text ← unsafe evalConst String n
  match Emit.A64.reparse text with
  | .ok p => return toExpr p
  | .error msg => throwError "Kraken's AArch64 parser rejects the text: {msg}"

end Scc.Cert.Arm
