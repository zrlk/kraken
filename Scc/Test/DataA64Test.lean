import Scc.Frontend
import Scc.Lower.Program
import Scc.Emit.A64
import Scc.Sem.Target
import Scc.Test.Src

/-!
# The AArch64 emitter's data sections against the statement's reading

The AArch64 emitter gives its data sections as `Kraken.DataImage` items
(`Scc.Emit.A64.dataSecs`) next to the text it writes; the statement's
loader reads them back from the text (`Scc.Sem.dataSections`). `agree`
checks, for a program, that the two coincide section by section: the
loader's `.rodata` image (`Scc.Sem.rodataWords`) is the one the emitter
meant.
-/

namespace Scc.Test.DataA64
open Scc

/-- Frontend, lowering (the default configuration, `--arch arm`), and both emitter
outputs; whether the text's data sections read back as the emitter's items. -/
def agree (src : String) : Except String Bool := do
  let c ← match Frontend.run src with
    | .ok c => pure c
    | .error ds => throw (String.intercalate "\n" (ds.map (·.render "input")))
  let ir ← Lower.lowerProgram { arch := .arm } c
  let text ← Emit.A64.emitProgram ir
  let s ← Emit.A64.dataSecs ir
  match Sem.dataSections text with
  | some d => pure (d.data == s.data && d.bss == s.bss && d.rodata == s.rodata)
  | none => throw "the text's data sections do not read back"

/-- info: Except.ok true -/
#guard_msgs in #eval agree (w_src% "Scc/Test/hello.w")

/-- info: Except.ok true -/
#guard_msgs in #eval agree (w_src% "Scc/Test/handoff.w")

/-- info: Except.ok true -/
#guard_msgs in #eval agree (w_src% "Scc/Test/growmany.w")

/-- info: Except.ok true -/
#guard_msgs in #eval agree (w_src% "Scc/Test/layout.w")

end Scc.Test.DataA64
