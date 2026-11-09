import Scc.Frontend
import Scc.Lower.Program
import Scc.Emit.X64
import Scc.Sem.Target
import Scc.Test.Src

/-!
# The x64 emitter's data sections against the statement's reading

The x64 emitter gives its data sections as `Kraken.DataImage` items
(`Scc.Emit.X64.dataSecs`) next to the text it writes; the statement's
loader reads them back from the text (`Scc.Sem.dataSections`). `agree`
checks, for a program, that the two coincide section by section: the
loader's `.rodata` image (`Scc.Sem.rodataWords`) is the one the emitter
meant.
-/

namespace Scc.Test.DataX64
open Scc

/-- Frontend, lowering (the default configuration), and both emitter
outputs; whether the text's data sections read back as the emitter's items. -/
def agree (src : String) : Except String Bool := do
  let c ← match Frontend.run src with
    | .ok c => pure c
    | .error ds => throw (String.intercalate "\n" (ds.map (·.render "input")))
  let ir ← Lower.lowerProgram {} c
  let text ← Emit.X64.emit ir
  let s ← Emit.X64.dataSecs ir
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

-- Difference words (the GC tables' position-independent words): `.quad A - B` and
-- `.quad A - .` read as `quadDiff`, `.` only as `B`; other shapes are refused.
#guard Sem.dataLine ".quad scc_gc_desc - ." == some [.quadDiff "scc_gc_desc" none]
#guard Sem.dataLine ".quad .Lf.ret - scc_text_start, 3" ==
  some [.quadDiff ".Lf.ret" (some "scc_text_start"), .quad 3]
#guard [".quad . - a", ".quad a - 3", ".quad a-b", ".quad a -  b", ".quad a - b - c", ".quad a + b"].all
  (Sem.dataLine · == none)
-- Their bytes: the difference modulo `2 ^ 64`, from the word's own address for `.`.
#guard (let items : List Kraken.DataImage.Item :=
    [.label "d", .quad 7, .quadDiff "d" none, .quadDiff "c" (some "d"), .quadDiff "d" (some "c")]
  let res := Kraken.DataImage.resolve (fun l => if l == "c" then 0x1000 else 0) 0x2000 items
  let img := Kraken.DataImage.image res 0x2000 items
  (List.range 4).map (fun i => Int.ofBytes ((img.drop (8 * i)).take 8)) ==
    [7, 2 ^ 64 - 8, 2 ^ 64 - 0x1000, 0x1000])

end Scc.Test.DataX64
