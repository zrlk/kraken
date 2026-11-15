/-
The canonical x64 loader's program reader: `textProgram`, the program of a
text's `.text` sections. Part of the trusted loader
(`Scc/Sem/TargetX64.lean` imports it). It is in a module of its own,
importing neither WeakCore nor Kraken's machine, so that
`scc --arch x64 --code`'s fragment check (`Scc/Cert/WideCheckX64.lean`)
reads the program by calling this definition. Do not import it together
with `Scc/Sem/TextA64.lean` (Kraken's AArch64 and x64 syntax cannot be
imported together).
-/
import Scc.Sem.TextRead
import Kraken.X64.Parser

namespace Scc.Sem.X64

/-- The cells of a data line of the `.text` sections (read by `dataLine`):
`.zero n` is one data cell (none for `n = 0`), each operand of `.quad` one
(a number, a label, or a difference `A - B` / `A - .`: `Kraken.DataImage.Item.quadDiff`);
a data cell is an empty `byteArray` whose size is its size-table entry
(code cells are not memory, so its contents are not loaded). A load from
the cell's address reads shared memory, not the cell
(`Kraken.Promising.X64.toEv`, `nonmem_load`), and the loader's initial
memory holds only `Λ.image` and `.rodata`, so the runtime's read of the word
is outside the model. `none`: not a `.zero` or `.quad` line;
`some (.error _)`: one the loader does not read. -/
def textData (t : String) : Option (Except String Program) :=
  let word := (t.splitOn " ").headD ""
  if word == ".zero" || word == ".quad" then
    some <| match dataLine t with
      | some is => .ok (is.flatMap fun
          | .zero 0 => []
          | .zero _ | .quad _ | .quadLabel _ | .quadDiff .. => [.byteArray (.mk #[])]
          | _ => [])
      | none => .error s!"unreadable data line in .text: {t}"
  else none

/-- **The program of a text's `.text` sections**: Kraken's parser on the
lines of `textSection`, directive lines dropped (`stripDirectives`), except
that an alignment directive (`.p2align k`, `.balign n`) becomes Kraken's
`nopalign` cell (`.align n`), whose size is the padding, and a `.zero` or
`.quad` line becomes data cells (`textData`), each sized by its entry. -/
def textProgram (asm : String) : Except String Program := do
  let parseChunk (ls : List String) : Except String Program :=
    Kraken.X64.Parser.parse (Kraken.X64.Parser.stripDirectives ("\n".intercalate ls.reverse))
  let alignOf (t : String) : Option Nat :=
    let ops := ((t.splitOn " ").filter (· ≠ "")).drop 1
    if t.startsWith ".p2align" then (ops.headD "").toNat?.map (2 ^ ·)
    else if t.startsWith ".balign" then (ops.headD "").toNat?
    else none
  let mut out : Program := []
  let mut cur : List String := []
  for l in (textSection asm).splitOn "\n" do
    let t := " ".intercalate ((l.trimAscii.toString.splitOn "\t").map (·.trimAscii.toString))
    match alignOf t, textData t with
    | some n, _ =>
        out := out ++ (← parseChunk cur) ++ (← Kraken.X64.Parser.parse s!".align {n}")
        cur := []
    | none, some cells =>
        out := out ++ (← parseChunk cur) ++ (← cells)
        cur := []
    | none, none => cur := l :: cur
  return out ++ (← parseChunk cur)

end Scc.Sem.X64
