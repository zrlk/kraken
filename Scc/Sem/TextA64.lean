/-
The canonical AArch64 loader's program reader: `textProgram`, the program
of a text's `.text` sections. Part of the trusted loader
(`Scc/Sem/TargetA64.lean` imports it). It is in a module of its own,
importing neither WeakCore nor Kraken's machine, so that `scc --code`'s
fragment check (`Scc/Cert/WideCheckA64.lean`) reads the program by calling
this definition. Do not import it together with `Scc/Sem/TextX64.lean`
(Kraken's AArch64 and x64 syntax cannot be imported together).
-/
import Scc.Sem.TextRead
import Kraken.AArch64.Parser

namespace Scc.Sem.A64

/-- The cells of a data line of the `.text` sections (read by `dataLine`):
`.zero n` is one `zeros n` cell (none for `n = 0`), each operand of `.quad`
(a number, a label, or a difference `A - B` / `A - .`:
`Kraken.DataImage.Item.quadDiff`) an 8-byte data cell of zeros (`byteArray`; the word's value is not loaded:
code cells are not memory). A load from the word's address reads shared
memory, not the cell (`Kraken.Promising.AArch64.toEv`, `nonmem_load`), and
the loader's initial memory holds only `Λ.image` and `.rodata`, so the
runtime's read of the word is outside the model. `none`: not a `.zero` or
`.quad` line; `some (.error _)`: one the loader does not read. -/
def textData (t : String) : Option (Except String Program) :=
  let word := (t.splitOn " ").headD ""
  if word == ".zero" || word == ".quad" then
    some <| match dataLine t with
      | some is => .ok (is.flatMap fun
          | .zero 0 => []
          | .zero n => [.zeros n]
          | .quad _ | .quadLabel _ | .quadDiff .. => [.byteArray ⟨Array.replicate 8 0⟩]
          | _ => [])
      | none => .error s!"unreadable data line in .text: {t}"
  else none

/-- The alignment of an alignment line of the `.text` sections (`.p2align k`,
`.balign n`, read by `dataLine`). `none`: not an alignment line;
`some (.error _)`: one the loader does not read. -/
def textAlign (t : String) : Option (Except String Nat) :=
  let word := (t.splitOn " ").headD ""
  if word == ".p2align" || word == ".balign" then
    some <| match dataLine t with
      | some [.align a] => .ok a
      | _ => .error s!"unreadable alignment line in .text: {t}"
  else none

/-- The bytes a cell occupies in the AArch64 layout (`Directive.fakeSize`,
restated here so that this module does not import Kraken's semantics): 4
per instruction, none per label, a data cell's length. -/
def cellBytes : Directive → Nat
  | .instr _ => 4
  | .label _ => 0
  | .byteArray bs => bs.size
  | .zeros n => n

/-- Whether an alignment line of alignment `a` at offset `o` from the start
of the text pads nothing: `a` is a power of two dividing `o`, and either
`a ≤ 4` (the text's start is at least 16-aligned) or `o = 0` and
`a ≤ 2 ^ 16` (the `.p2align 4` opening `.text`; the link pins the text's
start at a 64 KiB boundary). -/
def padFree (o a : Nat) : Bool :=
  0 < a && a &&& (a - 1) == 0 && o % a == 0 && (a ≤ 4 || (o == 0 && a ≤ 2 ^ 16))

/-- The symbol and assembler directives the `.text` sections may carry,
none of which emits bytes: `.globl`, `.local` (symbol binding), `.type`,
`.size` (symbol attributes in the symbol table), `.arch` (the instruction
set the assembler accepts; the emitter's `.arch armv8.4-a`). -/
def symbolDirectives : List String := [".globl", ".local", ".type", ".size", ".arch"]

/-- The program of a text's `.text` sections. Each line of `textSection`
is one of:
- a label (`name:`), an instruction, a comment or blank: given to Kraken's
  parser (with the other such lines up to the next directive);
- a data line `.zero n` / `.quad …`: data cells (`textData`);
- an alignment line `.p2align k` / `.balign n` that pads nothing at its
  offset (`padFree`; the offset is the size of the cells before it, each
  `cellBytes`): no cell (the loader has no alignment cell for AArch64);
- a `symbolDirectives` line: no cell.
Any other line starting with `.` (say `.skip`, `.align`, `.byte`, `.word`,
`.inst`, `.fill`, `.space`, `.ascii`, `.org`, a CFI directive, an unknown
directive, or a label followed by more text) refuses the text: Kraken's
`stripDirectives` would drop it without a cell. Section switches are
`textSection`'s. AArch64 instructions are 4 bytes, so `.p2align 2` after
instructions pads nothing. -/
def textProgram (asm : String) : Except String Program := do
  let parseChunk (ls : List String) : Except String Program :=
    Kraken.AArch64.Parser.parse (Kraken.AArch64.Parser.stripDirectives ("\n".intercalate ls.reverse))
  let mut out : Program := []
  let mut cur : List String := []
  for l in (textSection asm).splitOn "\n" do
    let t := " ".intercalate ((l.trimAscii.toString.splitOn "\t").map (·.trimAscii.toString))
    let word := (t.splitOn " ").headD ""
    match textData t, textAlign t with
    | some cells, _ =>
        out := out ++ (← parseChunk cur) ++ (← cells)
        cur := []
    | none, some a? =>
        let a ← a?
        out := out ++ (← parseChunk cur)
        cur := []
        let o := (out.map cellBytes).sum
        unless padFree o a do
          throw s!"alignment line in .text would pad (offset {o}, alignment {a}): {t}"
    | none, none =>
        if t.startsWith "." && !(t.endsWith ":" && isSym (t.dropEnd 1).toString) then
          unless symbolDirectives.contains word do
            throw s!"directive the loader does not read in .text: {t}"
        else cur := l :: cur
  return out ++ (← parseChunk cur)

end Scc.Sem.A64
