import Scc.Sem.TargetA64
import Scc.Emit.A64Print

/-!
# Data lines in the AArch64 `.text`: what the loader reads

The granule pass puts data in `.text`: a granule word (`.quad L`) at the
end of each touched granule and before it a zero pad (`.zero k`). The
canonical loader (`Scc.Sem.A64.textProgram`, `textData`) reads `.zero n`
as one `Directive.zeros n` cell (none for `n = 0`) and each `.quad`
operand as an 8-byte `byteArray` cell; their sizes (`Directive.fakeSize`)
are `n` and `8`. Checked by evaluation:

- on the test texts under `Scc/Test/elf/` (no data lines in `.text`) the
  loader's program is the program of the parser without data lines
  (`oldProgram`, the loader before data lines);
- a granule end and a 64 KiB pad give the expected cells and sizes, and
  a pad's size is a kernel-checked `decide` whatever its length (the cell
  holds the count, not the bytes);
- a data line the loader does not read is refused.
-/

namespace Scc.Test.LoaderDataA64

open Scc.Sem Scc.Sem.A64 Kraken.Promising.AArch64

/-- The test texts of AArch64 programs. -/
def fixtures : List String :=
  ["Scc/Test/elf/call1a64/call1.s", "Scc/Test/elf/hello1a64/hello1.s",
   "Scc/Test/elf/helloa64/hello.s", "Scc/Test/elf/ret0a64/ret0.s",
   "Scc/Test/elf/wakea64/wake.s"]

/-- The loader before data lines: Kraken's parser on the `.text` sections,
directive lines dropped. -/
def oldProgram (asm : String) : Except String Program :=
  Kraken.AArch64.Parser.parse (Kraken.AArch64.Parser.stripDirectives (textSection asm))

/-- Whether the loader reads the same program from `asm` as the parser
without data lines (both parse it). -/
def sameAsOld (asm : String) : Bool :=
  match textProgram asm, oldProgram asm with
  | .ok p, .ok q => p == q
  | _, _ => false

/-- info: [true, true, true, true, true] -/
#guard_msgs in
#eval fixtures.mapM fun f => do return sameAsOld (← IO.FS.readFile f)

/-- A granule end: code, a pad, the granule word's label and word. -/
def granule : String :=
  ".text\nf:\n\tnop\n\t.zero 12\n.Lgw0:\n\t.quad scc_gc_desc - .\n\tret\n"

/-- The cells of `text` as `(kind, fakeSize)`, or the error. -/
def shape (text : String) : Except String (List (String × Nat)) :=
  (textProgram text).map fun p => p.map fun d =>
    (match d with
     | .label l => l | .instr _ => "instr" | .byteArray _ => "bytes" | .zeros _ => "zeros",
     d.fakeSize)

/-- info: Except.ok [("f", 0), ("instr", 4), ("zeros", 12), (".Lgw0", 0), ("bytes", 8), ("instr", 4)] -/
#guard_msgs in
#eval shape granule

-- The cells themselves: `.zero 12` is `zeros 12`, the word 8 zero bytes.
#guard match textProgram granule with
  | .ok [_, _, .zeros 12, .label ".Lgw0", .byteArray b, _] => b.toList == List.replicate 8 0
  | _ => false

-- `.zero 0` gives no cell; several `.quad` operands give one cell each.
/-- info: Except.ok [("instr", 4), ("bytes", 8), ("bytes", 8)] -/
#guard_msgs in
#eval shape ".text\n\tnop\n\t.zero 0\n\t.quad a, 7\n"

-- The end-of-text pad (`.zero N`, about 59 KiB) and the last granule
-- word: one cell of size `N`.
/-- info: Except.ok [("instr", 4), ("zeros", 65536), (".Lgw1", 0), ("bytes", 8)] -/
#guard_msgs in
#eval shape ".text\n\tret\n\t.zero 65536\n.Lgw1:\n\t.quad scc_gc_desc - .\n"

-- A data line the loader does not read is refused: a negative count, an
-- expression operand other than a label difference `A - B` / `A - .`.
#guard (textProgram ".text\n\t.zero -1\n").toOption.isNone
#guard (textProgram ".text\n\t.quad a + 8\n").toOption.isNone
#guard (textProgram ".text\n\t.quad a-b\n").toOption.isNone
#guard (textProgram ".text\n\t.quad . - a\n").toOption.isNone
#guard (textProgram ".text\n\t.quad a - b - c\n").toOption.isNone

-- The self-relative granule word `A - .` and a label difference `A - B` are
-- one data cell each (`quadDiff`), 8 zero bytes, as a `.quad L` is.
/-- info: Except.ok [("instr", 4), ("bytes", 8), ("bytes", 8)] -/
#guard_msgs in
#eval shape ".text\n\tnop\n\t.quad scc_gc_desc - .\n\t.quad a - b\n"
#guard match textData ".quad scc_gc_desc - ." with
  | some (.ok [.byteArray b]) => b.toList == List.replicate 8 0
  | _ => false

/-! ## The printer's pad reads back

The emitter's `render` (`Scc/Emit/A64Print.lean`) refuses a `.d (.zeros _)`
item (`Item.ok`, as for `byteArray`), so the emitter writes the pad and the
granule word as raw lines (`.raw ".zero k"`, `.raw ".quad scc_gc_desc - ."`),
the label as a label item. The loader reads `render`'s text back to the
pad cell and the word's 8-byte cell. `ppDirective` prints a `zeros n` cell
as the same `.zero n` line. -/

open Scc.Emit.A64 in
/-- A granule end as the emitter's items. -/
def granuleItems : List Item :=
  [.raw ".text", .d (.label "f"), .d (.instr ⟨.W64, .NOP⟩), .raw ".zero 12", .d (.label ".Lgw0"),
   .raw ".quad scc_gc_desc - .", .d (.instr ⟨.W64, .NOP⟩)]

open Scc.Emit.A64 in
#guard match render granuleItems with
  | .ok text =>
    match textProgram text with
    | .ok [.label "f", .instr i, .zeros 12, .label ".Lgw0", .byteArray b, .instr j] =>
      i == ⟨.W64, .NOP⟩ && j == ⟨.W64, .NOP⟩ && b.toList == List.replicate 8 0
    | _ => false
  | .error _ => false

-- `render` refuses a pad as a directive item.
open Scc.Emit.A64 in
#guard (render [.d (.zeros 12)]).toOption.isNone

open Scc.Emit.A64 in
#guard Item.render (.raw ".zero 59000") == ppDirective (.zeros 59000)

/-! ## The cost of a pad does not grow with its length

`Directive.zeros n` holds the count: its size is `n` by one `match`, so the
kernel checks a 64 KiB pad, and the end of a program holding one, in the
time it checks a 4-byte one. -/

example : (Directive.zeros 65536).fakeSize = 65536 := by decide +kernel

example : codeEnd 0x210000
    [.label "f", .instr ⟨.W64, .NOP⟩, .zeros 65536, .label ".Lgw1", .byteArray ⟨Array.replicate 8 0⟩]
    = 0x210000 + 65548 := by decide +kernel

example : (Directive.zeros 65536 == Directive.zeros 65536) = true := by decide +kernel

end Scc.Test.LoaderDataA64
