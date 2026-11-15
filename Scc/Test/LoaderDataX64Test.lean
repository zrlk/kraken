import Scc.Sem.TargetX64

/-!
# Data lines in the x64 `.text`: what the loader reads

The granule pass puts data in `.text`: a granule word (`.quad L`) at the
end of each touched granule and before it a zero pad (`.zero k`). The
canonical loader (`Scc.Sem.X64.textProgram`, `textData`) reads `.zero n`
(`n > 0`) and each `.quad` operand as one data cell, an empty
`byteArray` whose size is its size-table entry (`sizedCells`; `SizeCheck`
asks that it be positive). Checked by evaluation:

- on the test texts under `Scc/Test/elf/` (no data lines in `.text`) the
  loader's program is the program of the parser without data lines
  (`oldProgram`, the loader before data lines);
- a granule end gives the expected cells, laid out at a size table with
  one entry per data cell, which passes `SizeCheck` with the label
  offsets of the layout;
- a data line the loader does not read is refused.
-/

namespace Scc.Test.LoaderDataX64

open Scc.Sem Scc.Sem.X64 Kraken.Promising.X64

/-- The test texts of x64 programs. -/
def fixtures : List String :=
  ["Scc/Test/elf/call1x64/call1.s", "Scc/Test/elf/frame0x64/frame0.s",
   "Scc/Test/elf/hello1x64/hello1.s", "Scc/Test/elf/hellox64/hello.s",
   "Scc/Test/elf/ret0x64/ret0.s", "Scc/Test/elf/ret0x64lld/ret0.s",
   "Scc/Test/elf/wakex64/wake.s"]

/-- The loader before data lines: Kraken's parser on the `.text` sections,
alignment directives as `nopalign` cells, other directive lines dropped. -/
def oldProgram (asm : String) : Except String Program := do
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
    match alignOf t with
    | some n =>
        out := out ++ (← parseChunk cur) ++ (← Kraken.X64.Parser.parse s!".align {n}")
        cur := []
    | none => cur := l :: cur
  return out ++ (← parseChunk cur)

/-- Whether the loader reads the same program from `asm` as the parser
without data lines (both parse it). -/
def sameAsOld (asm : String) : Bool :=
  match textProgram asm, oldProgram asm with
  | .ok p, .ok q => p == q
  | _, _ => false

/-- info: [true, true, true, true, true, true, true] -/
#guard_msgs in
#eval fixtures.mapM fun f => do return sameAsOld (← IO.FS.readFile f)

/-- A granule end: code, a pad, the granule word's label and word. -/
def granule : String :=
  ".text\nf:\n\tnop\n\t.zero 7\n.Lgw0:\n\t.quad scc_gc_desc - .\n\tret\n"

/-- The cells of `text`, as kinds, or the error. -/
def shape (text : String) : Except String (List String) :=
  (textProgram text).map fun p => p.map fun d =>
    match d with
    | .label l => l
    | .instr _ => "instr"
    | .byteArray b => s!"bytes{b.size}"

/-- info: Except.ok ["f", "instr", "bytes0", ".Lgw0", "bytes0", "instr"] -/
#guard_msgs in
#eval shape granule

-- `.zero 0` gives no cell; several `.quad` operands give one cell each.
/-- info: Except.ok ["instr", "bytes0", "bytes0"] -/
#guard_msgs in
#eval shape ".text\n\tnop\n\t.zero 0\n\t.quad a, 7\n"

-- Laid out at `as`'s sizes (`nop` 1, the pad 7, the word 8, `ret` 1) the
-- granule word sits at offset 8 and the cells pass `SizeCheck`; a table
-- missing the data entries does not fit.
#guard match cellsOf { text := granule, sizes := [1, 7, 8, 1] } with
  | some cells => SizeCheck (Int64.ofNat 0x401000) cells [("f", 0), (".Lgw0", 8)]
  | none => false
#guard (cellsOf { text := granule, sizes := [1, 1] }).isNone

-- A 64 KiB pad is one empty data cell: its size is the size-table entry,
-- so the cell's term does not grow with the pad's length.
def bigPad : String := ".text\nf:\n\tret\n\t.zero 65536\n.Lgw1:\n\t.quad scc_gc_desc - .\n"

/-- info: Except.ok ["f", "instr", "bytes0", ".Lgw1", "bytes0"] -/
#guard_msgs in
#eval shape bigPad

#guard match cellsOf { text := bigPad, sizes := [1, 65536, 8] } with
  | some cells => SizeCheck (Int64.ofNat 0x401000) cells [("f", 0), (".Lgw1", 65537)]
  | none => false

-- The laid-out pad, kernel-checked: the end of the code is a sum of sizes.
example : codeEnd 0x401000
    [(.label "f", 0), (.byteArray (.mk #[]), 65536), (.label ".Lgw1", 0),
     (.byteArray (.mk #[]), 8)]
    = 0x401000 + 65544 := by decide +kernel

example : (Directive.byteArray (.mk #[]), 65536) == (Directive.byteArray (.mk #[]), 65536) := by
  decide +kernel

-- The empty 64 KiB-aligned section after the last granule word (the
-- granule pass's alignment request) and the data sections after it give
-- no cells: `textSection` skips from `.section` to `.text`, so the program
-- and its size table are the granule's own.
def galignTail : String :=
  granule ++ "\t.section .text.scc_galign,\"ax\",@progbits\n\t.p2align 16\n\t.text\n" ++
    "\t.section .rodata\nmsg:\n\t.byte 104\n"

#guard (textProgram galignTail).toOption == (textProgram granule).toOption
#guard (textProgram galignTail).toOption.isSome
#guard match cellsOf { text := galignTail, sizes := [1, 7, 8, 1] } with
  | some cells => SizeCheck (Int64.ofNat 0x401000) cells [("f", 0), (".Lgw0", 8)]
  | none => false

-- A data line the loader does not read is refused: a negative count, an
-- expression operand other than a label difference `A - B` / `A - .`.
#guard (textProgram ".text\n\t.zero -1\n").toOption.isNone
#guard (textProgram ".text\n\t.quad a + 8\n").toOption.isNone
#guard (textProgram ".text\n\t.quad a-b\n").toOption.isNone
#guard (textProgram ".text\n\t.quad . - a\n").toOption.isNone
#guard (textProgram ".text\n\t.quad a - b - c\n").toOption.isNone

-- The self-relative granule word `A - .` and a label difference `A - B` are
-- one data cell each (`quadDiff`), as a `.quad L` is.
/-- info: Except.ok ["instr", "bytes0", "bytes0"] -/
#guard_msgs in
#eval shape ".text\n\tnop\n\t.quad scc_gc_desc - .\n\t.quad a - b\n"
#guard match textData ".quad scc_gc_desc - ." with
  | some (.ok [.byteArray b]) => b.size == 0
  | _ => false

end Scc.Test.LoaderDataX64
