import Scc.Sem.TargetA64

/-!
# Lines of the AArch64 `.text`: only those the loader models

The AArch64 loader reads a `.text` line as an instruction, a label, a data
cell, a symbol directive or an alignment line that pads nothing
(`Scc.Sem.A64.textProgram`); any other directive refuses the text.
Checked by evaluation:

- on the test texts under `Scc/Test/elf/` (`.arch`, `.globl`, `.type`, a
  `.p2align 4` opening `.text`, `.p2align 2` between functions) the program
  is the one the loader read before the check (`oldProgram`);
- the granule pass's tail (an empty 64 KiB-aligned section, then `.text`)
  gives no cell;
- a `.p2align 4` after an odd number of instructions, a `.balign 8` after
  one, a `.p2align 3` after a 12-byte pad, and any alignment above 4 bytes
  past offset 0 are refused; `.p2align 2` after instructions and a
  `.p2align 4` after labels at offset 0 are not;
- `.skip`, `.align`, `.byte`, `.inst`, `.word`, `.fill`, `.cfi_startproc`
  and an unknown directive are refused.
-/

namespace Scc.Test.LoaderAlignA64

open Scc.Sem Scc.Sem.A64 Kraken.Promising.AArch64

/-- The test texts of AArch64 programs. -/
def fixtures : List String :=
  ["Scc/Test/elf/call1a64/call1.s", "Scc/Test/elf/hello1a64/hello1.s",
   "Scc/Test/elf/helloa64/hello.s", "Scc/Test/elf/ret0a64/ret0.s",
   "Scc/Test/elf/wakea64/wake.s"]

/-- The loader before data lines and the line check: Kraken's parser on the
`.text` sections, directive lines dropped. -/
def oldProgram (asm : String) : Except String Program :=
  Kraken.AArch64.Parser.parse (Kraken.AArch64.Parser.stripDirectives (textSection asm))

/-- Whether the loader reads the same program from `asm` as before (both
parse it). -/
def sameAsOld (asm : String) : Bool :=
  match textProgram asm, oldProgram asm with
  | .ok p, .ok q => p == q
  | _, _ => false

/-- info: [true, true, true, true, true] -/
#guard_msgs in
#eval fixtures.mapM fun f => do return sameAsOld (← IO.FS.readFile f)

/-- Whether the loader accepts `asm`. -/
def loads (asm : String) : Bool := (textProgram asm).toOption.isSome

/-- A text as the granule pass ends it: code, a pad, a granule word, the
empty 64 KiB-aligned section, `.text` again, then `.rodata`. -/
def galignTail : String :=
  ".text\n\t.globl _start\n\t.p2align 4\n_start:\n\tnop\n\tret\n\t.zero 12\n.Lgw0:\n" ++
  "\t.quad scc_gc_desc - .\n\t.section .text.scc_galign,\"ax\",%progbits\n\t.p2align 16\n" ++
  "\t.text\n\t.section .rodata\n\t.balign 8\nscc_gc_desc:\n\t.quad _start\n"

-- The tail gives no cell: the program is the code's.
#guard ((textProgram galignTail).map (·.length)).toOption == some 6
#guard (textProgram galignTail).toOption ==
  (textProgram (".text\n\t.globl _start\n\t.p2align 4\n_start:\n\tnop\n\tret\n\t.zero 12\n.Lgw0:\n" ++
    "\t.quad scc_gc_desc - .\n")).toOption

-- Refused: a `.p2align 4` after three instructions (offset 12).
/-- info: Except.error "alignment line in .text would pad (offset 12, alignment 16): .p2align 4" -/
#guard_msgs in
#eval (textProgram ".text\n\t.p2align 4\nf:\n\tnop\n\tnop\n\tnop\n\t.p2align 4\ng:\n\tret\n").map (·.length)
#guard !loads ".text\n\tnop\n\t.balign 8\n\tret\n"
#guard !loads ".text\n\t.zero 12\n\t.p2align 3\n\tret\n"
-- A 16-byte alignment above offset 0 is refused even where it pads nothing
-- (the text's base is only known to be 16-aligned at offset 0).
#guard !loads ".text\n\tnop\n\tnop\n\tnop\n\tnop\n\t.p2align 4\n\tret\n"
-- Accepted: `.p2align 2` after instructions and data, `.p2align 4` at
-- offset 0 after labels and symbol directives.
#guard loads ".text\n\t.globl _start\n_start:\n\t.p2align 4\n\tnop\n\t.p2align 2\n\tret\n"
#guard loads ".text\n\t.p2align 4\n\tnop\n\t.zero 4\n\t.p2align 2\n\tret\n"
-- An unreadable alignment line is refused.
#guard !loads ".text\n\t.p2align x\n\tret\n"

-- Directives that emit bytes, or that the loader does not know, are refused.
/-- info: Except.error "directive the loader does not read in .text: .skip 4" -/
#guard_msgs in
#eval (textProgram ".text\n\tnop\n\t.skip 4\n\tret\n").map (·.length)
#guard !loads ".text\n\tnop\n\t.align 4\n\tret\n"
#guard !loads ".text\n\tnop\n\t.byte 1, 2, 3, 4\n\tret\n"
#guard !loads ".text\n\tnop\n\t.inst 0xd503201f\n\tret\n"
#guard !loads ".text\n\tnop\n\t.word 0\n\tret\n"
#guard !loads ".text\n\tnop\n\t.fill 4, 1, 0\n\tret\n"
#guard !loads ".text\n\tnop\n\t.cfi_startproc\n\tret\n"
#guard !loads ".text\n\tnop\n\t.frobnicate\n\tret\n"
-- The symbol directives are accepted.
#guard loads ".text\n\t.arch armv8.4-a\n\t.globl f\n\t.local g\n\t.type f, %function\nf:\n\tret\n\t.size f, 4\n"

end Scc.Test.LoaderAlignA64
