/-!
# Instruction sizes from the assembler

x64 instructions have variable lengths, chosen by the assembler. The
statement's x64 loader (`Scc.Sem.X64.target`) lays the code out at the sizes
a certificate gives (`Scc.Sem.X64.Asm`): one entry per instruction of the
text's `.text` sections in text order (an alignment directive's entry is its
padding), and the offsets of the text's labels. `sizesOf` reads both off
GNU `as`'s object file for the text:

* the text is assembled with `as --64 -L` (local labels kept in the symbol
  table), after a pair of labels `.Lscc_pad_s<i>` / `.Lscc_pad_e<i>` is put
  around each alignment directive (`.p2align`, `.balign`) and each data line
  of the granule pass (`.zero k` filler, `.quad` descriptor words;
  `Scc.Emit.Granule`) of a `.text` section, so that its bytes are `s .. e`;
* `objdump -d` gives the start offset of every decoded instruction of
  `.text` (those inside a marked range are the padding's `nop`s or data
  decoded as code, and are skipped), `objdump -h` the size of the section
  `.text` (not of other sections whose name starts with `.text`, such as the
  granule alignment's empty `.text.scc_galign`) and `objdump -t` the labels in
  `.text`;
* the cells are the instructions, paddings, fillers (none for an empty one)
  and words (one of 8 bytes per `.quad` operand) in address order, each as
  long as the distance to the next (the last to the end of the section).

Untrusted: the loader checks the table against the parsed program
(`Kraken.Promising.X64.sizedCells`, `SizeCheck`); a wrong table gives a
different layout, not an unsound one, and a table read off another assembly
would not describe the binary. This module imports no ISA.
-/

namespace Scc.Cert.Sizes

/-- Is `t` (a trimmed line) an alignment directive? -/
def isAlign (t : String) : Bool := t.startsWith ".p2align" || t.startsWith ".balign"

/-- What a marked line of a `.text` section is. -/
inductive Mark where
  /-- An alignment directive: one cell, its padding (which must be nonempty). -/
  | align
  /-- A `.zero k` filler: one cell, none if empty. -/
  | zero
  /-- A `.quad` line with `n` operands: `n` cells of 8 bytes. -/
  | quad (n : Nat)
  deriving BEq, Repr

/-- The mark of a trimmed line, if it is marked. -/
def markOf (t : String) : Option Mark :=
  if isAlign t then some .align
  else if t.startsWith ".zero " then some .zero
  else if t.startsWith ".quad " then some (.quad (t.splitOn ",").length)
  else none

/-- The text with labels around every alignment directive and granule data
line of its `.text` sections, and the marks of those lines in order. A line
starting `.text` opens a `.text` section, `.data`, `.bss`, `.rodata` or
`.section` another. -/
def markAligns (asm : String) : String × List Mark := Id.run do
  let mut out : Array String := #[]
  let mut inText := true
  let mut ms : Array Mark := #[]
  for l in asm.splitOn "\n" do
    let t := l.trimAscii.toString
    if t.startsWith ".text" then inText := true
    else if t.startsWith ".data" || t.startsWith ".bss" || t.startsWith ".rodata" ||
        t.startsWith ".section" then inText := false
    match inText, markOf t with
    | true, some m =>
      out := out.push s!".Lscc_pad_s{ms.size}:" |>.push l |>.push s!".Lscc_pad_e{ms.size}:"
      ms := ms.push m
    | _, _ => out := out.push l
  return ("\n".intercalate out.toList, ms.toList)

/-- The cell starts of the marked ranges `(s, e)` with their marks, or an error
for an alignment directive that pads nothing. -/
def markCells : List (Mark × Nat × Nat) → Except String (List Nat)
  | [] => .ok []
  | (m, s, e) :: rest => do
    let r ← markCells rest
    match m with
    | .align => if e ≤ s then throw "an alignment directive in .text pads nothing" else pure (s :: r)
    | .zero => pure (if e ≤ s then r else s :: r)
    | .quad n => pure ((List.range n).map (s + 8 * ·) ++ r)

/-- Run a command; its standard output, or an error with its standard error. -/
def runCmd (cmd : String) (args : Array String) : IO (Except String String) := do
  let o ← IO.Process.output { cmd, args }
  if o.exitCode == 0 then return .ok o.stdout
  else return .error s!"{cmd} {" ".intercalate args.toList}: {o.stderr}"

/-- A hexadecimal number. -/
def hex? (s : String) : Option Nat :=
  if s.isEmpty then none else
  s.toList.foldl (fun acc c => acc.bind fun a =>
    if c.isDigit then some (16 * a + (c.toNat - '0'.toNat))
    else if 'a' ≤ c && c ≤ 'f' then some (16 * a + (c.toNat - 'a'.toNat + 10))
    else none) (some 0)

/-- The instruction start offsets of an `objdump -d -w` listing. -/
def insnStarts (dis : String) : List Nat :=
  (dis.splitOn "\n").filterMap fun l =>
    match l.splitOn ":\t" with
    | a :: _ :: _ => hex? a.trimAscii.toString
    | _ => none

/-- The size of `.text` in an `objdump -h` listing. -/
def textSize (hdr : String) : Option Nat :=
  (hdr.splitOn "\n").findSome? fun l =>
    match (l.splitOn " ").filter (· ≠ "") with
    | _ :: ".text" :: sz :: _ => hex? sz
    | _ => none

/-- The labels in `.text` of an `objdump -t` listing (not the section
symbol), with their offsets. -/
def textSyms (tab : String) : List (String × Nat) :=
  (tab.splitOn "\n").filterMap fun l =>
    match l.splitOn "\t" with
    | [pre, post] =>
      let ws := (pre.splitOn " ").filter (· ≠ "")
      let name := ((post.splitOn " ").filter (· ≠ "")).getLast?.getD ""
      if ws.getLast? == some ".text" && !(ws.contains "d") && name != "" then
        (hex? (ws.headD "")).map (name, ·)
      else none
    | _ => none

/-- **The size table of an x64 text**: the size of every instruction and
alignment padding of its `.text` sections in text order, and the offset of
every label of the text in `.text`, from GNU `as` and `objdump` (see the
module docstring). The temporary files are `pre.s` and `pre.o`. -/
def sizesOf (pre : String) (asm : String) : IO (Except String (List Nat × List (String × Nat))) := do
  let (marked, marks) := markAligns asm
  let src : System.FilePath := pre ++ ".s"
  let obj : System.FilePath := pre ++ ".o"
  IO.FS.writeFile src marked
  let r ← ExceptT.run do
    let _ ← ExceptT.mk (runCmd "as" #["--64", "-L", "-o", obj.toString, src.toString])
    let dis ← ExceptT.mk (runCmd "objdump" #["-d", "-w", "--no-show-raw-insn", "-j", ".text", obj.toString])
    let hdr ← ExceptT.mk (runCmd "objdump" #["-h", obj.toString])
    let tab ← ExceptT.mk (runCmd "objdump" #["-t", obj.toString])
    let some size := textSize hdr | throw "objdump -h: no .text section"
    let syms := textSyms tab
    let pads := marks.zipIdx.map fun (m, k) =>
      (m, (syms.lookup s!".Lscc_pad_s{k}").getD 0, (syms.lookup s!".Lscc_pad_e{k}").getD 0)
    let padCells ← ExceptT.mk (pure (markCells pads))
    let starts := (insnStarts dis).filter fun a => !(pads.any fun (_, s, e) => s ≤ a && a < e)
    let cells := ((starts ++ padCells).mergeSort (· ≤ ·))
    let sizes := (cells.zip (cells.drop 1 ++ [size])).map fun (a, b) => b - a
    let labels := syms.filter fun (n, _) => !n.startsWith ".Lscc_pad_"
    pure (sizes, labels)
  try IO.FS.removeFile src catch _ => pure ()
  try IO.FS.removeFile obj catch _ => pure ()
  return r

#guard (markAligns "\t.text\n\tnop\n\t.p2align 4\n\t.zero 3\n\t.quad a, b\n\t.data\n\t.quad c\n\t.zero 1").2 ==
  [.align, .zero, .quad 2]
#guard (markAligns "\t.text\n\t.zero 3\n\t.section .text.scc_galign\n\t.p2align 16\n\t.text\n\t.quad d").2 ==
  [.zero, .quad 1]
#guard (markCells [(.align, 0, 3), (.zero, 3, 3), (.zero, 3, 8), (.quad 2, 8, 24)]).toOption == some [0, 3, 8, 16]
#guard (markCells [(.align, 3, 3)]).toOption.isNone

end Scc.Cert.Sizes
