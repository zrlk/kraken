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
  around each alignment directive (`.p2align`, `.balign`) of a `.text`
  section, so that its padding is `e − s`;
* `objdump -d` gives the start offset of every decoded instruction of
  `.text` (those inside a padding are the padding's `nop`s and are skipped),
  `objdump -h` the section's size and `objdump -t` the labels in `.text`;
* the cells are the instructions and paddings in address order, each as long
  as the distance to the next (the last to the end of the section).

Untrusted: the loader checks the table against the parsed program
(`Kraken.Promising.X64.sizedCells`, `SizeCheck`); a wrong table gives a
different layout, not an unsound one, and a table read off another assembly
would not describe the binary. This module imports no ISA.
-/

namespace Scc.Cert.Sizes

/-- Is `t` (a trimmed line) an alignment directive? -/
def isAlign (t : String) : Bool := t.startsWith ".p2align" || t.startsWith ".balign"

/-- The text with labels around every alignment directive of its `.text`
sections, and the number of such directives. A line starting `.text` opens
a `.text` section, `.data`, `.bss`, `.rodata` or `.section` another. -/
def markAligns (asm : String) : String × Nat := Id.run do
  let mut out : Array String := #[]
  let mut inText := true
  let mut k := 0
  for l in asm.splitOn "\n" do
    let t := l.trimAscii.toString
    if t.startsWith ".text" then inText := true
    else if t.startsWith ".data" || t.startsWith ".bss" || t.startsWith ".rodata" ||
        t.startsWith ".section" then inText := false
    if inText && isAlign t then
      out := out.push s!".Lscc_pad_s{k}:" |>.push l |>.push s!".Lscc_pad_e{k}:"
      k := k + 1
    else out := out.push l
  return ("\n".intercalate out.toList, k)

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
  let (marked, npads) := markAligns asm
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
    let pads := (List.range npads).map fun k =>
      ((syms.lookup s!".Lscc_pad_s{k}").getD 0, (syms.lookup s!".Lscc_pad_e{k}").getD 0)
    if pads.any fun (s, e) => e ≤ s then throw "an alignment directive in .text pads nothing"
    let starts := (insnStarts dis).filter fun a => !(pads.any fun (s, e) => s ≤ a && a < e)
    let cells := ((starts ++ pads.map (·.1)).mergeSort (· ≤ ·))
    let sizes := (cells.zip (cells.drop 1 ++ [size])).map fun (a, b) => b - a
    let labels := syms.filter fun (n, _) => !n.startsWith ".Lscc_pad_"
    pure (sizes, labels)
  try IO.FS.removeFile src catch _ => pure ()
  try IO.FS.removeFile obj catch _ => pure ()
  return r

end Scc.Cert.Sizes
