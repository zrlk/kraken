import Scc.Lower.Spec
import Scc.Emit.X64

/-!
# scc's pipeline as one function, x86-64

The x86-64 twin of `Scc/Lower/SpecA64.lean`. `lowerAll cfg p`: scc's x86-64
pipeline from a checked WeakCore program to its output at the level of
Kraken's syntax, as one total function the kernel reduces: the lowering to
the IR (`lowerIR`), the emitter's items (`Scc.Emit.X64.emitItemsMaps`), and
from them

* `prog`, the instruction list: the items of the `.text` sections, an
  alignment directive (`.p2align k`, `.balign n`) as Kraken's `nopalign`
  cell and other directive lines, comments and blank lines dropped
  (`textDirectives`), which is what the canonical loader parses from the
  printed text (`Scc.Sem.X64.textProgram`; checked on the test programs);
  `none` if the `.text` sections hold a raw instruction line, which Kraken's
  parser refuses;
* `secs`, the data sections as data items (`Scc.Emit.Data.Secs.ofProgram`,
  as `Scc.Emit.X64.dataSecs`);
* the stack need table (`stackNeed`) and the lowering's record (`Lowered`).

The code cells need the instruction sizes, which come from the assembler
(`Scc.Cert.Sizes.sizesOf`, untrusted, checked by the certificate's
`SizeCheck`): they stay an input, `Kraken.Promising.X64.sizedCells prog sizes`
(`Scc.Sem.X64.cellsOf`), outside this module.

`scc --arch x64` runs exactly this: `Scc.Cli.run` calls `lowerIR`, then
`emitAll` (through `Emitted.listing`, which also renders the text), so the
text it writes is `Scc.Emit.X64.render` of `items`.
-/

open CoreLang CoreTerm
open Scc.IR

namespace Scc.Lower.X64

open Scc.Emit.X64 (Item emitItemsMaps render dataSecs)

/-! The line functions below work on lists of characters: core's
`String.trimAscii`, `String.splitOn` and `String.toNat?` do not reduce in
the kernel, so `decide +kernel` could not evaluate `prog` with them. Each
is the list transcription of the string function named in its docstring.
`textDirectives` tests a line's prefix with `Scc.Lower.lineStarts` (on
bytes, which the kernel evaluates faster), the same test as a prefix test
on `lineChars` for the white-space-free prefixes it uses, and reads the
operand (`alignOf (lineChars s)`) only of `.p2align` and `.balign` lines. -/

/-- A line with leading and trailing white space dropped
(`String.trimAscii`). -/
def trimChars (l : List Char) : List Char :=
  ((l.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

/-- A directive line as the loader reads it: trimmed, its tab-separated
fields trimmed and joined by single spaces
(`" ".intercalate ((s.trimAscii.splitOn "\t").map trimAscii)`). -/
def lineChars (s : String) : List Char :=
  [' '].intercalate (((trimChars s.toList).splitOn '\t').map trimChars)

/-- A decimal natural number, `_` allowed between digits
(`String.toNat?`). -/
def natOfChars? (l : List Char) : Option Nat :=
  let ok := l.foldl (fun (st : Option Bool) c =>
    st.bind fun lastDigit =>
      if c = '_' then (if lastDigit then some false else none)
      else if c.isDigit then some true else none) (some false)
  if ok = some true then
    some (l.foldl (fun n c => if c = '_' then n else n * 10 + (c.toNat - '0'.toNat)) 0)
  else none

/-- The alignment of a directive line (`lineChars`) as the loader reads it
(`Scc.Sem.X64.textProgram`): `.p2align k` is `2^k`, `.balign n` is `n`. -/
def alignOf (t : List Char) : Option Nat :=
  let ops := ((t.splitOn ' ').filter (· ≠ [])).drop 1
  if ".p2align".toList.isPrefixOf t then (natOfChars? (ops.headD [])).map (2 ^ ·)
  else if ".balign".toList.isPrefixOf t then natOfChars? (ops.headD [])
  else none

/-- The program of the `.text` sections of an item list (see the module
docstring), `none` if they hold a raw instruction line. -/
def textDirectives (items : List Item) : Option _root_.Program :=
  let step (acc : Option (Bool × List Directive)) (it : Item) : Option (Bool × List Directive) :=
    acc.bind fun (txt, ds) =>
      match it with
      | .dir s =>
        let pre := lineStarts s
        if pre ".text" then some (true, ds)
        else if pre ".data" || pre ".bss" || pre ".section" || pre ".rodata" then some (false, ds)
        else if txt then
          match if pre ".p2align" || pre ".balign" then alignOf (lineChars s) else none with
          | some n => some (true, .instr (Kraken.X64.Parser.toInstr .none (w := .W64) (.nopalign n none)) :: ds)
          | none => some (true, ds)
        else some (txt, ds)
      | .d x => if txt then some (true, x :: ds) else some (txt, ds)
      | .raw _ => if txt then none else some (txt, ds)
      | .comment _ | .blank => some (txt, ds)
  (items.foldl step (some (true, []))).map (·.2.reverse)

/-- **scc's x86-64 output** for one program (see the module docstring). -/
structure Emitted where
  /-- The lowering to the IR. -/
  low : Lowered
  /-- The emitter's items: the printed text is `Scc.Emit.X64.render items`. -/
  items : List Item
  /-- The safepoints, in code order (`Scc.Emit.X64.emitItemsMaps`). -/
  safepoints : List (String × List Int × List Int)
  /-- The instruction list (`textDirectives items`). -/
  prog : Option _root_.Program
  /-- The data sections. -/
  secs : Scc.Emit.Data.Secs
  /-- The stack need table (`stackNeed`), `none` with non-tail recursion. -/
  need : Option (List (Sym × Nat × Nat))

instance : Inhabited Emitted :=
  ⟨{ low := default, items := [], safepoints := [], prog := none, secs := {}, need := none }⟩

/-- **The x86-64 emission** of a lowered program. It fails only where the
emitter's items fail (`emitItemsMaps`); the other fields are computed from
the items and the IR. -/
def emitAll (l : Lowered) : Except String Emitted := do
  let (items, sps) ← emitItemsMaps l.ir
  pure { low := l, items, safepoints := sps, prog := textDirectives items,
         secs := Scc.Emit.Data.Secs.ofProgram l.ir.data (if l.ir.growth.isSome then some sps else none)
         need := (stackNeed .x64 l.ir).toOption }

/-- **scc's x86-64 pipeline**, failing with the first error. -/
def lowerAll? (cfg : Config) (p : Prog) : Except String Emitted :=
  lowerIR cfg p >>= emitAll

/-- **scc's x86-64 pipeline** as a total function: an empty output (no
instruction list) where `lowerAll?` fails. -/
def lowerAll (cfg : Config) (p : Prog) : Emitted :=
  match lowerAll? cfg p with
  | .ok e => e
  | .error _ => default

/-- The text and the other outputs of `scc` (`Scc.Cli.run`): the items
rendered (`Scc.Emit.X64.render`, which refuses an item it cannot print) and
the stack need table; no placement data on x86-64. -/
def Emitted.listing (e : Emitted) : Except String Listing := do
  pure { text := ← render e.items, need := e.need }

/-- `emitAll`'s data sections are the emitter's (`Scc.Emit.X64.dataSecs`). -/
theorem emitAll_secs {l : Lowered} {e : Emitted} (h : emitAll l = .ok e) :
    dataSecs l.ir = .ok e.secs := by
  unfold emitAll at h
  unfold dataSecs
  cases hm : emitItemsMaps l.ir with
  | error _ => rw [hm] at h; cases h
  | ok r =>
    rw [hm] at h
    cases h
    rfl

end Scc.Lower.X64
