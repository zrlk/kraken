import Scc.Lower.SpecX64
import Scc.Test.Src
import Spike.Lib.Ret0Src

/-!
# x86-64 pipeline functions in kernel-friendly form, against their plain forms

The x86-64 twin of `Spike/Test/EmitKernel.lean` (the two specifications
cannot be imported together). `Scc.Lower.X64.textDirectives` tests its
directive lines' prefixes on their bytes (`Scc.Lower.lineStarts`) and reads
alignments as lists of characters (`lineChars`, `alignOf`);
`textDirectivesPlain` is the form on `String.trimAscii`, `String.splitOn`
and `String.toNat?`.
-/

namespace Spike.Test.EmitKernelX64

open Scc.Lower.X64
open Scc.Emit.X64 (Item)

/-- A directive line as the plain form reads it. -/
def linePlain (s : String) : String :=
  " ".intercalate ((s.trimAscii.toString.splitOn "\t").map (·.trimAscii.toString))

/-- The plain alignment of a directive line. -/
def alignOfPlain (t : String) : Option Nat :=
  let ops := ((t.splitOn " ").filter (· ≠ "")).drop 1
  if t.startsWith ".p2align" then (ops.headD "").toNat?.map (2 ^ ·)
  else if t.startsWith ".balign" then (ops.headD "").toNat?
  else none

/-- `textDirectives` on strings. -/
def textDirectivesPlain (items : List Item) : Option _root_.Program :=
  let step (acc : Option (Bool × List Directive)) (it : Item) : Option (Bool × List Directive) :=
    acc.bind fun (txt, ds) =>
      match it with
      | .dir s =>
        let t := linePlain s
        if t.startsWith ".text" then some (true, ds)
        else if t.startsWith ".data" || t.startsWith ".bss" || t.startsWith ".section" ||
            t.startsWith ".rodata" then some (false, ds)
        else if txt then
          match alignOfPlain t with
          | some n => some (true, .instr (Kraken.X64.Parser.toInstr .none (w := .W64) (.nopalign n none)) :: ds)
          | none => some (true, ds)
        else some (txt, ds)
      | .d x => if txt then some (true, x :: ds) else some (txt, ds)
      | .raw _ => if txt then none else some (txt, ds)
      | .comment _ | .blank => some (txt, ds)
  (items.foldl step (some (true, []))).map (·.2.reverse)

/-- Directive lines: section switches and alignments with white space in
various places, numbers with `_`, and lines that only look like them. -/
def dirSamples : List String :=
  [".text", "\t.text", "  \t.text 0 ", "\n.text\n", ".data", "\t.data\t", " .bss", "\t.section\t.rodata",
   ".rodata", ".tex", "text", "\t.globl\tmain", "", " ", "\t", "\t\t", ". text", "x.data",
   ".p2align 4", "\t.p2align\t4", ".p2align  3 ", ".p2align", ".p2align\n4", ".p2align 4\n",
   " .p2align \t 5 \t", ".p2align 1_0", ".p2align _1", ".p2align 1_", ".p2align 1__0", ".p2align -1",
   ".p2align 4,0x90", ".p2align4", ".balign 16", "\t.balign\t16", ".balign 1_6", ".balign", ".balign x",
   ".balign 0", ".balign 16 32", ".balignx 8", "\r.bss", "a\tb\t\tc", " \t a \t "]

-- The line forms agree on the samples.
#guard dirSamples.all fun s => lineChars s == (linePlain s).toList
#guard dirSamples.all fun s => alignOf (lineChars s) == alignOfPlain (linePlain s)
#guard dirSamples.all fun s => natOfChars? s.toList == s.toNat?
#guard (dirSamples ++ ["é.data", "\u00a0.text", "\t.textÿ", "\t\u2003.bss", "\t.rodataé"]).all fun s =>
  [".text", ".data", ".bss", ".section", ".rodata", ".p2align", ".balign"].all fun p =>
    Scc.Lower.lineStarts s p == (linePlain s).startsWith p

/-- The emitter's items for `ret0.w`. -/
def ret0Items : List Item :=
  (lowerAll { arch := .x64 } Spike.Lib.Ret0Src.ret0Src).items

/-- The emitter's items for `hello1.w`. -/
def hello1Items : List Item :=
  match Scc.Frontend.run (w_src% "Scc/Test/hello1.w") with
  | .ok c => (lowerAll { arch := .x64 } c.prog).items
  | .error _ => []

/-- The directive samples, each followed by the first two directives of
`ret0.w`. -/
def dirItems : List Item :=
  let ds := (ret0Items.filter fun | .d _ => true | _ => false).take 2
  dirSamples.flatMap fun s => .dir s :: ds

-- The two forms agree on the emitted programs and the samples.
#guard !ret0Items.isEmpty && !hello1Items.isEmpty
#guard decide (textDirectives ret0Items = textDirectivesPlain ret0Items)
#guard decide (textDirectives hello1Items = textDirectivesPlain hello1Items)
#guard decide (textDirectives dirItems = textDirectivesPlain dirItems)
#guard decide (textDirectives (.raw "\tnop" :: dirItems) = textDirectivesPlain (.raw "\tnop" :: dirItems))

-- The kernel evaluates the instruction list of `ret0.w` (about 6 s).
set_option maxRecDepth 100000 in
example : (lowerAll { arch := .x64 } Spike.Lib.Ret0Src.ret0Src).prog.isSome = true := by
  decide +kernel

end Spike.Test.EmitKernelX64
