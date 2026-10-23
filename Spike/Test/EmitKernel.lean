import Scc.Emit.A64Print
import Scc.Lower.SpecA64
import Scc.Test.Src
import Spike.Lib.Ret0Src

/-!
# Emitter functions in kernel-friendly form, against their plain forms

Checks for the forms of emitter and pipeline functions chosen so that the
kernel evaluates them quickly (or at all): each agrees with the plain form
on the inputs that matter.

* `Scc.Emit.A64.labelOk` skips the register-name lookups for names of four
  or more characters; `labelOkPlain` is the plain check.
* `Scc.Lower.A64.textDirectives` tests its raw lines' prefixes on their
  bytes (`Scc.Lower.lineStarts`); `textDirectivesPlain` is the form on
  `String.trimAsciiStart`.
-/

namespace Spike.Test.EmitKernel

open Scc.Emit.A64

/-- The plain label check: a letter, `_` or `.`, then letters, digits, `_`
or `.`; and not a register name. -/
def labelOkPlain (l : Label) : Bool :=
  match l.toList with
  | [] => false
  | c :: cs =>
    (c.isAlpha || c == '_' || c == '.') &&
    cs.all (fun c => c.isAlphanum || c == '_' || c == '.') &&
    (Kraken.AArch64.Parser.parseXRegName l).isNone &&
    !(["sp", "wsp", "xzr", "wzr"].contains l.toLower)

/-- Every register name and special register, in lower and upper case, with
one more character, and some ordinary names. -/
def labelSamples : List String :=
  let regs := (List.range 31).flatMap (fun i => [s!"x{i}", s!"w{i}"]) ++
    ["fp", "lr", "sp", "wsp", "xzr", "wzr"]
  let all := regs ++ regs.map String.toUpper
  all ++ all.map (· ++ "0") ++ all.map (· ++ "_") ++ all.map ("_" ++ ·) ++
    ["", "a", "ab", "abc", "abcd", "1abc", ".L0_f.1_b", "main", "scc_rt_main", "x", "w",
     "x31", "w31", "x0a", "xz", "sp.", ".sp", "a-b", "a b"]

-- The two checks agree on the samples.
#guard labelSamples.all fun l => labelOk l == labelOkPlain l

-- Some names the emitter uses.
#guard labelOk "_start" && labelOk "scc_rt_main" && labelOk ".L3_main.0_entry" &&
  !labelOk "x29" && !labelOk "XZR" && !labelOk "Wsp" && labelOk "x290"

/-! ## The `.text` directives -/

open Scc.Lower.A64 in
/-- `textDirectives` with string prefix tests. -/
def textDirectivesPlain (items : List Item) : _root_.Program :=
  let step (acc : Bool × List Directive) : Item → Bool × List Directive
    | .raw s =>
      let t := s.trimAsciiStart.toString
      if t.startsWith ".text" then (true, acc.2)
      else if t.startsWith ".data" || t.startsWith ".bss" || t.startsWith ".section" ||
          t.startsWith ".rodata" then (false, acc.2)
      else acc
    | .d x => if acc.1 then (true, x :: acc.2) else acc
    | .comment _ => acc
  (items.foldl step (true, [])).2.reverse

/-- The emitter's items for `ret0.w`. -/
def ret0Items : List Item :=
  (Scc.Lower.A64.lowerAll { arch := .arm } Spike.Lib.Ret0Src.ret0Src).items

/-- The emitter's items for `hello1.w`. -/
def hello1Items : List Item :=
  match Scc.Frontend.run (w_src% "Scc/Test/hello1.w") with
  | .ok c => (Scc.Lower.A64.lowerAll { arch := .arm } c.prog).items
  | .error _ => []

/-- Raw lines: section switches with and without leading white space, and
lines that only look like them. -/
def rawSamples : List String :=
  [".text", "\t.text", "  \t.text 0", "\n.text", ".data", "\t.data", " .bss", "\t.section .rodata",
   ".rodata", "\t.rodata.str", ".tex", "text", "\t.globl main", "", " ", "\t", ". text", "x.data",
   "\t.p2align 2", "\r.bss"]

/-- The prefixes `textDirectives` tests. -/
def prefixes : List String := [".text", ".data", ".bss", ".section", ".rodata", ".p2align", ".balign"]

-- `lineStarts` is the prefix test after `String.trimAsciiStart`, also on
-- lines with other characters than ASCII.
#guard (rawSamples ++ ["é.data", "\u00a0.text", "\t.textÿ", "\t\u2003.bss", "π", "\t.rodataé"]).all
  fun s => prefixes.all fun p => Scc.Lower.lineStarts s p == s.trimAsciiStart.toString.startsWith p

/-- The raw samples, each followed by the first two directives of `ret0.w`. -/
def rawItems : List Item :=
  let ds := (ret0Items.filter fun | .d _ => true | _ => false).take 2
  rawSamples.flatMap fun r => .raw r :: ds

-- The two forms agree on the emitted programs and the samples.
#guard !ret0Items.isEmpty && !hello1Items.isEmpty
#guard decide (Scc.Lower.A64.textDirectives ret0Items = textDirectivesPlain ret0Items)
#guard decide (Scc.Lower.A64.textDirectives hello1Items = textDirectivesPlain hello1Items)
#guard decide (Scc.Lower.A64.textDirectives rawItems = textDirectivesPlain rawItems)
-- Only the directives after the first four samples (each opening `.text`)
-- are kept: the fifth closes it and no later sample reopens it.
#guard (Scc.Lower.A64.textDirectives rawItems).length == 8

-- The kernel evaluates the instruction list of `ret0.w` (about 10 s).
set_option maxRecDepth 100000 in
example : (Scc.Lower.A64.lowerAll { arch := .arm } Spike.Lib.Ret0Src.ret0Src).prog.isEmpty = false := by
  decide +kernel

end Spike.Test.EmitKernel
