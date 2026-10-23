import Scc.Cert.Rt.WideOkA64
import Kraken.AArch64.Parser

/-!
# `scc --code`'s one-word fragment check on AArch64

`check asm`: the listing's program, as the canonical loader parses it
(`progOf`, which is `Scc.Sem.A64.textProgram`: `Scc/Test/WideCheckTest.lean`
checks the equation by `rfl`), is in the certified one-word fragment
(`Scc.Cert.WideA64.wideIn`, `Scc/Cert/Rt/WideOkA64.lean`, keyed off the parsed
`Operation` by `Operation.wideOk`), or the error names the listing lines
outside it. The loader's modules bring WeakCore's root `main` into scope, so
the compiler cannot import them; `textOf` and `progOf` restate
`Scc.Sem.textSection` and `textProgram`.
`scc-arm` passes it to `Scc.Cert.Blocks.code` (`Scc.Cli.run`'s `wide`), which
refuses a program outside the fragment and states `<P>_wide` for one inside.

The lines are found by parsing each listing line alone (Kraken's parser
needs no label definitions), the verdict is the whole program's `wideIn`.
-/

namespace Scc.Cert.WideCheckA64

open Kraken Kraken.Promising.AArch64

/-- `Scc.Sem.textSection`: the lines of the `.text` sections. -/
def textOf (asm : String) : String :=
  let step (acc : Bool × List String) (l : String) : Bool × List String :=
    let t := l.trimAscii.toString
    if t.startsWith ".text" then (true, acc.2)
    else if t.startsWith ".data" || t.startsWith ".bss" || t.startsWith ".section" ||
        t.startsWith ".rodata" then (false, acc.2)
    else if acc.1 then (true, l :: acc.2) else acc
  "\n".intercalate ((asm.splitOn "\n").foldl step (true, [])).2.reverse

/-- `Scc.Sem.A64.textProgram`: Kraken's AArch64 parser on the `.text`
sections. -/
def progOf (asm : String) : Except String Program :=
  Kraken.AArch64.Parser.parse (Kraken.AArch64.Parser.stripDirectives (textOf asm))

/-- The stores outside the fragment, as text for messages. -/
def fragmentLimit : String :=
  "str/stur/stlr w, strb/strh/sturb/sturh, stp, stxr/stxp, casp, and sub-word swp/cas/ld<op>"

/-- The listing lines (1-based, with their text) whose instructions are
outside the fragment. -/
def offending (asm : String) : List (Nat × String) :=
  ((asm.splitOn "\n").zipIdx 1).filterMap fun (l, n) =>
    match Kraken.AArch64.Parser.parse (Kraken.AArch64.Parser.stripDirectives l) with
    | .ok p => if p.all Directive.wideOk then none else some (n, l.trimAscii.toString)
    | .error _ => none

/-- **The fragment check**: `ok` iff the canonical loader's program of `asm`
is `wideIn`; otherwise the number of directives outside the fragment and
(up to five of) their listing lines. -/
def check (asm : String) : Except String Unit := do
  let prog ← match progOf asm with
    | .ok p => pure p
    | .error m => throw s!"Kraken's AArch64 parser rejects the text: {m}"
  if Scc.Cert.WideA64.wideIn prog then return
  let n := (prog.filter fun d => !d.wideOk).length
  let ls := offending asm
  let shown := ls.take 5 |>.map fun (k, t) => s!"line {k}: {t}"
  let more := if ls.length > 5 then s!"; and {ls.length - 5} more" else ""
  throw s!"{n} store(s) outside the certified one-word fragment ({fragmentLimit}), \
    which the code check does not cover yet: {"; ".intercalate shown}{more}"

end Scc.Cert.WideCheckA64

/-! ## Tests -/

namespace Scc.Cert.WideCheckA64

#guard check ".text\nf:\n  str x1, [x0, #8]\n  stur x2, [x0, #-8]\n  swpal x9, x11, [x10]\n  ret\n" matches .ok ()

/--
info: "2 store(s) outside the certified one-word fragment (str/stur/stlr w, strb/strh/sturb/sturh, stp, stxr/stxp, casp, and sub-word swp/cas/ld<op>), which the code check does not cover yet: line 3: str w1, [x0]; line 5: stp x29, x30, [sp, #-16]!"
-/
#guard_msgs in
#eval match check ".text\nf:\n  str w1, [x0]\n  str x1, [x0, #8]\n  stp x29, x30, [sp, #-16]!\n  ret\n" with
  | .ok () => "ok"
  | .error m => m

end Scc.Cert.WideCheckA64
