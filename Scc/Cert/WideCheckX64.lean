import Kraken.X64.Parser
import Scc.Cert.Rt.WideOkX64

/-!
# `scc --arch x64 --code`'s one-word fragment check

The x64 twin of `Scc/Cert/WideCheckA64.lean`. `Scc/Cert/Rt/WideX64.lean`
certifies programs whose memory writes are all 8 bytes
(`Scc.Cert.WideX64.wideIn`, `Scc/Cert/Rt/WideOkX64.lean`). `check asm` runs
that test on the program the canonical loader reads from the listing
(`progOf`: `Scc.Sem.X64.textProgram`, restated here because `scc-x64`
cannot import the loader's modules, which bring WeakCore's root `main`;
`Scc/Test/WideCheckX64Test.lean` checks the restatement by `rfl`) and, when
it fails, names the offending listing lines. `scc-x64` passes it to
`Scc.Cert.Blocks.code` (`Scc.Cli.run`'s `wide`), which refuses a program
outside the fragment and states `<P>_wide` for one inside.

The lines are found by parsing each listing line alone (Kraken's parser
needs no label definitions), the verdict is the whole program's `wideIn`.
-/

namespace Scc.Cert.WideCheckX64

/-- `Scc.Sem.textSection`: the lines of the `.text` sections. -/
def textOf (asm : String) : String :=
  let step (acc : Bool × List String) (l : String) : Bool × List String :=
    let t := l.trimAscii.toString
    if t.startsWith ".text" then (true, acc.2)
    else if t.startsWith ".data" || t.startsWith ".bss" || t.startsWith ".section" ||
        t.startsWith ".rodata" then (false, acc.2)
    else if acc.1 then (true, l :: acc.2) else acc
  "\n".intercalate ((asm.splitOn "\n").foldl step (true, [])).2.reverse

/-- `Scc.Sem.X64.textProgram`: Kraken's x64 parser on the `.text` sections,
alignment directives as `nopalign` cells. -/
def progOf (asm : String) : Except String Program := do
  let parseChunk (ls : List String) : Except String Program :=
    Kraken.X64.Parser.parse (Kraken.X64.Parser.stripDirectives ("\n".intercalate ls.reverse))
  let alignOf (t : String) : Option Nat :=
    let ops := ((t.splitOn " ").filter (· ≠ "")).drop 1
    if t.startsWith ".p2align" then (ops.headD "").toNat?.map (2 ^ ·)
    else if t.startsWith ".balign" then (ops.headD "").toNat?
    else none
  let mut out : Program := []
  let mut cur : List String := []
  for l in (textOf asm).splitOn "\n" do
    let t := " ".intercalate ((l.trimAscii.toString.splitOn "\t").map (·.trimAscii.toString))
    match alignOf t with
    | some n =>
        out := out ++ (← parseChunk cur) ++ (← Kraken.X64.Parser.parse s!".align {n}")
        cur := []
    | none => cur := l :: cur
  return out ++ (← parseChunk cur)

/-- The memory writes outside the fragment, as text for messages. -/
def fragmentLimit : String :=
  "every memory write 8 bytes: movb/movw/movl or another 1/2/4-byte memory destination \
  (setcc to memory, pushw, narrow lock/xchg/xadd/cmpxchg/movnti), vector stores \
  (movups/movaps/movdqa/movdqu/... to memory) and cmpxchg16b are refused"

/-- The listing lines (1-based, with their text) whose instructions are
outside the fragment. -/
def offending (asm : String) : List (Nat × String) :=
  ((asm.splitOn "\n").zipIdx 1).filterMap fun (l, n) =>
    match Kraken.X64.Parser.parse (Kraken.X64.Parser.stripDirectives l) with
    | .ok p => if p.all Directive.wideOk then none else some (n, l.trimAscii.toString)
    | .error _ => none

/-- **The fragment check**: `ok` iff the canonical loader's program of `asm`
is `wideIn`; otherwise the number of directives outside the fragment and
(up to five of) their listing lines. -/
def check (asm : String) : Except String Unit := do
  let prog ← match progOf asm with
    | .ok p => pure p
    | .error m => throw s!"Kraken's x64 parser rejects the text: {m}"
  if Scc.Cert.WideX64.wideIn prog then return
  let n := (prog.filter fun d => !d.wideOk).length
  let ls := offending asm
  let shown := ls.take 5 |>.map fun (k, t) => s!"line {k}: {t}"
  let more := if ls.length > 5 then s!"; and {ls.length - 5} more" else ""
  throw s!"{n} instruction(s) outside the certified one-word fragment ({fragmentLimit}), \
    which the code check does not cover yet: {"; ".intercalate shown}{more}"

end Scc.Cert.WideCheckX64

/-! ## Tests -/

namespace Scc.Cert.WideCheckX64

#guard check ".text\nf:\n\tmovq %rax, 8(%rdi)\n\tpushq %rbp\n\tmovl (%rdi), %eax\n\tcall f\n\tret\n" matches .ok ()

/--
info: "2 instruction(s) outside the certified one-word fragment (every memory write 8 bytes: movb/movw/movl or another 1/2/4-byte memory destination (setcc to memory, pushw, narrow lock/xchg/xadd/cmpxchg/movnti), vector stores (movups/movaps/movdqa/movdqu/... to memory) and cmpxchg16b are refused), which the code check does not cover yet: line 3: movb %al, (%rdi); line 5: movl %eax, -4(%rbp)"
-/
#guard_msgs in
#eval match check ".text\nf:\n\tmovb %al, (%rdi)\n\tmovq %rax, 8(%rdi)\n\tmovl %eax, -4(%rbp)\n\tret\n" with
  | .ok () => "ok"
  | .error m => m

end Scc.Cert.WideCheckX64
