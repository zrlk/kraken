/-
Programs larger than a litmus test: the `.kl` format.

    AArch64 Spinlock2
    { lock=0; counter=0;
      0:X0=lock; 0:X1=counter; 1:X0=lock; 1:X1=counter; }
    threads { P0: worker done; P1: worker done; }
    stack 64
    code {
    worker:
      ...
      B done
    done:
    }
    forall [counter]=2

- The init block is the litmus one (locations, registers, types).
- `threads { Pn: entry exit; ... }`: each thread starts at label `entry` of
  the common `code` block and has halted when its pc reaches label `exit`.
  Threads with the same entry run the same code; registers distinguish them.
- `stack N` (optional): each thread gets `N` bytes of private, mapped memory
  with `SP`/`rsp` at its top.
- `code { ... }`: one assembly listing in the ISA's syntax, with labels;
  symbolic data locations may be named in init only (addresses reach the
  code through registers), except on x64 where `(x)` operands are resolved
  through the executable's label table as for litmus tests.
- The final section is the litmus one: `exists`/`~exists`/`forall`,
  `locations`.
- Comments: `(* ... *)` anywhere, and whole lines starting with `#` (used
  for `# flags:` / `# expect:` metadata read by regression scripts).

The thread programs are returned as source lines so the ISA runners can
reuse their litmus set-up, with the entry/exit labels alongside.
-/
import Kraken.Litmus.Syntax

namespace Kraken.Litmus

structure ThreadSpec where
  tid : Nat
  entry : String
  exit : String
  deriving Repr, Inhabited

structure Program where
  arch : String
  name : String
  inits : List Init
  threads : List ThreadSpec
  stack : Nat
  /-- The code block, one source line per entry (labels included). -/
  code : List String
  quant : Quant
  cond : Cond
  locations : List Obs
  deriving Repr, Inhabited

namespace Program

/-- The `Test` view of a program: every thread's program is the whole code
block, so that the observable/condition machinery applies unchanged. -/
def toTest (p : Program) : Test :=
  { arch := p.arch, name := p.name, inits := p.inits,
    threads := p.threads.map fun _ => p.code,
    quant := p.quant, cond := p.cond, locations := p.locations }

end Program

open Parse in
/-- Parse a `.kl` file. -/
def parseProgram (src : String) : Except String Program := do
  -- `normalizeColons` is applied to the init block only: in the code block
  -- it would glue a label ending in a digit (`enq1:`) to the next line.
  let src := stripComments src
  -- `#` line comments (e.g. `# flags: -sym`, `# expect: Always`, read by
  -- `Kraken/Examples/LockFree/run.sh`); no code line starts with `#`.
  let lines := ((src.splitOn "\n").map trim).filter fun l => !l.startsWith "#"
  let header ← match lines.find? (fun l => !l.isEmpty) with
    | some h => pure h
    | none => throw "empty file"
  let (arch, name) ← match header.splitOn " " |>.filter (· ≠ "") with
    | a :: n :: _ => pure (a, n)
    | _ => throw s!"bad header: {header}"
  let body := "\n".intercalate ((lines.dropWhile (fun l => l.isEmpty)).drop 1)
  -- init block
  let some (_, afterOpen) := splitFirst body '{' | throw "no init block"
  let some (initText, rest) := splitMatchingBrace afterOpen | throw "unterminated init block"
  let initText := normalizeColons initText
  let inits ← ((normalizeColons initText).splitOn ";").filterMapM fun item => do
    let item := trim item
    if item.isEmpty then pure none else
    match parseInit item with
    | some i => pure (some i)
    | none => throw s!"unsupported init: {item}"
  -- keyword blocks
  let mut rest := trim rest
  let mut threads : List ThreadSpec := []
  let mut stack := 0
  let mut code : List String := []
  let mut finalText := ""
  while !rest.isEmpty do
    if rest.startsWith "threads" then
      let some (_, after) := splitFirst rest '{' | throw "bad threads block"
      let some (inner, after) := splitMatchingBrace after | throw "unterminated threads block"
      threads := ← (inner.splitOn ";").filterMapM fun item => do
        let item := trim item
        if item.isEmpty then pure none else
        match item.splitOn ":" with
        | [p, spec] =>
          let p := trim p
          let some tid := (if p.startsWith "P" then sdrop p 1 else p).toNat? | throw s!"bad thread name {p}"
          match (spec.splitOn " ").filter (· ≠ "") with
          | [entry, exit] => pure (some { tid, entry, exit })
          | _ => throw s!"bad thread spec: {item} (want `Pn: entry exit`)"
        | _ => throw s!"bad thread spec: {item}"
      rest := trim after
    else if rest.startsWith "stack" then
      let after := trim (sdrop rest 5)
      let num := String.ofList (after.toList.takeWhile Char.isDigit)
      stack := num.toNat?.getD 0
      rest := trim (sdrop after num.length)
    else if rest.startsWith "code" then
      let some (_, after) := splitFirst rest '{' | throw "bad code block"
      let some (inner, after) := splitMatchingBrace after | throw "unterminated code block"
      code := (inner.splitOn "\n").map trim |>.filter (· ≠ "")
      rest := trim after
    else
      finalText := rest
      rest := ""
  if threads.isEmpty then throw "no threads block"
  if code.isEmpty then throw "no code block"
  -- final section, through the litmus parser on a stub test
  let stub := s!"{arch} {name}\n\{ }\nP0;\nNOP;\n{finalText}"
  let t ← parse stub
  return { arch, name, inits, threads := threads.mergeSort (·.tid ≤ ·.tid), stack, code,
           quant := t.quant, cond := t.cond, locations := t.locations }

end Kraken.Litmus
