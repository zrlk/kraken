/-
The canonical loaders' text readers, ISA-independent part: the lines of a
text's `.text` sections (`textSection`) and the reader of a data line
(`dataLine`, with `parseInt?`, `isSym`, `operands`). Part of the trusted
loader (`Scc/Sem/Target.lean` re-exports them through its import). They are
in a module of their own, importing neither WeakCore nor Kraken's machine,
so that `scc`'s fragment checks (`Scc/Cert/WideCheckA64.lean`,
`Scc/Cert/WideCheckX64.lean`) can read the program the loader reads by
calling the loader's own definitions (`Scc/Sem/TextA64.lean`,
`Scc/Sem/TextX64.lean`).
-/
import Kraken.DataImage

namespace Scc.Sem

/-- The lines of the `.text` sections of an assembly text: a line starting
`.text` opens one, a line starting `.data`, `.bss`, `.section` or
`.rodata` opens a data section, and the text starts in `.text`. Section
directives themselves are dropped. -/
def textSection (asm : String) : String :=
  let step (acc : Bool × List String) (l : String) : Bool × List String :=
    let t := l.trimAscii.toString
    if t.startsWith ".text" then (true, acc.2)
    else if t.startsWith ".data" || t.startsWith ".bss" || t.startsWith ".section" ||
        t.startsWith ".rodata" then (false, acc.2)
    else if acc.1 then (true, l :: acc.2) else acc
  "\n".intercalate ((asm.splitOn "\n").foldl step (true, [])).2.reverse

/-- A decimal or `0x` hexadecimal integer, with an optional `-`. -/
def parseInt? (s : String) : Option Int :=
  let s := s.trimAscii.toString
  let (neg, body) := if s.startsWith "-" then (true, (s.drop 1).toString) else (false, s)
  let n? : Option Nat :=
    if body.startsWith "0x" || body.startsWith "0X" then
      let ds := (body.drop 2).toString.toList
      if ds.isEmpty then none else
      ds.foldl (fun acc c => acc.bind fun a =>
        if c.isDigit then some (16 * a + (c.toNat - '0'.toNat))
        else if 'a' ≤ c && c ≤ 'f' then some (16 * a + (c.toNat - 'a'.toNat + 10))
        else if 'A' ≤ c && c ≤ 'F' then some (16 * a + (c.toNat - 'A'.toNat + 10))
        else none) (some 0)
    else body.toNat?
  n?.map fun n => if neg then -(n : Int) else n

/-- A label name (`[A-Za-z_.$][A-Za-z0-9_.$]*`). -/
def isSym (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => (c.isAlpha || c == '_' || c == '.' || c == '$') &&
      cs.all fun c => c.isAlphanum || c == '_' || c == '.' || c == '$'

/-- The operands of a directive line, comma-separated. -/
def operands (t : String) (dir : String) : List String :=
  ((t.drop dir.length).toString.splitOn ",").map (·.trimAscii.toString)

/-- A `.quad` operand `A - B` or `A - .` (one space each side of the `-`): the
difference word of label `A` and label `B` (`some B`) or the word's own address
(`none`); `A` is a label other than `.`. -/
def quadDiff? (x : String) : Option Kraken.DataImage.Item :=
  match x.splitOn " - " with
  | [a, b] =>
    if a != "." && isSym a then
      if b == "." then some (.quadDiff a none)
      else if isSym b then some (.quadDiff a (some b)) else none
    else none
  | _ => none

/-- The items of one line of a data section: a label, `.balign n`,
`.p2align k`, `.zero n` / `.skip n`, `.byte`, `.quad` (numbers, labels or
label differences, `quadDiff?`);
symbol directives (`.globl`, `.type`, `.size`) and blank or comment lines
have none. `none`: a line the loader does not read (it refuses the text). -/
def dataLine (t : String) : Option (List Kraken.DataImage.Item) :=
  let word := (t.splitOn " ").headD "" |>.splitOn "\t" |>.headD ""
  if t.isEmpty || t.startsWith "#" || t.startsWith "//" then some []
  else if t.endsWith ":" && isSym (t.dropEnd 1).toString then some [.label (t.dropEnd 1).toString]
  else if word == ".globl" || word == ".type" || word == ".size" || word == ".local" then some []
  else if word == ".balign" then
    match operands t ".balign" with
    | [n] => (parseInt? n).bind fun n => if 0 ≤ n then some [.align n.toNat] else none
    | _ => none
  else if word == ".p2align" then
    match operands t ".p2align" with
    | [k] => (parseInt? k).bind fun k => if 0 ≤ k ∧ k < 64 then some [.align (2 ^ k.toNat)] else none
    | _ => none
  else if word == ".zero" || word == ".skip" then
    match operands t word with
    | [n] => (parseInt? n).bind fun n => if 0 ≤ n then some [.zero n.toNat] else none
    | _ => none
  else if word == ".byte" then
    (operands t ".byte").mapM (fun b => (parseInt? b).bind fun v =>
      if 0 ≤ v ∧ v < 256 then some (UInt8.ofNat v.toNat) else none) |>.map fun bs => [.bytes bs]
  else if word == ".quad" then
    (operands t ".quad").mapM fun x =>
      match parseInt? x with
      | some v => some (.quad v)
      | none => if isSym x then some (.quadLabel x) else quadDiff? x
  else none

end Scc.Sem
