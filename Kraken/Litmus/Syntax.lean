/-
The herd7 `.litmus` test format, independently of the ISA.

    AArch64 MP+rel+acq            -- architecture and name
    (* comments *)  Key=Value     -- metadata, ignored
    { 0:X1=x; 0:X3=y; x=1; uint64_t 1:X0; }
     P0           | P1           ;
     MOV W0,#1    | LDAR W0,[X3] ;
     STLR W0,[X3] | LDR W2,[X1]  ;
    locations [1:X6;]
    exists (1:X0=1 /\ 1:X2=0)

Thread programs are kept as lines of text for the ISA's own parser. The
single-thread form `P0;` followed by one instruction per line is accepted too.
-/
namespace Kraken.Litmus

/-- A register of a thread, as written in the test: `0:X1`, `1:rax`. -/
structure ThreadReg where
  tid : Nat
  reg : String
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

/-- A value in an init or condition: a number (of any width up to 128 bits),
a symbolic location (`x`, or an array element `a[1]` as an address), or a
whole array `{1,2}`. -/
inductive Value
  | num (n : Int)
  | sym (x : String)
  | arr (vs : List Value)
  deriving Repr, BEq, Hashable, Inhabited

/-- An initialisation: `0:X1=x`, `x=1`, `uint64_t 0:X0` (no value: zero). -/
inductive Init
  | reg (r : ThreadReg) (v : Value) (ty : Option String)
  | loc (x : String) (v : Value) (ty : Option String)
  deriving Repr, BEq, Inhabited

/-- An observable: a thread register or a memory location. -/
inductive Obs
  | reg (r : ThreadReg)
  | loc (x : String)
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

inductive Cond
  | eq (o : Obs) (v : Value)
  | not (c : Cond)
  | and (a b : Cond)
  | or (a b : Cond)
  | true
  deriving Repr, BEq, Inhabited

inductive Quant | exists | notExists | forall
  deriving Repr, BEq, DecidableEq, Inhabited

structure Test where
  arch : String
  name : String
  inits : List Init
  /-- One list of source lines per thread (labels included). -/
  threads : List (List String)
  quant : Quant
  cond : Cond
  locations : List Obs
  deriving Repr, Inhabited

/-! ## Lexing helpers

Written over `List Char` to stay independent of the evolving `String` API. -/

namespace Parse

def trim (s : String) : String := s.trimAscii.copy
def dropLast (s : String) : String := String.ofList s.toList.dropLast
def sdrop (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)
/-- Split at the first occurrence of `c`: the text before, and the text after. -/
def splitFirst (s : String) (c : Char) : Option (String × String) :=
  let cs := s.toList
  let before := cs.takeWhile (· != c)
  if before.length == cs.length then none
  else some (String.ofList before, String.ofList (cs.drop (before.length + 1)))

/-- Split at the `}` matching an already-consumed `{`, skipping nested braces. -/
def splitMatchingBrace (s : String) : Option (String × String) :=
  let rec go (cs : List Char) (depth : Nat) (acc : List Char) : Option (String × String) :=
    match cs with
    | [] => none
    | '{' :: rest => go rest (depth + 1) ('{' :: acc)
    | '}' :: rest => if depth = 0 then some (String.ofList acc.reverse, String.ofList rest)
                     else go rest (depth - 1) ('}' :: acc)
    | c :: rest => go rest depth (c :: acc)
  go s.toList 0 []

/-- Split at the `]` matching an already-consumed `[`, skipping nested brackets. -/
def splitMatchingBracket (s : String) : Option (String × String) :=
  let rec go (cs : List Char) (depth : Nat) (acc : List Char) : Option (String × String) :=
    match cs with
    | [] => none
    | '[' :: rest => go rest (depth + 1) ('[' :: acc)
    | ']' :: rest => if depth = 0 then some (String.ofList acc.reverse, String.ofList rest)
                     else go rest (depth - 1) (']' :: acc)
    | c :: rest => go rest depth (c :: acc)
  go s.toList 0 []

/-- Strip `(* ... *)` comments (possibly spanning lines). -/
partial def stripComments (s : String) : String :=
  let rec go (cs : List Char) (depth : Nat) (acc : List Char) : List Char :=
    match cs with
    | '(' :: '*' :: rest => go rest (depth + 1) acc
    | '*' :: ')' :: rest => if depth > 0 then go rest (depth - 1) acc else go rest depth (')' :: '*' :: acc)
    | c :: rest => if depth > 0 then go rest depth acc else go rest depth (c :: acc)
    | [] => acc.reverse
  String.ofList (go s.toList 0 [])

/-- `0: X1` → `0:X1`: drop whitespace after a `:` that follows a digit, so
thread registers are single tokens. -/
partial def normalizeColons (s : String) : String :=
  let rec go : List Char → List Char
    | d :: ':' :: rest => if d.isDigit then d :: ':' :: go (rest.dropWhile Char.isWhitespace) else d :: go (':' :: rest)
    | c :: rest => c :: go rest
    | [] => []
  String.ofList (go s.toList)

/-- Parse `tid:reg` or a bare identifier. -/
def parseObs (s : String) : Option Obs :=
  let s := trim s
  match s.splitOn ":" with
  | [t, r] => ((trim t).toNat?).map fun n => .reg { tid := n, reg := trim r }
  | [x] =>
    let x := trim x
    -- `[x]` is also accepted for a location
    let x := if x.startsWith "[" && x.endsWith "]" then dropLast (sdrop x 1) else x
    if x.isEmpty then none else some (.loc x)
  | _ => none

/-- A value: decimal or hex (`0x`), unbounded (128-bit literals are
allowed), a symbol, or an array `{v, ...}` of values. -/
partial def parseValue (s : String) : Option Value :=
  let s := trim s
  if s.startsWith "{" && s.endsWith "}" then
    let inner := trim (dropLast (sdrop s 1))
    if inner.isEmpty then some (.arr []) else
    ((inner.splitOn ",").mapM parseValue).map .arr
  else if s.startsWith "-" then (trim (sdrop s 1)).toNat?.map fun n => .num (-n)
  else if s.startsWith "0x" || s.startsWith "0X" then
    let hex := (sdrop s 2).toList
    let n : Nat := hex.foldl (fun acc c => acc * 16 + (if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10)) 0
    if hex.all (fun c => c.isDigit || ('a' ≤ c.toLower && c.toLower ≤ 'f')) && !hex.isEmpty then some (.num (Int.ofNat n)) else none
  else match s.toNat? with
    | some n => some (.num n)
    | none => if s.isEmpty then none else some (.sym s)

/-- Parse one init item: `[type] obs [= value]`. -/
def parseInit (s : String) : Option Init := do
  let s := trim s
  if s.isEmpty then none else
  let (lhs, rhs) := match s.splitOn "=" with
    | [l] => (trim l, none)
    | l :: r => (trim l, some (trim ("=".intercalate r)))
    | [] => ("", none)
  -- an optional type before the observable, possibly of several words
  -- (`unsigned __int128 x`)
  let ws := lhs.splitOn " " |>.filter (· ≠ "")
  let (ty, target) := match ws.reverse with
    | [o] => (none, o)
    | o :: t => (some (" ".intercalate t.reverse), o)
    | [] => (none, lhs)
  -- a pointer-typed register (`int64_t *0:X3=x`) holds an address: its type
  -- is `t*`, which presents values as symbols or 64-bit numbers
  let (ty, target) :=
    if target.startsWith "*" && target.any (· == ':') then (ty.map (· ++ "*"), sdrop target 1)
    else (ty, target)
  -- pointer locations (`int *p = &x`) and code addresses (`P1:L0`) are not supported
  if target.startsWith "*" then none else
  if (match rhs with | some r => r.startsWith "&" || (r.startsWith "P" && r.any (· == ':')) | none => false) then none else
  let v ← match rhs with
    | some r => parseValue r
    | none => some (.num 0)
  match ← parseObs target with
  | .reg r => some (.reg r v ty)
  | .loc x => some (.loc x v ty)

/-- Tokens of a condition. -/
inductive Tok | lp | rp | and | or | not | atom (s : String)
  deriving Repr, BEq

partial def tokenize (s : String) : List Tok :=
  let rec go (cs : List Char) (cur : List Char) (acc : List Tok) : List Tok :=
    let flush := if cur.isEmpty then acc else .atom (String.ofList cur.reverse) :: acc
    match cs with
    | [] => flush.reverse
    | '(' :: rest => go rest [] (.lp :: flush)
    | ')' :: rest => go rest [] (.rp :: flush)
    | '/' :: '\\' :: rest => go rest [] (.and :: flush)
    | '\\' :: '/' :: rest => go rest [] (.or :: flush)
    | '~' :: rest => go rest [] (.not :: flush)
    | 'n' :: 'o' :: 't' :: c :: rest => if c.isWhitespace || c == '(' then go (c :: rest) [] (.not :: flush) else go (c :: rest) ('t' :: 'o' :: 'n' :: cur) acc
    | c :: rest => if c.isWhitespace then go rest [] flush else go rest (c :: cur) acc
  go s.toList [] []

-- Recursive-descent condition parser: `or` < `and` < `not` < atom. Atoms
-- are `obs=value`, possibly written with spaces as separate tokens.
mutual
partial def condAtom : List Tok → Option (Cond × List Tok)
  | .lp :: rest => do
    let (c, rest) ← condOr rest
    match rest with
    | .rp :: rest => some (c, rest)
    | _ => none
  | .not :: rest => do let (c, rest) ← condAtom rest; some (.not c, rest)
  | .atom "true" :: rest => some (.true, rest)
  | .atom a :: rest =>
    -- `o=v`, or `o` `=` `v`, or `o=` `v`, or `o` `=v`
    let (lhs, rhs, rest) : String × String × List Tok :=
      match a.splitOn "=" with
      | [l, r] => if r.isEmpty then
          (match rest with | .atom r' :: rest' => (l, r', rest') | _ => (l, "", rest))
        else (l, r, rest)
      | [l] => (match rest with
        | .atom "=" :: .atom r :: rest' => (l, r, rest')
        | .atom r :: rest' => if r.startsWith "=" then (l, sdrop r 1, rest') else (l, "", rest)
        | _ => (l, "", rest))
      | _ => (a, "", rest)
    do
      let o ← parseObs lhs
      let v ← parseValue rhs
      some (.eq o v, rest)
  | _ => none

partial def condAnd (toks : List Tok) : Option (Cond × List Tok) := do
  let (a, rest) ← condAtom toks
  match rest with
  | .and :: rest => do let (b, rest) ← condAnd rest; some (.and a b, rest)
  | _ => some (a, rest)

partial def condOr (toks : List Tok) : Option (Cond × List Tok) := do
  let (a, rest) ← condAnd toks
  match rest with
  | .or :: rest => do let (b, rest) ← condOr rest; some (.or a b, rest)
  | _ => some (a, rest)
end

def parseCond (toks : List Tok) : Option (Cond × List Tok) := condOr toks

end Parse

/-! ## Types and arrays

A type in the init block (`int8_t x=1;`, `uint64_t 0:X0;`) is one of herd's
C types: it gives a location its width (`Kraken/Litmus/Layout.lean`) and
says how a value is printed. `int64_t a[2]` declares an array of two
elements, each its own location at the element width; `a={1,2}` initialises
or compares the whole array, `a[1]` names an element (in conditions,
`locations`, and as an address `0:X0=a[1]`). -/

/-- herd's C types: width in bytes and signedness. -/
def typeInfo? : String → Option (Nat × Bool)
  | "int8_t" | "char" | "signed char" => some (1, true)
  | "uint8_t" | "unsigned char" => some (1, false)
  | "int16_t" | "short" => some (2, true)
  | "uint16_t" | "unsigned short" => some (2, false)
  | "int32_t" | "int" => some (4, true)
  | "uint32_t" | "unsigned" | "unsigned int" => some (4, false)
  | "int64_t" | "long" | "long long" | "intptr_t" => some (8, true)
  | "uint64_t" | "unsigned long" | "uintptr_t" => some (8, false)
  | "int128_t" | "__int128" | "__int128_t" => some (16, true)
  | "uint128_t" | "unsigned __int128" | "__uint128_t" => some (16, false)
  | _ => none

/-- `x[n]`: the array name and the text between the brackets. -/
def arrayRef? (s : String) : Option (String × String) := do
  let (name, rest) ← Parse.splitFirst s '['
  let (idx, after) ← Parse.splitFirst rest ']'
  if after.isEmpty then some (name, idx) else none

/-- The symbol a name refers to: `a[1]` → `a`. -/
def baseName (s : String) : String :=
  match arrayRef? s with
  | some (a, _) => a
  | none => s

/-! ## The file -/

open Parse in
/-- Parse a `.litmus` file. -/
def parse (src : String) : Except String Test := do
  let src := normalizeColons (stripComments src)
  let lines := (src.splitOn "\n").map trim
  -- header
  let header ← match lines.find? (fun l => !l.isEmpty) with
    | some h => pure h
    | none => throw "empty file"
  let (arch, name) ← match header.splitOn " " |>.filter (· ≠ "") with
    | a :: n :: _ => pure (a, n)
    | _ => throw s!"bad header: {header}"
  let rest := (lines.dropWhile (fun l => l.isEmpty)).drop 1
  -- init block: between the first `{` and the matching `}`
  let body := "\n".intercalate rest
  let some (_, afterOpen) := splitFirst body '{' | throw "no init block"
  let some (initText, afterInit) := splitMatchingBrace afterOpen | throw "unterminated init block"
  let inits ← (initText.splitOn ";").filterMapM fun item => do
    let item := trim item
    if item.isEmpty then pure none else
    match parseInit item with
    | some i => pure (some i)
    | none => throw s!"unsupported init: {item}"
  -- program: lines up to the first final-section keyword
  let progLines := (afterInit.splitOn "\n").map trim |>.filter (· ≠ "")
  let isFinal (l : String) : Bool :=
    ["exists", "~exists", "forall", "locations", "filter"].any (l.startsWith ·)
  let prog := progLines.takeWhile (fun l => !isFinal l)
  let finals := progLines.dropWhile (fun l => !isFinal l)
  let some header := prog.head? | throw "no program"
  let nthreads := (header.splitOn "|").length
  if !(header.startsWith "P") then throw s!"bad program header: {header}"
  let rows := prog.drop 1 |>.map fun l =>
    let l := if l.endsWith ";" then dropLast l else l
    (l.splitOn "|").map trim
  let threads := (List.range nthreads).map fun i =>
    rows.filterMap fun row => match row[i]? with
      | some cell => if cell.isEmpty then none else some cell
      | none => none
  -- final section
  let finalText := " ".intercalate finals
  let mut locations : List Obs := []
  let mut quant := Quant.exists
  let mut cond := Cond.true
  let mut t := finalText
  while !(trim t).isEmpty do
    t := trim t
    if t.startsWith "locations" then
      let after := trim (sdrop t "locations".length)
      -- the `]` closing the list, skipping the brackets of `a[0]`
      let some (inner, after') := splitMatchingBracket (sdrop after 1) | throw "bad locations"
      locations := (inner.splitOn ";").filterMap fun s => if (trim s).isEmpty then none else parseObs s
      t := after'
    else
      let (q, after) :=
        if t.startsWith "~exists" then (Quant.notExists, sdrop t 7)
        else if t.startsWith "exists" then (Quant.exists, sdrop t 6)
        else if t.startsWith "forall" then (Quant.forall, sdrop t 6)
        else (Quant.exists, t)
      if after == t then throw s!"unsupported final clause: {t}"
      quant := q
      let after := trim after
      let after := if after.endsWith ";" then dropLast after else after
      match parseCond (tokenize after) with
      | some (c, []) => cond := c
      | some (_, extra) => throw s!"trailing tokens in condition: {repr extra}"
      | none => throw s!"bad condition: {after}"
      t := ""
  return { arch, name, inits, threads, quant, cond, locations }

/-! ## Evaluating conditions and printing herd-style results -/

/-- A final state: the observables and their values. -/
abbrev FinalState := List (Obs × Value)

/-- `norm o v` re-presents a literal `v` the way the observable `o`'s values
are presented (width, signedness), so that `0:X1=0xffffffff` matches a
32-bit register holding `-1`. -/
def Cond.eval (env : Obs → Option Value) (norm : Obs → Value → Value := fun _ v => v) : Cond → Bool
  | .eq o v => env o == some (norm o v)
  | .not c => !c.eval env norm
  | .and a b => a.eval env norm && b.eval env norm
  | .or a b => a.eval env norm || b.eval env norm
  | .true => Bool.true

/-- The observables a condition mentions. -/
def Cond.obs : Cond → List Obs
  | .eq o _ => [o]
  | .not c => c.obs
  | .and a b | .or a b => a.obs ++ b.obs
  | .true => []

/-- Everything a test observes: the condition's observables and `locations`. -/
def Test.observables (t : Test) : List Obs := (t.cond.obs ++ t.locations).eraseDups

/-- An observable as herd prints it: a scalar location as `[x]`, an array
element or a whole array bare (`a[1]`, `a`). -/
def Obs.toString : Obs → String
  | .reg r => s!"{r.tid}:{r.reg}"
  | .loc x => if (arrayRef? x).isSome then x else s!"[{x}]"

partial def Value.toString : Value → String
  | .num n => s!"{n}"
  | .sym x => x
  | .arr vs => "{" ++ ",".intercalate (vs.map Value.toString) ++ "}"

/-- One entry of a state line: a whole array prints bare, `a={1,2}`. -/
def entryString (o : Obs) (v : Value) : String :=
  match o, v with
  | .loc x, .arr _ => s!"{x}={v.toString}"
  | _, _ => s!"{o.toString}={v.toString}"

/-- herd's ordering of state entries: thread registers by thread then
register, memory locations after. -/
def Obs.key : Obs → String
  | .reg r => s!"0:{r.tid}:{r.reg}"
  | .loc x => s!"1:0:{x}"

/-- One state line, `0:X0=1; 1:X2=0;`. -/
def FinalState.line (s : FinalState) : String :=
  let sorted := s.mergeSort fun a b => decide (a.1.key ≤ b.1.key)
  " ".intercalate (sorted.map fun (o, v) => s!"{entryString o v};")

def Cond.toString : Cond → String
  | .eq o v => entryString o v
  | .not c => s!"not ({c.toString})"
  | .and a b => s!"{a.toString} /\\ {b.toString}"
  | .or a b => s!"{a.toString} \\/ {b.toString}"
  | .true => "true"

/-- Does the test's expectation hold of these final states? (`Ok`/`No`.) -/
def verdict (t : Test) (states : List FinalState) (norm : Obs → Value → Value := fun _ v => v) : Bool :=
  let env (s : FinalState) (o : Obs) : Option Value := (s.find? (·.1 == o)).map (·.2)
  let p := (states.filter fun s => t.cond.eval (env s) norm).length
  let n := states.length - p
  match t.quant with
  | .exists => decide (p > 0)
  | .notExists => p == 0
  | .forall => n == 0

/-- herd's report for a set of final states. `kind` overrides the verdict
label (from a `kinds.txt`); otherwise it follows the quantifier. -/
def report (t : Test) (states : List FinalState) (kind : Option String := none)
    (norm : Obs → Value → Value := fun _ v => v) : String :=
  let env (s : FinalState) (o : Obs) : Option Value := (s.find? (·.1 == o)).map (·.2)
  let hits := states.filter fun s => t.cond.eval (env s) norm
  let p := hits.length
  let n := states.length - p
  let kindStr := kind.getD (match t.quant with
    | .exists => "Allowed" | .notExists => "Forbidden" | .forall => "Required")
  -- `Positive`/`Negative` count the whole condition; `Observation` counts
  -- the existential core.
  let (pos, neg) := match t.quant with
    | .notExists => (n, p)
    | _ => (p, n)
  let ok : Bool := match t.quant with
    | .exists => decide (p > 0)
    | .notExists => p == 0
    | .forall => n == 0
  let obsWord := if p == 0 then "Never" else if n == 0 then "Always" else "Sometimes"
  let quantStr := match t.quant with
    | .exists => "exists" | .notExists => "~exists" | .forall => "forall"
  let lines := (states.map FinalState.line).mergeSort (· ≤ ·)
  "\n".intercalate <| [s!"Test {t.name} {kindStr}", s!"States {states.length}"] ++ lines ++
    [if ok then "Ok" else "No", "Witnesses", s!"Positive: {pos} Negative: {neg}",
     s!"Condition {quantStr} ({t.cond.toString})",
     s!"Observation {t.name} {obsWord} {p} {n}", ""]

end Kraken.Litmus
