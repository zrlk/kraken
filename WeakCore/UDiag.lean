/-
# UDiag — diagnostics for UnElab sources

A diagnostic prints `file:line:col: in f: message`, then the source line in a line-number gutter with the
offending span underlined (`^~~~`), then any secondary labelled spans the same way.

A checker error is placed on the source operand that became the failing core node: the checker runs block by
block (`checkDecl`, which names the block), and `locate` walks the elaborated body with `Scope.branches` — the
checker's own context for each immediate subterm, `none` where the checker would stop — to the first core node
the checker fails at; the parser's span table (block, core path) ↦ source range gives the position.  Nothing
here is trusted: a wrong position misplaces a message, never changes a verdict (the verdict is `checkDecl`'s).

`diagnose` continues after errors: parse errors (resynchronised at the next top-level item), then one checker
error per block (each block checked independently against all signatures), then rule 4's lint as warnings.
-/
import WeakCore.USyntax
import WeakCore.UCheck
import WeakCore.Scope
open CoreLang CoreTerm Syntax UnElab USyntax

namespace UDiag

/-- A source range with a label (`line`/`col` 1-based; `eline`/`ecol` the end, exclusive). -/
structure Rng where
  line  : Nat
  col   : Nat
  eline : Nat
  ecol  : Nat
  label : String := ""
  deriving Repr, BEq, Inhabited

structure Diag where
  file     : String
  severity : String := "error"
  block    : Option String := none
  msg      : String
  at_      : Rng
  notes    : List Rng := []
  deriving Repr, Inhabited

def Rng.ofSpan (s : Span) (label : String := "") : Rng :=
  { line := s.line, col := s.col, eline := s.eline, ecol := s.ecol, label }

/-! ## Rendering -/

def padL (w : Nat) (s : String) : String := String.ofList (List.replicate (w - s.length) ' ') ++ s

/-- The gutter and underline for one range: the range's first line, underlined from `col` to the end of the
range (or of the line, for a range spanning lines); at least one `^`. -/
def excerpt (lines : Array String) (w : Nat) (r : Rng) : List String :=
  let src := lines[r.line - 1]?.getD ""
  let stop := if r.eline == r.line then r.ecol else src.length + 1
  let n := if stop > r.col then stop - r.col else 1
  let mark := "^" ++ String.ofList (List.replicate (n - 1) '~')
  let lab := if r.label.isEmpty then "" else " " ++ r.label
  [padL w (toString r.line) ++ " | " ++ src,
   String.ofList (List.replicate w ' ') ++ " | " ++ String.ofList (List.replicate (r.col - 1) ' ') ++ mark ++ lab]

def render (src : String) (d : Diag) : String :=
  let lines := (src.splitOn "\n").toArray
  let w := ((d.at_ :: d.notes).map (fun r => (toString r.line).length)).foldl max 1
  -- `file:line:col: in f: message` for an error; a warning (or note) says so
  let sev := if d.severity == "error" then "" else d.severity ++ ": "
  let head := s!"{d.file}:{d.at_.line}:{d.at_.col}: " ++ sev ++
    (match d.block with | some b => s!"in {b}: " | none => "") ++ d.msg
  String.intercalate "\n" (head :: excerpt lines w d.at_ ++ d.notes.flatMap (excerpt lines w))

/-! ## Placing a checker error -/

/-- The immediate subterms of a core term, in `Scope.branches` order. -/
def kids : Expr → List Expr
  | .let_ _ _ e | .split _ _ _ e | .unpack _ _ _ e | .unpackT _ _ _ e | .region _ _ _ _ e
  | .openPub _ _ _ _ e => [e]
  | .case _ _ e1 _ e2 | .ifnull _ e1 _ e2 | .parity _ _ e1 e2 | .ifeq _ _ e1 e2
  | .cas _ _ _ _ _ _ e1 e2 | .casp _ _ _ _ _ _ _ _ e1 e2 => [e1, e2]
  | .ret _ | .tail .. => []

/-- The core path (child indices, from the root) of the node the checker fails at, if `check p cx e` fails:
the first subterm the checker does not reach makes its parent the culprit; otherwise the first failing subterm
is entered; a failing node with no failing subterm is the culprit. -/
partial def locate (p : Prog) (cx : Cx) (e : Expr) (path : List Nat := []) : Option (List Nat) :=
  match check p cx e with
  | .ok _ => none
  | .error _ =>
      let rec go : List (Option Cx × Expr) → Nat → List Nat
        | [], _ => path
        | (none, _) :: _, _ => path
        | (some cx', c) :: rest, i =>
            match locate p cx' c (path ++ [i]) with
            | some q => q
            | none => go rest (i + 1)
      some (go ((Scope.branches p cx e).zip (kids e)) 0)

/-- The span of the core node at `path`, or of its nearest ancestor that has one. -/
def spanOf (sp : List Span) (blk : String) (path : List Nat) : Option Span :=
  let rec up : List Nat → Nat → Option Span
    | q, 0 => spanAt sp blk q
    | q, fuel + 1 => match spanAt sp blk q with
      | some s => some s
      | none => if q.isEmpty then none else up q.dropLast fuel
  up path path.length

/-! ## Rule 4's lint, placed

`ret f(args)` elaborates to `let «%k» = f(args)` immediately followed by `ret «%k»`, and only it does (a user
cannot write a `%` name); so the lint is found on the core with the span table (`UCheck.retCallLint` is the same
check on the UnElab AST; the tests compare the two). -/
def retSites (blocks : List String) : Expr → List Nat → List (List Nat × String)
  | .let_ x (.call f _ _ _) (.ret (.var y)), path =>
      if x == y && reserved x && blocks.contains f then [(path, f)] else []
  | .let_ _ _ e, path | .split _ _ _ e, path | .unpack _ _ _ e, path | .unpackT _ _ _ e, path
  | .region _ _ _ _ e, path | .openPub _ _ _ _ e, path => retSites blocks e (path ++ [0])
  | .case _ _ e1 _ e2, path | .ifnull _ e1 _ e2, path | .parity _ _ e1 e2, path | .ifeq _ _ e1 e2, path
  | .cas _ _ _ _ _ _ e1 e2, path | .casp _ _ _ _ _ _ _ _ e1 e2, path =>
      retSites blocks e1 (path ++ [0]) ++ retSites blocks e2 (path ++ [1])
  | _, _ => []

/-! ## All diagnostics of a unit -/

/-- Every diagnostic of an UnElab unit `src` (named `file`), in order: parse errors, one checker error per block,
then the `ret f(args)` warnings.  `env` supplies the imports' signatures. -/
def diagnose (file src : String) (env : Env := {}) : List Diag :=
  let lines := (src.splitOn "\n").toArray
  let slice (c : Span) : String :=
    if c.line == c.eline then String.ofList (((lines[c.line - 1]?.getD "").toList.drop (c.col - 1)).take (c.ecol - c.col))
    else "…"
  let r := parseUnitAll src env
  let sp := r.spans.toList
  let parseDs := r.errs.map fun e =>
    { file, msg := e.msg, at_ := { line := e.line, col := e.col, eline := e.line, ecol := e.col + 1 } : Diag }
  let own := elabProg r.unit.decls
  let p := env.lib.reverse ++ own
  let blocks := p.map (·.name)
  let checkDs := own.filterMap fun d =>
    match checkDecl p d with
    | .ok _ => none
    | .error m =>
        let path := (locate p (Scope.start d) d.body).getD []
        let rng := match spanOf sp d.name path with
          | some s => Rng.ofSpan s
          | none => { line := 1, col := 1, eline := 1, ecol := 2 }
        some { file, block := some d.name, msg := m, at_ := rng }
  let lintDs := own.flatMap fun d =>
    (retSites blocks d.body []).filterMap fun (path, f) =>
      (spanOf sp d.name (path ++ [0])).map fun s =>
        { file, severity := "warning", block := some d.name,
          msg := s!"`ret {f}(…)` returns after a call (a stack frame per call): did you mean `tail {f}(args)`?",
          at_ := Rng.ofSpan s,
          notes := ((spanAt sp d.name path).map fun c => Rng.ofSpan c ("suggested: tail " ++ slice c)).toList }
  parseDs ++ checkDs ++ lintDs

def renderAll (src : String) (ds : List Diag) : String := String.intercalate "\n" (ds.map (render src))

end UDiag
