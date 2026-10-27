/-
# DocU — UnElab snippets in checked documents (`tools/cldoc.py`, `syntax=u`)

For `syntax=u` every checking and running option applies to the elaboration (the snippet's `it` is the core
AST, as for `syntax=cl`); what is typeset is the author's UnElab text, or (`show=lowered`/`both`) the
elaboration, through `Doc`'s printers.  This module adds:

* `dispSourceU`: the author's text with a tooltip on every variable occurrence, its type in the checker's
  context there.  The occurrences are placed through the parser's position table, not by matching identifiers
  in order (`Doc.dispSourceT`), because the elaboration reorders operands and adds temporaries that have no
  source text: an identifier inside the source span of a core node gets the context before that node (the
  innermost span that uses the name); a binder gets the context where it is first bound (`USyntax.Bind`).  A
  nested operand's first token (its `(`, or its first token if it is bare) also says what it becomes:
  `let «%k» = …`.  If some core variable occurrence is not found in its span, the snippet fails rather than
  show a tooltip on the wrong token.
* `check`: `Doc.check` where, in an expected refusal message, a temporary `«%k»` (any number, or `k`) matches
  any temporary.

Nothing here is trusted: tooltips and typesetting only; the verdicts are `Doc.check`'s and the machine's.
-/
import WeakCore.Doc
import WeakCore.USyntax
import WeakCore.UDiag
open CoreLang CoreTerm Syntax UnElab USyntax CoreUtils

namespace DocU

/-- The atoms a core node reads at its head (its subterms excluded). -/
def headAts : Expr → List At
  | .let_ _ op _ => TermScope.opAts op
  | .split a .. | .unpack a .. | .unpackT a .. | .region a .. | .openPub a .. | .case a .. | .ifnull a ..
  | .parity a .. | .ret a | .tail _ _ a _ => [a]
  | .ifeq a b .. => [a, b]
  | .cas _ _ w e v .. => [w, e, v]
  | .casp _ _ w e0 e1 v0 v1 .. => [w, e0, e1, v0, v1]

/-- The user variables a node reads, with multiplicity. -/
def uses (e : Expr) : List String :=
  (headAts e).filterMap fun a => match a with
    | .var x => if reserved x then none else some x
    | _ => none

/-- Every core node of a body with its path and the checker's context before it (`none`: not reached). -/
partial def nodes (p : Prog) (cx : Option Cx) (e : Expr) (path : List Nat := []) :
    List (List Nat × Option Cx × Expr) :=
  let bs : List (Option Cx) := match cx with
    | some c => Scope.branches p c e
    | none => []
  (path, cx, e) :: ((UDiag.kids e).zipIdx.flatMap fun (c, i) => nodes p (bs[i]?.join) c (path ++ [i]))

/-- A node with a source span, and how many occurrences of each name it still expects. -/
structure Ent where
  sp   : Span
  cx   : Option Cx
  tvt  : List String
  node : Expr
  left : List String

def Ent.size (en : Ent) : Nat := (en.sp.eline - en.sp.line) * 100000 + en.sp.ecol - en.sp.col

def lexLt (a b : Nat × Nat) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

def inSpan (sp : Span) (l c : Nat) : Bool := !lexLt (l, c) (sp.line, sp.col) && lexLt (l, c) (sp.eline, sp.ecol)

/-- Remove one occurrence. -/
def eraseOne (x : String) : List String → List String
  | [] => []
  | y :: ys => if y == x then ys else y :: eraseOne x ys

/-- `"%k"`-style temporaries in a message, normalised: `«%3»`, `«%k»`, `%3` all become `%k`. -/
partial def normTmp (s : String) : String :=
  let rec go : List Char → List Char → List Char
    | [], acc => acc.reverse
    | '«' :: '%' :: r, acc =>
        let ds := r.takeWhile (fun c => c.isDigit || c == 'k')
        match r.drop ds.length with
        | '»' :: r' => if ds.isEmpty then go r' ('»' :: '%' :: '«' :: acc) else go r' ('k' :: '%' :: acc)
        | r' => go r' ('k' :: '%' :: acc)
    | '%' :: r, acc =>
        let ds := r.takeWhile Char.isDigit
        if ds.isEmpty then go r ('%' :: acc) else go (r.drop ds.length) ('k' :: '%' :: acc)
    | c :: r, acc => go r (c :: acc)
  String.ofList (go s.toList [])

#guard normTmp "«%12» was already used; «%k» and %3 too, 50% off" == "%k was already used; %k and %k too, 50% off"

/-- `Doc.check`, with `«%k»` in the expected message matching any temporary. -/
def check {γ : Type} [Doc.Checkable γ] (L : Prog) (x : γ) (expect : Option String := none) : Doc.Out :=
  match Doc.Checkable.check L x, expect with
  | .ok _, none => { tex := "\\claccepted" }
  | .error e, none => Doc.fail s!"the checker refused it: {e}"
  | .ok _, some why => Doc.fail s!"expected a refusal mentioning \"{why}\", but the checker accepted it"
  | .error e, some why =>
      if ((normTmp e).splitOn (normTmp why)).length > 1 then { tex := "\\clrefused{" ++ Doc.texEsc e ++ "}" }
      else Doc.fail s!"refused, but for another reason: {e} (expected \"{why}\")"

/-! ## The author's text with tooltips -/

/-- The state of the walk over the source: entries (with what they still expect), binders, output, failures. -/
structure W where
  ents  : Array Ent
  out   : String := ""
  bad   : List String := []

/-- The tooltip text of variable `x` in `cx`. -/
def tipText (st : Doc.Style) (env : Env) (cx : Option Cx) (tvt : List String) (x : String) : Option String :=
  match cx.bind (fun c => Doc.varTipText env c tvt x) with
  | some t => some t
  | none => if st.strict then none else some (x ++ " : not in the checker's context here")

/-- What a nested operand becomes: `let «%k» = op`, with the temporary's type where the checker has it. -/
def nestedText (env : Env) (en : Ent) (after : Option Cx) : String :=
  match en.node with
  | .let_ x op _ =>
      let sc : Sc := { tvs := en.tvt, ivs := (en.cx.map (·.inames.map some)).getD [] }
      let ty := (after.bind fun c => Doc.varTipText env c en.tvt x).map (fun t => "   (" ++ t.replace x ("«" ++ x ++ "»") ++ ")")
      s!"let «{x}» = {Syntax.showOp env sc op}" ++ ty.getD ""
  | _ => ""

/-- Typeset an UnElab program's text `src`, with tooltips (see the module comment).  `st.lib` is the library;
`env` the concrete-syntax environment the snippet was parsed in. -/
partial def dispSourceU (st : Doc.Style) (env : Env) (src : String) : Doc.Out :=
  match parseUnit src env with
  | .error e => Doc.fail s!"@{e.line}:{e.col} {e.msg}"
  | .ok r =>
    let tenv := st.tips.getD env
    let own := elabProg r.unit.decls
    let p := own ++ st.lib
    let sp := r.spans.toList
    -- every core node with a span; the contexts by (block, path)
    let perBlock := own.map fun d =>
      let tvt := (tparamNames d.tparams []).reverse
      (d, tvt, nodes p (some (Scope.start d)) d.body)
    let ctxAt (blk : String) (path : List Nat) : Option (Option Cx × List String) :=
      (perBlock.find? (·.1.name == blk)).bind fun (_, tvt, ns) =>
        (ns.find? (·.1 == path)).map fun n => (n.2.1, tvt)
    let ents : Array Ent := (perBlock.flatMap fun (d, tvt, ns) => ns.filterMap fun (path, cx, e) =>
      (spanAt sp d.name path).map fun s => { sp := s, cx, tvt, node := e, left := uses e }).toArray
    let tipFor (st' : Doc.Style) (cx : Option Cx) (tvt : List String) (x : String) : String × Bool :=
      match tipText st' tenv cx tvt x with
      | some t => (t, true)
      | none => (x ++ " : no type in the checker's context", false)
    -- the walk
    let lines := (src.trimAsciiEnd.toString.splitOn "\n")
    let rec walkLine (ln : Nat) (cs : List Char) (col : Nat) (w : W) : W :=
      match cs with
      | [] => w
      | '-' :: '-' :: rest => { w with out := w.out ++ Doc.alltt ("--" ++ String.ofList rest) }
      | c :: rest =>
        -- nested operands starting here
        let nest := w.ents.toList.filter fun en => en.sp.line == ln && en.sp.col == col && reserved en.sp.what
        let nestTxt := nest.map fun en =>
          let after := match en.node with
            | .let_ x op _ => en.cx.bind fun c => (checkOp p c x op).toOption
            | _ => none
          nestedText tenv en after
        if Syntax.isIdChar c && !c.isDigit then
          let wd := String.ofList (cs.takeWhile Syntax.isIdChar)
          let n := wd.length
          let bnd := r.binds.toList.find? fun b => b.line == ln && b.col == col && b.name == wd
          let (tip, ok, w) : Option String × Bool × W := match bnd with
            | some b => match ctxAt b.block b.ctx with
              | some (cx, tvt) => let (t, ok) := tipFor st cx tvt wd; (some t, ok, w)
              | none => (some (wd ++ " : not in the checker's context here"), !st.strict, w)
            | none =>
              let cands := (w.ents.toList.zipIdx.filter fun (en, _) => inSpan en.sp ln col && en.left.contains wd)
              match cands.foldl (fun best (en, i) => match best with
                  | none => some (en, i)
                  | some (b, j) => if en.size < b.size then some (en, i) else some (b, j)) none with
              | some (en, i) =>
                  let (t, ok) := tipFor st en.cx en.tvt wd
                  (some t, ok, { w with ents := w.ents.set! i { en with left := eraseOne wd en.left } })
              | none => (none, true, w)
          let all := (tip.toList ++ nestTxt)
          let piece := if all.isEmpty then Doc.alltt wd
            else cltip ("; ".intercalate all) (Doc.alltt wd)
          let w := { w with out := w.out ++ piece, bad := if ok then w.bad else s!"{ln}:{col} {wd}" :: w.bad }
          walkLine ln (cs.drop n) (col + n) w
        else
          let piece := if nestTxt.isEmpty then Doc.alltt c.toString
            else cltip ("; ".intercalate nestTxt) (Doc.alltt c.toString)
          walkLine ln rest (col + 1) { w with out := w.out ++ piece }
    let rec walk : List String → Nat → W → W
      | [], _, w => w
      | l :: ls, ln, w =>
          let w := walkLine ln l.toList 1 w
          walk ls (ln + 1) (if ls.isEmpty then w else { w with out := w.out ++ "\n" })
    let w := walk lines 1 { ents }
    let missing := w.ents.toList.filter (!·.left.isEmpty)
    let err :=
      if !missing.isEmpty then
        some ("the source text and the elaboration do not line up (tooltips): " ++
          ", ".intercalate (missing.map fun en => s!"{en.sp.line}:{en.sp.col} {en.left}"))
      else if !w.bad.isEmpty then
        some ("a variable occurrence has no type in the checker's context (no tooltip): " ++
          ", ".intercalate w.bad.reverse)
      else none
    { tex := "\\begin{clsrc}\n" ++ w.out ++ "\n\\end{clsrc}", err }

end DocU
