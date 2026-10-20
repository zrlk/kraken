/-
# Doc — helpers for checked CoreLang documents

A document tool turns a LaTeX file with `cl` blocks into a Lean driver that
imports this module (and whatever the document asks for), evaluates each
snippet, and writes one fragment per item: `<dir>/<id>.tex` (the LaTeX to
splice in) and `<dir>/<id>.status` (`OK`, or `FAIL <why>`).  Nothing here is
trusted: the checker and the machine are the ones in `CoreTerm`/`TermRun`;
this file only calls them and formats what they say.

Every item is an `Out`: some LaTeX and, possibly, a failure.  A block is the
concatenation (`cat`) of the parts its options ask for:

| part      | what it does |
|-----------|--------------|
| `disp`    | typeset the snippet (a `Decl`, `Prog`, `Ty`, `Op`, `Expr`, `Proto`, `Kind`) |
| `check`   | `checkDecl`/`checkProg`, then the local-token discipline (`Robust.checkDeclL`); must accept, or must reject with a given reason |
| `sig`     | a code block's signature |
| `kind`    | a type's width and kind facts |
| `robust`  | a protocol's crash-robustness and ABA report (`Robust.report`) |
| `opType`  | the type the checker binds for an op, in a given context |
| `run`     | one thread on the machine, from an empty memory |
| `threads` | a setup thread, then several threads explored exhaustively |

Build: LEAN_PATH=build lean -o build/Doc.olean Doc.lean
(after CoreUtils.olean and TermSmoke.olean)
-/
import WeakCore.TermSmoke
import WeakCore.TermLive
import WeakCore.CoreUtils
import WeakCore.Syntax
import WeakCore.Robust
open CoreLang CoreTerm TermRun TermSmoke TermLive CoreUtils
open WeakMem (Val)

namespace Doc

/-! ## Output -/

structure Out where
  tex : String := ""
  err : Option String := none

def cat (os : List Out) : Out :=
  { tex := "\n".intercalate ((os.map (·.tex)).filter (· ≠ ""))
    err := match os.filterMap (·.err) with
      | [] => none
      | es => some ("; ".intercalate es) }

def fail (why : String) : Out := { err := some why }

/-- Text-mode escaping for checker messages and names. -/
def texEsc (s : String) : String :=
  String.join (s.toList.map fun c => match c with
    | '\\' => "\\textbackslash{}"
    | '{' => "\\{" | '}' => "\\}" | '_' => "\\_" | '&' => "\\&" | '%' => "\\%"
    | '#' => "\\#" | '$' => "\\$" | '~' => "\\textasciitilde{}" | '^' => "\\textasciicircum{}"
    | c => c.toString)

#guard texEsc "a_b {x} 50% #1" == "a\\_b \\{x\\} 50\\% \\#1"

/-- Write the fragment and its status (the driver's only side effect). -/
def emit (dir id : String) (o : Out) : IO Unit := do
  IO.FS.writeFile (dir ++ "/" ++ id ++ ".tex") o.tex
  IO.FS.writeFile (dir ++ "/" ++ id ++ ".status")
    (match o.err with
     | none => "OK\n"
     | some e => "FAIL " ++ (e.replace "\n" " ") ++ "\n")

/-! ## Typesetting a snippet -/

/-- How a document typesets: its type abbreviations, and the protocols it
prints by name (the library's, and those its `%!cl proto` lines declare). -/
structure Style where
  abbrevs : Abbrevs := []
  protos  : List (Proto × String) := protoNames
  /-- Code blocks a snippet may call (its library), so index variables bound
  by loads are named exactly (`Scope`). -/
  lib     : Prog := []
  /-- Hover tooltips: every variable occurrence in a code block carries its
  type, and every type written in code its kind, printed in the concrete
  syntax of this environment (`CoreUtils.cltip`).  `none`: no tooltips. -/
  tips    : Option Syntax.Env := none
  /-- Every variable occurrence must be in the checker's context.  Off for a
  snippet that must be refused, whose point may be exactly a variable that is
  not (its tooltip then says so). -/
  strict  : Bool := true

instance : Coe Abbrevs Style := ⟨fun ab => { abbrevs := ab }⟩

/-- A type's kind facts as plain text, for a tooltip. -/
def kindText (t : Ty) : String :=
  let w := match t.width.bind Idx.closed with
    | some n => s!"width {n}"
    | none => "width depends on indices"
  ", ".intercalate [w,
    if t.affine then "affine" else "copyable",
    if t.zeroable then "zeroable" else "not zeroable",
    if t.sensitive then "view-sensitive" else "not view-sensitive",
    if t.secondClass then "second-class" else "first-class"]

/-- The tooltip for variable `x` in the checker's context `cx`: its type, in
the concrete syntax, with the index variables the checker has in scope. -/
def varTipText (env : Syntax.Env) (cx : Cx) (tvt : List String) (x : String) : Option String :=
  let txt (t : Ty) := Syntax.showTy env { tvs := tvt, ivs := cx.inames.map some } 0 t
  match cx.vars.find? (·.1 == x) with
  | some (_, t, live) => some (x ++ " : " ++ txt t ++ (if live then "" else "   (affine, already used)"))
  | none =>
    -- A torn read (§4.4): not a value yet, until the seqlock word is rechecked.
    (cx.torn.find? (·.x == x)).map fun tr =>
      let ph := match tr.φ with
        | .opn => "open" | .fenced => "fenced" | .rechecked _ => "rechecked"
      x ++ " :~ " ++ txt tr.ty ++ "   (torn read under " ++ tr.w ++ ", " ++ ph ++ ")"

def Style.names (st : Style) : Names :=
  { abbrevs := st.abbrevs, protos := st.protos,
    tipVar := st.tips.map fun env cx tvt x =>
      (varTipText env cx tvt x).orElse fun _ =>
        if st.strict then none else some (x ++ " : not in the checker's context here")
    tipTy := st.tips.map fun _ t => some ("kind: " ++ kindText t) }

/-- The protocols a concrete-syntax environment names, for `Style.protos`. -/
def protosOf (env : Syntax.Env) : List (Proto × String) :=
  env.protos.map (fun (n, P) => (P, esc n)) ++ protoNames

/-- `block` is display material (math already wrapped); `inl` is the content of
inline math. -/
class Render (α : Type) where
  block : Style → α → String
  inl   : Style → α → String

/-- A code block's names, as `fmtDecl` sets them up. -/
def declNames (d : Decl) (st : Style) : Names × List String :=
  let tns := tparamNames d.tparams []
  ({ st.names with tv := tns.reverse, iv := d.idx.reverse.map ident, tbase := tns.length }, tns)

/-- `f[α]{r} : σ → τ`. -/
def sigOf (st : Style) (d : Decl) : String :=
  let (n, tns) := declNames d st
  let tps := (tns.zip d.tparams).map fun (a, κ) =>
    if κ == {} then a else a ++ "{:}" ++ fmtKind κ
  fn (esc d.name) ++
    (if tps.isEmpty then "" else "[" ++ commas tps ++ "]") ++
    (if d.idx.isEmpty then "" else "\\{" ++ commas (d.idx.map ident) ++ "\\}") ++
    " : " ++ fmtTy n 0 d.argTy ++ " \\to " ++ fmtTy n 0 d.retTy

instance : Render Decl where
  block st d := "\\begin{clcode}\n$" ++ fmtDecl d st.abbrevs st.protos st.lib st.names ++ "$\n\\end{clcode}"
  inl st d := sigOf st d

/-- Each block typeset knowing the blocks before it (as the parser reads them). -/
def progBlocks (st : Style) : Prog → Prog → List String
  | [], _ => []
  | d :: ds, prev =>
      ("\\begin{clcode}\n$" ++ fmtDecl d st.abbrevs st.protos (prev ++ st.lib) st.names ++ "$\n\\end{clcode}") ::
        progBlocks st ds (d :: prev)

instance : Render Prog where
  block st p := "\n".intercalate (progBlocks st p [])
  inl _ p := commas (p.map fun d => fn (esc d.name))

instance : Render Ty where
  block st t := "\\[" ++ st.names.tyTip t (fmtType t [] st.abbrevs [] st.protos) ++ "\\]"
  inl st t := st.names.tyTip t (fmtType t [] st.abbrevs [] st.protos)

instance : Render Op where
  block st o := "\\[" ++ fmtOp st.names o ++ "\\]"
  inl st o := fmtOp st.names o

instance : Render Expr where
  block st e := "\\begin{clcode}\n$" ++ fmtLines (fmtExpr st.names 0 e) ++ "$\n\\end{clcode}"
  inl st e := "; ".intercalate ((fmtExpr st.names 0 e).map (·.2))

instance : Render Proto where
  block st P := "\\[" ++ fmtProto P st.protos ++ "\\]"
  inl st P := fmtProto P st.protos

instance : Render Kind where
  block _ κ := "\\[" ++ fmtKind κ ++ "\\]"
  inl _ κ := fmtKind κ

/-- A typeset snippet must have a tooltip on every variable occurrence the
checker's context covers (`CoreUtils.Names.varTip`). -/
def tipsOK (tex : String) : Out :=
  if (tex.splitOn "\\clnotip").length > 1 then
    fail "a variable occurrence has no type in the checker's context (no tooltip)"
  else {}

def disp {γ : Type} [Render γ] (st : Style) (x : γ) : Out :=
  let tex := Render.block st x
  { tex := tex, err := (tipsOK tex).err }
def inline {γ : Type} [Render γ] (st : Style) (x : γ) : Out :=
  let tex := Render.inl st x
  { tex := "\\ensuremath{" ++ tex ++ "}", err := (tipsOK tex).err }

/-! ## The concrete syntax (`Syntax.lean`) in documents -/

/-- Printable in the concrete syntax. -/
class Textual (γ : Type) where
  text : Syntax.Env → γ → String

instance : Textual Decl := ⟨fun env d => Syntax.showDecl d env⟩
instance : Textual Prog := ⟨fun env p => Syntax.showProg p env⟩
instance : Textual Ty := ⟨fun env t => Syntax.showType t env⟩
instance : Textual Op := ⟨fun env o => Syntax.showOp env {} o⟩
instance : Textual Expr := ⟨fun env e => Syntax.showExpr e env⟩

/-- Text for an `alltt` environment: braces and backslashes escaped, the
Unicode the syntax accepts as math. -/
def alltt (s : String) : String :=
  let m (c : String) := "\\ensuremath{" ++ c ++ "}"
  String.join (s.toList.map fun c => match c with
    | '\\' => "\\textbackslash{}" | '{' => "\\{" | '}' => "\\}"
    | 'α' => m "\\alpha" | 'β' => m "\\beta" | 'γ' => m "\\gamma" | 'δ' => m "\\delta"
    | 'ε' => m "\\epsilon" | 'ζ' => m "\\zeta" | 'η' => m "\\eta" | 'θ' => m "\\theta"
    | 'μ' => m "\\mu" | 'ν' => m "\\nu" | 'κ' => m "\\kappa" | 'σ' => m "\\sigma" | 'τ' => m "\\tau"
    | '∃' => m "\\exists" | '∀' => m "\\forall" | '×' => m "\\times" | '·' => m "\\cdot"
    | '→' => m "\\to" | '↦' => m "\\mapsto" | '⇒' => m "\\Rightarrow"
    | '⟨' => m "\\langle" | '⟩' => m "\\rangle" | '≤' => m "\\le" | '≥' => m "\\ge"
    | '∧' => m "\\wedge" | '⊤' => m "\\top" | '«' => m "\\langle\\!\\langle" | '»' => m "\\rangle\\!\\rangle"
    | c => c.toString)

#guard alltt "f{r}(x : α)" == "f\\{r\\}(x : \\ensuremath{\\alpha})"

/-- Typeset in the concrete syntax, as the printer writes it. -/
def dispText {γ : Type} [Textual γ] (env : Syntax.Env) (x : γ) : Out :=
  { tex := "\\begin{clsrc}\n" ++ alltt (Textual.text env x) ++ "\n\\end{clsrc}" }

/-- Typeset the author's own source text. -/
def dispSource (src : String) : Out :=
  { tex := "\\begin{clsrc}\n" ++ alltt src.trimAsciiEnd.toString ++ "\n\\end{clsrc}" }

/-! ### Tooltips on the author's own text

The math printer puts a tooltip on every variable occurrence (`CoreUtils.cltip`)
and knows the checker's context there.  The author's text has no such
structure, but the parser reads it in order and the printer writes the parsed
program in the same order, so the printer's variable occurrences are the
text's identifier tokens that are variables, in order.  `sourceTips` walks the
two together: an identifier equal to the next expected variable gets that
variable's tooltip.  If any expected occurrence is left over, the two did not
line up, and the snippet fails rather than showing a tooltip on the wrong token. -/

/-- The contents of a `{...}` group (the opening brace already read), and the
rest; a backslash escapes the next character. -/
partial def braced : List Char → Nat → List Char → Option (String × List Char)
  | [], _, _ => none
  | '}' :: r, 0, acc => some (String.ofList acc.reverse, r)
  | '}' :: r, d + 1, acc => braced r d ('}' :: acc)
  | '{' :: r, d, acc => braced r (d + 1) ('{' :: acc)
  | '\\' :: c :: r, d, acc => braced r d (c :: '\\' :: acc)
  | c :: r, d, acc => braced r d (c :: acc)

/-- The encoded texts of the `\cltip`s in `tex`, in order. -/
partial def tipTexts : List Char → List String → List String
  | [], acc => acc.reverse
  | '\\' :: 'c' :: 'l' :: 't' :: 'i' :: 'p' :: '{' :: r, acc =>
      match braced r 0 [] with
      | some (_, '{' :: r2) =>
          match braced r2 0 [] with
          | some (t, r3) => tipTexts r3 (t :: acc)
          | none => acc.reverse
      | _ => acc.reverse
  | _ :: r, acc => tipTexts r acc

/-- Undo `CoreUtils.tipEnc`. -/
def tipDec (s : String) : String :=
  let hexv (c : Char) : Nat :=
    if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'A'.toNat + 10
  let rec go : List Char → List UInt8 → List UInt8
    | '\\' :: '%' :: h :: l :: r, acc => go r ((hexv h * 16 + hexv l).toUInt8 :: acc)
    | c :: r, acc => go r (c.toString.toUTF8.toList.reverse ++ acc)
    | [], acc => acc.reverse
  (String.fromUTF8? (ByteArray.mk (go s.toList []).toArray)).getD s

#guard tipDec (tipEnc "x : Int[n+1] {α}") == "x : Int[n+1] {α}"

/-- The variable occurrences of a typeset snippet, in order: the variable's
name and its encoded tooltip.  Types' kind tooltips are not occurrences. -/
def varOccs (tex : String) : List (String × String) :=
  (tipTexts tex.toList []).filterMap fun t =>
    let d := tipDec t
    if d.startsWith "kind: " then none
    else some (String.ofList (d.toList.takeWhile (· != ' ')), t)

/-- The author's text with each variable occurrence wrapped in `\\cltip`
(`occs` in order), and whether every expected occurrence was found. -/
partial def sourceTipsGo (cs : List Char) (occs : List (String × String)) (acc : String) : String × Bool :=
  match cs with
  | [] => (acc, occs.isEmpty)
  | '-' :: '-' :: r =>
      -- a comment: to the end of the line, untouched
      let com := r.takeWhile (· != '\n')
      sourceTipsGo (r.drop com.length) occs (acc ++ alltt ("--" ++ String.ofList com))
  | c :: r =>
      if Syntax.isIdChar c then
        let w := String.ofList (cs.takeWhile Syntax.isIdChar)
        let rest := cs.drop w.length
        match occs with
        | (x, t) :: more =>
            if x == w then sourceTipsGo rest more (acc ++ "\\cltip{" ++ alltt w ++ "}{" ++ t ++ "}")
            else sourceTipsGo rest occs (acc ++ alltt w)
        | [] => sourceTipsGo rest [] (acc ++ alltt w)
      else sourceTipsGo r occs (acc ++ alltt c.toString)

def sourceTips (src : String) (occs : List (String × String)) : String × Bool :=
  sourceTipsGo src.toList occs ""

/-- The author's own text, with the tooltips the printer gives the parsed
snippet `x` (in style `st`, which has `tips` set). -/
def dispSourceT {γ : Type} [Render γ] (st : Style) (src : String) (x : γ) : Out :=
  let occs := varOccs (Render.block st x)
  let (body, ok) := sourceTips src.trimAsciiEnd.toString occs
  { tex := "\\begin{clsrc}\n" ++ body ++ "\n\\end{clsrc}",
    err := if ok then (tipsOK (Render.block st x)).err
           else some "the source text and the parsed program do not line up (tooltips)" }

/-- Go on with a parsed snippet, or fail with `@line:col` (relative to the
snippet; the document tool maps it to the `.tex` line). -/
def parsed {γ : Type} (r : Except Syntax.Err γ) (k : γ → Out) : Out :=
  match r with
  | .ok x => k x
  | .error e => fail s!"@{e.line}:{e.col} {e.msg}"

def getD {γ : Type} (r : Except Syntax.Err γ) (d : γ) : γ :=
  match r with
  | .ok x => x
  | .error _ => d

def dummyDecl : Decl := { name := "?", idx := [], arg := "a", argTy := .unit, retTy := .unit, body := .ret .unit }

/-- Structural equality, for `same=`: a snippet written out is the library's. -/
class Same (γ : Type) where
  same : γ → γ → Bool

instance : Same Decl := ⟨Syntax.sameDecl⟩
instance : Same Prog := ⟨fun p q => p.length == q.length && (p.zip q).all fun (a, b) => Syntax.sameDecl a b⟩
instance : Same Ty := ⟨(· == ·)⟩
instance : Same Op := ⟨Syntax.sameOp⟩
instance : Same Expr := ⟨Syntax.sameExpr⟩

def same {γ : Type} [Same γ] (x y : γ) (what : String) : Out :=
  if Same.same x y then {} else fail s!"the snippet is not the same as {what}"

/-- The environment a document's `%!cl type`/`%!cl proto` lines build. -/
def envFrom (text : String) (base : Syntax.Env := {}) : Except Syntax.Err Syntax.Env :=
  (Syntax.parseProgEnv text base).map (·.2)

/-- A code block's name alone, in the `\fn` style. -/
def name (d : Decl) : Out := { tex := "\\ensuremath{" ++ fn (esc d.name) ++ "}" }

/-! ## Checking -/

/-- Snippets the checker can judge, and the program they contribute to a run. -/
class Checkable (α : Type) where
  check : Prog → α → M Unit
  prog  : α → Prog

/-- A code block is checked against the library with itself in front, so a
variant that tail-calls its own name calls itself. -/
instance : Checkable Decl where
  check L d := Robust.checkDeclL (d :: L) d
  prog d := [d]

instance : Checkable Prog where
  check L p := p.forM (Robust.checkDeclL (p ++ L))
  prog p := p

/-- `expect = none`: must be accepted.  `some why`: must be refused, with a
message containing `why`; the message is typeset. -/
def check {γ : Type} [Checkable γ] (L : Prog) (x : γ) (expect : Option String := none) : Out :=
  match Checkable.check L x, expect with
  | .ok _, none => { tex := "\\claccepted" }
  | .error e, none => fail s!"the checker refused it: {e}"
  | .ok _, some why => fail s!"expected a refusal mentioning \"{why}\", but the checker accepted it"
  | .error e, some why =>
      if (e.splitOn why).length > 1 then { tex := "\\clrefused{" ++ texEsc e ++ "}" }
      else fail s!"refused, but for another reason: {e} (expected \"{why}\")"

def sig (st : Style) (d : Decl) : Out := { tex := "\\clsigline{$" ++ sigOf st d ++ "$}" }

/-! ## Kinds -/

def kindFacts (t : Ty) : List String :=
  let w := match t.width with
    | some i => match i.closed with
      | some n => s!"width {n}"
      | none => "width $" ++ fmtIdx {} 0 i ++ "$"
    | none => "width unknown"
  [w,
   if t.affine then "affine (used at most once)" else "copyable",
   if t.zeroable then "zeroable" else "not zeroable",
   if t.sensitive then "view-sensitive (loads need acq)" else "not view-sensitive",
   if t.secondClass then "second-class (passed, never stored or returned)" else "first-class"]

def kindLine (t : Ty) : String := ", ".intercalate (kindFacts t)

def kind (t : Ty) : Out := { tex := "\\clkindline{" ++ kindLine t ++ "}" }

#guard kindLine .int ==
  "width 1, copyable, zeroable, not view-sensitive, first-class"

/-! ## Robustness -/

def robustLine (P : Proto) : String := texEsc (Robust.report P)

def robust (P : Proto) : Out := { tex := "\\clrobustline{" ++ robustLine P ++ "}" }

/-- The program with the environment's protocol `n` declared local (an unknown
name leaves the program as it is, and a check then says nothing new). -/
def localise (env : Syntax.Env) (n : String) (p : Prog) : Prog :=
  match env.protos.find? (·.1 == n) with
  | some (_, P) => Robust.localise P p
  | none => p

#guard robustLine mutexP ==
  "blocking (a participant that dies in a held state leaves the word stuck); " ++
  "a shared state can repeat a value (ABA: a cas out of it may be fooled)"

/-! ## The type of an op -/

/-- Run `checkOp` on `x := op` in the context `ctx` (index variables `idx`,
outermost first) and read back the type bound for `x`, with the index
variables it is relative to (an op may bind some: a load of a protocol word
binds `x` itself). -/
def opTypeOf (L : Prog) (idx : List String) (ctx : List (String × Ty)) (op : Op) (x : String := "_r") :
    M (Ty × List String) := do
  let cx : Cx := { inames := idx.reverse, vars := ctx.map fun (n, t) => (n, t, true), ret := .unit }
  let cx' ← checkOp L cx x op
  match cx'.vars.find? (·.1 == x) with
  | some (_, t, _) => pure (t, cx'.inames)
  | none => throw "the op bound nothing"

def opType (st : Style) (L : Prog) (idx : List String) (ctx : List (String × Ty)) (op : Op)
    (expect : Option String := none) : Out :=
  -- The context the op is checked in, so its operands carry their types.
  let cx0 : Cx := { inames := idx.reverse, vars := ctx.map fun (n, t) => (n, t, true), ret := .unit }
  let n : Names := { st.names with iv := idx.reverse.map ident, cx := some cx0 }
  -- The op's result is named `v` (or another name not in use), so a type
  -- that mentions an index it binds reads naturally: `load acq w : Int(v)`.
  let x := (["v", "u", "y", "z"].find? fun y => !(ctx.any (·.1 == y)) && !idx.contains y).getD "_r"
  match opTypeOf L idx ctx op x, expect with
  | .ok (t, ins), none =>
      let n' : Names := { n with iv := ins.map ident }
      { tex := "\\cltypeline{$" ++ fmtOp n op ++ " : " ++ fmtTy n' 0 t ++ "$}" }
  | .error e, none => fail s!"the checker refused the op: {e}"
  | .ok _, some why => fail s!"expected a refusal mentioning \"{why}\", but the op was accepted"
  | .error e, some why =>
      if (e.splitOn why).length > 1 then
        { tex := "\\cltypeline{$" ++ fmtOp n op ++ "$}\n\\clrefused{" ++ texEsc e ++ "}" }
      else fail s!"refused, but for another reason: {e} (expected \"{why}\")"

/-! ## Running -/

def fmtVal : Val → String
  | .num n => toString n
  | .null => "\\mathsf{null}"
  | .undef => "\\mathsf{undef}"
  | .loc a t => "\\ell_{" ++ toString a.label ++ (if a.offset == 0 then "" else "+" ++ toString a.offset) ++
                "}" ++ (if t == 0 then "" else "^{" ++ toString t ++ "}")

def fmtVals (vs : List Val) : String :=
  match vs with
  | [] => "()"
  | [v] => fmtVal v
  | vs => "(" ++ commas (vs.map fmtVal) ++ ")"

/-- Result words as plain numbers, for `expect=` (non-numbers never match). -/
def nums (vs : List Val) : Option (List Nat) :=
  vs.mapM fun | .num n => some n | _ => none

/-- One thread, alone, from an empty memory. -/
def run (p : Prog) (f : String) (argTy : Ty) (args : List Nat) (ts : List Ty := [])
    (expect : Option (List Nat) := none) (depth : Nat := 60) : Out :=
  let call := fn (esc f) ++ "(" ++ commas (args.map toString) ++ ")"
  match runSetup p f ts argTy (args.map fun n => cst (.num n)) depth with
  | none => fail s!"{f} did not run to completion (stuck, undef, or past depth {depth})"
  | some s =>
    let vs := s.res.map (·.val)
    let line : Out := { tex := "\\clrunline{$" ++ call ++ " \\Downarrow " ++ fmtVals vs ++ "$}" }
    match expect with
    | none => line
    | some e => if nums vs == some e then line
                else { line with err := some s!"{f} returned {repr vs}, expected {e}" }

/-! ## Crashes

A thread that *stops* --- a handler that crashes, a client that is killed ---
is the case the linear-token rule says nothing about (it never reaches its
`ret`).  The explorer can still show what it leaves behind: at every
configuration, one more move is offered in which the chosen thread stops.
The move is a silent step of that thread (it touches no memory and no view),
so it commutes with everything else; the search is otherwise `exploreM`.
Nothing in `TermRun` changes. -/

/-- `exploreM`, with thread `crash` allowed to stop at any configuration
(`TermLive.crashCfg`). -/
def exploreCrash (p : Prog) (k : Promises.Knobs) (arch : WeakMem.Arch) (b : Bounds) (fuel : Nat) (c : Cfg)
    (crash : Nat) : Explored := Id.run do
  let mut seen : Std.HashSet CfgKey := Std.HashSet.emptyWithCapacity.insert (cfgKey c)
  let mut frontier : List Cfg := [c]
  let mut finals : List Cfg := []
  for _ in [0:fuel] do
    if frontier.isEmpty then break
    let mut next : List Cfg := []
    for d in frontier do
      if d.final then finals := d :: finals
      else
        for e in successors p k arch b d ++ (crashCfg d crash).toList do
          let key := cfgKey e
          if !seen.contains key then
            seen := seen.insert key
            next := e :: next
    frontier := next
  return ⟨finals, seen.size, !frontier.isEmpty⟩

/-- The distinct final outcomes of an exploration: each thread's result, then
the coherence-last value at each watched address `(name, label, offset)`. -/
def finalOutcomes (ex : Explored) (n : Nat) (watch : List (String × Nat × Nat)) :
    List (List (Option (List Val)) × List (Option Val)) :=
  (ex.finals.map fun c =>
    ((List.range n).map fun i => (c.ths[i]?).bind resWs,
     watch.map fun (_, l, o) => lastAt c ⟨l, o⟩)).eraseDups

/-- An outcome as one list of numbers (results, then memory), for `expectFinal`.
A thread that may have stopped (`crash`) contributes nothing when it did. -/
def finalNums (o : List (Option (List Val)) × List (Option Val)) (crash : Option Nat := none) :
    Option (List Nat) := do
  let rs ← (enumFrom o.1 0).mapM fun (i, r) => if some i == crash then some (r.getD []) else r
  let r ← nums rs.flatten
  let ms ← o.2.mapM id
  let m ← nums ms
  pure (r ++ m)

/-- The final outcomes as a table: a column per thread, then per watched address. -/
def finalsTable (thr : List (String × Ty × List Nat)) (watch : List (String × Nat × Nat))
    (fins : List (List (Option (List Val)) × List (Option Val))) : String :=
  let cols := thr.length + watch.length
  let head := (thr.map fun (g, _, _) => "$" ++ fn (esc g) ++ "$") ++
    (watch.map fun (nm, _, _) => "$" ++ nm ++ "$")
  let row (o : List (Option (List Val)) × List (Option Val)) : String :=
    " & ".intercalate ((o.1.map fun r => "$" ++ (r.map fmtVals).getD "-" ++ "$") ++
      (o.2.map fun v => "$" ++ (v.map fmtVal).getD "-" ++ "$")) ++ " \\\\"
  "\\par\\noindent{\\small final states, " ++ toString fins.length ++
    " distinct (thread results; memory):}\\par\\noindent\\begin{tabular}{" ++
    String.join (List.replicate cols "c") ++ "}\n" ++ " & ".intercalate head ++ " \\\\\\hline\n" ++
    "\n".intercalate (fins.map row) ++ "\n\\end{tabular}\\par\\smallskip"

/-- A setup thread `f(args)`, then `thr`: each thread `(g, argTy, extra)` gets
the setup's result followed by `extra`.  Every interleaving (and, with
`maxP > 0`, promise) is explored; the distinct results per thread are shown.
`expect` gives, per thread, the exact set of results. -/
def threads (p : Prog) (f : String) (argTy : Ty) (args : List Nat)
    (thr : List (String × Ty × List Nat)) (maxP : Nat := 0)
    (expect : Option (List (List (List Nat))) := none) (depth : Nat := 300)
    (watch : List (String × Nat × Nat) := [])
    (expectFinal : Option (List (List Nat)) := none) (crash : Option Nat := none)
    (live : Option Nat := none) : Out :=
  let s := runSetup p f [] argTy (args.map fun n => cst (.num n)) depth
  match s with
  | none => fail s!"setup {f} did not run to completion"
  | some _ =>
  let thr' (s : Setup) := thr.map fun (g, t, xs) => (g, [], t, s.res ++ xs.map fun n => cst (.num n))
  -- with `live`, the graph is kept and analysed (`TermLive`); the finals are the same
  let gr : Option Graph := match live with
    | none => none
    | some _ => s.map fun s =>
        exploreG p Promises.Knobs.all WeakMem.Arch.arm { maxP := maxP } depth (spawn s (thr' s))
          (fun d => match crash with | some i => (crashCfg d i).toList | none => [])
  let lv := gr.map analyse
  let r := match gr, crash with
    | some g, _ => some g.toExplored
    | none, none => runE p s thr' maxP depth
    | none, some i => s.map fun s =>
        exploreCrash p Promises.Knobs.all WeakMem.Arch.arm { maxP := maxP } depth (spawn s (thr' s)) i
  match r with
  | none => fail "no exploration"
  | some ex =>
    let undef := ex.finals.any (·.ths.any (·.undefs > 0))
    let rows := (enumFrom thr 0).map fun (i, (g, _, xs)) =>
      let outs := resultsOf r i
      (g, xs, outs)
    let status := s!"{ex.finals.length} final states, {ex.seen} configurations" ++
      (if ex.cut then ", CUT OFF at the depth bound" else ", search complete") ++
      (if undef then ", some load returned undef" else ", no undef") ++
      (if maxP > 0 then s!", promises $\\le$ {maxP}" else "") ++
      (match crash with | some i => s!", thread {i} may stop anywhere" | none => "") ++
      (match lv with | some l => ", " ++ l.describe | none => "")
    let tex := "\\begin{clthreads}{" ++ fn (esc f) ++ "(" ++ commas (args.map toString) ++ ")}{" ++
      status ++ "}\n" ++
      "\n".intercalate (rows.map fun (g, xs, outs) =>
        "\\clthread{$" ++ fn (esc g) ++ (if xs.isEmpty then "" else "(\\ldots, " ++ commas (xs.map toString) ++ ")") ++
        "$}{$" ++ (if outs.isEmpty then "\\text{none}" else "\\{" ++ commas (outs.map fmtVals) ++ "\\}") ++ "$}") ++
      "\n\\end{clthreads}"
    let fins := finalOutcomes ex thr.length watch
    let tex := if watch.isEmpty then tex else tex ++ "\n" ++ finalsTable thr watch fins
    let errs := (if ex.cut then ["the search was cut off at the depth bound"] else []) ++
      (if undef then ["a load returned undef"] else []) ++
      (if ex.finals.isEmpty then ["no final state"] else []) ++
      (match live, lv with
       | some n, some l =>
         if l.livelocks.length + l.stuck == n then []
         else [s!"liveness: {l.describe}, expected {n} fair livelock(s)"]
       | _, _ => []) ++
      (match expect with
       | none => []
       | some es =>
         (enumFrom es 0).filterMap fun (i, e) =>
           let got := (resultsOf r i).map nums
           let want := e.map some
           if got.all want.contains && want.all got.contains then none
           else some s!"thread {i}: results {repr (resultsOf r i)}, expected {e}")
      ++
      (match expectFinal with
       | none => []
       | some es =>
         let got := fins.map (finalNums · crash)
         let want := es.map some
         if got.all want.contains && want.all got.contains then []
         else [s!"final outcomes {repr got}, expected {es}"])
    { tex := tex, err := match errs with | [] => none | es => some ("; ".intercalate es) }

/-! ## Pinned behaviour -/

#guard (Doc.check seqLib readD).err.isNone
#guard (Doc.check seqLib (readD' (readBody true false false true)) (some "no fence ld")).err.isNone
#guard (Doc.check seqLib (readD' (readBody true false false true))).err.isSome
#guard (run seqLib "mkSeq" pay [1, 1]).err.isNone
#guard (opType {} [] [] [("x", .int)] (.add (v "x") (.lit 1))).err.isNone

/-! ## Pinned: tooltips

`lock`'s every variable occurrence carries its type, in order (the binder `m`,
then `w`, its operand `m`, the `cas`'s `w` and binder `t`, `ret t`, the tail
call's `m`), and a refused-for-scope variable would show as `\\clnotip`. -/
#guard
  let tex := Render.block ({ tips := some {} } : Style) lockD
  (tex.splitOn "\\clnotip").length == 1 &&
  (varOccs tex).map (fun (x, t) => (x, tipDec t)) ==
    [("m", "m : Ptr pub (Word[r, Mutex] * Ptr[r] Int)"), ("w", "w : Loc pub Word[r, Mutex]"),
     ("m", "m : Ptr pub (Word[r, Mutex] * Ptr[r] Int)"), ("w", "w : Loc pub Word[r, Mutex]"),
     ("t", "t : Tok[r, Mutex, 1]"), ("t", "t : Tok[r, Mutex, 1]"),
     ("m", "m : Ptr pub (Word[r, Mutex] * Ptr[r] Int)")]
-- Without `tips`, the output is the printer's, unchanged.
#guard Render.block ({} : Style) lockD == "\\begin{clcode}\n$" ++ fmtDecl lockD ++ "$\n\\end{clcode}"
-- The author's text lines up with the printer's occurrences, comments untouched.
#guard (sourceTips "x -- x\ny" [("x", "T1"), ("y", "T2")]) ==
  ("\\cltip{x}{T1} -- x\n\\cltip{y}{T2}", true)
#guard (sourceTips "x" [("x", "T1"), ("y", "T2")]).2 == false

end Doc
