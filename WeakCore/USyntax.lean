/-
# USyntax — the UnElab parser (`.u`, `.i`) and the `--print-elab` printer

Types, kinds, protocols and index terms are read by `Syntax`'s
own parsers (`pTy`, `pProto`, `pProto2`, `pKind`, `pIdx`), against the checker's context as `Syntax` follows it
(`Sc`, `Scope.nth`).  The operation table is a copy of `Syntax.pOp` with every atom position read as an operand
(UnElab's *surface syntax* may copy from `Syntax.lean` and drift; its
meaning stays the elaboration `UnElab.elabT`, judged by the core checker).

Operands.  `ARG ::= atom | "(" op ")" | tuple` is the operand of a keyword operation; `TARG ::= ARG | call` the
operand of a term form (`ret`, `if`, `case`, …) or of a binary operator; `ITEM ::= ARG | op` a call argument or
tuple component.  Whitespace is never
significant.  The parser elaborates as it reads: it threads the elaborator's counter (`ES.k`) and steps the
checker's context after every nested operation exactly as the elaborated `let «%k» = …` would, so index names in
types written inside code resolve as the checker's de Bruijn indices.  A type written *before*
the operands of its operation (`inl[τ] a`, `newBuf[τ] n`, `f[τ](a)`, `spawn f[τ] a`) is read again after them, in
the context the elaborated head is checked in.

Positions.  The lexer (a copy of `Syntax.lex`) also records every token's end; the parser records a span table:
(block, path of the core node in the elaborated body) ↦ source span, for diagnostics and `--print-elab`.

Nothing here is trusted: the elaborated program is judged by `checkProg`.
-/
import WeakCore.Syntax
import WeakCore.UnElab
open CoreLang CoreTerm Syntax UnElab

namespace USyntax

/-! ## Tokens with end positions (a copy of `Syntax.lexAux`) -/

partial def ulexAux (cs : Array Char) (i line col : Nat) (acc : Array Tok) (ends : Array (Nat × Nat)) :
    Except Err (Array Tok × Array (Nat × Nat)) :=
  if h : i < cs.size then
    let c := cs[i]
    let nxt := cs[i + 1]?
    if c == '\n' then ulexAux cs (i + 1) (line + 1) 1 acc ends
    else if c == ' ' || c == '\t' || c == '\r' then ulexAux cs (i + 1) line (col + 1) acc ends
    else if c == '-' && nxt == some '-' then
      let rec skip (j : Nat) : Nat := if j < cs.size && cs[j]! != '\n' then skip (j + 1) else j
      let j := skip i
      ulexAux cs j line (col + (j - i)) acc ends
    else if c == '«' then
      let rec close (j : Nat) : Nat := if j < cs.size && cs[j]! != '»' then close (j + 1) else j
      let j := close (i + 1)
      if j ≥ cs.size then .error ⟨line, col, "unterminated «"⟩
      else
        let s := String.ofList (cs.extract (i + 1) j).toList
        let w := j + 1 - i
        ulexAux cs (j + 1) line (col + w) (acc.push ⟨.qid s, line, col⟩) (ends.push (line, col + w))
    else if c.isDigit then
      let rec digits (j : Nat) : Nat := if j < cs.size && cs[j]!.isDigit then digits (j + 1) else j
      let j := digits i
      let n := (String.ofList (cs.extract i j).toList).toNat!
      ulexAux cs j line (col + (j - i)) (acc.push ⟨.num n, line, col⟩) (ends.push (line, col + (j - i)))
    else if isIdStart c then
      let rec word (j : Nat) : Nat := if j < cs.size && isIdChar cs[j]! then word (j + 1) else j
      let j := word i
      let s := String.ofList (cs.extract i j).toList
      let (s, j) := if s == "Ptr" && cs[j]? == some '?' then ("Ptr?", j + 1) else (s, j)
      let s := if s == "μ" then "mu" else s
      ulexAux cs j line (col + (j - i)) (acc.push ⟨.id s, line, col⟩) (ends.push (line, col + (j - i)))
    else match uniSym c with
      | some t => ulexAux cs (i + 1) line (col + 1) (acc.push ⟨t, line, col⟩) (ends.push (line, col + 1))
      | none =>
        let two := String.ofList [c, nxt.getD ' ']
        if syms2.contains two then
          ulexAux cs (i + 2) line (col + 2) (acc.push ⟨.sym two, line, col⟩) (ends.push (line, col + 2))
        else if syms1.contains c then
          ulexAux cs (i + 1) line (col + 1) (acc.push ⟨.sym c.toString, line, col⟩) (ends.push (line, col + 1))
        else .error ⟨line, col, s!"unexpected character '{c}'"⟩
  else .ok (acc.push ⟨.eof, line, col⟩, ends.push (line, col))

def ulex (s : String) : Except Err (Array Tok × Array (Nat × Nat)) := ulexAux s.toList.toArray 0 1 1 #[] #[]

/-! ## The parser state -/

/-- A source span of a core node: `path` is the node's position in the elaborated body (`Scope` child indices,
from the root), `what` its binder (`x`, `%3`) or its head form (`if`, `ret`, `split`, …). -/
structure Span where
  block : String
  path  : List Nat
  line  : Nat
  col   : Nat
  eline : Nat
  ecol  : Nat
  what  : String
  deriving Repr, Inhabited, BEq

/-- A value binder in the source: its token, and the core path of the node whose checker context (before that
node) first has it bound (for tooltips, `DocU`). -/
structure Bind where
  block : String
  name  : String
  line  : Nat
  col   : Nat
  ctx   : List Nat
  deriving Repr, Inhabited, BEq

structure USt where
  ends  : Array (Nat × Nat) := #[]
  block : String := ""
  spans : Array Span := #[]
  binds : Array Bind := #[]
  deriving Inhabited

abbrev UP := StateT USt Syntax.P

instance {γ : Type} : Inhabited (UP γ) := ⟨fun _ => default⟩

def liftP {γ : Type} (x : Syntax.P γ) : UP γ := StateT.lift x
def failU {γ : Type} (msg : String) : UP γ := liftP (failP msg)
def tokPos : UP Nat := liftP (get : Syntax.P Nat)
def setPos (n : Nat) : UP Unit := liftP (set n : Syntax.P Unit)
def curU : UP Tok := liftP cur
def bumpU : UP Unit := liftP bump
def isSymU (s : String) : UP Bool := liftP (isSym s)
def isKwU (s : String) : UP Bool := liftP (isKw s)
def eatSymU (s : String) : UP Bool := liftP (eatSym s)
def eatKwU (s : String) : UP Bool := liftP (eatKw s)
def expectSymU (s : String) : UP Unit := liftP (expectSym s)
def expectKwU (s : String) : UP Unit := liftP (expectKw s)

/-- The elaborator's state at a point of the source: the checker's scope, the next temporary, and the path of
the next core node (reversed). -/
structure ES where
  sc   : Sc
  k    : Nat := 0
  path : List Nat := []

/-- After a core `let x = op`, continuing with counter `k'`. -/
def ES.stepLet (env : Env) (es : ES) (x : String) (op : Op) (k' : Nat) : ES :=
  { sc := es.sc.step env.lib (.let_ x op Scope.hole) 0 (afterOp · x op), k := k', path := 0 :: es.path }

/-- Into subterm `i` of the core head `hd`, with the syntactic fallback `syn`. -/
def ES.into (env : Env) (es : ES) (hd : Expr) (i : Nat) (syn : Sc → Sc) : ES :=
  { es with sc := es.sc.step env.lib hd i syn, path := i :: es.path }

/-- Record the span of the core node at `es.path`, from token `i0` to the current position. -/
def recSpan (es : ES) (what : String) (i0 : Nat) : UP Unit := do
  let i1 ← tokPos
  let ts ← liftP (read : Syntax.P (Array Tok))
  let st ← get
  let t0 := ts[i0]?.getD default
  let (el, ec) := st.ends[i1 - 1]?.getD (t0.line, t0.col)
  let sp : Span :=
    { block := st.block, path := es.path.reverse, line := t0.line, col := t0.col, eline := el, ecol := ec, what }
  set { st with spans := st.spans.push sp }

/-- Record the binder `x` written at token `ti`, bound in the context before the node at `ctx` (reversed). -/
def recBind (x : String) (ti : Nat) (ctx : List Nat) : UP Unit := do
  if x == "_" || UnElab.reserved x then return
  let ts ← liftP (read : Syntax.P (Array Tok))
  let t := ts[ti]?.getD default
  modify fun st => { st with binds := st.binds.push { block := st.block, name := x, line := t.line, col := t.col,
                                                      ctx := ctx.reverse } }

/-- The current token's name (`""` if it is not a name). -/
def curName : UP String := do
  match (← curU).tk with
  | .id x => pure x
  | _ => pure ""

/-- The identifiers of the tokens `i0 … i1 - 1` (a pattern's or binder list's names), with their token indices. -/
def idsIn (i0 i1 : Nat) : UP (List (String × Nat)) := do
  let ts ← liftP (read : Syntax.P (Array Tok))
  pure ((List.range (i1 - i0)).filterMap fun j =>
    match ts[i0 + j]? with
    | some t => (match t.tk with | .id x => some (x, i0 + j) | _ => none)
    | none => none)

/-! ## Names -/

def msgReserved : String :=
  "names beginning with '%' are the elaborator's temporaries («%0», «%1», …); they cannot be written in UnElab"
def msgUnderscore : String :=
  "'_' is not a variable (only `let _ = …` and patterns discard a value)"
def msgParen : String :=
  "an operation used as the operand of another operation must be parenthesised: load acq (fld 0 m), store rel c (f(x))"
def msgParenT : String :=
  "an operation used as the operand of a term form must be parenthesised: ret (x + 1), if (x + 1) = y"
def msgChain : String :=
  "binary operators take one level: write (x + y) + z, not x + y + z"
def msgJoin : String :=
  "a branching form (if, case, parity, ifnull, cas, casp) ends a term: `let x = if …` is refused (no join points)"

/-- A name: not `_`, not reserved (`«%k»`), not a keyword. -/
def pNameU : Syntax.P String := do
  match (← cur).tk with
  | .id "_" => failP msgUnderscore
  | .qid s => if reserved s then failP msgReserved else bump; pure s
  | _ => pName

def sepByU {γ : Type} (p : UP γ) (sep : String) : UP (List γ) := do
  let x ← p
  let rec more (acc : List γ) (fuel : Nat) : UP (List γ) := do
    match fuel with
    | 0 => pure acc.reverse
    | f + 1 => if ← eatSymU sep then more ((← p) :: acc) f else pure acc.reverse
  more [x] 100000

/-- Read `p` at token position `pos`, then come back. -/
def reparse {γ : Type} (pos : Nat) (p : UP γ) : UP γ := do
  let save ← tokPos
  setPos pos
  let x ← p
  setPos save
  pure x

/-- The keywords that head an operation. -/
def opKeywords : List String :=
  ["inl", "inr", "new", "publish", "intoRgn", "newBuf", "bufInit", "null", "fold", "fld", "load", "store", "fence",
   "mkWord", "mkTicket", "claim", "fetch", "mkWord2", "ldp", "stp", "mkEPair", "pack", "validate", "borrow",
   "endBorrow", "freeze", "xchg", "fnptr", "callc", "nameI", "bits", "bit1", "vmatch", "zero", "cvt", "toInt",
   "asLanes", "fop", "fcmp", "fop1", "lane", "spawn", "emit", "current", "exitEv", "setLane", "ldl", "stl", "ldlw",
   "stlw", "park", "unpark", "mmioRead", "mmioWrite", "regAt", "devRecv", "devWrite", "devChoice", "devIrq",
   "devOut"]

def branchKeywords : List String := ["if", "case", "parity", "ifnull", "cas", "casp", "let"]

/-- A binary operator next (`+ - mod & [`)? -/
def atBinOp : UP Bool := do
  match (← curU).tk with
  | .sym "+" | .sym "-" | .sym "&" | .sym "[" | .id "mod" => pure true
  | _ => pure false

/-! ## Operations -/

/-- An operation whose operands have been read (and elaborated): its head (atom positions are holes), its
operands, their atoms, and the token where its text starts. -/
structure POp where
  head  : Op
  args  : List UArg
  ats   : List At
  start : Nat

instance : Inhabited POp := ⟨{ head := .atom .unit, args := [], ats := [], start := 0 }⟩

/-- An item read but not yet placed: an atom, an operation, or (`call := true`) an operation that is a call. -/
inductive PItem
  | atom (a : At)
  | op (po : POp) (call : Bool)

instance : Inhabited PItem := ⟨.atom .unit⟩

/-- Place an item as an operand: an operation becomes `let «%k» = …` (the next temporary). -/
def finish (env : Env) (es : ES) : PItem → UP (UArg × At × ES)
  | .atom a => pure (.at a, a, es)
  | .op po _ => do
      let x := tmp es.k
      recSpan es x po.start
      pure (.op po.head po.args, .var x, es.stepLet env x (setAts po.head po.ats) (es.k + 1))

/-- Components `(a₁, …, aₙ)` (each already placed), as right-nested pairs: the inner pairs become temporaries,
innermost first; the outer pair is returned unplaced. -/
def buildTuple (env : Env) (es : ES) (i0 : Nat) : List (UArg × At) → UP (POp × ES)
  | [(u1, a1), (u2, a2)] => pure ({ head := .pair .unit .unit, args := [u1, u2], ats := [a1, a2], start := i0 }, es)
  | (u1, a1) :: rest@(_ :: _ :: _) => do
      let (inner, es) ← buildTuple env es i0 rest
      let (ui, ai, es) ← finish env es (.op inner false)
      pure ({ head := .pair .unit .unit, args := [u1, ui], ats := [a1, ai], start := i0 }, es)
  | _ => failU "a tuple has at least two components"

def pBrTyU (env : Env) (sc : Sc) : UP Ty := liftP (pBrTy env sc)

mutual
/-- `ITEM ::= ARG | op` (a call argument, a tuple component, a `let` right-hand side): unplaced. -/
partial def pItem (env : Env) (es : ES) : UP (PItem × ES) := do
  let i0 ← tokPos
  match (← curU).tk with
  | .id s =>
      if opKeywords.contains s then
        let (po, es) ← pKwOp env es s i0
        if ← atBinOp then failU msgParen
        pure (.op po false, es)
      else if branchKeywords.contains s then failU msgJoin
      else pBin env es i0
  | _ => pBin env es i0

/-- A primary (atom, parenthesised operation, tuple, or call), then possibly one binary operator, whose
operands are `TARG`s (a call may be bare: `f(x) + 1`, `b[f(x)]`). -/
partial def pBin (env : Env) (es : ES) (i0 : Nat) : UP (PItem × ES) := do
  let (p, es) ← pPrimary env es true
  if ← atBinOp then
    let (u1, a1, es) ← finish env es p
    let t ← curU
    bumpU
    let (u2, a2, es) ← pTOperand env es
    let head : Op ← match t.tk with
      | .sym "+" => pure (.add .unit .unit)
      | .sym "-" => pure (.sub .unit .unit)
      | .sym "&" => pure (.band .unit .unit)
      | .sym "[" => do expectSymU "]"; pure (.idx .unit .unit)
      | _ => pure (.rem .unit .unit)
    if ← atBinOp then failU msgChain
    pure (.op { head, args := [u1, u2], ats := [a1, a2], start := i0 } false, es)
  else pure (p, es)

/-- A primary: an atom, `(op)`, a tuple, or (`calls`) a call. -/
partial def pPrimary (env : Env) (es : ES) (calls : Bool) : UP (PItem × ES) := do
  let i0 ← tokPos
  match (← curU).tk with
  | .num n => bumpU; pure (.atom (.lit n), es)
  | .sym "(" =>
      bumpU
      if ← eatSymU ")" then return (.atom .unit, es)
      let (it, es) ← pItem env es
      if ← isSymU "," then
        let (u1, a1, es) ← finish env es it
        let rec comps (es : ES) (acc : List (UArg × At)) (fuel : Nat) : UP (List (UArg × At) × ES) := do
          match fuel with
          | 0 => pure (acc.reverse, es)
          | f + 1 =>
            if ← eatSymU "," then
              let (it, es) ← pItem env es
              let (u, a, es) ← finish env es it
              comps es ((u, a) :: acc) f
            else pure (acc.reverse, es)
        let (cs, es) ← comps es [(u1, a1)] 100000
        expectSymU ")"
        let (po, es) ← buildTuple env es i0 cs
        pure (.op po false, es)
      else
        expectSymU ")"
        match it with
        | .op po _ => pure (.op { po with start := i0 } false, es)
        | it => pure (it, es)
  | .id s =>
      if opKeywords.contains s then failU msgParen
      else if keywords.contains s then failU s!"'{s}' cannot start an operand"
      else pNamed env es calls i0
  | .qid _ => pNamed env es calls i0
  | t => failU s!"expected an operand, found {t.show}"

/-- A name: a call (where calls are allowed and `(`, `{` or `[τ…](` follows), else a variable. -/
partial def pNamed (env : Env) (es : ES) (calls : Bool) (i0 : Nat) : UP (PItem × ES) := do
  let f ← liftP pNameU
  if !calls then return (.atom (.var f), es)
  let isCall ← match (← curU).tk with
    | .sym "(" | .sym "{" => pure true
    | .sym "[" =>
        let save ← tokPos
        let ok ← tryCatch (do
            bumpU
            let _ ← sepByU (liftP (pTy env es.sc)) ","
            expectSymU "]"
            pure ((← isSymU "(") || (← isSymU "{")))
          (fun _ => pure false)
        setPos save
        pure ok
    | _ => pure false
  if isCall then
    let (po, es) ← pCallRest env es f i0
    pure (.op po true, es)
  else pure (.atom (.var f), es)

/-- `[τ…]{r…}(ITEM, …)` after the name `f`: the call's argument is one operand (a tuple of several). -/
partial def pCallRest (env : Env) (es : ES) (f : String) (i0 : Nat) : UP (POp × ES) := do
  let tpos ← tokPos
  let hasTs ← isSymU "["
  if hasTs then
    bumpU; let _ ← sepByU (liftP (pTy env es.sc)) ","; expectSymU "]"
  let is ← if ← eatSymU "{" then do
      let is ← sepByU (liftP pNameU) ","; expectSymU "}"; pure is
    else pure []
  expectSymU "("
  let (u, a, es) ← if ← eatSymU ")" then pure (.at .unit, .unit, es) else do
    let (it, es) ← pItem env es
    let (u1, a1, es) ← finish env es it
    let rec comps (es : ES) (acc : List (UArg × At)) (fuel : Nat) : UP (List (UArg × At) × ES) := do
      match fuel with
      | 0 => pure (acc.reverse, es)
      | f + 1 =>
        if ← eatSymU "," then
          let (it, es) ← pItem env es
          let (u, a, es) ← finish env es it
          comps es ((u, a) :: acc) f
        else pure (acc.reverse, es)
    let (cs, es) ← comps es [(u1, a1)] 100000
    expectSymU ")"
    match cs with
    | [(u1, a1)] => pure (u1, a1, es)
    | _ =>
      let (po, es) ← buildTuple env es (i0 + 1) cs
      finish env es (.op po false)
  let ts ← if hasTs then reparse tpos (do
      bumpU; let ts ← sepByU (liftP (pTy env es.sc)) ","; expectSymU "]"; pure ts) else pure []
  pure ({ head := .call f is .unit ts, args := [u], ats := [a], start := i0 }, es)

/-- `ARG`, placed: the operand of an operation. -/
partial def pOperand (env : Env) (es : ES) : UP (UArg × At × ES) := do
  let (p, es) ← pPrimary env es false
  finish env es p

/-- `TARG`, placed: the operand of a term form (a call may be bare). -/
partial def pTOperand (env : Env) (es : ES) : UP (UArg × At × ES) := do
  let (p, es) ← pPrimary env es true
  finish env es p

/-- `TARG` as the operand of a term form: a binary operation after it must be parenthesised. -/
partial def pTermOperand (env : Env) (es : ES) : UP (UArg × At × ES) := do
  let r ← pTOperand env es
  if ← atBinOp then failU msgParenT
  pure r

/-- An operation headed by the keyword `s` (the copied table of `Syntax.pOp`, operands for atoms). -/
partial def pKwOp (env : Env) (es : ES) (s : String) (i0 : Nat) : UP (POp × ES) := do
  let mk (h : Op) (us : List UArg) (as : List At) (es : ES) : UP (POp × ES) :=
    pure ({ head := h, args := us, ats := as, start := i0 }, es)
  let one (h : Op) (es : ES) : UP (POp × ES) := do
    let (u, a, es) ← pOperand env es; mk h [u] [a] es
  let two (h : Op) (es : ES) : UP (POp × ES) := do
    let (u, a, es) ← pOperand env es; let (v, b, es) ← pOperand env es; mk h [u, v] [a, b] es
  let three (h : Op) (es : ES) : UP (POp × ES) := do
    let (u, a, es) ← pOperand env es; let (v, b, es) ← pOperand env es; let (w, c, es) ← pOperand env es
    mk h [u, v, w] [a, b, c] es
  let four (h : Op) (es : ES) : UP (POp × ES) := do
    let (u, a, es) ← pOperand env es; let (v, b, es) ← pOperand env es; let (w, c, es) ← pOperand env es
    let (x, d, es) ← pOperand env es
    mk h [u, v, w, x] [a, b, c, d] es
  let word {γ : Type} (names : List (String × γ)) (what : String) : UP γ := liftP (pWordOf names what)
  let U := At.unit
  bumpU
  match s with
  | "inl" | "inr" =>
      let tpos ← tokPos
      let _ ← pBrTyU env es.sc
      let (u, a, es) ← pOperand env es
      let t ← reparse tpos (pBrTyU env es.sc)
      mk (if s == "inl" then .inl t U else .inr t U) [u] [a] es
  | "new" => let tpos ← tokPos; let _ ← pBrTyU env es.sc; let (u, a, es) ← pOperand env es; let t ← reparse tpos (pBrTyU env es.sc); mk (.new U (some t)) [u] [a] es
  | "publish" => one (.publish U) es
  | "intoRgn" => let r ← liftP pNameU; one (.intoRgn r U) es
  | "newBuf" =>
      let tpos ← tokPos
      let _ ← pBrTyU env es.sc
      let (u, a, es) ← pOperand env es
      let t ← reparse tpos (pBrTyU env es.sc)
      mk (.newBuf U t) [u] [a] es
  | "bufInit" => three (.bufInit U U U) es
  | "null" =>
      expectSymU ":"
      match ← liftP (pTy env es.sc) with
      | .ptrOpt μ t => mk (.null μ t) [] [] es
      | _ => failU "null needs a type Ptr? μ τ"
  | "fold" =>
      let (u, a, es) ← pOperand env es
      expectSymU ":"
      mk (.fold U (← liftP (pTy env es.sc))) [u] [a] es
  | "fld" => let i ← liftP pNat; one (.fld i U) es
  | "load" =>
      let acq ← eatKwU "acq"
      let (u, a, es) ← pOperand env es
      if ← isSymU "[" then
        if acq then failU "a slot load has no acq"
        bumpU
        let (v, b, es) ← pOperand env es
        expectSymU "]"
        let p ← liftP pPath
        mk (if p.isEmpty then .loadAt U U else .loadAtF U U p) [u, v] [a, b] es
      else mk (.load acq U) [u] [a] es
  | "store" =>
      let rel ← eatKwU "rel"
      let (u, a, es) ← pOperand env es
      let (v, b, es) ← pOperand env es
      if ← eatKwU "with" then
        let (w, c, es) ← pOperand env es
        mk (.store rel U U (some U)) [u, v, w] [a, b, c] es
      else mk (.store rel U U none) [u, v] [a, b] es
  | "fence" => mk (.fence (← word fenceNames "a fence (ld, st, full)")) [] [] es
  | "mkWord" => let r ← liftP pNameU; let P ← liftP (pProto env); two (.mkWord r P U U) es
  | "mkTicket" =>
      let r ← liftP pNameU; let N ← liftP (pProto env); let P ← liftP (pProto env)
      two (.mkTicket r N P U U) es
  | "claim" =>
      let (u, a, es) ← pOperand env es
      expectKwU "with"
      let (v, b, es) ← pOperand env es
      mk (.claim U U) [u, v] [a, b] es
  | "fetch" =>
      let o ← word fetchNames "a fetch-op (add, or, and, xor)"
      let acq ← eatKwU "acq"; let rel ← eatKwU "rel"
      two (.fetch o acq rel U U) es
  | "mkWord2" =>
      let r ← liftP pNameU; let P ← liftP (pProto2 env)
      expectSymU "("; let (u, a, es) ← pOperand env es; expectSymU ","; let (v, b, es) ← pOperand env es
      expectSymU ")"
      let (w, c, es) ← pOperand env es
      mk (.mkWord2 r P U U U) [u, v, w] [a, b, c] es
  | "ldp" =>
      let acq ← eatKwU "acq"
      let (u, a, es) ← pOperand env es
      expectKwU "as"
      expectSymU "("; let n0 ← liftP pNameU; expectSymU ","; let n1 ← liftP pNameU; expectSymU ")"
      mk (.ldp acq U n0 n1) [u] [a] es
  | "stp" =>
      let rel ← eatKwU "rel"
      let (u, a, es) ← pOperand env es
      expectSymU "("; let (v, b, es) ← pOperand env es; expectSymU ","; let (w, c, es) ← pOperand env es
      expectSymU ")"
      expectKwU "with"
      let (x, d, es) ← pOperand env es
      mk (.stp rel U U U U) [u, v, w, x] [a, b, c, d] es
  | "mkEPair" =>
      let r ← liftP pNameU; let P ← liftP (pECounter env)
      expectSymU "("; let (u, a, es) ← pOperand env es; expectSymU ","; let (v, b, es) ← pOperand env es
      expectSymU ")"
      mk (.mkEPair r P U U) [u, v] [a, b] es
  | "pack" =>
      let (u, a, es) ← pOperand env es
      expectKwU "at"
      if ← eatSymU "[" then
        let σ ← liftP (pTy env es.sc); expectSymU "]"; expectSymU ":"
        mk (.packT U σ (← liftP (pTy env es.sc))) [u] [a] es
      else
        let w ← liftP pNameU; expectSymU ":"
        mk (.pack U w (← liftP (pTy env es.sc))) [u] [a] es
  | "validate" =>
      let (u, a, es) ← pOperand env es
      match a with
      | .var y => mk (.validate y) [u] [a] es
      | _ => failU "validate needs a variable (the torn read), or a nested load"
  | "borrow" => let c ← liftP pCap; one (.borrow c U) es
  | "endBorrow" => one (.endBorrow U) es
  | "freeze" => one (.freeze U) es
  | "xchg" =>
      let (u, a, es) ← pOperand env es
      if ← isSymU "[" then
        bumpU
        let (v, b, es) ← pOperand env es
        expectSymU "]"
        let p ← liftP pPath
        let (w, c, es) ← pOperand env es
        mk (if p.isEmpty then .xchgAt U U U else .xchgAtF U U p U) [u, v, w] [a, b, c] es
      else
        let (v, b, es) ← pOperand env es
        mk (.xchg U U) [u, v] [a, b] es
  | "fnptr" => mk (.fnptr (← liftP pNameU)) [] [] es
  | "callc" => two (.callc U U) es
  | "nameI" => one (.nameI U) es
  | "bits" => let o ← word bitNames "a word operation"; two (.bits o U U) es
  | "bit1" => let o ← word bit1Names "a unary word operation"; one (.bit1 o U) es
  | "vmatch" => three (.vmatch U U U) es
  | "zero" => mk (.zero (← pBrTyU env es.sc)) [] [] es
  | "cvt" => let (sg, w) ← liftP pFix; one (.cvt sg w U) es
  | "toInt" => one (.toInt U) es
  | "asLanes" => let (sg, w) ← liftP pFix; one (.asLanes sg w U) es
  | "fop" => let o ← word fopNames "a fixed-width operation"; two (.fop o U U) es
  | "fcmp" => let o ← word fcmpNames "a comparison"; two (.fcmp o U U) es
  | "fop1" => let o ← word fop1Names "a unary fixed-width operation"; one (.fop1 o U) es
  | "lane" => two (.lane U U) es
  | "spawn" =>
      let f ← liftP pNameU
      let tpos ← tokPos
      let hasTs ← isSymU "["
      if hasTs then
        bumpU; let _ ← sepByU (liftP (pTy env es.sc)) ","; expectSymU "]"
      let (u, a, es) ← pOperand env es
      let ts ← if hasTs then reparse tpos (do
          bumpU; let ts ← sepByU (liftP (pTy env es.sc)) ","; expectSymU "]"; pure ts) else pure []
      expectSymU ":"
      mk (.spawn f U (← liftP (pTy env es.sc)) ts) [u] [a] es
  | "emit" => one (.ext .emit U) es
  | "current" => one (.ext .current U) es
  | "exitEv" => one (.ext .exitEv U) es
  -- (M1, T4) the machine and device externs (TEXTS T4 surface; `regAt` spells its block type, as in `Syntax`)
  | "park" => one (.ext .park U) es
  | "unpark" => one (.ext .unpark U) es
  | "mmioRead" =>
      let (w, acc, mo) ← liftP (do
        expectSym "["; let w ← pWd; expectSym ","; let acc ← pAcc; expectSym ","; let mo ← pMo; expectSym "]"
        pure (w, acc, mo))
      one (.ext (.mmioR w acc mo) U) es
  | "mmioWrite" =>
      let (w, acc, mo) ← liftP (do
        expectSym "["; let w ← pWd; expectSym ","; let acc ← pAcc; expectSym ","; let mo ← pMo; expectSym "]"
        pure (w, acc, mo))
      one (.ext (.mmioW w acc mo) U) es
  | "regAt" =>
      let n ← liftP (do
        expectSym "["; let k ← pNat; expectKw "of"
        match ← pTyAtom env es.sc with
        | .opq (.blk n w acc st tk) => expectSym "]"; pure (ExtName.regAt n w acc st tk k)
        | _ => failP "regAt: expected a block type `Blk[…]` after `of`")
      one (.ext n U) es
  | "devRecv" => let w ← liftP pWdB; one (.ext (.devRecv w) U) es
  | "devWrite" => let w ← liftP pWdB; one (.ext (.devWrite w) U) es
  | "devChoice" => let w ← liftP pWdB; one (.ext (.devChoice w) U) es
  | "devIrq" => one (.ext .devIrq U) es
  | "devOut" => let w ← liftP pWdB; one (.ext (.devOut w) U) es
  | "setLane" => three (.setLane U U U) es
  | "ldl" => two (.ldl U U) es
  | "stl" => three (.stl U U U) es
  | "ldlw" => three (.ldlw U U U) es
  | "stlw" => four (.stlw U U U U) es
  | _ => failU s!"'{s}' cannot start an operation"
end

/-! ## Terms -/

/-- `pat ::= x | _ | (pat, pat, …)`; `(p1, p2, p3)` is `pair p1 (pair p2 p3)`. -/
partial def pPat : Syntax.P UPat := do
  if ← eatSym "(" then
    let ps ← sepBy pPat ","
    expectSym ")"
    let rec nest : List UPat → Option UPat
      | [p, q] => some (.pair p q)
      | p :: rest@(_ :: _ :: _) => (nest rest).map (.pair p)
      | _ => none
    match nest ps with
    | some p => pure p
    | none => failP "a pattern in parentheses has at least two components: (x, y)"
  else if (← cur).tk == .id "_" then bump; pure (.bind none)
  else pure (.bind (some (← pNameU)))

/-- The core splits of a pattern-let, in `UnElab.destr`'s order, stepping the scope. -/
def destrP (env : Env) (i0 : Nat) : ES → At → UPat → UP ES
  | es, _, .bind _ => pure es
  | es, s, .pair p q => do
      let b1 := patBinder p es.k
      let b2 := patBinder q b1.2
      recSpan es "split" i0
      let es1 : ES := { sc := es.sc.step env.lib (.split s b1.1 b2.1 Scope.hole) 0 id, k := b2.2, path := 0 :: es.path }
      let es2 ← destrP env i0 es1 (.var b1.1) p
      destrP env i0 es2 (.var b2.1) q

partial def pExprU (env : Env) (es : ES) : UP UExpr := do
  let i0 ← tokPos
  match (← curU).tk with
  | .id "let" =>
      bumpU
      if ← isSymU "(" then
        let pat ← liftP pPat
        let iEq ← tokPos
        expectSymU "="
        let (u, a, es) ← pTermOperand env es
        match pat with
        | .pair p q =>
            let es ← destrP env i0 es a pat
            for (x, ti) in ← idsIn (i0 + 1) iEq do recBind x ti es.path
            let _ ← eatSymU ";"
            pure (.split u p q (← pExprU env es))
        | .bind _ => failU "a pattern in parentheses has at least two components: (x, y)"
      else if ← eatSymU "<" then
        if ← eatSymU "[" then
          let al ← liftP pNameU; expectSymU "]"; expectSymU ","; let ix ← tokPos; let x ← liftP pNameU
          expectSymU ">"; expectSymU "="; expectKwU "unpack"
          let (u, a, es) ← pTermOperand env es
          recSpan es "unpack" i0
          recBind x ix (0 :: es.path)
          let es := { es with sc := es.sc.pushT al }
          return .unpackT u al x (← pExprU env (es.into env (.unpackT a al x Scope.hole) 0 id))
        let iN ← tokPos
        let ns ← sepByU (liftP pNameU) ","
        let iN1 ← tokPos
        let nis := (← idsIn iN iN1).map (·.2)
        expectSymU ">"; expectSymU "="
        if ← eatKwU "unpack" then
          match ns with
          | [i, x] =>
              let (u, a, es) ← pTermOperand env es
              recSpan es "unpack" i0
              recBind x (nis.getD 1 0) (0 :: es.path)
              pure (.unpack u i x (← pExprU env (es.into env (.unpack a i x Scope.hole) 0 (·.pushI i))))
          | _ => failU "unpack binds <index, value>"
        else if ← eatKwU "region" then
          match ns with
          | [r, p, t] =>
              let (u, a, es) ← pTermOperand env es
              recSpan es "region" i0
              recBind p (nis.getD 1 0) (0 :: es.path); recBind t (nis.getD 2 0) (0 :: es.path)
              pure (.region u r p t (← pExprU env (es.into env (.region a r p t Scope.hole) 0 (·.pushI r))))
          | _ => failU "region binds <region, pointer, token>"
        else if ← eatKwU "openPub" then
          match ns with
          | [r, p, c] =>
              let (u, a, es) ← pTermOperand env es
              recSpan es "openPub" i0
              recBind p (nis.getD 1 0) (0 :: es.path); recBind c (nis.getD 2 0) (0 :: es.path)
              pure (.openPub u r p c (← pExprU env (es.into env (.openPub a r p c Scope.hole) 0 (·.pushI r))))
          | _ => failU "openPub binds <region, pointer, capability>"
        else failU s!"expected unpack, region or openPub, found {(← curU).tk.show}"
      else
        let ix ← tokPos
        let x ← if (← curU).tk == .id "_" then do bumpU; pure none else some <$> liftP pNameU
        expectSymU "="
        let r0 ← tokPos
        let (it, es) ← pItem env es
        if ← isSymU "(" then failU msgParen
        let (h, us, as) := match it with
          | .atom a => (Op.atom .unit, [UArg.at a], [a])
          | .op po _ => (po.head, po.args, po.ats)
        let b := binder x es.k
        recSpan es (if x.isSome then b.1 else "_") r0   -- `_`: a discarded result, not a nested operand
        if let some x := x then recBind x ix (0 :: es.path)
        let es := es.stepLet env b.1 (setAts h as) b.2
        let _ ← eatSymU ";"
        pure (.let_ x h us (← pExprU env es))
  | .id "case" =>
      bumpU
      let (u, a, es) ← pTermOperand env es
      recSpan es "case" i0
      expectKwU "of"; let _ ← eatSymU "|"
      expectKwU "inl"; recBind (← curName) (← tokPos) (0 :: es.path); let x ← liftP pNameU; expectSymU "=>"
      let e₁ ← pExprU env (es.into env (.case a x Scope.hole "" Scope.hole) 0 id)
      let _ ← eatSymU "|"
      expectKwU "inr"; recBind (← curName) (← tokPos) (1 :: es.path); let y ← liftP pNameU; expectSymU "=>"
      let e₂ ← pExprU env (es.into env (.case a x Scope.hole y Scope.hole) 1 id)
      pure (.case u x e₁ y e₂)
  | .id "parity" =>
      bumpU
      let (u, a, es) ← pTermOperand env es
      recSpan es "parity" i0
      expectKwU "of"; let _ ← eatSymU "|"
      let two : UP Unit := do
        match (← curU).tk with
        | .num 2 => bumpU
        | t => failU s!"expected 2k, found {t.show}"
      two; let k ← liftP pNameU; expectSymU "=>"
      let hd : Expr := .parity a k Scope.hole Scope.hole
      let ev ← pExprU env (es.into env hd 0 (·.pushI k))
      let _ ← eatSymU "|"
      two; let k' ← liftP pNameU
      if k' != k then failU s!"expected 2{k}+1"
      expectSymU "+"
      match (← curU).tk with
      | .num 1 => bumpU
      | t => failU s!"expected 2{k}+1, found {t.show}"
      expectSymU "=>"
      let od ← pExprU env (es.into env hd 1 (·.pushI k))
      pure (.parity u k ev od)
  | .id "if" =>
      bumpU
      let (u, a, es) ← pTermOperand env es
      expectSymU "="
      let (v, b, es) ← pTermOperand env es
      recSpan es "if" i0
      expectKwU "then"
      let hd : Expr := .ifeq a b Scope.hole Scope.hole
      let yes ← pExprU env (es.into env hd 0 id)
      expectKwU "else"
      pure (.ifeq u v yes (← pExprU env (es.into env hd 1 Sc.barrier)))
  | .id "ifnull" =>
      bumpU
      let (u, a, es) ← pTermOperand env es
      recSpan es "ifnull" i0
      expectKwU "then"
      let e₁ ← pExprU env (es.into env (.ifnull a Scope.hole "" Scope.hole) 0 id)
      expectKwU "else"; recBind (← curName) (← tokPos) (1 :: es.path); let x ← liftP pNameU; expectSymU "=>"
      pure (.ifnull u e₁ x (← pExprU env (es.into env (.ifnull a Scope.hole x Scope.hole) 1 id)))
  | .id "cas" =>
      bumpU
      let acq ← eatKwU "acq"
      let rel ← eatKwU "rel"
      let (uw, w, es) ← pTermOperand env es
      let (ue, e, es) ← pTermOperand env es
      expectSymU "->"
      let (uv, v, es) ← pTermOperand env es
      recSpan es "cas" i0
      expectKwU "as"; recBind (← curName) (← tokPos) (0 :: es.path); let t ← liftP pNameU; expectKwU "then"
      let hd : Expr := .cas acq rel w e v t Scope.hole Scope.hole
      let ok ← pExprU env (es.into env hd 0 id)
      expectKwU "else"
      pure (.cas acq rel uw ue uv t ok (← pExprU env (es.into env hd 1 id)))
  | .id "casp" =>
      bumpU
      let acq ← eatKwU "acq"
      let rel ← eatKwU "rel"
      let (uw, w, es) ← pTermOperand env es
      expectSymU "("
      let (u0, e0, es) ← pTermOperand env es; expectSymU ","; let (u1, e1, es) ← pTermOperand env es
      expectSymU ")"; expectSymU "->"; expectSymU "("
      let (w0, v0, es) ← pTermOperand env es; expectSymU ","; let (w1, v1, es) ← pTermOperand env es
      expectSymU ")"
      recSpan es "casp" i0
      expectKwU "as"; recBind (← curName) (← tokPos) (0 :: es.path); let t ← liftP pNameU; expectKwU "then"
      let hd : Expr := .casp acq rel w e0 e1 v0 v1 t Scope.hole Scope.hole
      let ok ← pExprU env (es.into env hd 0 id)
      expectKwU "else"
      pure (.casp acq rel uw u0 u1 w0 w1 t ok (← pExprU env (es.into env hd 1 id)))
  | .id "ret" =>
      bumpU
      let (u, _, es) ← pTermOperand env es
      recSpan es "ret" i0
      pure (.ret u)
  | .id "tail" =>
      bumpU
      let f ← liftP pNameU
      let (po, es) ← pCallRest env es f (i0 + 1)
      recSpan es "tail" i0
      match po.head, po.args with
      | .call f is _ ts, [u] => pure (.tail f is u ts)
      | _, _ => failU "tail needs a call f(…)"
  | t => failU s!"expected a term (let, case, parity, if, ifnull, cas, casp, ret, tail), found {t.show}"

/-! ## Code blocks, signatures, units -/

/-- `def f[α : κ]{r}(x : σ) : τ`: the signature (body `Scope.hole`) and the scope for the body. -/
def pSigHead (env : Env) : UP (Decl × Sc) := do
  -- the decl kind prefix, as in `Syntax.pDecl`, with `, loop B` and `, ro`
  let kind ← if ← eatKwU "device" then pure DeclKind.device
    else if ← eatKwU "restricted" then do
      expectSymU "["; expectKwU "fuel"; let f ← liftP pNat; expectSymU ","; expectKwU "stack"; let s ← liftP pNat
      let mut lp : Option Nat := none
      let mut ro := false
      if ← eatSymU "," then
        if ← eatKwU "loop" then
          lp := some (← liftP pNat)
          if ← eatSymU "," then expectKwU "ro"; ro := true
        else
          expectKwU "ro"; ro := true
      expectSymU "]"; pure (DeclKind.restricted f s ro lp)
    else pure DeclKind.plain
  expectKwU "def"
  let name ← liftP pNameU
  modify fun st => { st with block := name }
  let tps ← if ← eatSymU "[" then do
      let ps ← sepByU (do
        let a ← liftP pNameU
        let κ ← if ← eatSymU ":" then liftP pKind else pure {}
        pure (a, κ)) ","
      expectSymU "]"; pure ps
    else pure []
  let idx ← if ← eatSymU "{" then do let is ← sepByU (liftP pNameU) ","; expectSymU "}"; pure is else pure []
  let sc : Sc := { tvs := (tps.map (·.1)).reverse, ivs := idx.reverse.map some }
  expectSymU "("; recBind (← curName) (← tokPos) []; let x ← liftP pNameU; expectSymU ":"
  let at_ ← liftP (pTy env sc); expectSymU ")"
  expectSymU ":"; let rt ← liftP (pTy env sc)
  pure ({ name, tparams := tps.map (·.2), idx, arg := x, argTy := at_, retTy := rt, body := Scope.hole, kind }, sc)

def pDeclU (env : Env) : UP UDecl := do
  let (sig, sc) ← pSigHead env
  expectSymU "="
  let body ← pExprU { env with lib := sig :: env.lib } { sc := { sc with cx := some (Scope.start sig) } }
  pure { name := sig.name, tparams := sig.tparams, idx := sig.idx, arg := sig.arg, argTy := sig.argTy,
         retTy := sig.retTy, body, kind := sig.kind }

/-- A scenario (data for `sce`; nothing of it reaches the `.w`). -/
structure Scenario where
  name     : String
  setup    : String × List At
  threads  : List (String × List At)
  promises : Option Nat := none
  depth    : Option Nat := none
  crash    : Option Nat := none
  live     : Nat := 0
  cert     : Option Nat := none
  deriving Repr, Inhabited

inductive UItem
  | type (n : String) (t : Ty)
  | proto (n : String) (P : Proto)
  | proto2 (n : String) (P : Proto2)
  | scenario (s : Scenario)
  /-- A code block; `live = some none`: `live def`, `some (some S)`: `live[S] def`. -/
  | decl (d : UDecl) (live : Option (Option String))
  /-- An `.i` signature (body `Scope.hole`). -/
  | sig (d : Decl) (live : Option (Option String))

structure UUnit where
  imports : List String := []
  items   : List UItem := []

def UUnit.decls (u : UUnit) : UProg :=
  u.items.filterMap fun | .decl d _ => some d | _ => none

/-- A literal argument (scenarios: literals only in v1). -/
def pLit : Syntax.P At := do
  match (← cur).tk with
  | .num n => bump; pure (.lit n)
  | .sym "(" => bump; expectSym ")"; pure .unit
  | t => failP s!"a scenario argument is a literal (a number or ()), found {t.show}"

/-- `f(lit, …)`, as a scenario names a block and its literal arguments. -/
def pLitCall : Syntax.P (String × List At) := do
  let f ← pNameU
  expectSym "("
  if ← eatSym ")" then return (f, [])
  let as ← sepBy pLit ","
  expectSym ")"
  pure (f, as)

def pScenario : Syntax.P Scenario := do
  let name ← pNameU
  expectSym "="; expectSym "{"
  let fields ← sepBy (do
    let k ← match (← cur).tk with
      | .id k => bump; pure k
      | t => failP s!"expected a scenario field (setup, threads, promises, depth, crash, live, cert), found {t.show}"
    expectSym "="
    match k with
    | "setup" => pure (k, some (← pLitCall), [], 0)
    | "threads" =>
        expectSym "["
        let ts ← if ← isSym "]" then pure [] else sepBy pLitCall ","
        expectSym "]"; pure (k, none, ts, 0)
    | "promises" | "depth" | "crash" | "live" | "cert" => pure (k, none, [], ← pNat)
    | _ => failP s!"unknown scenario field '{k}' (setup, threads, promises, depth, crash, live, cert)") ";"
  expectSym "}"
  let get (k : String) := fields.find? (·.1 == k)
  let some (_, some setup, _, _) := get "setup" | failP s!"scenario {name}: no setup = f(…)"
  let some (_, _, threads, _) := get "threads" | failP s!"scenario {name}: no threads = [g(…), …]"
  pure { name, setup, threads, promises := (get "promises").map (·.2.2.2), depth := (get "depth").map (·.2.2.2),
         crash := (get "crash").map (·.2.2.2), live := ((get "live").map (·.2.2.2)).getD 0,
         cert := (get "cert").map (·.2.2.2) }

/-- One top-level item (`isI`: an interface file, `def` without bodies). -/
def pTopItem (env : Env) (isI : Bool) : UP (UItem × Env) := do
  match (← curU).tk with
  | .id "type" =>
      bumpU; let n ← liftP pNameU; expectSymU "="; let t ← liftP (pTy env {})
      pure (.type n t, env.addType n t)
  | .id "proto" =>
      bumpU; let n ← liftP pNameU; expectSymU "="
      if ← liftP (atProto2 env) then
        let P ← liftP (pProto2 env); pure (.proto2 n P, env.addProto2 n P)
      else
        let P ← liftP (pProto env); pure (.proto n P, env.addProto n P)
  | .id "scenario" => bumpU; pure (.scenario (← liftP pScenario), env)
  | .id "import" => failU "imports come first, before every item"
  | _ =>
      let live ← if ← eatKwU "live" then do
          if ← eatSymU "[" then
            let s ← liftP pNameU; expectSymU "]"; pure (some (some s))
          else pure (some none)
        else pure none
      unless (← curU).tk == .id "def" || (← curU).tk == .id "device" || (← curU).tk == .id "restricted" do
        failU s!"expected an item (def, live def, type, proto, scenario), found {(← curU).tk.show}"
      if isI then
        let (sig, _) ← pSigHead env
        pure (.sig sig live, { env with lib := sig :: env.lib })
      else
        let d ← pDeclU env
        pure (.decl d live, { env with lib := elabDecl d :: env.lib })

/-- Run a `UP` parser at token `pos`. -/
def runAt {γ : Type} (p : UP γ) (toks : Array Tok) (st : USt) (pos : Nat) : Except Err (γ × USt × Nat) :=
  match ((p.run st).run toks).run pos with
  | .ok ((x, st'), pos') => .ok (x, st', pos')
  | .error e => .error e

/-- Does token `t` start a top-level item (for resynchronising after an error)?  `def`, `type`, `proto` are
keywords anywhere; `live`, `scenario`, `import` only at column 1. -/
def startsItem (t : Tok) : Bool :=
  match t.tk with
  | .id "def" | .id "type" | .id "proto" => true
  | .id "live" | .id "scenario" | .id "import" => t.col == 1
  | .eof => true
  | _ => false

/-- A parsed unit: its items, the item start positions, the span table, every parse error (parsing resumes at
the next item after an error), and the environment its `type`/`proto` items build. -/
structure UParsed where
  unit   : UUnit
  itemAt : List (Nat × Nat)
  spans  : Array Span
  errs   : List Err
  env    : Env
  binds  : Array Bind := #[]

/-- Parse a whole `.u` (or `.i`) file, continuing after errors. -/
def parseUnitAll (s : String) (env : Env := {}) (isI : Bool := false) : UParsed :=
  match ulex s with
  | .error e => { unit := {}, itemAt := [], spans := #[], errs := [e], env }
  | .ok (toks, ends) =>
    let tokAt (i : Nat) : Tok := toks[i]?.getD (toks.back?.getD default)
    -- imports
    let rec imps (pos : Nat) (acc : List String) (fuel : Nat) : Except Err (List String × Nat) :=
      match fuel with
      | 0 => .ok (acc.reverse, pos)
      | f + 1 =>
        if (tokAt pos).tk == .id "import" then
          match runAt (liftP pNameU) toks {} (pos + 1) with
          | .ok (n, _, pos') => imps pos' (n :: acc) f
          | .error e => .error e
        else .ok (acc.reverse, pos)
    let rec resync (i : Nat) (fuel : Nat) : Nat :=
      match fuel with
      | 0 => i
      | f + 1 => if startsItem (tokAt i) then i else resync (i + 1) f
    let rec items (pos : Nat) (env : Env) (st : USt) (acc : List UItem) (at_ : List (Nat × Nat)) (errs : List Err)
        (fuel : Nat) : UParsed :=
      match fuel with
      | 0 => { unit := { items := acc.reverse }, itemAt := at_.reverse, spans := st.spans, errs := errs.reverse, env := env, binds := st.binds }
      | f + 1 =>
        let t := tokAt pos
        if t.tk == .eof then
          { unit := { items := acc.reverse }, itemAt := at_.reverse, spans := st.spans, errs := errs.reverse, env := env, binds := st.binds }
        else
          match runAt (pTopItem env isI) toks st pos with
          | .ok ((it, env'), st', pos') => items pos' env' st' (it :: acc) ((t.line, t.col) :: at_) errs f
          | .error e => items (resync (pos + 1) toks.size) env st acc at_ (e :: errs) f
    match imps 0 [] toks.size with
    | .error e =>
        let r := items (resync 1 toks.size) env { ends } [] [] [e] toks.size
        r
    | .ok (is, pos) =>
        let r := items pos env { ends } [] [] [] toks.size
        { r with unit := { r.unit with imports := is } }

/-- The first error, or the parsed unit. -/
def parseUnit (s : String) (env : Env := {}) (isI : Bool := false) : Except Err UParsed :=
  let r := parseUnitAll s env isI
  match r.errs with
  | e :: _ => .error e
  | [] => .ok r

/-- Run a parser on a whole string (to the end of the input). -/
def runU {γ : Type} (p : UP γ) (s : String) : Except Err (γ × USt) := do
  let (toks, ends) ← ulex s
  let q : UP γ := do
    let x ← p
    match (← curU).tk with
    | .eof => pure x
    | t => failU s!"unexpected {t.show} after the end"
  match runAt q toks { ends } 0 with
  | .ok (x, st, _) => .ok (x, st)
  | .error e => .error e

/-! ## Entry points (cldoc `syntax=u`): parse, then elaborate -/

/-- A program (code blocks, with `type`/`proto` items naming things for what follows), elaborated. -/
def parseProgE (s : String) (env : Env := {}) : Except Err Prog :=
  (parseUnit s env).map fun r => elabProg r.unit.decls

def parseProgEnvE (s : String) (env : Env := {}) : Except Err (Prog × Env) :=
  (parseUnit s env).map fun r => (elabProg r.unit.decls, r.env)

/-- One code block, elaborated. -/
def parseDeclE (s : String) (env : Env := {}) : Except Err Decl := do
  let r ← parseUnit s env
  match r.unit.decls with
  | [d] => pure (elabDecl d)
  | _ => .error ⟨1, 1, "expected exactly one code block"⟩

/-- A term (at counter 0), elaborated. -/
def parseExprU (s : String) (env : Env := {}) (idx : List String := []) : Except Err UExpr :=
  (runU (pExprU env { sc := { ivs := idx.reverse.map some } }) s).map (·.1)

def parseExprE (s : String) (env : Env := {}) (idx : List String := []) : Except Err Expr :=
  (parseExprU s env idx).map (elabT 0)

/-- An operation whose operands are atoms (`as=Op`); a nested operation is refused. -/
def parseOpE (s : String) (env : Env := {}) (idx : List String := []) : Except Err Op := do
  let ((it, _), _) ← runU (pItem env { sc := { ivs := idx.reverse.map some } }) s
  match it with
  | .atom a => pure (.atom a)
  | .op po _ =>
      if po.args.all (fun | .at _ => true | .op _ _ => false) then pure (setAts po.head po.ats)
      else .error ⟨1, 1, "type= and as=Op need an operation whose operands are atoms (a nested operation becomes a let «%k»): write a let"⟩

def parseTyE (s : String) (env : Env := {}) (idx : List String := []) : Except Err Ty := parseTy s env idx

/-! ## `--print-elab`: the elaborated `.w` with `-- line:col` on every node that has a source span -/

def spanAt (sp : List Span) (block : String) (path : List Nat) : Option Span :=
  sp.find? fun s => s.block == block && s.path == path

def posNote (sp : List Span) (block : String) (path : List Nat) : String :=
  match spanAt sp block path with
  | some s => s!"  -- {s.line}:{s.col}"
  | none => ""

/-- A copy of `Syntax.showExprLines` that also follows the node path and appends the source position. -/
def elabLines (env : Env) (sp : List Span) (blk : String) (sc : Sc) (d : Nat) (path : List Nat) :
    Expr → List (Nat × String)
  | .let_ x op e =>
      (d, "let " ++ nameStr x ++ " = " ++ showOp env sc op ++ posNote sp blk path) ::
        elabLines env sp blk (sc.step env.lib (.let_ x op e) 0 (afterOp · x op)) d (path ++ [0]) e
  | .split a x y e =>
      (d, "let (" ++ nameStr x ++ ", " ++ nameStr y ++ ") = " ++ showAt a ++ posNote sp blk path) ::
        elabLines env sp blk (sc.step env.lib (.split a x y e) 0 id) d (path ++ [0]) e
  | .unpack a i x e =>
      (d, "let <" ++ nameStr i ++ ", " ++ nameStr x ++ "> = unpack " ++ showAt a ++ posNote sp blk path) ::
        elabLines env sp blk (sc.step env.lib (.unpack a i x e) 0 (·.pushI i)) d (path ++ [0]) e
  | .unpackT a al x e =>
      (d, "let <[" ++ nameStr al ++ "], " ++ nameStr x ++ "> = unpack " ++ showAt a ++ posNote sp blk path) ::
        elabLines env sp blk ((sc.pushT al).step env.lib (.unpackT a al x e) 0 id) d (path ++ [0]) e
  | .region a r p t e =>
      (d, "let <" ++ nameStr r ++ ", " ++ nameStr p ++ ", " ++ nameStr t ++ "> = region " ++ showAt a ++
          posNote sp blk path) ::
        elabLines env sp blk (sc.step env.lib (.region a r p t e) 0 (·.pushI r)) d (path ++ [0]) e
  | .openPub a r p c e =>
      (d, "let <" ++ nameStr r ++ ", " ++ nameStr p ++ ", " ++ nameStr c ++ "> = openPub " ++ showAt a ++
          posNote sp blk path) ::
        elabLines env sp blk (sc.step env.lib (.openPub a r p c e) 0 (·.pushI r)) d (path ++ [0]) e
  | .case a x e₁ y e₂ =>
      let hd : Expr := .case a x e₁ y e₂
      [(d, "case " ++ showAt a ++ " of" ++ posNote sp blk path), (d + 1, "inl " ++ nameStr x ++ " =>")] ++
      elabLines env sp blk (sc.step env.lib hd 0 id) (d + 2) (path ++ [0]) e₁ ++
      [(d + 1, "inr " ++ nameStr y ++ " =>")] ++ elabLines env sp blk (sc.step env.lib hd 1 id) (d + 2) (path ++ [1]) e₂
  | .parity a k ev od =>
      let hd : Expr := .parity a k ev od
      [(d, "parity " ++ showAt a ++ " of" ++ posNote sp blk path), (d + 1, "2" ++ nameStr k ++ " =>")] ++
      elabLines env sp blk (sc.step env.lib hd 0 (·.pushI k)) (d + 2) (path ++ [0]) ev ++
      [(d + 1, "2" ++ nameStr k ++ "+1 =>")] ++
      elabLines env sp blk (sc.step env.lib hd 1 (·.pushI k)) (d + 2) (path ++ [1]) od
  | .ifeq a b yes no =>
      let hd : Expr := .ifeq a b yes no
      [(d, "if " ++ showAt a ++ " = " ++ showAt b ++ " then" ++ posNote sp blk path)] ++
      elabLines env sp blk (sc.step env.lib hd 0 id) (d + 1) (path ++ [0]) yes ++
      [(d, "else")] ++ elabLines env sp blk (sc.step env.lib hd 1 Sc.barrier) (d + 1) (path ++ [1]) no
  | .ifnull a e₁ x e₂ =>
      let hd : Expr := .ifnull a e₁ x e₂
      [(d, "ifnull " ++ showAt a ++ " then" ++ posNote sp blk path)] ++
      elabLines env sp blk (sc.step env.lib hd 0 id) (d + 1) (path ++ [0]) e₁ ++
      [(d, "else " ++ nameStr x ++ " =>")] ++ elabLines env sp blk (sc.step env.lib hd 1 id) (d + 1) (path ++ [1]) e₂
  | .cas acq rel w e v t ok fail =>
      let hd : Expr := .cas acq rel w e v t ok fail
      [(d, "cas " ++ (if acq then "acq " else "") ++ (if rel then "rel " else "") ++ showAt w ++ " " ++
           showAt e ++ " -> " ++ showAt v ++ " as " ++ nameStr t ++ " then" ++ posNote sp blk path)] ++
      elabLines env sp blk (sc.step env.lib hd 0 id) (d + 1) (path ++ [0]) ok ++ [(d, "else")] ++
      elabLines env sp blk (sc.step env.lib hd 1 id) (d + 1) (path ++ [1]) fail
  | .casp acq rel w e0 e1 v0 v1 t ok fail =>
      let hd : Expr := .casp acq rel w e0 e1 v0 v1 t ok fail
      [(d, "casp " ++ (if acq then "acq " else "") ++ (if rel then "rel " else "") ++ showAt w ++ " (" ++
           showAt e0 ++ ", " ++ showAt e1 ++ ") -> (" ++ showAt v0 ++ ", " ++ showAt v1 ++ ") as " ++
           nameStr t ++ " then" ++ posNote sp blk path)] ++
      elabLines env sp blk (sc.step env.lib hd 0 id) (d + 1) (path ++ [0]) ok ++ [(d, "else")] ++
      elabLines env sp blk (sc.step env.lib hd 1 id) (d + 1) (path ++ [1]) fail
  | .ret a => [(d, "ret " ++ showAt a ++ posNote sp blk path)]
  | .tail f is a ts => [(d, "tail " ++ showCall env sc f is a ts ++ posNote sp blk path)]

def showDeclElab (d : Decl) (sp : List Span) (env : Env := {}) : String :=
  let (sc, tns) := declSc d
  let tps := (tns.zip d.tparams).map fun (a, κ) => if κ == {} then a else a ++ " : " ++ showKind κ
  let head := "def " ++ nameStr d.name ++
    (if tps.isEmpty then "" else "[" ++ ", ".intercalate tps ++ "]") ++
    (if d.idx.isEmpty then "" else "{" ++ ", ".intercalate (d.idx.map nameStr) ++ "}") ++
    "(" ++ nameStr d.arg ++ " : " ++ showTy env sc 0 d.argTy ++ ") : " ++ showTy env sc 0 d.retTy ++ " ="
  render ((0, head) :: elabLines { env with lib := d :: env.lib } sp d.name sc 1 [] d.body)

/-- The elaborated program, each block printed knowing the blocks before it (as `Syntax.showProg`). -/
def showProgElab (p : Prog) (sp : List Span) (env : Env := {}) : String :=
  let rec go : Prog → Env → List String
    | [], _ => []
    | d :: ds, env => showDeclElab d sp env :: go ds { env with lib := d :: env.lib }
  "\n\n".intercalate (go p env)

/-- `--print-elab` of a source text: the elaborated program with source positions, or the first error. -/
def printElab (s : String) (env : Env := {}) : Except Err String :=
  (parseUnit s env).map fun r => showProgElab (elabProg r.unit.decls) r.spans.toList env

end USyntax
