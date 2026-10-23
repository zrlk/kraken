/-
# Syntax — a concrete syntax for CoreLang (parser and printer)

CoreLang programs are Lean values (`Decl`, `Expr`, `Op`, `Ty`).  This file
gives them a textual form: `parseDecl`/`parseProg`/`parseTy`/… read it, and
`showDecl`/`showTy`/… print it.  The printer's output is read back by the
parser to the same AST (`#guard`s below, and `SyntaxTest.lean` for every
library program), so the two agree by test, not by hope.

Nothing here is trusted: a parsed program is judged by the same checker as a
hand-built one.

## The grammar, by example

```
def read{r}(m : Ptr pub (Word[r, Seq] * Ptr[r] (Int * Int))) : Int * Int =
  let w = fld 0 m
  let c1 = load acq w
  parity c1 of
    2k =>
      let d0 = fld 1 m
      let d = load d0
      let x = load d
      let f2 = fence ld
      let c2 = load w
      if c2 = c1 then
        let y = validate x
        ret y
      else
        tail read{r}(m)
    2k+1 =>
      tail read{r}(m)
```

Whitespace and newlines are insignificant; `--` starts a comment.  Every
term ends in `ret` or `tail`, so branches need no brackets.

**Index terms** (brackets `[…]` always mean an index): `a`, `3`, `i + j`,
`i - j` (truncated), `2*i`.

**Types**, loosest first:

| form | meaning |
|---|---|
| `exists a. τ`, `forall a. τ` | index quantifiers |
| `exists (α : κ). τ`, `mu α. τ` | type existential, recursive type |
| `σ + τ`, `σ * τ` | sum, product (both associate to the right) |
| `Ptr μ τ`, `Ptr? μ τ`, `Loc μ τ`, `Array[i] τ` | μ is `own`, `pub` or `[r]` |
| `Unit Void Int Int[i]` | `Int[i]` is the singleton |
| `U8 … U64 I8 … I64 LanesU8 … LanesI64` | fixed width; packed lanes |
| `Code(σ, τ)` | a bare code pointer |
| `Word[r, P]`, `Tok[r]`, `Tok[r, P, i]`, `Share[r]`, `Cap[c, r]`, `Pair[r, P]`, `Tok[r, P, i, j]` | protocol word, token (fresh; taken, in state `i` of `P`), share, capability (`c` is `pub`/`bor`/`rd`/`frz`) |
| `{τ | ψ}` | refinement; ψ is `true`, `i <= j`, `i = j`, `ini >= i`, `ψ && ψ` |
| `α`, `Name`, `Name(τ, …)` | a type variable, or a name from the `Env` (`Mutex(τ)`, `SeqLock(τ)`, and `Fn(σ, τ)`, the region arrow `CoreLang.arrowRgn .bor σ τ`) |

**Kinds**: `*` (asserts nothing) or `{zero, insens, share, noOwn, copy, noWord, atom=word}`.

**Protocols**: a name from the `Env` (`Mutex`, `Seq`, `Claim`), or literally
`<2k!, 2k+1 ; 0->1, 1->0+1 ; ghost, local, robust, norepeat, lends(0), lendsDown(1), recover(1->0)>`: the state
families (`!` marks those that hold the region), the transitions (`+d`/`-d`
when the parameter moves, `*` for a wild move, which relates any parameters),
then optional flags (`recover(h->s)`: the declared recovery target of held
family `h`, `Proto.recover`).

**Pair protocols** (`Pair[r, P]`, `Tok[r, P, i, j]`): a name from the `Env`
(`Ticket`, `Epoch`) or `<<(k, k | k1 = k0)!, (k, k | k1 <= k0 - 1) ; 0->1(+1, 0),
1->0(0, +1) ; robust>>`: each family is a pattern per half with an optional
relation `k1 = | <= | >= k0 [+ d | - d]` between the parameters; a move gives
a delta per half, `*` for a half it forgets.

**Operations** (the right-hand side of `let x = …`): an atom (`x`, `3`, `()`),
`(a, b)`, `a + b`, `a - b`, `a mod n`, `a & m`, `b[i]`, `f[τ…]{r…}(a)`,
`inl[τ] a`, `inr[τ] a`, `new a`, `publish a`, `intoRgn r a`, `newBuf[τ] n`, `bufInit b i v`,
`null : Ptr? μ τ`, `fold a : τ`, `fld 0 a`, `load a`, `load acq a`, `load b[i]`,
`load b[i].0.1`, `store a v`, `store rel a v with t`, `fence ld|st|full`,
`mkWord r P v t`, `mkWord2 r P (v0, v1) t`, `ldp acq w as (k0, k1)`,
`stp rel w (v0, v1) with t`, `mkEPair r P (v0, v1)`, `pack a at r : τ`, `validate x`, `borrow bor t`, `endBorrow t`,
`freeze t`, `xchg a v`, `xchg b[i] v`, `xchg b[i].0 v`, `fetch add acq rel a v`
(`add`, `or`, `and`, `xor`; `acq`/`rel` optional), `fnptr f`, `callc f a`,
`nameI a`, `bits and a b`, `bit1 ctz a`, `vmatch lo hi b`, `zero[τ]`,
`cvt U8 a`, `toInt a`, `asLanes U8 a`, `fop add a b`, `fcmp lt a b`,
`fop1 neg a`, `lane a j`, `setLane a j v`, `ldl b i`, `stl b i v`,
`ldlw b w j`, `stlw b w j v`.

**Terms**: `let x = op e`, `let (x, y) = a e`, `let <i, x> = unpack a e`,
`let <r, p, t> = region a e`, `let <r, p, c> = openPub a e`,
`case a of inl x => e inr y => e`, `parity a of 2k => e 2k+1 => e`,
`if a = b then e else e`, `ifnull a then e else x => e`,
`cas acq rel w e -> v as t then e else e`,
`casp acq rel w (e0, e1) -> (v0, v1) as t then e else e`, `ret a`, `tail f[τ…]{r…}(a)`.

**Code blocks**: `def f[α : κ, …]{r, …}(x : σ) : τ = e`.  A program is a
sequence of code blocks, with `type Name = τ` and `proto Name = P` in between
to name things for what follows.

A keyword used as a name is written `«load»`.  Unicode is accepted for
`∃ ∀ μ × → ⇒ ↦ ⟨ ⟩ ≤ ≥ ∧ ⊤`.

## Index variables inside code

Index variables are named where they are bound (`unpack`, `region`,
`openPub`, `parity`, `rem`/`band`/`nameI`) and referred to by name.  In a type
written inside a code block, a name is resolved against those binders.  Two
binders depend on types: loading a *protocol word* binds a fresh index (named
by the variable: after `let c1 = load acq w`, `Int[c1]` is the observed
value), and the `else` of an `if` may bind one.  The parser and printer follow
the checker's own context through the block (`Scope.lean`), using the
signatures of the block itself and of the blocks before it in the program
(`Env.lib`), so they bind exactly what the checker binds.  Where that context
is lost (a call to a block not in `Env.lib`, or a prefix the checker would
refuse), they fall back to a syntactic rule: after a `load` or in an `else`,
an index name bound *before* it cannot be used in a type, and the parser says
so rather than guess.

Build: LEAN_PATH=build lean -o build/Syntax.olean Syntax.lean
(after Scope.olean)
-/
import WeakCore.Scope
open CoreLang CoreTerm

namespace Syntax

/-! ## Tokens -/

inductive Tk
  | id (s : String)     -- identifier or keyword
  | qid (s : String)    -- `«…»`: always a name, never a keyword
  | num (n : Nat)
  | sym (s : String)
  | eof
  deriving Repr, BEq, Inhabited

structure Tok where
  tk   : Tk
  line : Nat
  col  : Nat
  deriving Repr, Inhabited

structure Err where
  line : Nat
  col  : Nat
  msg  : String
  deriving Repr, Inhabited

instance : ToString Err := ⟨fun e => s!"{e.line}:{e.col}: {e.msg}"⟩

def Tk.show : Tk → String
  | .id s => s!"'{s}'" | .qid s => s!"'«{s}»'" | .num n => s!"'{n}'"
  | .sym s => s!"'{s}'" | .eof => "the end of the input"

/-- Greek letters (except the few with a meaning of their own) are letters. -/
def isGreek (c : Char) : Bool := c.val ≥ 0x391 && c.val ≤ 0x3C9

def isIdStart (c : Char) : Bool := c.isAlpha || c == '_' || isGreek c
def isIdChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\'' || isGreek c

/-- Unicode spellings, as the ASCII token they stand for. -/
def uniSym (c : Char) : Option Tk :=
  match c with
  | '×' => some (.sym "*") | '·' => some (.sym "*")
  | '→' => some (.sym "->") | '↦' => some (.sym "->") | '⇒' => some (.sym "=>")
  | '⟨' => some (.sym "<") | '⟩' => some (.sym ">")
  | '≤' => some (.sym "<=") | '≥' => some (.sym ">=") | '∧' => some (.sym "&&")
  | '∃' => some (.id "exists") | '∀' => some (.id "forall") | '⊤' => some (.id "true")
  | _ => none

def syms2 : List String := ["->", "=>", "<=", ">=", "&&"]
def syms1 : List Char := ['(', ')', '[', ']', '{', '}', '<', '>', ',', '.', ':', ';', '=', '+', '-', '*', '|', '&', '!']

partial def lexAux (cs : Array Char) (i line col : Nat) (acc : Array Tok) : Except Err (Array Tok) :=
  if h : i < cs.size then
    let c := cs[i]
    let nxt := cs[i + 1]?
    if c == '\n' then lexAux cs (i + 1) (line + 1) 1 acc
    else if c == ' ' || c == '\t' || c == '\r' then lexAux cs (i + 1) line (col + 1) acc
    else if c == '-' && nxt == some '-' then
      -- a comment, to the end of the line
      let rec skip (j : Nat) : Nat := if j < cs.size && cs[j]! != '\n' then skip (j + 1) else j
      let j := skip i
      lexAux cs j line (col + (j - i)) acc
    else if c == '«' then
      let rec close (j : Nat) : Nat := if j < cs.size && cs[j]! != '»' then close (j + 1) else j
      let j := close (i + 1)
      if j ≥ cs.size then .error ⟨line, col, "unterminated «"⟩
      else
        let s := String.ofList (cs.extract (i + 1) j).toList
        lexAux cs (j + 1) line (col + (j + 1 - i)) (acc.push ⟨.qid s, line, col⟩)
    else if c.isDigit then
      let rec digits (j : Nat) : Nat := if j < cs.size && cs[j]!.isDigit then digits (j + 1) else j
      let j := digits i
      let n := (String.ofList (cs.extract i j).toList).toNat!
      lexAux cs j line (col + (j - i)) (acc.push ⟨.num n, line, col⟩)
    else if isIdStart c then
      let rec word (j : Nat) : Nat := if j < cs.size && isIdChar cs[j]! then word (j + 1) else j
      let j := word i
      let s := String.ofList (cs.extract i j).toList
      -- `Ptr?` is one word
      let (s, j) := if s == "Ptr" && cs[j]? == some '?' then ("Ptr?", j + 1) else (s, j)
      let s := if s == "μ" then "mu" else s
      lexAux cs j line (col + (j - i)) (acc.push ⟨.id s, line, col⟩)
    else match uniSym c with
      | some t => lexAux cs (i + 1) line (col + 1) (acc.push ⟨t, line, col⟩)
      | none =>
        let two := String.ofList [c, nxt.getD ' ']
        if syms2.contains two then lexAux cs (i + 2) line (col + 2) (acc.push ⟨.sym two, line, col⟩)
        else if syms1.contains c then lexAux cs (i + 1) line (col + 1) (acc.push ⟨.sym c.toString, line, col⟩)
        else .error ⟨line, col, s!"unexpected character '{c}'"⟩
  else .ok (acc.push ⟨.eof, line, col⟩)

def lex (s : String) : Except Err (Array Tok) := lexAux s.toList.toArray 0 1 1 #[]

/-! ## Names in scope, and the environment -/

/-- Type variables and index variables in scope, innermost first.  `none` in
`ivs` is a barrier: an unknown number of index binders (a `load`). -/
structure Sc where
  tvs : List String := []
  ivs : List (Option String) := []
  /-- The checker's context here, while the walk has followed it
  (`Scope.branches`); then `ivs` is exactly its index names. -/
  cx : Option Cx := none

namespace Sc
def pushT (sc : Sc) (a : String) : Sc := { sc with tvs := a :: sc.tvs }
def pushI (sc : Sc) (a : String) : Sc := { sc with ivs := some a :: sc.ivs }
def barrier (sc : Sc) : Sc := { sc with ivs := none :: sc.ivs }

/-- The de Bruijn index of an index name. -/
def resolveI (sc : Sc) (x : String) : Except String Nat :=
  let rec go : List (Option String) → Nat → Except String Nat
    | [], _ => .error s!"unknown index variable '{x}'"
    | none :: _, _ => .error s!"index variable '{x}' is bound before a load (or an if), which may bind index variables of its own; it cannot be named in a type here"
    | some y :: r, k => if y == x then .ok k else go r (k + 1)
  go sc.ivs 0

/-- The name of de Bruijn index `k`, if it can be written (not behind a
barrier, not shadowed by a nearer binder of the same name). -/
def ivName (sc : Sc) (k : Nat) : Option String :=
  let rec go : List (Option String) → Nat → List String → Option String
    | [], _, _ => none
    | none :: _, _, _ => none
    | some y :: _, 0, seen => if seen.contains y then none else some y
    | some y :: r, k + 1, seen => go r k (y :: seen)
  go sc.ivs k []

/-- The scope for subterm `i` of `e` (whose head only is looked at): the
checker's, if it is known; otherwise the syntactic rule `syn`. -/
def step (lib : Prog) (sc : Sc) (e : Expr) (i : Nat) (syn : Sc → Sc) : Sc :=
  match Scope.nth lib sc.cx e i with
  | some c => { sc with ivs := c.inames.map some, cx := some c }
  | none => { syn sc with cx := none }

def tvName (sc : Sc) (k : Nat) : Option String :=
  match sc.tvs[k]? with
  | some a => if (sc.tvs.take k).contains a then none else some a
  | none => none
end Sc

/-- What the parser knows by name: protocols, and type names or families
(`Name` or `Name(τ, …)`: a name, its arity, its meaning). -/
structure Env where
  protos : List (String × Proto) := [("Mutex", mutexP), ("Seq", seqP), ("Claim", claimP)]
  protos2 : List (String × Proto2) := [("Ticket", ticketP), ("Epoch", epochP)]
  types  : List (String × Nat × (List Ty → Ty)) :=
    [("Mutex", 1, fun ts => mutex (ts.headD .unit)), ("SeqLock", 1, fun ts => seqLock (ts.headD .unit)),
     ("Fn", 2, fun ts => arrowRgn .bor (ts.headD .unit) (ts.getD 1 .unit))]
  /-- Code blocks whose signatures calls may use (for `Scope`: the index
  variables a `load` binds depend on types). -/
  lib : Prog := []

namespace Env
def default : Env := {}
def addProto (e : Env) (n : String) (P : Proto) : Env := { e with protos := (n, P) :: e.protos }
def addProto2 (e : Env) (n : String) (P : Proto2) : Env := { e with protos2 := (n, P) :: e.protos2 }
def addType (e : Env) (n : String) (t : Ty) : Env := { e with types := (n, 0, fun _ => t) :: e.types }
def addFamily (e : Env) (n : String) (f : Ty → Ty) : Env :=
  { e with types := (n, 1, fun ts => f (ts.headD .unit)) :: e.types }
end Env

/-! ## The parser -/

abbrev P := ReaderT (Array Tok) (StateT Nat (Except Err))

instance {γ : Type} : Inhabited (P γ) := ⟨fun _ _ => .error default⟩

def cur : P Tok := do
  let ts ← read
  let i ← get
  pure (ts[i]?.getD (ts.back?.getD default))

def peekAt (k : Nat) : P Tk := do
  let ts ← read
  let i ← get
  pure ((ts[i + k]?.map (·.tk)).getD .eof)

def bump : P Unit := modify (· + 1)

def failP {γ : Type} (msg : String) : P γ := do
  let t ← cur
  throw ⟨t.line, t.col, msg⟩

def isSym (s : String) : P Bool := return (← cur).tk == .sym s
def isKw (s : String) : P Bool := return (← cur).tk == .id s

def eatSym (s : String) : P Bool := do
  if ← isSym s then bump; pure true else pure false
def eatKw (s : String) : P Bool := do
  if ← isKw s then bump; pure true else pure false

def expectSym (s : String) : P Unit := do
  unless ← eatSym s do failP s!"expected '{s}', found {(← cur).tk.show}"
def expectKw (s : String) : P Unit := do
  unless ← eatKw s do failP s!"expected '{s}', found {(← cur).tk.show}"

def pNat : P Nat := do
  match (← cur).tk with
  | .num n => bump; pure n
  | t => failP s!"expected a number, found {t.show}"

/-- Words with a meaning in terms; as names they are written `«…»`. -/
def keywords : List String :=
  ["let", "case", "of", "inl", "inr", "parity", "if", "then", "else", "ifnull", "cas", "acq",
   "rel", "as", "ret", "tail", "def", "with", "at", "mod", "new", "publish", "intoRgn", "newBuf", "bufInit",
   "null", "fold", "fld", "load", "store", "fence", "mkWord", "pack", "validate", "borrow",
   "endBorrow", "xchg", "fnptr", "callc", "nameI", "bits", "bit1", "vmatch", "zero", "freeze",
   "cvt", "toInt", "asLanes", "fop", "fcmp", "fop1", "lane", "setLane", "ldl", "stl", "ldlw",
   "stlw", "unpack", "region", "openPub", "type", "proto", "exists", "forall", "mu",
   "mkWord2", "ldp", "stp", "casp", "mkEPair", "mkTicket", "claim", "fetch",
   "spawn", "emit", "current", "exitEv"]

def validName (s : String) : Bool :=
  match s.toList with
  | c :: cs => isIdStart c && cs.all isIdChar && !keywords.contains s && s != "μ" && s != "Ptr"
  | [] => false

def pName : P String := do
  match (← cur).tk with
  | .id s => if keywords.contains s then failP s!"'{s}' is a keyword; write «{s}» for a name"
             else bump; pure s
  | .qid s => bump; pure s
  | t => failP s!"expected a name, found {t.show}"

def sepBy {γ : Type} (p : P γ) (sep : String) : P (List γ) := do
  let x ← p
  let rec more (acc : List γ) (fuel : Nat) : P (List γ) := do
    match fuel with
    | 0 => pure acc.reverse
    | f + 1 => if ← eatSym sep then more ((← p) :: acc) f else pure acc.reverse
  more [x] 100000

/-! ### Indices, predicates, kinds, protocols -/

mutual
partial def pIdx (sc : Sc) : P Idx := do
  let a ← pIdxTerm sc
  pIdxMore sc a

partial def pIdxMore (sc : Sc) (a : Idx) : P Idx := do
  if ← eatSym "+" then pIdxMore sc (.add a (← pIdxTerm sc))
  else if ← eatSym "-" then pIdxMore sc (.sub a (← pIdxTerm sc))
  else pure a

partial def pIdxTerm (sc : Sc) : P Idx := do
  match (← cur).tk with
  | .num n =>
      bump
      if ← eatSym "*" then pure (.smul n (← pIdxAtom sc)) else pure (.lit n)
  | _ => pIdxAtom sc

partial def pIdxAtom (sc : Sc) : P Idx := do
  match (← cur).tk with
  | .num n => bump; pure (.lit n)
  | .sym "(" => bump; let i ← pIdx sc; expectSym ")"; pure i
  | _ =>
      let x ← pName
      match sc.resolveI x with
      | .ok k => pure (.var k)
      | .error m => failP m
end

def pMode (sc : Sc) : P Mode := do
  if ← eatKw "own" then pure .own
  else if ← eatKw "pub" then pure .pub
  else if ← eatSym "[" then let r ← pIdx sc; expectSym "]"; pure (.rgn r)
  else failP s!"expected a mode (own, pub or [r]), found {(← cur).tk.show}"

def pCap : P Cap := do
  if ← eatKw "pub" then pure .pub
  else if ← eatKw "bor" then pure .bor
  else if ← eatKw "rd" then pure .rd
  else if ← eatKw "frz" then pure .frz
  else failP s!"expected a capability (pub, bor, rd, frz), found {(← cur).tk.show}"

partial def pPredAtom (sc : Sc) : P Pred := do
  if ← eatKw "true" then return .tt
  if ← eatKw "ini" then expectSym ">="; return .ini (← pIdx sc)
  -- `(ψ)`, else an index term that happens to start with a parenthesis
  let paren : P Pred := do expectSym "("; let p ← pPred sc; expectSym ")"; pure p
  let cmp : P Pred := do
    let i ← pIdx sc
    if ← eatSym "<=" then pure (.le i (← pIdx sc))
    else if ← eatSym "=" then pure (.eq i (← pIdx sc))
    else failP s!"expected '<=' or '=', found {(← cur).tk.show}"
  if ← isSym "(" then (paren <|> cmp) else cmp
where
  pPred (sc : Sc) : P Pred := do
    let a ← pPredAtom sc
    if ← eatSym "&&" then pure (.and a (← pPred sc)) else pure a

def pPred (sc : Sc) : P Pred := pPredAtom.pPred sc

def pKind : P Kind := do
  if ← eatSym "*" then return {}
  expectSym "{"
  if ← eatSym "}" then return {}
  let flags ← sepBy (do
    match (← cur).tk with
    | .id "atom" =>
        bump; expectSym "="
        if ← eatKw "word" then pure ("atom", Atom.word)
        else if ← eatKw "pair" then pure ("atom", Atom.pair)
        else if ← eatKw "none" then pure ("atom", Atom.none)
        else failP "expected word, pair or none"
    | .id s =>
        if ["zero", "insens", "share", "noOwn", "copy", "noWord"].contains s then bump; pure (s, Atom.none)
        else failP s!"unknown kind flag '{s}'"
    | t => failP s!"expected a kind flag, found {t.show}") ","
  expectSym "}"
  let has (s : String) := flags.any (·.1 == s)
  let atm := (flags.find? (·.1 == "atom")).map (·.2) |>.getD .none
  pure { zero := has "zero", insens := has "insens", share := has "share", noOwn := has "noOwn",
         copy := has "copy", noWord := has "noWord", atom := atm }

def pClause : P Clause := do
  let (scale, off) ← match (← cur).tk with
    | .num n =>
        bump
        if ← eatKw "k" then
          if ← eatSym "+" then pure (n, ← pNat) else pure (n, 0)
        else pure (0, n)
    | .id "k" => bump; if ← eatSym "+" then pure (1, ← pNat) else pure (1, 0)
    | t => failP s!"expected a state family (2k, 2k+1, k, 0, …), found {t.show}"
  let holds ← eatSym "!"
  pure ⟨scale, off, holds⟩

/-- A transition; `none` for a wild one (`a->b*`). -/
def pTrans : P (Nat × Nat × Option Int) := do
  let a ← pNat
  expectSym "->"
  let b ← pNat
  if ← eatSym "+" then pure (a, b, some (Int.ofNat (← pNat)))
  else if ← eatSym "-" then pure (a, b, some (-Int.ofNat (← pNat)))
  else if ← eatSym "*" then pure (a, b, none)
  else pure (a, b, some 0)

def pNatList : P (List Nat) := do
  expectSym "("
  if ← eatSym ")" then return []
  let xs ← sepBy pNat ","
  expectSym ")"
  pure xs

/-- `(2->0, 4->0)`: the recovery targets of `recover(…)`. -/
def pPairList : P (List (Nat × Nat)) := do
  expectSym "("
  if ← eatSym ")" then return []
  let xs ← sepBy (do let a ← pNat; expectSym "->"; let b ← pNat; pure (a, b)) ","
  expectSym ")"
  pure xs

def pProto (env : Env) : P Proto := do
  if ← eatSym "<" then
    let cls ← sepBy pClause ","
    expectSym ";"
    let trs ← if (← isSym ";") || (← isSym ">") then pure [] else sepBy pTrans ","
    let mut ghost := false
    let mut isLocal := false
    let mut robust := false
    let mut norepeat := false
    let mut epoch := false
    let mut ticket := false
    let mut lends : List Nat := []
    let mut lendsDown : List Nat := []
    let mut recover : List (Nat × Nat) := []
    if ← eatSym ";" then
      let fs ← sepBy (do
        match (← cur).tk with
        | .id "ghost" => bump; pure ("ghost", [], [])
        | .id "local" => bump; pure ("local", [], [])
        | .id "robust" => bump; pure ("robust", [], [])
        | .id "norepeat" => bump; pure ("norepeat", [], [])
        | .id "epoch" => bump; pure ("epoch", [], [])
        | .id "ticket" => bump; pure ("ticket", [], [])
        | .id "lends" => bump; pure ("lends", ← pNatList, [])
        | .id "lendsDown" => bump; pure ("lendsDown", ← pNatList, [])
        | .id "recover" => bump; pure ("recover", [], ← pPairList)
        | t => failP s!"expected ghost, local, robust, norepeat, epoch, ticket, lends(…), lendsDown(…) or recover(…), found {t.show}") ","
      for (f, ns, ps) in fs do
        if f == "ghost" then ghost := true
        else if f == "local" then isLocal := true
        else if f == "robust" then robust := true
        else if f == "norepeat" then norepeat := true
        else if f == "epoch" then epoch := true
        else if f == "ticket" then ticket := true
        else if f == "lends" then lends := ns
        else if f == "recover" then recover := ps
        else lendsDown := ns
    expectSym ">"
    let ords := trs.filterMap fun (a, b, d) => d.map fun d => (a, b, d)
    let wild := trs.filterMap fun (a, b, d) => if d.isNone then some (a, b) else none
    pure ⟨cls, ords, ghost, lends, lendsDown, wild, isLocal, robust, norepeat, epoch, ticket, recover⟩
  else
    let n ← pName
    match env.protos.find? (·.1 == n) with
    | some (_, P) => pure P
    | none => failP s!"unknown protocol '{n}'"

/-- A signed delta: `+3`, `-1`. -/
def pDelta : P Int := do
  if ← eatSym "+" then pure (Int.ofNat (← pNat))
  else if ← eatSym "-" then pure (-Int.ofNat (← pNat))
  else failP "expected +d or -d"

/-- `(k, 2k+1 | k1 <= k0 - 1)!`: a pair family. -/
def pClause2 : P Clause2 := do
  expectSym "("
  let a ← pClause
  expectSym ","
  let b ← pClause
  let rel ← if ← eatSym "|" then
      expectKw "k1"
      let mk : Int → Rel2 ←
        if ← eatSym "=" then pure Rel2.eq
        else if ← eatSym "<=" then pure Rel2.le
        else if ← eatSym ">=" then pure Rel2.ge
        else failP "expected =, <= or >= after k1"
      expectKw "k0"
      let d ← if (← isSym "+") || (← isSym "-") then pDelta else pure 0
      pure (mk d)
    else pure Rel2.free
  expectSym ")"
  let holds ← eatSym "!"
  pure ⟨a.scale, a.off, b.scale, b.off, rel, holds⟩

/-- `0->1(+1, 0)`, `0->0(+1, *)`; no parenthesis: both deltas 0. -/
def pTrans2 : P (Nat × Nat × Option Int × Option Int) := do
  let a ← pNat
  expectSym "->"
  let b ← pNat
  if ← eatSym "(" then
    let half : P (Option Int) := do
      if ← eatSym "*" then pure none
      else if (← isSym "+") || (← isSym "-") then some <$> pDelta
      else do let n ← pNat; pure (some (Int.ofNat n))
    let d0 ← half
    expectSym ","
    let d1 ← half
    expectSym ")"
    pure (a, b, d0, d1)
  else pure (a, b, some 0, some 0)

/-- Is a pair protocol next: `<<`, or a name from `Env.protos2`? -/
def atProto2 (env : Env) : P Bool := do
  match (← cur).tk with
  | .sym "<" => pure ((← peekAt 1) == .sym "<")
  | .id n => pure (env.protos2.any (·.1 == n))
  | .qid n => pure (env.protos2.any (·.1 == n))
  | _ => pure false

def pProto2 (env : Env) : P Proto2 := do
  if ← eatSym "<" then
    expectSym "<"
    let cls ← sepBy pClause2 ","
    expectSym ";"
    let trs ← if (← isSym ";") || (← isSym ">") then pure [] else sepBy pTrans2 ","
    let mut robust := false
    let mut epoch := false
    if ← eatSym ";" then
      let fs ← sepBy (do
        match (← cur).tk with
        | .id "robust" => bump; pure "robust"
        | .id "epoch" => bump; pure "epoch"
        | t => failP s!"expected robust or epoch, found {t.show}") ","
      robust := fs.contains "robust"
      epoch := fs.contains "epoch"
    expectSym ">"; expectSym ">"
    pure { clauses := cls, trans := trs, robust := robust, epoch := epoch }
  else
    let n ← pName
    match env.protos2.find? (·.1 == n) with
    | some (_, P) => pure P
    | none => failP s!"unknown pair protocol '{n}'"

/-- An epoch counter of either shape, as a type or `mkEPair` names it. -/
def pECounter (env : Env) : P ECounter := do
  if ← atProto2 env then pure (.pair (← pProto2 env)) else pure (.word (← pProto env))


/-! ### Types -/

def fixOfName (s : String) : Option (Bool × Wd) :=
  let w (t : String) : Option Wd := match t with
    | "8" => some .w8 | "16" => some .w16 | "32" => some .w32 | "64" => some .w64 | _ => none
  if s.startsWith "U" then (w (s.drop 1).toString).map (false, ·)
  else if s.startsWith "I" then (w (s.drop 1).toString).map (true, ·)
  else none

def fixName (sg : Bool) (w : Wd) : String := (if sg then "I" else "U") ++ w.name

mutual
partial def pTy (env : Env) (sc : Sc) : P Ty := do
  match (← cur).tk with
  | .id "exists" =>
      bump
      if ← eatSym "(" then
        let a ← pName; expectSym ":"; let κ ← pKind; expectSym ")"; expectSym "."
        pure (.tex κ (← pTy env (sc.pushT a)))
      else
        let a ← pName; expectSym "."
        pure (.iex (← pTy env (sc.pushI a)))
  | .id "forall" => bump; let a ← pName; expectSym "."; pure (.iall (← pTy env (sc.pushI a)))
  | .id "mu" => bump; let a ← pName; expectSym "."; pure (.mu (← pTy env (sc.pushT a)))
  | _ => pTySum env sc

partial def pTySum (env : Env) (sc : Sc) : P Ty := do
  let a ← pTyProd env sc
  if ← eatSym "+" then pure (.sum a (← pTySum env sc)) else pure a

partial def pTyProd (env : Env) (sc : Sc) : P Ty := do
  let a ← pTyApp env sc
  if ← eatSym "*" then pure (.prod a (← pTyProd env sc)) else pure a

partial def pTyApp (env : Env) (sc : Sc) : P Ty := do
  match (← cur).tk with
  | .id "Ptr" => bump; let μ ← pMode sc; pure (.ptr μ (← pTyApp env sc))
  | .id "Ptr?" => bump; let μ ← pMode sc; pure (.ptrOpt μ (← pTyApp env sc))
  | .id "Loc" => bump; let μ ← pMode sc; pure (.loc μ (← pTyApp env sc))
  | .id "Array" =>
      bump; expectSym "["; let i ← pIdx sc; expectSym "]"; pure (.array i (← pTyApp env sc))
  | _ => pTyAtom env sc

partial def pTyAtom (env : Env) (sc : Sc) : P Ty := do
  match (← cur).tk with
  | .sym "(" => bump; let t ← pTy env sc; expectSym ")"; pure t
  | .sym "{" =>
      bump; let t ← pTy env sc; expectSym "|"; let ψ ← pPred sc; expectSym "}"; pure (.refine t ψ)
  | .id "Unit" => bump; pure .unit
  | .id "Void" => bump; pure .void
  | .id "ThreadId" => bump; pure .tid
  | .id "Int" =>
      bump
      if ← eatSym "[" then let i ← pIdx sc; expectSym "]"; pure (.intS i) else pure .int
  | .id "Code" =>
      bump; expectSym "("; let a ← pTy env sc; expectSym ","; let b ← pTy env sc; expectSym ")"
      pure (.code a b)
  | .id "Word" =>
      bump; expectSym "["; let r ← pIdx sc; expectSym ","; let P ← pProto env; expectSym "]"
      pure (.word r P)
  | .id "Pair" =>
      bump; expectSym "["; let r ← pIdx sc; expectSym ","; let P ← pProto2 env; expectSym "]"
      pure (.word2 r P)
  | .id "EPair" =>
      bump; expectSym "["; let r ← pIdx sc; expectSym ","; let P ← pECounter env; expectSym "]"
      pure (.epair r P)
  | .id "Share" => bump; expectSym "["; let r ← pIdx sc; expectSym "]"; pure (.share r)
  | .id "Cap" =>
      bump; expectSym "["; let c ← pCap; expectSym ","; let r ← pIdx sc; expectSym "]"
      pure (.cap c r)
  | .id "Tok" =>
      bump; expectSym "["; let r ← pIdx sc
      if ← eatSym "," then
        if ← atProto2 env then
          let P ← pProto2 env; expectSym ","; let i ← pIdx sc
          if ← eatSym "," then
            let j ← pIdx sc; expectSym "]"; pure (.tok2 r P i j)
          else
            -- `Tok[r, P, e]` of an epoch pair is the epoch token.
            expectSym "]"
            if P.epoch then pure (.tokE r (.pair P) i)
            else failP "a pair token names both halves: Tok[r, P, i, j]"
        else
          let P ← pProto env; expectSym ","; let i ← pIdx sc
          expectSym "]"
          -- `Tok[r, P, e]` of an epoch protocol is the epoch token.
          pure (if P.epoch then .tokE r (.word P) i else .tok r (some (P, i)))
      else
        expectSym "]"; pure (.tok r none)
  | .id s =>
      if s.startsWith "Lanes" then
        if let some (sg, w) := fixOfName (s.drop 5).toString then bump; return .lanes sg w
      if let some (sg, w) := fixOfName s then bump; return .fix sg w
      pTyName env sc
  | .qid _ => pTyName env sc
  | t => failP s!"expected a type, found {t.show}"

partial def pTyName (env : Env) (sc : Sc) : P Ty := do
  let n ← pName
  match sc.tvs.idxOf? n with
  | some k => pure (.tvar k)
  | none =>
    match env.types.find? (·.1 == n) with
    | none => failP s!"unknown type '{n}'"
    | some (_, ar, f) =>
        if ar == 0 then pure (f [])
        else
          expectSym "("
          let ts ← sepBy (pTy env sc) ","
          expectSym ")"
          if ts.length != ar then failP s!"'{n}' takes {ar} type argument(s)"
          pure (f ts)
end

/-! ### Operations and terms -/

def pAt : P At := do
  match (← cur).tk with
  | .num n => bump; pure (.lit n)
  | .sym "(" => bump; expectSym ")"; pure .unit
  | _ => .var <$> pName

def pBrTy (env : Env) (sc : Sc) : P Ty := do
  expectSym "["; let t ← pTy env sc; expectSym "]"; pure t

def pBrAt : P At := do
  expectSym "["; let a ← pAt; expectSym "]"; pure a

/-- `.0.1` after a slot. -/
partial def pPath : P (List Nat) := do
  if ← eatSym "." then pure ((← pNat) :: (← pPath)) else pure []

/-- `f[τ…]{r…}(a)`, after the name. -/
def pCallRest (env : Env) (sc : Sc) : P (List Ty × List String × At) := do
  let ts ← if ← eatSym "[" then do let ts ← sepBy (pTy env sc) ","; expectSym "]"; pure ts else pure []
  let is ← if ← eatSym "{" then do let is ← sepBy pName ","; expectSym "}"; pure is else pure []
  expectSym "("; let a ← pAt; expectSym ")"
  pure (ts, is, a)

def pWordOf {γ : Type} (names : List (String × γ)) (what : String) : P γ := do
  match (← cur).tk with
  | .id s => match names.find? (·.1 == s) with
      | some (_, x) => bump; pure x
      | none => failP s!"unknown {what} '{s}'"
  | t => failP s!"expected {what}, found {t.show}"

def fopNames : List (String × FOp) :=
  [("add", .add), ("sub", .sub), ("mul", .mul), ("div", .div), ("rem", .rem), ("and", .and),
   ("or", .or), ("xor", .xor), ("shl", .shl), ("shr", .shr)]
def fcmpNames : List (String × FCmp) := [("eq", .eq), ("ne", .ne), ("lt", .lt), ("le", .le)]
def fop1Names : List (String × FOp1) := [("not", .not), ("neg", .neg)]
def bitNames : List (String × BitOp) :=
  [("and", .and), ("or", .or), ("xor", .xor), ("shl", .shl), ("shr", .shr), ("wadd", .wadd),
   ("wsub", .wsub), ("wmul", .wmul), ("mulhi", .mulhi), ("msb16", .msb16)]
def bit1Names : List (String × BitOp1) := [("not", .not), ("ctz", .ctz), ("popcnt", .popcnt)]
def fenceNames : List (String × Fence) := [("ld", .ld), ("st", .st), ("full", .full)]
def fetchNames : List (String × FetchOp) := [("add", .add), ("or", .or), ("and", .and), ("xor", .xor)]

def pFix : P (Bool × Wd) := do
  match (← cur).tk with
  | .id s => match fixOfName s with
      | some x => bump; pure x
      | none => failP s!"expected a width (U8 … I64), found '{s}'"
  | t => failP s!"expected a width (U8 … I64), found {t.show}"

/-- After an atom on the right of `=`: an operator, or the atom itself. -/
def pAfterAtom (a : At) : P Op := do
  if ← eatSym "+" then pure (.add a (← pAt))
  else if ← eatSym "-" then pure (.sub a (← pAt))
  else if ← eatKw "mod" then pure (.rem a (← pAt))
  else if ← eatSym "&" then pure (.band a (← pAt))
  else if ← isSym "[" then let i ← pBrAt; pure (.idx a i)
  else pure (.atom a)

def pOp (env : Env) (sc : Sc) : P Op := do
  let a1 : P At := pAt
  match (← cur).tk with
  | .sym "(" =>
      bump
      if ← eatSym ")" then return .atom .unit
      let a ← pAt; expectSym ","; let b ← pAt; expectSym ")"; pure (.pair a b)
  | .num _ => pAfterAtom (← pAt)
  | .qid _ =>
      let f ← pName
      if (← isSym "{") || (← isSym "(") then
        let (ts, is, a) ← pCallRest env sc; pure (.call f is a ts)
      else if ← isSym "[" then
        let save ← get
        (do let (ts, is, a) ← pCallRest env sc; pure (Op.call f is a ts)) <|>
          (do set save; pAfterAtom (.var f))
      else pAfterAtom (.var f)
  | .id s =>
    match s with
    | "inl" => bump; let t ← pBrTy env sc; pure (.inl t (← a1))
    | "inr" => bump; let t ← pBrTy env sc; pure (.inr t (← a1))
    | "new" => bump; pure (.new (← a1))
    | "publish" => bump; pure (.publish (← a1))
    | "intoRgn" => bump; let r ← pName; pure (.intoRgn r (← a1))
    | "newBuf" => bump; let t ← pBrTy env sc; pure (.newBuf (← a1) t)
    | "bufInit" => bump; pure (.bufInit (← a1) (← a1) (← a1))
    | "null" =>
        bump; expectSym ":"
        match ← pTy env sc with
        | .ptrOpt μ t => pure (.null μ t)
        | _ => failP "null needs a type Ptr? μ τ"
    | "fold" => bump; let a ← a1; expectSym ":"; pure (.fold a (← pTy env sc))
    | "fld" => bump; let i ← pNat; pure (.fld i (← a1))
    | "load" =>
        bump
        let acq ← eatKw "acq"
        let a ← a1
        if ← isSym "[" then
          if acq then failP "a slot load has no acq"
          let i ← pBrAt
          let p ← pPath
          pure (if p.isEmpty then .loadAt a i else .loadAtF a i p)
        else pure (.load acq a)
    | "store" =>
        bump
        let rel ← eatKw "rel"
        let a ← a1; let v ← a1
        let t ← if ← eatKw "with" then some <$> a1 else pure none
        pure (.store rel a v t)
    | "fence" => bump; pure (.fence (← pWordOf fenceNames "a fence (ld, st, full)"))
    | "mkWord" => bump; let r ← pName; let P ← pProto env; pure (.mkWord r P (← a1) (← a1))
    | "mkTicket" =>
        bump; let r ← pName; let N ← pProto env; let P ← pProto env
        pure (.mkTicket r N P (← a1) (← a1))
    | "claim" => bump; let a ← a1; expectKw "with"; pure (.claim a (← a1))
    | "fetch" =>
        bump; let o ← pWordOf fetchNames "a fetch-op (add, or, and, xor)"
        let acq ← eatKw "acq"; let rel ← eatKw "rel"
        pure (.fetch o acq rel (← a1) (← a1))
    | "mkWord2" =>
        bump; let r ← pName; let P ← pProto2 env
        expectSym "("; let v0 ← a1; expectSym ","; let v1 ← a1; expectSym ")"
        pure (.mkWord2 r P v0 v1 (← a1))
    | "ldp" =>
        bump; let acq ← eatKw "acq"; let a ← a1; expectKw "as"
        expectSym "("; let n0 ← pName; expectSym ","; let n1 ← pName; expectSym ")"
        pure (.ldp acq a n0 n1)
    | "stp" =>
        bump; let rel ← eatKw "rel"; let a ← a1
        expectSym "("; let v0 ← a1; expectSym ","; let v1 ← a1; expectSym ")"
        expectKw "with"; pure (.stp rel a v0 v1 (← a1))
    | "mkEPair" =>
        bump; let r ← pName; let P ← pECounter env
        expectSym "("; let v0 ← a1; expectSym ","; let v1 ← a1; expectSym ")"
        pure (.mkEPair r P v0 v1)
    | "pack" =>
        bump; let a ← a1; expectKw "at"
        if ← eatSym "[" then
          -- A type existential: `pack a at [σ] : ∃(α:κ). τ`.
          let σ ← pTy env sc; expectSym "]"; expectSym ":"; pure (.packT a σ (← pTy env sc))
        else
          let w ← pName; expectSym ":"; pure (.pack a w (← pTy env sc))
    | "validate" => bump; pure (.validate (← pName))
    | "borrow" => bump; let c ← pCap; pure (.borrow c (← a1))
    | "endBorrow" => bump; pure (.endBorrow (← a1))
    | "freeze" => bump; pure (.freeze (← a1))
    | "xchg" =>
        bump
        let a ← a1
        if ← isSym "[" then
          let i ← pBrAt
          let p ← pPath
          let v ← a1
          pure (if p.isEmpty then .xchgAt a i v else .xchgAtF a i p v)
        else pure (.xchg a (← a1))
    | "fnptr" => bump; pure (.fnptr (← pName))
    | "callc" => bump; pure (.callc (← a1) (← a1))
    | "nameI" => bump; pure (.nameI (← a1))
    | "bits" => bump; let o ← pWordOf bitNames "a word operation"; pure (.bits o (← a1) (← a1))
    | "bit1" => bump; let o ← pWordOf bit1Names "a unary word operation"; pure (.bit1 o (← a1))
    | "vmatch" => bump; pure (.vmatch (← a1) (← a1) (← a1))
    | "zero" => bump; pure (.zero (← pBrTy env sc))
    | "cvt" => bump; let (sg, w) ← pFix; pure (.cvt sg w (← a1))
    | "toInt" => bump; pure (.toInt (← a1))
    | "asLanes" => bump; let (sg, w) ← pFix; pure (.asLanes sg w (← a1))
    | "fop" => bump; let o ← pWordOf fopNames "a fixed-width operation"; pure (.fop o (← a1) (← a1))
    | "fcmp" => bump; let o ← pWordOf fcmpNames "a comparison"; pure (.fcmp o (← a1) (← a1))
    | "fop1" => bump; let o ← pWordOf fop1Names "a unary fixed-width operation"; pure (.fop1 o (← a1))
    | "lane" => bump; pure (.lane (← a1) (← a1))
    | "spawn" =>
        -- (E1) `spawn f[ts] a : T`: the child's entry `f`, its type arguments, the argument and its checked type
        bump; let f ← pName
        let ts ← if ← eatSym "[" then do let ts ← sepBy (pTy env sc) ","; expectSym "]"; pure ts else pure []
        let a ← a1; expectSym ":"; pure (.spawn f a (← pTy env sc) ts)
    | "emit" => bump; pure (.ext .emit (← a1))
    | "current" => bump; pure (.ext .current (← a1))
    | "exitEv" => bump; pure (.ext .exitEv (← a1))
    | "setLane" => bump; pure (.setLane (← a1) (← a1) (← a1))
    | "ldl" => bump; pure (.ldl (← a1) (← a1))
    | "stl" => bump; pure (.stl (← a1) (← a1) (← a1))
    | "ldlw" => bump; pure (.ldlw (← a1) (← a1) (← a1))
    | "stlw" => bump; pure (.stlw (← a1) (← a1) (← a1) (← a1))
    | _ =>
      if keywords.contains s then failP s!"'{s}' cannot start an operation"
      let f ← pName
      if (← isSym "{") || (← isSym "(") then
        let (ts, is, a) ← pCallRest env sc; pure (.call f is a ts)
      else if ← isSym "[" then
        let save ← get
        (do let (ts, is, a) ← pCallRest env sc; pure (Op.call f is a ts)) <|>
          (do set save; pAfterAtom (.var f))
      else pAfterAtom (.var f)
  | t => failP s!"expected an operation, found {t.show}"

/-- The index binders an operation adds (see "Index variables inside code"). -/
def afterOp (sc : Sc) (x : String) : Op → Sc
  | .load _ _ => sc.barrier
  | .ldp _ _ n0 n1 => (sc.pushI n0).pushI n1
  | .rem _ _ | .band _ _ => (sc.pushI (x ++ "_d")).pushI x
  | .nameI _ => sc.pushI x
  | _ => sc

partial def pExpr (env : Env) (sc : Sc) : P Expr := do
  match (← cur).tk with
  | .id "let" =>
      bump
      if ← eatSym "(" then
        let x ← pName; expectSym ","; let y ← pName; expectSym ")"; expectSym "="
        let a ← pAt
        pure (.split a x y (← pExpr env (sc.step env.lib (.split a x y Scope.hole) 0 id)))
      else if ← eatSym "<" then
        if ← eatSym "[" then
          -- `let <[α], x> = unpack a`: a type existential; `α` is opaque below.
          let al ← pName; expectSym "]"; expectSym ","; let x ← pName
          expectSym ">"; expectSym "="; expectKw "unpack"
          let a ← pAt
          return .unpackT a al x (← pExpr env ((sc.pushT al).step env.lib (.unpackT a al x Scope.hole) 0 id))
        let ns ← sepBy pName ","
        expectSym ">"; expectSym "="
        if ← eatKw "unpack" then
          match ns with
          | [i, x] => let a ← pAt
                      pure (.unpack a i x (← pExpr env (sc.step env.lib (.unpack a i x Scope.hole) 0 (·.pushI i))))
          | _ => failP "unpack binds <index, value>"
        else if ← eatKw "region" then
          match ns with
          | [r, p, t] => let a ← pAt
                         pure (.region a r p t (← pExpr env (sc.step env.lib (.region a r p t Scope.hole) 0 (·.pushI r))))
          | _ => failP "region binds <region, pointer, token>"
        else if ← eatKw "openPub" then
          match ns with
          | [r, p, c] => let a ← pAt
                         pure (.openPub a r p c (← pExpr env (sc.step env.lib (.openPub a r p c Scope.hole) 0 (·.pushI r))))
          | _ => failP "openPub binds <region, pointer, capability>"
        else failP s!"expected unpack, region or openPub, found {(← cur).tk.show}"
      else
        let x ← pName
        expectSym "="
        let op ← pOp env sc
        let _ ← eatSym ";"
        pure (.let_ x op (← pExpr env (sc.step env.lib (.let_ x op Scope.hole) 0 (afterOp · x op))))
  | .id "case" =>
      bump; let a ← pAt; expectKw "of"; let _ ← eatSym "|"
      expectKw "inl"; let x ← pName; expectSym "=>"
      let e₁ ← pExpr env (sc.step env.lib (.case a x Scope.hole "" Scope.hole) 0 id)
      let _ ← eatSym "|"
      expectKw "inr"; let y ← pName; expectSym "=>"
      let e₂ ← pExpr env (sc.step env.lib (.case a x Scope.hole y Scope.hole) 1 id)
      pure (.case a x e₁ y e₂)
  | .id "parity" =>
      bump; let a ← pAt; expectKw "of"; let _ ← eatSym "|"
      let two : P Unit := do
        match (← cur).tk with
        | .num 2 => bump
        | t => failP s!"expected 2k, found {t.show}"
      two; let k ← pName; expectSym "=>"
      let hd : Expr := .parity a k Scope.hole Scope.hole
      let ev ← pExpr env (sc.step env.lib hd 0 (·.pushI k))
      let _ ← eatSym "|"
      two; let k' ← pName
      if k' != k then failP s!"expected 2{k}+1"
      expectSym "+"
      match (← cur).tk with
      | .num 1 => bump
      | t => failP s!"expected 2{k}+1, found {t.show}"
      expectSym "=>"
      let od ← pExpr env (sc.step env.lib hd 1 (·.pushI k))
      pure (.parity a k ev od)
  | .id "if" =>
      bump; let a ← pAt; expectSym "="; let b ← pAt; expectKw "then"
      let hd : Expr := .ifeq a b Scope.hole Scope.hole
      let yes ← pExpr env (sc.step env.lib hd 0 id)
      expectKw "else"
      pure (.ifeq a b yes (← pExpr env (sc.step env.lib hd 1 Sc.barrier)))
  | .id "ifnull" =>
      bump; let a ← pAt; expectKw "then"
      let e₁ ← pExpr env (sc.step env.lib (.ifnull a Scope.hole "" Scope.hole) 0 id)
      expectKw "else"; let x ← pName; expectSym "=>"
      pure (.ifnull a e₁ x (← pExpr env (sc.step env.lib (.ifnull a Scope.hole x Scope.hole) 1 id)))
  | .id "cas" =>
      bump
      let acq ← eatKw "acq"
      let rel ← eatKw "rel"
      let w ← pAt; let e ← pAt; expectSym "->"; let v ← pAt
      expectKw "as"; let t ← pName; expectKw "then"
      let hd : Expr := .cas acq rel w e v t Scope.hole Scope.hole
      let ok ← pExpr env (sc.step env.lib hd 0 id)
      expectKw "else"
      pure (.cas acq rel w e v t ok (← pExpr env (sc.step env.lib hd 1 id)))
  | .id "casp" =>
      bump
      let acq ← eatKw "acq"
      let rel ← eatKw "rel"
      let w ← pAt
      expectSym "("; let e0 ← pAt; expectSym ","; let e1 ← pAt; expectSym ")"
      expectSym "->"
      expectSym "("; let v0 ← pAt; expectSym ","; let v1 ← pAt; expectSym ")"
      expectKw "as"; let t ← pName; expectKw "then"
      let hd : Expr := .casp acq rel w e0 e1 v0 v1 t Scope.hole Scope.hole
      let ok ← pExpr env (sc.step env.lib hd 0 id)
      expectKw "else"
      pure (.casp acq rel w e0 e1 v0 v1 t ok (← pExpr env (sc.step env.lib hd 1 id)))
  | .id "ret" => bump; pure (.ret (← pAt))
  | .id "tail" =>
      bump; let f ← pName; let (ts, is, a) ← pCallRest env sc
      pure (.tail f is a ts)
  | t => failP s!"expected a term (let, case, parity, if, ifnull, cas, casp, ret, tail), found {t.show}"

/-! ### Code blocks and programs -/

def pDecl (env : Env) : P Decl := do
  expectKw "def"
  let name ← pName
  let tps ← if ← eatSym "[" then do
      let ps ← sepBy (do
        let a ← pName
        let κ ← if ← eatSym ":" then pKind else pure {}
        pure (a, κ)) ","
      expectSym "]"; pure ps
    else pure []
  let idx ← if ← eatSym "{" then do let is ← sepBy pName ","; expectSym "}"; pure is else pure []
  let sc : Sc := { tvs := (tps.map (·.1)).reverse, ivs := idx.reverse.map some }
  expectSym "("; let x ← pName; expectSym ":"; let at_ ← pTy env sc; expectSym ")"
  expectSym ":"; let rt ← pTy env sc
  expectSym "="
  -- The signature, for the body's scope (and its own recursive calls).
  let sig : Decl := { name, tparams := tps.map (·.2), idx, arg := x, argTy := at_, retTy := rt,
                      body := Scope.hole }
  let body ← pExpr { env with lib := sig :: env.lib } { sc with cx := some (Scope.start sig) }
  pure { name, tparams := tps.map (·.2), idx, arg := x, argTy := at_, retTy := rt, body }

/-- Code blocks, with `type N = τ` and `proto N = P` naming things for what follows. -/
partial def pProg (env : Env) (acc : List Decl) : P (List Decl × Env) := do
  match (← cur).tk with
  | .eof => pure (acc.reverse, env)
  | .id "type" =>
      bump; let n ← pName; expectSym "="; let t ← pTy env {}
      pProg (env.addType n t) acc
  | .id "proto" =>
      bump; let n ← pName; expectSym "="
      if ← atProto2 env then
        let P ← pProto2 env
        pProg (env.addProto2 n P) acc
      else
        let P ← pProto env
        pProg (env.addProto n P) acc
  | _ => let d ← pDecl env; pProg { env with lib := d :: env.lib } (d :: acc)

def runP {γ : Type} (p : P γ) (s : String) : Except Err γ := do
  let toks ← lex s
  let q : P γ := do
    let x ← p
    match (← cur).tk with
    | .eof => pure x
    | t => failP s!"unexpected {t.show} after the end"
  (q.run toks |>.run 0).map (·.1)

def parseTy (s : String) (env : Env := {}) (idx : List String := []) : Except Err Ty :=
  runP (pTy env { ivs := idx.reverse.map some }) s
def parseOp (s : String) (env : Env := {}) (idx : List String := []) : Except Err Op :=
  runP (pOp env { ivs := idx.reverse.map some }) s
def parseExpr (s : String) (env : Env := {}) (idx : List String := []) : Except Err Expr :=
  runP (pExpr env { ivs := idx.reverse.map some }) s
def parseDecl (s : String) (env : Env := {}) : Except Err Decl := runP (pDecl env) s
def parseProto (s : String) (env : Env := {}) : Except Err Proto := runP (pProto env) s
def parseProto2 (s : String) (env : Env := {}) : Except Err Proto2 := runP (pProto2 env) s
def parseProg (s : String) (env : Env := {}) : Except Err Prog := (runP (pProg env []) s).map (·.1)
/-- The program and the environment extended by its `type`/`proto` lines. -/
def parseProgEnv (s : String) (env : Env := {}) : Except Err (Prog × Env) := runP (pProg env []) s

/-! ## The printer -/

def nameStr (s : String) : String := if validName s then s else "«" ++ s ++ "»"

def paren (b : Bool) (s : String) : String := if b then "(" ++ s ++ ")" else s

def ivPool : List String := ["a", "b", "c", "d", "e", "f", "g", "h", "m", "n", "p", "q", "u", "w"]
def tvPool : List String := ["α", "β", "γ", "δ", "ε", "ζ", "η", "θ"]

def freshIn (pool used : List String) (pre : String) : String :=
  match pool.find? (!used.contains ·) with
  | some x => x
  | none => (List.range 1000).map (fun i => pre ++ toString i) |>.find? (!used.contains ·) |>.getD pre

def Sc.freshI (sc : Sc) : String := freshIn ivPool (sc.ivs.filterMap id) "a"
def Sc.freshT (sc : Sc) : String := freshIn tvPool sc.tvs "t"

def showIdx (sc : Sc) : Nat → Idx → String
  | _, .lit n => toString n
  | _, .var k => ((sc.ivName k).map nameStr).getD s!"?{k}"
  | p, .add i j => paren (p > 0) (showIdx sc 0 i ++ " + " ++ showIdx sc 1 j)
  | p, .sub i j => paren (p > 0) (showIdx sc 0 i ++ " - " ++ showIdx sc 1 j)
  | p, .smul n i => paren (p > 1) (toString n ++ "*" ++ showIdx sc 2 i)

/-- A mode after `Ptr`/`Ptr?`/`Loc`: ` own`, ` pub`, or `[r]` (no space). -/
def showMode (sc : Sc) : Mode → String
  | .own => " own" | .pub => " pub" | .rgn r => "[" ++ showIdx sc 0 r ++ "]"

def showCap : Cap → String
  | .pub => "pub" | .bor => "bor" | .rd => "rd" | .frz => "frz"

def showPred (sc : Sc) : Pred → String
  | .tt => "true"
  | .le i j => showIdx sc 0 i ++ " <= " ++ showIdx sc 0 j
  | .eq i j => showIdx sc 0 i ++ " = " ++ showIdx sc 0 j
  | .ini i => "ini >= " ++ showIdx sc 0 i
  | .and p q => paren (match p with | .and _ _ => true | _ => false) (showPred sc p) ++ " && " ++ showPred sc q

def showKind (κ : Kind) : String :=
  let fs := [(κ.zero, "zero"), (κ.insens, "insens"), (κ.share, "share"), (κ.noOwn, "noOwn"),
             (κ.copy, "copy"), (κ.noWord, "noWord")].filterMap fun (b, s) => if b then some s else none
  let atm := match κ.atom with | .none => [] | .word => ["atom=word"] | .pair => ["atom=pair"]
  match fs ++ atm with
  | [] => "*"
  | xs => "{" ++ ", ".intercalate xs ++ "}"

def showClause (c : Clause) : String :=
  let b := match c.scale, c.off with
    | 0, o => toString o
    | 1, 0 => "k"
    | 1, o => "k+" ++ toString o
    | s, 0 => toString s ++ "k"
    | s, o => toString s ++ "k+" ++ toString o
  if c.holds then b ++ "!" else b

def showProto (env : Env) (P : Proto) : String :=
  match env.protos.find? (·.2 == P) with
  | some (n, _) => nameStr n
  | none =>
    let tr := P.trans.map (fun (a, b, d) =>
      s!"{a}->{b}" ++ (if d > 0 then s!"+{d}" else if d < 0 then s!"-{-d}" else "")) ++
      P.wild.map fun (a, b) => s!"{a}->{b}*"
    let nl (ns : List Nat) := "(" ++ ", ".intercalate (ns.map toString) ++ ")"
    let fl := (if P.ghost then ["ghost"] else []) ++ (if P.isLocal then ["local"] else []) ++
      (if P.robust then ["robust"] else []) ++ (if P.norepeat then ["norepeat"] else []) ++
      (if P.epoch then ["epoch"] else []) ++ (if P.ticket then ["ticket"] else []) ++
      (if P.lends.isEmpty then [] else ["lends" ++ nl P.lends]) ++
      (if P.lendsDown.isEmpty then [] else ["lendsDown" ++ nl P.lendsDown]) ++
      (if P.recover.isEmpty then [] else
        ["recover(" ++ ", ".intercalate (P.recover.map fun (h, t) => s!"{h}->{t}") ++ ")"])
    "<" ++ ", ".intercalate (P.clauses.map showClause) ++ " ; " ++ ", ".intercalate tr ++
      (if fl.isEmpty then "" else " ; " ++ ", ".intercalate fl) ++ ">"

def showDelta (d : Int) : String := if d < 0 then s!"-{-d}" else s!"+{d}"

def showClause2 (c : Clause2) : String :=
  let off (d : Int) : String := if d == 0 then "" else if d < 0 then s!" - {-d}" else s!" + {d}"
  let rel := match c.rel with
    | .free => ""
    | .eq d => " | k1 = k0" ++ off d
    | .le d => " | k1 <= k0" ++ off d
    | .ge d => " | k1 >= k0" ++ off d
  let b := "(" ++ showClause ⟨c.s0, c.o0, false⟩ ++ ", " ++ showClause ⟨c.s1, c.o1, false⟩ ++ rel ++ ")"
  if c.holds then b ++ "!" else b

def showProto2 (env : Env) (P : Proto2) : String :=
  match env.protos2.find? (·.2 == P) with
  | some (n, _) => nameStr n
  | none =>
    let half : Option Int → String
      | none => "*"
      | some d => if d == 0 then "0" else showDelta d
    let tr := P.trans.map fun (a, b, d0, d1) =>
      s!"{a}->{b}" ++ (if d0 == some 0 && d1 == some 0 then "" else "(" ++ half d0 ++ ", " ++ half d1 ++ ")")
    "<<" ++ ", ".intercalate (P.clauses.map showClause2) ++ " ; " ++ ", ".intercalate tr ++
      (let fl := (if P.robust then ["robust"] else []) ++ (if P.epoch then ["epoch"] else [])
       if fl.isEmpty then "" else " ; " ++ ", ".intercalate fl) ++ ">>"

def showEC (env : Env) : ECounter → String
  | .word P => showProto env P
  | .pair P => showProto2 env P

partial def showTy (env : Env) (sc : Sc) (p : Nat) : Ty → String
  | .unit => "Unit" | .void => "Void" | .int => "Int" | .tid => "ThreadId"
  | .intS i => "Int[" ++ showIdx sc 0 i ++ "]"
  | .fix sg w => fixName sg w
  | .lanes sg w => "Lanes" ++ fixName sg w
  | .prod a b => paren (p > 2) (showTy env sc 3 a ++ " * " ++ showTy env sc 2 b)
  | .sum a b => paren (p > 1) (showTy env sc 2 a ++ " + " ++ showTy env sc 1 b)
  | .code a b => "Code(" ++ showTy env sc 0 a ++ ", " ++ showTy env sc 0 b ++ ")"
  | .array i t => paren (p > 3) ("Array[" ++ showIdx sc 0 i ++ "] " ++ showTy env sc 3 t)
  | .ptr μ t => paren (p > 3) ("Ptr" ++ showMode sc μ ++ " " ++ showTy env sc 3 t)
  | .ptrOpt μ t => paren (p > 3) ("Ptr?" ++ showMode sc μ ++ " " ++ showTy env sc 3 t)
  | .loc μ t => paren (p > 3) ("Loc" ++ showMode sc μ ++ " " ++ showTy env sc 3 t)
  | .share r => "Share[" ++ showIdx sc 0 r ++ "]"
  | .cap c r => "Cap[" ++ showCap c ++ ", " ++ showIdx sc 0 r ++ "]"
  | .word r P => "Word[" ++ showIdx sc 0 r ++ ", " ++ showProto env P ++ "]"
  | .word2 r P => "Pair[" ++ showIdx sc 0 r ++ ", " ++ showProto2 env P ++ "]"
  | .epair r P => "EPair[" ++ showIdx sc 0 r ++ ", " ++ showEC env P ++ "]"
  | .tokE r P e => "Tok[" ++ showIdx sc 0 r ++ ", " ++ showEC env P ++ ", " ++ showIdx sc 0 e ++ "]"
  | .tok2 r P i j =>
      "Tok[" ++ showIdx sc 0 r ++ ", " ++ showProto2 env P ++ ", " ++ showIdx sc 0 i ++ ", " ++
        showIdx sc 0 j ++ "]"
  | .tok r none => "Tok[" ++ showIdx sc 0 r ++ "]"
  | .tok r (some (P, i)) =>
      "Tok[" ++ showIdx sc 0 r ++ ", " ++ showProto env P ++ ", " ++ showIdx sc 0 i ++ "]"
  | .tvar k => ((sc.tvName k).map nameStr).getD s!"?t{k}"
  | .mu t => let a := sc.freshT; paren (p > 0) ("mu " ++ a ++ ". " ++ showTy env (sc.pushT a) 0 t)
  | .iall t => let a := sc.freshI; paren (p > 0) ("forall " ++ a ++ ". " ++ showTy env (sc.pushI a) 0 t)
  | .iex t => let a := sc.freshI; paren (p > 0) ("exists " ++ a ++ ". " ++ showTy env (sc.pushI a) 0 t)
  | .tex κ t =>
      let a := sc.freshT
      paren (p > 0) ("exists (" ++ a ++ " : " ++ showKind κ ++ "). " ++ showTy env (sc.pushT a) 0 t)
  | .refine t ψ => "{" ++ showTy env sc 0 t ++ " | " ++ showPred sc ψ ++ "}"

def showAt : At → String
  | .var x => nameStr x | .lit n => toString n | .unit => "()"

def showCall (env : Env) (sc : Sc) (f : String) (is : List String) (a : At) (ts : List Ty) : String :=
  nameStr f ++
  (if ts.isEmpty then "" else "[" ++ ", ".intercalate (ts.map (showTy env sc 0)) ++ "]") ++
  (if is.isEmpty then "" else "{" ++ ", ".intercalate (is.map nameStr) ++ "}") ++
  "(" ++ showAt a ++ ")"

def nameOf {γ : Type} [BEq γ] (names : List (String × γ)) (x : γ) : String :=
  ((names.find? (·.2 == x)).map (·.1)).getD "?"

def showPath (p : List Nat) : String := String.join (p.map fun k => "." ++ toString k)

def showOp (env : Env) (sc : Sc) : Op → String
  | .atom a => showAt a
  | .pair a b => "(" ++ showAt a ++ ", " ++ showAt b ++ ")"
  | .inl t a => "inl[" ++ showTy env sc 0 t ++ "] " ++ showAt a
  | .inr t a => "inr[" ++ showTy env sc 0 t ++ "] " ++ showAt a
  | .add a b => showAt a ++ " + " ++ showAt b
  | .sub a b => showAt a ++ " - " ++ showAt b
  | .new a => "new " ++ showAt a
  | .null μ t => "null : " ++ showTy env sc 0 (.ptrOpt μ t)
  | .fold a t => "fold " ++ showAt a ++ " : " ++ showTy env sc 0 t
  | .publish a => "publish " ++ showAt a
  | .intoRgn r a => "intoRgn " ++ nameStr r ++ " " ++ showAt a
  | .newBuf n t => "newBuf[" ++ showTy env sc 0 t ++ "] " ++ showAt n
  | .idx b i => showAt b ++ "[" ++ showAt i ++ "]"
  | .bufInit b i v => "bufInit " ++ showAt b ++ " " ++ showAt i ++ " " ++ showAt v
  | .fld i a => "fld " ++ toString i ++ " " ++ showAt a
  | .load acq a => "load " ++ (if acq then "acq " else "") ++ showAt a
  | .store rel a v t => "store " ++ (if rel then "rel " else "") ++ showAt a ++ " " ++ showAt v ++
      (match t with | some t => " with " ++ showAt t | none => "")
  | .fence f => "fence " ++ nameOf fenceNames f
  | .mkWord r P v t => "mkWord " ++ nameStr r ++ " " ++ showProto env P ++ " " ++ showAt v ++ " " ++ showAt t
  | .mkTicket r N P v t => "mkTicket " ++ nameStr r ++ " " ++ showProto env N ++ " " ++ showProto env P ++ " " ++
      showAt v ++ " " ++ showAt t
  | .claim a t => "claim " ++ showAt a ++ " with " ++ showAt t
  | .spawn f a T ts => "spawn " ++ nameStr f ++
      (if ts.isEmpty then "" else "[" ++ ", ".intercalate (ts.map (showTy env sc 0)) ++ "]") ++
      " " ++ showAt a ++ " : " ++ showTy env sc 0 T
  | .ext n a => n.name ++ " " ++ showAt a
  | .fetch o acq rel a v => "fetch " ++ nameOf fetchNames o ++ " " ++ (if acq then "acq " else "") ++
      (if rel then "rel " else "") ++ showAt a ++ " " ++ showAt v
  | .mkWord2 r P v0 v1 t => "mkWord2 " ++ nameStr r ++ " " ++ showProto2 env P ++ " (" ++ showAt v0 ++ ", " ++
      showAt v1 ++ ") " ++ showAt t
  | .ldp acq a n0 n1 => "ldp " ++ (if acq then "acq " else "") ++ showAt a ++ " as (" ++ nameStr n0 ++ ", " ++
      nameStr n1 ++ ")"
  | .stp rel a v0 v1 t => "stp " ++ (if rel then "rel " else "") ++ showAt a ++ " (" ++ showAt v0 ++ ", " ++
      showAt v1 ++ ") with " ++ showAt t
  | .mkEPair r P v0 v1 => "mkEPair " ++ nameStr r ++ " " ++ showEC env P ++ " (" ++ showAt v0 ++ ", " ++
      showAt v1 ++ ")"
  | .pack a w t => "pack " ++ showAt a ++ " at " ++ nameStr w ++ " : " ++ showTy env sc 0 t
  | .packT a σ t => "pack " ++ showAt a ++ " at [" ++ showTy env sc 0 σ ++ "] : " ++ showTy env sc 0 t
  | .validate x => "validate " ++ nameStr x
  | .call f is a ts => showCall env sc f is a ts
  | .borrow c t => "borrow " ++ showCap c ++ " " ++ showAt t
  | .endBorrow t => "endBorrow " ++ showAt t
  | .xchg a v => "xchg " ++ showAt a ++ " " ++ showAt v
  | .fnptr f => "fnptr " ++ nameStr f
  | .callc f a => "callc " ++ showAt f ++ " " ++ showAt a
  | .rem a n => showAt a ++ " mod " ++ showAt n
  | .nameI a => "nameI " ++ showAt a
  | .xchgAt b i v => "xchg " ++ showAt b ++ "[" ++ showAt i ++ "] " ++ showAt v
  | .loadAt b i => "load " ++ showAt b ++ "[" ++ showAt i ++ "]"
  | .bits o a b => "bits " ++ nameOf bitNames o ++ " " ++ showAt a ++ " " ++ showAt b
  | .bit1 o a => "bit1 " ++ nameOf bit1Names o ++ " " ++ showAt a
  | .vmatch lo hi b => "vmatch " ++ showAt lo ++ " " ++ showAt hi ++ " " ++ showAt b
  | .band a m => showAt a ++ " & " ++ showAt m
  | .zero t => "zero[" ++ showTy env sc 0 t ++ "]"
  | .loadAtF b i p => "load " ++ showAt b ++ "[" ++ showAt i ++ "]" ++ showPath p
  | .xchgAtF b i p v => "xchg " ++ showAt b ++ "[" ++ showAt i ++ "]" ++ showPath p ++ " " ++ showAt v
  | .freeze t => "freeze " ++ showAt t
  | .cvt sg w a => "cvt " ++ fixName sg w ++ " " ++ showAt a
  | .toInt a => "toInt " ++ showAt a
  | .asLanes sg w a => "asLanes " ++ fixName sg w ++ " " ++ showAt a
  | .fop o a b => "fop " ++ nameOf fopNames o ++ " " ++ showAt a ++ " " ++ showAt b
  | .fcmp o a b => "fcmp " ++ nameOf fcmpNames o ++ " " ++ showAt a ++ " " ++ showAt b
  | .fop1 o a => "fop1 " ++ nameOf fop1Names o ++ " " ++ showAt a
  | .lane a j => "lane " ++ showAt a ++ " " ++ showAt j
  | .setLane a j v => "setLane " ++ showAt a ++ " " ++ showAt j ++ " " ++ showAt v
  | .ldl b i => "ldl " ++ showAt b ++ " " ++ showAt i
  | .stl b i v => "stl " ++ showAt b ++ " " ++ showAt i ++ " " ++ showAt v
  | .ldlw b i j => "ldlw " ++ showAt b ++ " " ++ showAt i ++ " " ++ showAt j
  | .stlw b i j v => "stlw " ++ showAt b ++ " " ++ showAt i ++ " " ++ showAt j ++ " " ++ showAt v

def showExprLines (env : Env) (sc : Sc) (d : Nat) : Expr → List (Nat × String)
  | .let_ x op e =>
      (d, "let " ++ nameStr x ++ " = " ++ showOp env sc op) ::
        showExprLines env (sc.step env.lib (.let_ x op e) 0 (afterOp · x op)) d e
  | .split a x y e =>
      (d, "let (" ++ nameStr x ++ ", " ++ nameStr y ++ ") = " ++ showAt a) ::
        showExprLines env (sc.step env.lib (.split a x y e) 0 id) d e
  | .unpack a i x e =>
      (d, "let <" ++ nameStr i ++ ", " ++ nameStr x ++ "> = unpack " ++ showAt a) ::
        showExprLines env (sc.step env.lib (.unpack a i x e) 0 (·.pushI i)) d e
  | .unpackT a al x e =>
      (d, "let <[" ++ nameStr al ++ "], " ++ nameStr x ++ "> = unpack " ++ showAt a) ::
        showExprLines env ((sc.pushT al).step env.lib (.unpackT a al x e) 0 id) d e
  | .region a r p t e =>
      (d, "let <" ++ nameStr r ++ ", " ++ nameStr p ++ ", " ++ nameStr t ++ "> = region " ++ showAt a) ::
        showExprLines env (sc.step env.lib (.region a r p t e) 0 (·.pushI r)) d e
  | .openPub a r p c e =>
      (d, "let <" ++ nameStr r ++ ", " ++ nameStr p ++ ", " ++ nameStr c ++ "> = openPub " ++ showAt a) ::
        showExprLines env (sc.step env.lib (.openPub a r p c e) 0 (·.pushI r)) d e
  | .case a x e₁ y e₂ =>
      let hd : Expr := .case a x e₁ y e₂
      [(d, "case " ++ showAt a ++ " of"), (d + 1, "inl " ++ nameStr x ++ " =>")] ++
      showExprLines env (sc.step env.lib hd 0 id) (d + 2) e₁ ++
      [(d + 1, "inr " ++ nameStr y ++ " =>")] ++ showExprLines env (sc.step env.lib hd 1 id) (d + 2) e₂
  | .parity a k ev od =>
      let hd : Expr := .parity a k ev od
      [(d, "parity " ++ showAt a ++ " of"), (d + 1, "2" ++ nameStr k ++ " =>")] ++
      showExprLines env (sc.step env.lib hd 0 (·.pushI k)) (d + 2) ev ++
      [(d + 1, "2" ++ nameStr k ++ "+1 =>")] ++ showExprLines env (sc.step env.lib hd 1 (·.pushI k)) (d + 2) od
  | .ifeq a b yes no =>
      let hd : Expr := .ifeq a b yes no
      [(d, "if " ++ showAt a ++ " = " ++ showAt b ++ " then")] ++
      showExprLines env (sc.step env.lib hd 0 id) (d + 1) yes ++
      [(d, "else")] ++ showExprLines env (sc.step env.lib hd 1 Sc.barrier) (d + 1) no
  | .ifnull a e₁ x e₂ =>
      let hd : Expr := .ifnull a e₁ x e₂
      [(d, "ifnull " ++ showAt a ++ " then")] ++ showExprLines env (sc.step env.lib hd 0 id) (d + 1) e₁ ++
      [(d, "else " ++ nameStr x ++ " =>")] ++ showExprLines env (sc.step env.lib hd 1 id) (d + 1) e₂
  | .cas acq rel w e v t ok fail =>
      let hd : Expr := .cas acq rel w e v t ok fail
      [(d, "cas " ++ (if acq then "acq " else "") ++ (if rel then "rel " else "") ++ showAt w ++ " " ++
           showAt e ++ " -> " ++ showAt v ++ " as " ++ nameStr t ++ " then")] ++
      showExprLines env (sc.step env.lib hd 0 id) (d + 1) ok ++ [(d, "else")] ++
      showExprLines env (sc.step env.lib hd 1 id) (d + 1) fail
  | .casp acq rel w e0 e1 v0 v1 t ok fail =>
      let hd : Expr := .casp acq rel w e0 e1 v0 v1 t ok fail
      [(d, "casp " ++ (if acq then "acq " else "") ++ (if rel then "rel " else "") ++ showAt w ++ " (" ++
           showAt e0 ++ ", " ++ showAt e1 ++ ") -> (" ++ showAt v0 ++ ", " ++ showAt v1 ++ ") as " ++
           nameStr t ++ " then")] ++
      showExprLines env (sc.step env.lib hd 0 id) (d + 1) ok ++ [(d, "else")] ++
      showExprLines env (sc.step env.lib hd 1 id) (d + 1) fail
  | .ret a => [(d, "ret " ++ showAt a)]
  | .tail f is a ts => [(d, "tail " ++ showCall env sc f is a ts)]

def render (ls : List (Nat × String)) : String :=
  "\n".intercalate (ls.map fun (i, s) => String.join (List.replicate i "  ") ++ s)

def declSc (d : Decl) : Sc × List String :=
  let rec names : List Kind → List String → List String
    | [], acc => acc.reverse
    | _ :: ks, acc => names ks (freshIn tvPool acc "t" :: acc)
  let tns := names d.tparams []
  ({ tvs := tns.reverse, ivs := d.idx.reverse.map some, cx := some (Scope.start d) }, tns)

def showDecl (d : Decl) (env : Env := {}) : String :=
  let (sc, tns) := declSc d
  let tps := (tns.zip d.tparams).map fun (a, κ) => if κ == {} then a else a ++ " : " ++ showKind κ
  let head := "def " ++ nameStr d.name ++
    (if tps.isEmpty then "" else "[" ++ ", ".intercalate tps ++ "]") ++
    (if d.idx.isEmpty then "" else "{" ++ ", ".intercalate (d.idx.map nameStr) ++ "}") ++
    "(" ++ nameStr d.arg ++ " : " ++ showTy env sc 0 d.argTy ++ ") : " ++ showTy env sc 0 d.retTy ++ " ="
  render ((0, head) :: showExprLines { env with lib := d :: env.lib } sc 1 d.body)

/-- Each block printed knowing the blocks before it, as `parseProg` reads them. -/
def showProg (p : Prog) (env : Env := {}) : String :=
  let rec go : Prog → Env → List String
    | [], _ => []
    | d :: ds, env => showDecl d env :: go ds { env with lib := d :: env.lib }
  "\n\n".intercalate (go p env)
def showType (t : Ty) (env : Env := {}) (idx : List String := []) : String :=
  showTy env { ivs := idx.reverse.map some } 0 t
def showExpr (e : Expr) (env : Env := {}) (idx : List String := []) : String :=
  render (showExprLines env { ivs := idx.reverse.map some } 0 e)

/-! ## Equality, for the round-trip tests -/

def sameExpr (a b : Expr) : Bool := toString (repr a) == toString (repr b)
def sameOp (a b : Op) : Bool := toString (repr a) == toString (repr b)
def sameDecl (a b : Decl) : Bool :=
  a.name == b.name && a.tparams == b.tparams && a.idx == b.idx && a.arg == b.arg &&
  a.argTy == b.argTy && a.retTy == b.retTy && sameExpr a.body b.body

/-- `parse (show d) = d`. -/
def roundTrips (d : Decl) (env : Env := {}) : Bool :=
  match parseDecl (showDecl d env) env with
  | .ok d' => sameDecl d d'
  | .error _ => false

/-- For a failing round trip: what went wrong. -/
def roundTripReport (d : Decl) (env : Env := {}) : String :=
  let s := showDecl d env
  match parseDecl s env with
  | .ok d' => if sameDecl d d' then "ok" else s!"{d.name}: reparsed to a different AST\n{s}"
  | .error e => s!"{d.name}: {e}\n{s}"

/-! ## Pinned behaviour -/

#guard parseTy "Int * Int" matches .ok (.prod .int .int)
#guard (parseTy "Int * Int + Unit").toOption == some (.sum (.prod .int .int) .unit)
#guard (parseTy "exists a. Ptr pub (Word[a, Mutex] * Ptr[a] Int)").toOption == some (mutex .int)
#guard (parseTy "SeqLock(Int * Int)").toOption == some (seqLock pay)
#guard (parseTy "∃a. Ptr pub (Word[a, Seq] × Ptr[a] (Int × Int))").toOption == some (seqLock pay)
#guard (parseTy "Word[0, <2k!, 2k+1 ; 0->1, 1->0+1>]").toOption == some (.word (.lit 0) seqP)
#guard (parseTy "mu t. Int * Ptr? pub t").toOption == some (.mu (.prod .int (.ptrOpt .pub (.tvar 0))))
#guard (parseTy "{Int | 2*3 + 1 <= 7 && true}").toOption ==
  some (.refine .int (.and (.le (.add (.smul 2 (.lit 3)) (.lit 1)) (.lit 7)) .tt))
#guard (parseTy "U8 * LanesI16").toOption == some (.prod (.fix false .w8) (.lanes true .w16))
#guard showType (seqLock pay) == "exists a. Ptr pub (Word[a, Seq] * Ptr[a] (Int * Int))"
-- Errors carry a position.
#guard match parseTy "Int * " with | .error e => e.line == 1 && e.col == 7 | _ => false
#guard match parseTy "Ptr[r] Int" with | .error e => (e.msg.splitOn "unknown index variable").length > 1 | _ => false
-- Index names across a load.  Where the checker's context is known, the load
-- binds exactly what the checker binds: nothing for a plain cell ...
#guard match parseDecl "def f{r}(x : Ptr pub Int) : Unit = let y = load x let z = null : Ptr? [r] Int ret ()" with
  | .ok d => (match d.body with | .let_ _ _ (.let_ _ (.null (.rgn (.var 0)) .int) _) => true | _ => false)
  | _ => false
-- ... and the observed value, named by the variable, for a protocol word:
-- here `r` is index 1 and `c1` index 0, and the checker agrees.
def obsSrc : String := "
def f{r}(m : Ptr pub (Word[r, Seq] * Ptr[r] (Int * Int))) : Unit =
  let w = fld 0 m
  let c1 = load acq w
  let z = null : Ptr? [r] Int[c1]
  ret ()"
#guard match parseDecl obsSrc with
  | .ok d => (match d.body with
               | .let_ _ _ (.let_ _ _ (.let_ _ (.null (.rgn (.var 1)) (.intS (.var 0))) _)) => true
               | _ => false) &&
             accepts (checkDecl [d] d) && roundTrips d
  | _ => false
-- Where it is not known (here `q` is unbound, so the checker would fail),
-- an index name behind a load cannot be used in a type.
#guard match parseDecl "def f{r}(x : Int) : Unit = let y = load q let z = null : Ptr? [r] Int ret ()" with
  | .error e => (e.msg.splitOn "bound before a load").length > 1 | _ => false
#guard match parseDecl "def f{r}(x : Ptr[r] Int) : Unit = let z = null : Ptr? [r] Int ret ()" with
  | .ok _ => true | _ => false

-- The reader, written out, is the library's reader.
def readSrc : String := "
def read{r}(m : Ptr pub (Word[r, Seq] * Ptr[r] (Int * Int))) : Int * Int =
  let w = fld 0 m
  let c1 = load acq w
  parity c1 of
    2k =>
      let d0 = fld 1 m
      let d = load d0
      let x = load d
      let f2 = fence ld
      let c2 = load w
      if c2 = c1 then
        let y = validate x
        ret y
      else
        tail read{r}(m)
    2k+1 =>
      tail read{r}(m)"
#guard match parseDecl readSrc with | .ok d => sameDecl d readD | .error _ => false

-- Round trips over the libraries in CoreTerm.
#guard mutexLib.all (roundTrips ·)
#guard seqLib.all (roundTrips ·)
#guard (queueLib .int).all (roundTrips ·)
#guard (claimLib .int).all (roundTrips ·)
#guard polyQueueLib.all (roundTrips ·)
#guard pcLib.all (roundTrips ·)

/-! ### `fetch` (item 18): accepted and refused forms, from source -/

/-- Parse and check a program; `none` if accepted, else the first message. -/
def fetchChk (s : String) : Option String :=
  match parseProg s with
  | .error e => some s!"parse: {e.msg}"
  | .ok p => match checkProg p with
    | .ok _ => none
    | .error e => some e

#guard fetchChk "def f(x : Ptr pub Int) : Int = let o = fetch add x 3 ret o" == none
#guard fetchChk "def f(x : Ptr pub Int) : Int = let o = fetch or acq rel x 3 ret o" == none
#guard fetchChk "def f(x : Ptr pub Int) : Int = let o = fetch and x () ret o" ==
  some "fetch: the operand is not an Int"
#guard fetchChk "def f(x : Ptr pub (Int * Int)) : Int = let o = fetch add x 3 ret o" ==
  some "fetch needs an Int cell or a protocol word"
-- The dispenser: `fetch add acq w 1` on an epoch counter yields the ticket.
#guard fetchChk "proto Nx = <k! ; 0->0+1 ; robust, epoch>
def g{r}(w : Ptr pub Word[r, Nx]) : exists n. Int[n] * Tok[r, Nx, n+1] = let p = fetch add acq w 1 ret p" == none
#guard fetchChk "proto Nx = <k! ; 0->0+1 ; robust, epoch>
def g{r}(w : Ptr pub Word[r, Nx]) : exists n. Int[n] * Tok[r, Nx, n+1] = let p = fetch add w 1 ret p" ==
  some "entering an epoch needs acq"
#guard fetchChk "proto Nx = <k! ; 0->0+1 ; robust, epoch>
def g{r}(w : Ptr pub Word[r, Nx]) : exists n. Int[n] * Tok[r, Nx, n+1] = let p = fetch add acq w 2 ret p" ==
  some "an epoch counter advances by 1"
#guard fetchChk "proto Nx = <k! ; 0->0+1 ; robust, epoch>
def g{r}(w : Ptr pub Word[r, Nx]) : Int = let p = fetch or acq w 1 ret p" ==
  some "a fetch on a protocol word must be add: a protocol's moves are increments"
-- A shared counter: the step must be one every clause admits.
#guard fetchChk "proto Ev = <2k! ; 0->0+1 ; robust>
def h{r}(w : Ptr pub Word[r, Ev]) : Int = let o = fetch add w 2 ret o" == none
#guard (fetchChk "proto Ev = <2k! ; 0->0+1 ; robust>
def h{r}(w : Ptr pub Word[r, Ev]) : Int = let o = fetch add w 1 ret o").isSome
-- A held counter (a ticket lock's owner) admits no fetch: its moves hand a token.
#guard (fetchChk "proto Ow = <k ; 0->0+1 ; ticket>
def h{r}(w : Ptr pub Word[r, Ow]) : Int = let o = fetch add w 1 ret o").isSome

-- `fetchOK` needs every move it uses to step the parameter up: `0 -> 1` at
-- `dk = -3` would take the even state `0` to `1`, in neither family.
#guard !fetchOK { clauses := [⟨2, 0, true⟩, ⟨2, 7, true⟩], trans := [(0, 1, -3), (1, 0, 4)], robust := true } 1

/-! ### `recover` (U6): declared recovery targets, parsed, shown, refused -/

#guard match parseProto "<0!, 2k+2!, 2k+3 ; 2->1, 1->2, 0->2*, 2->0* ; local, recover(2->0)>" with
  | .ok P => P == { identP with isLocal := true, recover := [(2, 0)] } | .error _ => false
#guard showProto {} { identP with recover := [(2, 0)] } ==
  "<0!, 2k+2!, 2k+3 ; 2->1, 1->2, 0->2*, 2->0* ; recover(2->0)>"
#guard match parseProto (showProto {} { identP with recover := [(2, 0)] }) with
  | .ok P => P == { identP with recover := [(2, 0)] } | .error _ => false
-- A bad target parses (like a false `robust` claim) and is refused at `mkWord` by `pwf`.
#guard match parseProto "<0!, 1 ; 0->1, 1->0 ; recover(0->1)>" with
  | .ok P => P.recover == [(0, 1)] && !pwf P | .error _ => false
#guard (fetchChk "def f{r}(t : Tok[r]) : Unit = let w = mkWord r <0!, 1 ; 0->1, 1->0 ; recover(1->1)> 0 t ret ()").any
  (·.endsWith "or a recovery target is not held -> shared)")

end Syntax
