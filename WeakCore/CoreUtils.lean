import WeakCore.Scope

/-!
# LaTeX listings of CoreLang programs

A *formatter*, not a delaborator: it turns the term layer's syntax
(`CoreTerm.Decl`, `Expr`, `Op`) and the type layer's (`CoreLang.Ty`, `Idx`,
`Pred`, `Proto`, `Kind`) into LaTeX source for papers and notes.  Lean's goal
view is untouched — `Repr` still shows constructors there.

**Output.**  Math-mode LaTeX.  Every piece of notation goes through one of six
macros, so a document restyles everything by redefining them (`latexMacros`
gives defaults):

| macro     | used for                         | default        |
|-----------|----------------------------------|----------------|
| `\kw`     | term keywords: let, case, cas …  | `\mathbf`      |
| `\op`     | operations: load, store, new …   | `\mathtt`      |
| `\ty`     | type formers: Int, Ptr, Word …   | `\mathsf`      |
| `\md`     | modes and kind fields            | `\mathit`      |
| `\fn`     | code-block names                 | `\mathsf`      |
| `\var`    | multi-letter identifiers         | `\mathit`      |

A code block becomes an `array` (one ANF binding per line, nesting by `\quad`).
`listing` gives a sequence of display-math blocks; `document` a standalone
file; `writeListing` writes one.

**Names.**  Types are de Bruijn; the formatter names binders as it goes — type
variables `α β γ …`, index variables `a b c …` — avoiding every name in scope.
A code block's index parameters keep their own names, and so do index
variables bound in terms by `unpack`, `region` and `parity`.

**One honest gap.**  A load of a *protocol word* also binds an index variable
(named after the load's binder), but whether a load is of a word depends on
types, which a formatter does not compute.  So after the first `load` in a
block, a type written *inside the term* (a `null`, `fold` or `pack` target) that
mentions an index variable from outside itself prints it as `ι_j` (de Bruijn
`j`) rather than guessing a name.  Signatures, and closed types anywhere, are
unaffected; so is every example in `CoreTerm.lean`. -/

namespace CoreUtils

open CoreLang CoreTerm

/-! ## Strings -/

def br (s : String) : String := "{" ++ s ++ "}"
def mac (m a : String) : String := "\\" ++ m ++ br a
def kw  : String → String := mac "kw"
def opn : String → String := mac "op"
def ty  : String → String := mac "ty"
def md  : String → String := mac "md"
def fn  : String → String := mac "fn"
def paren (b : Bool) (s : String) : String := if b then "(" ++ s ++ ")" else s
def sp : String := "\\;"
def commas (xs : List String) : String := ", ".intercalate xs

def esc (s : String) : String := s.replace "_" "\\_"

/-- An identifier in math mode: `x` stays `x`; `t0` becomes `t_{0}`; a longer
name is set upright-italic as a word (`\var{nx}`), keeping digit suffixes as
subscripts (`\var{dp}`, `\var{wv}`, `c_{1}`). -/
def ident (x : String) : String :=
  let cs := x.toList
  let letters := cs.takeWhile Char.isAlpha
  let rest := cs.dropWhile Char.isAlpha
  let base := String.ofList letters
  let baseF := if letters.length ≤ 1 then base else mac "var" base
  if letters.isEmpty then mac "var" (esc x)
  else if rest.isEmpty then baseF
  else if rest.all Char.isDigit then baseF ++ "_" ++ br (String.ofList rest)
  else mac "var" (esc x)

/-! ## Names in scope -/

/-- The protocols with names in the note; any other prints structurally
(unless a document names it: `Names.protos`). -/
def protoNames : List (Proto × String) :=
  [(mutexP, "Mutex"), (seqP, "Seq"), (claimP, "Claim")]


structure Names where
  tv    : List String := []   -- type variables, innermost first
  iv    : List String := []   -- index variables, innermost first
  /-- Index binders crossed inside the type being printed. -/
  inner : Nat := 0
  /-- `false` once a `load` may have bound an index variable we did not see. -/
  exact : Bool := true
  /-- Named types, printed by name wherever they occur (see `Abbrevs`). -/
  abbrevs : List (Ty × String) := []
  /-- Type variables in scope at the code block's own level. -/
  tbase : Nat := 0
  /-- Protocols printed by name. -/
  protos : List (Proto × String) := protoNames
  protos2 : List (Proto2 × String) := []
  /-- The checker's context at this point of a code block, while `Scope`
  follows it; then `iv` is exactly its index names. -/
  cx : Option Cx := none
  /-- Code blocks whose signatures calls may use (for `Scope`). -/
  lib : Prog := []
  /-- Hover tooltips (`\cltip`), when a document asks for them (`Doc.Style`):
  the text for term variable `x` in the checker's context `cx`, with the
  term-level type variables named `tvt`; `none` if `x` is not in `cx`. -/
  tipVar : Option (Cx → List String → String → Option String) := none
  /-- The text for a type written in code (its kind). -/
  tipTy : Option (Ty → Option String) := none
  /-- The term-level type variables as plain text, innermost first (for `tipVar`). -/
  tvt : List String := []

def tvPool : List String :=
  ["\\alpha", "\\beta", "\\gamma", "\\delta", "\\epsilon", "\\zeta", "\\eta", "\\theta"]
def ivPool : List String :=
  ["a", "b", "c", "d", "e", "f", "g", "h", "m", "n", "p", "q", "u", "w"]

def fresh (pool used : List String) (pre : String) : String :=
  match pool.find? (fun x => !used.contains x) with
  | some x => x
  | none   => pre ++ "_" ++ br (toString used.length)

namespace Names

def bindT (n : Names) : String × Names :=
  let a := fresh tvPool n.tv "\\alpha"
  (a, { n with tv := a :: n.tv })

def bindI (n : Names) : String × Names :=
  let a := fresh ivPool n.iv "a"
  (a, { n with iv := a :: n.iv, inner := n.inner + 1 })

def tvName (n : Names) (k : Nat) : String :=
  n.tv[k]?.getD ("\\alpha_" ++ br (toString k))

def ivName (n : Names) (k : Nat) : String :=
  let fallback := "\\iota_" ++ br (toString (k - n.inner))
  if k < n.inner || n.exact then n.iv[k]?.getD fallback else fallback

/-- A term-level index binder with a name of its own. -/
def pushI (n : Names) (x : String) : Names := { n with iv := ident x :: n.iv }

/-- A term-level type binder (`unpackT`) with a name of its own. -/
def pushT (n : Names) (x : String) : Names := { n with tv := ident x :: n.tv, tvt := x :: n.tvt }

/-- The names for subterm `i` of `e` (whose head only is looked at): the
checker's, if `Scope` knows them; otherwise the syntactic rule `syn`. -/
def step (n : Names) (e : Expr) (i : Nat) (syn : Names → Names) : Names :=
  match Scope.nth n.lib n.cx e i with
  | some c => { n with iv := c.inames.map ident, exact := true, cx := some c }
  | none => { syn n with cx := none }

end Names

/-! ## The type layer -/

/-- Precedence: 0 sums and differences, 1 scaling, 2 atoms. -/
def fmtIdx (n : Names) : Nat → Idx → String
  | _, .lit k    => toString k
  | _, .var k    => n.ivName k
  | p, .add i j  => paren (p > 0) (fmtIdx n 0 i ++ " + " ++ fmtIdx n 1 j)
  | p, .sub i j  => paren (p > 0) (fmtIdx n 0 i ++ " \\mathbin{\\dot{-}} " ++ fmtIdx n 1 j)
  | p, .smul k i => paren (p > 1) (match i with
      | .lit m => toString k ++ " \\cdot " ++ toString m
      | _      => toString k ++ fmtIdx n 2 i)

def fmtMode (n : Names) : Mode → String
  | .own   => md "own"
  | .pub   => md "pub"
  | .rgn r => fmtIdx n 0 r

def fmtPred (n : Names) : Pred → String
  | .tt      => "\\top"
  | .le i j  => fmtIdx n 0 i ++ " \\le " ++ fmtIdx n 0 j
  | .eq i j  => fmtIdx n 0 i ++ " = " ++ fmtIdx n 0 j
  | .and p q => fmtPred n p ++ " \\wedge " ++ fmtPred n q
  | .ini i   => "\\mathrm{ini}\\,\\nu \\ge " ++ fmtIdx n 0 i

/-- `⋆` is the top kind (asserts nothing). -/
def fmtKind (κ : Kind) : String :=
  let fs := [(κ.zero, "zero"), (κ.insens, "insens"), (κ.share, "share"),
             (κ.noOwn, "noOwn"), (κ.copy, "copy"), (κ.noWord, "noWord")].filterMap fun (b, s) =>
               if b then some (md s) else none
  let atm := match κ.atom with
    | .none => []
    | .word => [md "atom" ++ "{=}" ++ md "word"]
    | .pair => [md "atom" ++ "{=}" ++ md "pair"]
  match fs ++ atm with
  | [] => "\\star"
  | xs => "\\{" ++ commas xs ++ "\\}"

/-- `scale·k + off`, written the way one would by hand. -/
def fmtClause (c : Clause) : String :=
  let body := match c.scale, c.off with
    | 0, o => toString o
    | 1, 0 => "k"
    | 1, o => "k{+}" ++ toString o
    | s, 0 => toString s ++ "k"
    | s, o => toString s ++ "k{+}" ++ toString o
  if c.holds then body ++ "^{\\bullet}" else body

/-- `⟨s₀ = 2k•, s₁ = 2k+1 | s₀→s₁, s₁→s₀⁺¹⟩`: states (• marks those that
hold the region), then transitions, `⁺ᵈ` when the parameter advances, `*` on a
wild move. -/
def fmtProto (P : Proto) (names : List (Proto × String) := protoNames) : String :=
  match names.find? (·.1 == P) with
  | some (_, s) => "\\mathrm" ++ br s
  | none =>
    let st (i : Nat) := "s_" ++ br (toString i)
    let cs := (enumFrom P.clauses 0).map fun (i, c) => st i ++ "{=}" ++ fmtClause c
    let ts := P.trans.map (fun (a, b, dk) =>
      st a ++ "{\\to}" ++ st b ++ (if dk == 0 then "" else "^{+" ++ toString dk ++ "}")) ++
      P.wild.map fun (a, b) => st a ++ "{\\to}" ++ st b ++ "^{*}"
    let fl := (if P.isLocal then ["local"] else []) ++ (if P.robust then ["robust"] else []) ++
      (if P.norepeat then ["norepeat"] else []) ++ (if P.epoch then ["epoch"] else []) ++
      (if P.ticket then ["ticket"] else []) ++
      (if P.recover.isEmpty then [] else
        ["recover\\," ++ ",".intercalate (P.recover.map fun (h, t) => st h ++ "{\\to}" ++ st t)])
    "\\langle " ++ commas cs ++ " \\mid " ++ commas ts ++ " \\rangle" ++
      (if fl.isEmpty then "" else "_{\\mathrm{" ++ ",".intercalate fl ++ "}}")

/-- `(2k, k{+}1 \mid k_1 = k_0 + 1)`: a pair family. -/
def fmtClause2 (c : Clause2) : String :=
  let delta (d : Int) : String := if d == 0 then "" else if d > 0 then "{+}" ++ toString d else "{-}" ++ toString (-d)
  let rel := match c.rel with
    | .free => ""
    | .eq d => " \\mid k_1 = k_0" ++ delta d
    | .le d => " \\mid k_1 \\le k_0" ++ delta d
    | .ge d => " \\mid k_1 \\ge k_0" ++ delta d
  let body := "(" ++ fmtClause ⟨c.s0, c.o0, false⟩ ++ ", " ++ fmtClause ⟨c.s1, c.o1, false⟩ ++ rel ++ ")"
  if c.holds then body ++ "^{\\bullet}" else body

/-- `⟨s₀ = (k, k | k₁ = k₀)•, s₁ = … | s₀→s₁^{(+1, 0)}⟩`: a pair protocol, with
a delta per half on each move (`*` for a half it forgets). -/
def fmtProto2 (P : Proto2) (names : List (Proto2 × String) := []) : String :=
  match names.find? (·.1 == P) with
  | some (_, s) => "\\mathrm" ++ br s
  | none =>
    let st (i : Nat) := "s_" ++ br (toString i)
    let half : Option Int → String
      | none => "*"
      | some d => if d > 0 then "+" ++ toString d else toString d
    let cs := (enumFrom P.clauses 0).map fun (i, c) => st i ++ "{=}" ++ fmtClause2 c
    let ts := P.trans.map fun (a, b, d0, d1) =>
      st a ++ "{\\to}" ++ st b ++
        (if d0 == some 0 && d1 == some 0 then "" else "^{(" ++ half d0 ++ "," ++ half d1 ++ ")}")
    let fl := (if P.robust then ["robust"] else []) ++ (if P.epoch then ["epoch"] else [])
    "\\langle " ++ commas cs ++ " \\mid " ++ commas ts ++ " \\rangle" ++
      (if fl.isEmpty then "" else "_{\\mathrm{" ++ ",".intercalate fl ++ "}}")

/-- An epoch counter of either shape. -/
def fmtEC (n : Names) : ECounter → String
  | .word P => fmtProto P n.protos
  | .pair P => fmtProto2 P n.protos2

/-- **Abbreviations.**  A type printed by name — `Queue(Int)` for the whole
μ-type.  Matching is syntactic on de Bruijn terms, so it is only sound where
the variables mean what they meant when the abbreviation was written: a type
with no free variables matches anywhere; one that mentions the code block's
type parameters matches only at the block's own level, under no further type
binder.  An abbreviation may not mention index variables. -/
abbrev Abbrevs := List (Ty × String)

def Names.abbrev? (n : Names) (t : Ty) : Option String :=
  (n.abbrevs.find? fun (a, _) =>
    a == t && (a.wf 0 0 || (a.wf n.tbase 0 && n.tv.length == n.tbase))).map (·.2)

def capName : Cap → String
  | .pub => "pub"
  | .bor => "bor"
  | .rd  => "rd"
  | .frz => "frz"

/-- Precedence: 0 binders (extend right), 1 `+`, 2 `×`, 3 application, 4 atoms.
`+` and `×` associate to the right.  The one-argument formers (`Ptr`, `Ptr?`,
`Loc`, `Array`) are prefix and chain without parentheses: `Ptr_a Ptr_own Int`. -/
def fmtTy (n : Names) (p : Nat) (t : Ty) : String :=
  match n.abbrev? t with
  | some s => s
  | none =>
  match p, t with
  | _, .unit       => ty "Unit"
  | _, .void       => ty "Void"
  | _, .int        => ty "Int"
  | _, .tid        => ty "ThreadId"
  | _, .opq (.reg w a) => ty "Reg" ++ "[" ++ toString w.bits ++ ", " ++ a.name ++ "]"
  | _, .opq (.blk m w a st tk) => ty "Blk" ++ "[" ++ toString m ++ ", " ++ toString w.bits ++ ", " ++ a.name ++ ", stride " ++ toString st ++ (if tk.isEmpty then "" else "; " ++ " ".intercalate (tk.map toString)) ++ "]"
  | _, .opq .bus   => ty "Bus"
  | _, .opq .irq   => ty "Irq"
  | _, .fix sg w   => ty ((if sg then "I" else "U") ++ w.name)
  | _, .lanes sg w => ty ("Lanes" ++ (if sg then "I" else "U") ++ w.name)
  | _, .intS i     => ty "Int" ++ "(" ++ fmtIdx n 0 i ++ ")"
  | p, .prod a b   => paren (p > 2) (fmtTy n 3 a ++ " \\times " ++ fmtTy n 2 b)
  | p, .sum a b    => paren (p > 1) (fmtTy n 2 a ++ " + " ++ fmtTy n 1 b)
  | p, .code a b k => paren (p > 3) (ty "Code" ++ "\\," ++ fmtTy n 4 a ++ "\\," ++ fmtTy n 4 b ++ (match k with | .plain => "" | .restricted f s ro => "\\,\\md{restricted}_{" ++ toString f ++ "," ++ toString s ++ (if ro then ",\\md{ro}" else "") ++ "}"))
  | p, .array i t  => paren (p > 3) (ty "Array" ++ "_" ++ br (fmtIdx n 0 i) ++ "\\," ++ fmtTy n 3 t)
  | p, .ptr μ t    => paren (p > 3) (ty "Ptr" ++ "_" ++ br (fmtMode n μ) ++ "\\," ++ fmtTy n 3 t)
  | p, .ptrOpt μ t => paren (p > 3) (ty "Ptr?" ++ "_" ++ br (fmtMode n μ) ++ "\\," ++ fmtTy n 3 t)
  | p, .loc μ t    => paren (p > 3) (ty "Loc" ++ "_" ++ br (fmtMode n μ) ++ "\\," ++ fmtTy n 3 t)
  | _, .word r P   => ty "Word" ++ "[" ++ fmtIdx n 0 r ++ ", " ++ fmtProto P n.protos ++ "]"
  | _, .word2 r P  => ty "Pair" ++ "[" ++ fmtIdx n 0 r ++ ", " ++ fmtProto2 P n.protos2 ++ "]"
  | _, .epair r P  => ty "EPair" ++ "[" ++ fmtIdx n 0 r ++ ", " ++ fmtEC n P ++ "]"
  | _, .tokE r P e => ty "Tok" ++ "_" ++ br (fmtIdx n 0 r) ++ "(" ++ fmtEC n P ++ ", " ++
                        fmtIdx n 0 e ++ ")"
  | _, .tok2 r P i j => ty "Tok" ++ "_" ++ br (fmtIdx n 0 r) ++ "(" ++ fmtProto2 P n.protos2 ++ ", " ++
                        fmtIdx n 0 i ++ ", " ++ fmtIdx n 0 j ++ ")"
  | _, .share r    => ty "Share" ++ "_" ++ br (fmtIdx n 0 r)
  | _, .cap c r    => ty "Cap" ++ "_" ++ br (capName c ++ "," ++ fmtIdx n 0 r)
  | _, .tok r st   => ty "Tok" ++ "_" ++ br (fmtIdx n 0 r) ++
                        (match st with
                         | some (P, i) => "(" ++ fmtProto P n.protos ++ ", " ++ fmtIdx n 0 i ++ ")"
                         | none        => "")
  | _, .tvar k     => n.tvName k
  | p, .mu t       =>
      let (a, n') := n.bindT
      paren (p > 0) ("\\mu " ++ a ++ ".\\," ++ fmtTy n' 0 t)
  | p, .iall t     =>
      let (a, n') := n.bindI
      paren (p > 0) ("\\forall " ++ a ++ ".\\," ++ fmtTy n' 0 t)
  | p, .iex t      =>
      let (a, n') := n.bindI
      paren (p > 0) ("\\exists " ++ a ++ ".\\," ++ fmtTy n' 0 t)
  | p, .tex κ t    =>
      let (a, n') := n.bindT
      paren (p > 0) ("\\exists (" ++ a ++ "{:}" ++ fmtKind κ ++ ").\\," ++ fmtTy n' 0 t)
  | _, .refine t ψ => "\\{" ++ fmtTy n 0 t ++ " \\mid " ++ fmtPred n ψ ++ "\\}"

/-- A type with no free variables, or with free type variables named `tvs`
(innermost first) and free index variables named `idx` (outermost first). -/
def fmtType (τ : Ty) (tvs : List String := []) (abbrevs : Abbrevs := []) (idx : List String := [])
    (protos : List (Proto × String) := protoNames) : String :=
  fmtTy { tv := tvs, iv := idx.reverse.map ident, abbrevs := abbrevs, tbase := tvs.length,
          protos := protos } 0 τ

/-- `name(σ)` for each `σ`: `family "Queue" queue [.int, α]`.  `tvs` names the
block's type parameters, innermost first, as `fmtDecl` will. -/
def family (name : String) (f : Ty → Ty) (σs : List Ty) (tvs : List String := ["\\alpha"]) :
    Abbrevs :=
  σs.map fun σ => (f σ, "\\ty" ++ br name ++ "(" ++ fmtTy { tv := tvs } 0 σ ++ ")")


/-! ## The term layer -/

def fmtAt : At → String
  | .var x => ident x
  | .lit k => toString k
  | .unit  => "()"

/-! ### Hover tooltips

A token with a tooltip is `\cltip{tex}{text}`: the document tool makes it a
link whose target ends in `#text`, which Chrome's PDF viewer shows in its status
bar.  The text is
percent-encoded (written `\%XX`, so LaTeX passes it through), except for a few
characters that read better raw and are safe in a URL, in a macro argument and
in `alltt` (so not the space, nor `` ` < > , ' - ``, which `alltt` makes active).
A variable with a known context but no type there prints as `\clnotip{tex}`,
which `Doc` reports as a failure: every occurrence must have its tooltip. -/

def tipEnc (s : String) : String :=
  let hx := "0123456789ABCDEF".toList
  let hex (k : Nat) : String := String.ofList [hx.getD (k / 16) '0', hx.getD (k % 16) '0']
  String.join (s.toUTF8.toList.map fun b =>
    let c := Char.ofNat b.toNat
    if b.toNat < 128 && (c.isAlphanum || ":()[].*+=|!?/;@".toList.contains c) then c.toString
    else "\\%" ++ hex b.toNat)

#guard tipEnc "x : Int[n+1] {α}" == "x\\%20:\\%20Int[n+1]\\%20\\%7B\\%CE\\%B1\\%7D"

def cltip (text tex : String) : String := "\\cltip{" ++ tex ++ "}{" ++ tipEnc text ++ "}"

/-- `tex` for variable `x`, with its type as a tooltip when tooltips are on and
the checker's context is known. -/
def Names.varTip (n : Names) (cx : Option Cx) (x tex : String) : String :=
  match n.tipVar, cx with
  | some f, some c =>
      match f c n.tvt x with
      | some text => cltip text tex
      | none => "\\clnotip{" ++ tex ++ "}"
  | _, _ => tex

/-- A type written in code, with its kind as a tooltip when tooltips are on. -/
def Names.tyTip (n : Names) (t : Ty) (tex : String) : String :=
  match n.tipTy.bind (· t) with
  | some text => cltip text tex
  | none => tex

/-- An operand: a variable carries its type. -/
def fmtAtN (n : Names) : At → String
  | .var x => n.varTip n.cx x (ident x)
  | a => fmtAt a

/-- A whole type in code, carrying its kind. -/
def fmtTyT (n : Names) (t : Ty) : String := n.tyTip t (fmtTy n 0 t)

def ord (acq rel : Bool) : String :=
  match acq, rel with
  | true,  true  => "^{\\mathsf{acq,rel}}"
  | true,  false => "^{\\mathsf{acq}}"
  | false, true  => "^{\\mathsf{rel}}"
  | false, false => ""

/-- `f[τ…]{i…}(a)`: type arguments, index arguments, the argument. -/
def fmtCall (n : Names) (f : String) (is : List String) (a : At) (ts : List Ty) : String :=
  fn f ++
  (if ts.isEmpty then "" else "[" ++ commas (ts.map (fmtTyT n)) ++ "]") ++
  (if is.isEmpty then "" else "\\{" ++ commas (is.map ident) ++ "\\}") ++
  "(" ++ fmtAtN n a ++ ")"

def fmtFence : Fence → String
  | .ld => "\\mathsf{ld}" | .st => "\\mathsf{st}" | .full => "\\mathsf{full}"

def fmtOp (n : Names) : Op → String
  | .atom a            => fmtAtN n a
  | .pair a b          => "(" ++ fmtAtN n a ++ ", " ++ fmtAtN n b ++ ")"
  | .inl τ a           => opn "inl" ++ "_" ++ br (fmtTyT n τ) ++ sp ++ fmtAtN n a
  | .inr τ a           => opn "inr" ++ "_" ++ br (fmtTyT n τ) ++ sp ++ fmtAtN n a
  | .add a b           => fmtAtN n a ++ " + " ++ fmtAtN n b
  | .sub a b           => fmtAtN n a ++ " - " ++ fmtAtN n b
  | .new a _           => opn "new" ++ sp ++ fmtAtN n a
  | .publish a         => opn "publish" ++ sp ++ fmtAtN n a
  | .intoRgn r a       => opn "intoRgn" ++ "_" ++ br (ident r) ++ sp ++ fmtAtN n a
  | .newBuf k τ        => opn "newBuf" ++ "_" ++ br (fmtTyT n τ) ++ sp ++ fmtAtN n k
  | .idx b i           => fmtAtN n b ++ "[" ++ fmtAtN n i ++ "]"
  | .bufInit b i v     => opn "bufInit" ++ sp ++ fmtAtN n b ++ sp ++ fmtAtN n i ++ sp ++ fmtAtN n v
  | .null μ τ          => opn "null" ++ " : " ++ fmtTyT n (.ptrOpt μ τ)
  | .fold a τ          => opn "fold" ++ sp ++ fmtAtN n a ++ " : " ++ fmtTyT n τ
  | .fld i a           => opn "fld" ++ "_" ++ br (toString i) ++ sp ++ fmtAtN n a
  | .load acq a        => opn "load" ++ ord acq false ++ sp ++ fmtAtN n a
  | .store rel a v tok => opn "store" ++ ord false rel ++ sp ++ fmtAtN n a ++ sp ++ fmtAtN n v ++
                            (match tok with
                             | some t => sp ++ kw "with" ++ sp ++ fmtAtN n t
                             | none   => "")
  | .fence f           => opn "fence" ++ "_" ++ br (fmtFence f)
  | .mkWord r P v tok  => opn "word" ++ "_" ++ br (ident r) ++ "[" ++ fmtProto P ++ "]" ++ sp ++
                            fmtAtN n v ++ sp ++ kw "with" ++ sp ++ fmtAtN n tok
  | .mkTicket r N P v tok => opn "ticket" ++ "_" ++ br (ident r) ++ "[" ++ fmtProto N ++ ", " ++ fmtProto P ++ "]" ++
                            sp ++ fmtAtN n v ++ sp ++ kw "with" ++ sp ++ fmtAtN n tok
  | .claim a tok       => opn "claim" ++ sp ++ fmtAtN n a ++ sp ++ kw "with" ++ sp ++ fmtAtN n tok
  | .spawn f a _ _ => opn "spawn" ++ sp ++ ident f ++ sp ++ fmtAtN n a
  | .ext e a => opn e.name ++ sp ++ fmtAtN n a
  | .isTy a τ => opn "isTy" ++ "_" ++ br (fmtTyT n τ) ++ sp ++ fmtAtN n a
  | .fetch o acq rel a v => opn "fetch" ++ "_" ++ o.name ++ ord acq rel ++ sp ++ fmtAtN n a ++ sp ++ fmtAtN n v
  | .mkWord2 r P v0 v1 tok => opn "pair" ++ "_" ++ br (ident r) ++ "[" ++ fmtProto2 P n.protos2 ++ "]" ++ sp ++
                            "(" ++ fmtAtN n v0 ++ ", " ++ fmtAtN n v1 ++ ")" ++ sp ++ kw "with" ++ sp ++ fmtAtN n tok
  | .ldp acq a n0 n1   => opn "ldp" ++ ord acq false ++ sp ++ fmtAtN n a ++ sp ++ kw "as" ++ sp ++
                            "(" ++ ident n0 ++ ", " ++ ident n1 ++ ")"
  | .stp rel a v0 v1 tok => opn "stp" ++ ord false rel ++ sp ++ fmtAtN n a ++ sp ++
                            "(" ++ fmtAtN n v0 ++ ", " ++ fmtAtN n v1 ++ ")" ++ sp ++ kw "with" ++ sp ++ fmtAtN n tok
  | .mkEPair r P v0 v1 => opn "epair" ++ "_" ++ br (ident r) ++ "[" ++ fmtEC n P ++ "]" ++ sp ++
                            "(" ++ fmtAtN n v0 ++ ", " ++ fmtAtN n v1 ++ ")"
  | .pack a w τ        => opn "pack" ++ sp ++ fmtAtN n a ++ sp ++ kw "at" ++ sp ++ ident w ++
                            " : " ++ fmtTyT n τ
  | .packT a σ τ       => opn "pack" ++ sp ++ fmtAtN n a ++ sp ++ kw "at" ++ sp ++ "[" ++ fmtTyT n σ ++ "]" ++
                            " : " ++ fmtTyT n τ
  | .validate x        => opn "validate" ++ sp ++ ident x
  | .call f is a ts    => fmtCall n f is a ts
  | .borrow c t        => opn "borrow" ++ "_" ++ br (capName c) ++ sp ++ fmtAtN n t
  | .freeze t          => opn "freeze" ++ sp ++ fmtAtN n t
  | .cvt sg w a        => opn "cvt" ++ "_" ++ br ((if sg then "I" else "U") ++ w.name) ++ sp ++ fmtAtN n a
  | .toInt a           => opn "toInt" ++ sp ++ fmtAtN n a
  | .asLanes sg w a    => opn "asLanes" ++ "_" ++ br ((if sg then "I" else "U") ++ w.name) ++ sp ++ fmtAtN n a
  | .fop o a b         => opn (toString (repr o)) ++ sp ++ fmtAtN n a ++ sp ++ fmtAtN n b
  | .fcmp o a b        => opn (toString (repr o)) ++ sp ++ fmtAtN n a ++ sp ++ fmtAtN n b
  | .fop1 o a          => opn (toString (repr o)) ++ sp ++ fmtAtN n a
  | .lane a j          => opn "lane" ++ sp ++ fmtAtN n a ++ sp ++ fmtAtN n j
  | .setLane a j v     => opn "setLane" ++ sp ++ fmtAtN n a ++ sp ++ fmtAtN n j ++ sp ++ fmtAtN n v
  | .ldl b i           => opn "ldl" ++ sp ++ fmtAtN n b ++ sp ++ fmtAtN n i
  | .stl b i v         => opn "stl" ++ sp ++ fmtAtN n b ++ sp ++ fmtAtN n i ++ sp ++ fmtAtN n v
  | .ldlw b i j        => opn "ldlw" ++ sp ++ fmtAtN n b ++ sp ++ fmtAtN n i ++ sp ++ fmtAtN n j
  | .stlw b i j v      => opn "stlw" ++ sp ++ fmtAtN n b ++ sp ++ fmtAtN n i ++ sp ++ fmtAtN n j ++ sp ++ fmtAtN n v
  | .endBorrow t       => opn "endBorrow" ++ sp ++ fmtAtN n t
  | .xchg a v          => opn "xchg" ++ sp ++ fmtAtN n a ++ sp ++ fmtAtN n v
  | .fnptr f           => opn "fnptr" ++ sp ++ ident f
  | .callc f a         => fmtAtN n f ++ "(" ++ fmtAtN n a ++ ")"
  | .rem a k           => fmtAtN n a ++ " " ++ kw "mod" ++ " " ++ fmtAtN n k
  | .nameI a           => opn "nameI" ++ sp ++ fmtAtN n a
  | .xchgAt b i v      => opn "xchg" ++ sp ++ fmtAtN n b ++ "[" ++ fmtAtN n i ++ "]" ++ sp ++ fmtAtN n v
  | .loadAt b i        => opn "load" ++ sp ++ fmtAtN n b ++ "[" ++ fmtAtN n i ++ "]"
  | .bits o a b        => opn (toString (repr o)) ++ sp ++ fmtAtN n a ++ sp ++ fmtAtN n b
  | .bit1 o a          => opn (toString (repr o)) ++ sp ++ fmtAtN n a
  | .vmatch lo hi b    => opn "vmatch" ++ sp ++ fmtAtN n lo ++ sp ++ fmtAtN n hi ++ sp ++ fmtAtN n b
  | .band a m          => fmtAtN n a ++ " \\mathbin{\\&} " ++ fmtAtN n m
  | .zero τ            => opn "zero" ++ "_" ++ br (fmtTyT n τ)
  | .loadAtF b i p     => opn "load" ++ sp ++ fmtAtN n b ++ "[" ++ fmtAtN n i ++ "]" ++
                            String.join (p.map fun k => "." ++ toString k)
  | .xchgAtF b i p v   => opn "xchg" ++ sp ++ fmtAtN n b ++ "[" ++ fmtAtN n i ++ "]" ++
                            String.join (p.map fun k => "." ++ toString k) ++ sp ++ fmtAtN n v

/-- The index binders an operation adds, by syntax alone (`Scope` falls back
to this): `rem`/`band` bind the quotient and remainder, `nameI` its result;
a `load` may bind one we cannot see. -/
def afterOpN (n : Names) (x : String) : Op → Names
  | .load _ _ => { n with exact := false }
  | .ldp _ _ n0 n1 => (n.pushI n0).pushI n1
  | .rem _ _ | .band _ _ => (n.pushI (x ++ "_d")).pushI x
  | .nameI _ => n.pushI x
  | _ => n

/-- A binder `x` in subterm names `n'`: its type is in the context the
subterm starts with. -/
def Names.bindTip (n' : Names) (x : String) : String := n'.varTip n'.cx x (ident x)

/-- One line per binding; `(indent, text)`.  `n` is the context before the
node, for its operands; each binder takes its type from the subterm's names. -/
def fmtExpr (n : Names) (d : Nat) : Expr → List (Nat × String)
  | .let_ x op e =>
      let n0 := n.step (.let_ x op e) 0 (afterOpN · x op)
      (d, kw "let" ++ sp ++ n0.bindTip x ++ " = " ++ fmtOp n op) :: fmtExpr n0 d e
  | .split a x y e =>
      let n0 := n.step (.split a x y e) 0 id
      (d, kw "let" ++ sp ++ "(" ++ n0.bindTip x ++ ", " ++ n0.bindTip y ++ ") = " ++ fmtAtN n a) ::
        fmtExpr n0 d e
  | .unpack a i x e =>
      let n0 := n.step (.unpack a i x e) 0 (·.pushI i)
      (d, kw "let" ++ sp ++ "\\langle " ++ ident i ++ ", " ++ n0.bindTip x ++ "\\rangle = " ++
          opn "unpack" ++ sp ++ fmtAtN n a) :: fmtExpr n0 d e
  | .unpackT a al x e =>
      let n0 := (n.pushT al).step (.unpackT a al x e) 0 id
      (d, kw "let" ++ sp ++ "\\langle [" ++ ident al ++ "], " ++ n0.bindTip x ++ "\\rangle = " ++
          opn "unpack" ++ sp ++ fmtAtN n a) :: fmtExpr n0 d e
  | .region a r p t e =>
      let n0 := n.step (.region a r p t e) 0 (·.pushI r)
      (d, kw "let" ++ sp ++ "\\langle " ++ ident r ++ ", " ++ n0.bindTip p ++ ", " ++ n0.bindTip t ++
          "\\rangle = " ++ opn "region" ++ sp ++ fmtAtN n a) :: fmtExpr n0 d e
  | .openPub a r p c e =>
      let n0 := n.step (.openPub a r p c e) 0 (·.pushI r)
      (d, kw "let" ++ sp ++ "\\langle " ++ ident r ++ ", " ++ n0.bindTip p ++ ", " ++ n0.bindTip c ++
          "\\rangle = " ++ opn "openPub" ++ sp ++ fmtAtN n a) :: fmtExpr n0 d e
  | .case a x e₁ y e₂ =>
      let hd : Expr := .case a x e₁ y e₂
      let n0 := n.step hd 0 id
      let n1 := n.step hd 1 id
      [(d, kw "case" ++ sp ++ fmtAtN n a ++ sp ++ kw "of"),
       (d + 1, opn "inl" ++ sp ++ n0.bindTip x ++ " \\Rightarrow")] ++ fmtExpr n0 (d + 2) e₁ ++
      [(d + 1, opn "inr" ++ sp ++ n1.bindTip y ++ " \\Rightarrow")] ++ fmtExpr n1 (d + 2) e₂
  | .parity a k ev od =>
      let hd : Expr := .parity a k ev od
      [(d, kw "parity" ++ sp ++ fmtAtN n a ++ sp ++ kw "of"),
       (d + 1, "2" ++ ident k ++ " \\Rightarrow")] ++ fmtExpr (n.step hd 0 (·.pushI k)) (d + 2) ev ++
      [(d + 1, "2" ++ ident k ++ "{+}1 \\Rightarrow")] ++ fmtExpr (n.step hd 1 (·.pushI k)) (d + 2) od
  | .ifeq a b yes no =>
      let hd : Expr := .ifeq a b yes no
      [(d, kw "if" ++ sp ++ fmtAtN n a ++ " = " ++ fmtAtN n b ++ sp ++ kw "then")] ++
      fmtExpr (n.step hd 0 id) (d + 1) yes ++ [(d, kw "else")] ++
      fmtExpr (n.step hd 1 fun n => { n with exact := false }) (d + 1) no
  | .ifnull a e₁ x e₂ =>
      let hd : Expr := .ifnull a e₁ x e₂
      let n1 := n.step hd 1 id
      [(d, kw "ifnull" ++ sp ++ fmtAtN n a ++ sp ++ kw "then")] ++ fmtExpr (n.step hd 0 id) (d + 1) e₁ ++
      [(d, kw "else" ++ sp ++ n1.bindTip x ++ " \\Rightarrow")] ++ fmtExpr n1 (d + 1) e₂
  | .cas acq rel w e v t ok fail =>
      let hd : Expr := .cas acq rel w e v t ok fail
      let n0 := n.step hd 0 id
      [(d, kw "cas" ++ ord acq rel ++ sp ++ fmtAtN n w ++ sp ++ fmtAtN n e ++ " \\mapsto " ++ fmtAtN n v ++
           sp ++ kw "as" ++ sp ++ n0.bindTip t ++ sp ++ kw "then")] ++
      fmtExpr n0 (d + 1) ok ++ [(d, kw "else")] ++ fmtExpr (n.step hd 1 id) (d + 1) fail
  | .casp acq rel w e0 e1 v0 v1 t ok fail =>
      let hd : Expr := .casp acq rel w e0 e1 v0 v1 t ok fail
      let n0 := n.step hd 0 id
      [(d, kw "casp" ++ ord acq rel ++ sp ++ fmtAtN n w ++ sp ++ "(" ++ fmtAtN n e0 ++ ", " ++ fmtAtN n e1 ++
           ") \\mapsto (" ++ fmtAtN n v0 ++ ", " ++ fmtAtN n v1 ++ ")" ++
           sp ++ kw "as" ++ sp ++ n0.bindTip t ++ sp ++ kw "then")] ++
      fmtExpr n0 (d + 1) ok ++ [(d, kw "else")] ++ fmtExpr (n.step hd 1 id) (d + 1) fail
  | .ret a => [(d, kw "ret" ++ sp ++ fmtAtN n a)]
  | .tail f is a ts => [(d, kw "tail" ++ sp ++ fmtCall n f is a ts)]

def fmtLines (ls : List (Nat × String)) : String :=
  "\\begin{array}{l}\n" ++
  " \\\\\n".intercalate (ls.map fun (i, s) => String.join (List.replicate i "\\quad ") ++ s) ++
  "\n\\end{array}"

/-- A type parameter's name as plain text (`\\alpha` is `α`), for tooltips. -/
def tvText (a : String) : String :=
  match (enumFrom tvPool 0).find? (·.2 == a) with
  | some (i, _) => ["α", "β", "γ", "δ", "ε", "ζ", "η", "θ"].getD i a
  | none => a

/-- Name the type parameters (outermost first) without clashes. -/
def tparamNames : List Kind → List String → List String
  | [], acc => acc.reverse
  | _ :: ks, acc => tparamNames ks (fresh tvPool acc "\\alpha" :: acc)

/-- `def f[α : κ]{r}(x : σ) : τ =` and the body.  `lib`: other blocks it may
call (so index variables bound by loads are named exactly; see `Scope`). -/
def fmtDecl (d : Decl) (abbrevs : Abbrevs := []) (protos : List (Proto × String) := protoNames)
    (lib : Prog := []) (tips : Names := {}) : String :=
  let tns := tparamNames d.tparams []
  let n : Names := { tv := tns.reverse, iv := d.idx.reverse.map ident, abbrevs := abbrevs,
                     tbase := tns.length, protos := protos, cx := some (Scope.start d),
                     lib := d :: lib, tipVar := tips.tipVar, tipTy := tips.tipTy,
                     tvt := (tns.map tvText).reverse }
  let tps := (tns.zip d.tparams).map fun (a, κ) =>
    if κ == {} then a else a ++ "{:}" ++ fmtKind κ
  let head := kw "def" ++ sp ++ fn d.name ++
    (if tps.isEmpty then "" else "[" ++ commas tps ++ "]") ++
    (if d.idx.isEmpty then "" else "\\{" ++ commas (d.idx.map ident) ++ "\\}") ++
    "(" ++ n.bindTip d.arg ++ " : " ++ fmtTyT n d.argTy ++ ") : " ++ fmtTyT n d.retTy ++ " ="
  fmtLines ((0, head) :: fmtExpr n 1 d.body)

/-! ## Documents -/

def latexMacros : String :=
  "\\providecommand{\\kw}[1]{\\mathbf{#1}}\n" ++
  "\\providecommand{\\op}[1]{\\mathtt{#1}}\n" ++
  "\\providecommand{\\ty}[1]{\\mathsf{#1}}\n" ++
  "\\providecommand{\\md}[1]{\\mathit{#1}}\n" ++
  "\\providecommand{\\fn}[1]{\\mathsf{#1}}\n" ++
  "\\providecommand{\\var}[1]{\\mathit{#1}}\n"

/-- Each code block as display math. -/
def listing (p : Prog) (abbrevs : Abbrevs := []) : String :=
  "\n\n".intercalate (p.map fun d => "\\[\n" ++ fmtDecl d abbrevs ++ "\n\\]")

/-- A standalone document: `pdflatex` it as is. -/
def document (title : String) (p : Prog) (abbrevs : Abbrevs := []) : String :=
  "\\documentclass[10pt,fleqn]{article}\n\\usepackage[margin=2cm,landscape]{geometry}\n" ++
  "\\usepackage{amsmath,amssymb}\n" ++ latexMacros ++
  "\\begin{document}\n\\section*{" ++ esc title ++ "}\n" ++ listing p abbrevs ++ "\n\\end{document}\n"

def writeListing (path : System.FilePath) (title : String) (p : Prog)
    (abbrevs : Abbrevs := []) : IO Unit :=
  IO.FS.writeFile path (document title p abbrevs)

/-! ## Pinned output

What the formatter prints for a few library types and one code block, so a
change in notation is a deliberate edit here and not drift. -/

#guard fmtType (.ptr .pub .int) == "\\ty{Ptr}_{\\md{pub}}\\,\\ty{Int}"
#guard fmtType (.prod .int (.sum .int .unit)) == "\\ty{Int} \\times (\\ty{Int} + \\ty{Unit})"
#guard fmtType (.prod (.prod .int .int) .int) == "(\\ty{Int} \\times \\ty{Int}) \\times \\ty{Int}"
#guard fmtType (mutex .int) ==
  "\\exists a.\\,\\ty{Ptr}_{\\md{pub}}\\,(\\ty{Word}[a, \\mathrm{Mutex}] \\times \\ty{Ptr}_{a}\\,\\ty{Int})"
#guard fmtType (node .int) ==
  "\\mu \\alpha.\\,\\ty{Int} \\times \\ty{Ptr?}_{\\md{pub}}\\,\\alpha"
-- A binder avoids the names in scope: `a` is taken by the outer `∃`.
#guard fmtType (.iex (.iex (.intS (.add (.var 0) (.var 1))))) ==
  "\\exists a.\\,\\exists b.\\,\\ty{Int}(b + a)"
#guard fmtType (claimed buf) ==
  "\\exists a.\\,\\ty{Ptr}_{a}\\,\\ty{Ptr}_{\\md{own}}\\,\\ty{Int} \\times \\ty{Tok}_{a}(\\mathrm{Claim}, 1)"
#guard fmtProto badSeqP ==
  "\\langle s_{0}{=}2k^{\\bullet}, s_{1}{=}2k{+}1 \\mid s_{0}{\\to}s_{1}, s_{1}{\\to}s_{0} \\rangle"
#guard fmtKind qκ == "\\{\\md{insens}, \\md{share}, \\md{noOwn}, \\md{copy}\\}"
-- Abbreviations: a closed type anywhere; one over `α` only at the block's level.
#guard fmtType (.ptr .pub (queue .int)) [] (family "Queue" queue [.int]) ==
  "\\ty{Ptr}_{\\md{pub}}\\,\\ty{Queue}(\\ty{Int})"
#guard fmtType (queue α) ["\\alpha"] (family "Queue" queue [α]) == "\\ty{Queue}(\\alpha)"
#guard fmtType (.mu (queue α)) ["\\alpha"] (family "Queue" queue [α]) != "\\mu \\beta.\\,\\ty{Queue}(\\alpha)"
#guard ident "t0" == "t_{0}" && ident "nx" == "\\var{nx}" && ident "x" == "x"
#guard fmtDecl lockD ==
  "\\begin{array}{l}\n" ++
  "\\kw{def}\\;\\fn{lock}\\{r\\}(m : \\ty{Ptr}_{\\md{pub}}\\,(\\ty{Word}[r, \\mathrm{Mutex}] \\times \\ty{Ptr}_{r}\\,\\ty{Int})) : \\ty{Tok}_{r}(\\mathrm{Mutex}, 1) = \\\\\n" ++
  "\\quad \\kw{let}\\;w = \\op{fld}_{0}\\;m \\\\\n" ++
  "\\quad \\kw{cas}^{\\mathsf{acq}}\\;w\\;0 \\mapsto 1\\;\\kw{as}\\;t\\;\\kw{then} \\\\\n" ++
  "\\quad \\quad \\kw{ret}\\;t \\\\\n" ++
  "\\quad \\kw{else} \\\\\n" ++
  "\\quad \\quad \\kw{tail}\\;\\fn{lock}\\{r\\}(m)\n" ++
  "\\end{array}"
-- Index variables bound by a load are named after the variable, as the checker
-- binds them (`Scope`): here `r` and the observed value `c1`.
def obsD : Decl :=
  { name := "f", idx := readD.idx, arg := "m", argTy := readD.argTy, retTy := .unit,
    body := .let_ "w" (.fld 0 (.var "m")) (.let_ "c1" (.load true (.var "w"))
              (.let_ "z" (.null (.rgn (.var 1)) (.intS (.var 0))) (.ret .unit))) }
#guard accepts (checkDecl [obsD] obsD)
#guard ((fmtDecl obsD).splitOn "\\ty{Ptr?}_{r}\\,\\ty{Int}(c_{1})").length > 1
-- A protocol a document names prints by that name.
#guard fmtType (.word (.lit 0) badSeqP) (protos := [(badSeqP, "Bad")] ++ protoNames) ==
  "\\ty{Word}[0, \\mathrm{Bad}]"
-- Free index variables of an inline type, by name.
#guard fmtType (.tok (.var 0) (some (mutexP, .var 1))) (idx := ["n", "r"]) ==
  "\\ty{Tok}_{r}(\\mathrm{Mutex}, n)"

end CoreUtils
