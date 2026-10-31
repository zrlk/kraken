import WeakCore.Syntax
import Scc.Lower.Obj
import Scc.PrintModel

/-!
# scc frontend: parsing, type checking, and the accepted fragment

Reads a `.w` file (WeakCore's concrete syntax, `Syntax.parseProg`), runs
WeakCore's checker (`CoreTerm.checkProg`), and checks that the program lies in
the fragment scc compiles (`accepted`).  Errors carry a
`line:col` where one is known.

## Provisional surface forms

WeakCore's concrete syntax has no `spawn` yet and no output extern.  Until it
does, scc reads:

* `let t = spawn{f}(a)` (with optional type arguments `spawn[τ…]{f}(a)`) as
  `Op.spawn f a T ts`, where `T` is `f`'s declared argument type.  The parser
  reads the form as a call of a block named `spawn`; `rewriteSpawn` turns it
  into the spawn.  A program may not define a block named `spawn`.
* A call of the block `print` is the output extern when `print` has exactly the
  signature `printSig` (a published byte slice and a byte count) or
  `printOwnSig` (the same with an owned slice, which the call consumes, so a
  program may print without `publish`): it writes the first `n` bytes of the
  slice to standard output.  Its body is ignored.
* The block `printL` is the output extern's loop when it is textually
  `printLoopD` or its published twin `printLoopPubD` (`Scc/PrintModel.lean`,
  `declIs`): the `emit` loop of the extern's WeakCore model, which `print`'s
  model body (`printExtD`, `printExtPubD`) tail-calls.
  Like the extern's body it is not checked or compiled (`externOf` lists it
  with the extern, so the lowering skips it), and no compiled block may call,
  tail-call or spawn it (`modelDiags`).  Any other block named `printL` is an
  ordinary block.

## The accepted fragment

Terms: `let`, `let (x, y) =`, `unpack` (index and type existentials), `if`,
`ret`, `tail`.  Operations: atoms and pairs, `Int` `+`/`-`, `new`, `publish`,
`newBuf`, `bufInit`, `b[i]`, `fld`, plain/acquire `load` (also `load b[i]`),
plain/release `store` (without a token), `fence`, `pack` (both kinds), calls,
`xchg` (also `xchg b[i]`), `nameI`, `zero`, the fixed-width family (`cvt`, `toInt`,
`asLanes`, `fop`, `fcmp`, `fop1`, `lane`, `setLane`, `bits` other than
`msb16`, `bit1`), `spawn`, and the machine externs `park` and `unpark`
(the runtime's `park`/`unpark`).  Types: `Unit`, `Void`, `Int`, `Int[i]`,
`ThreadId`, fixed-width and lanes words, products, `Ptr`/`Loc` with mode `own`
or `pub`, arrays of one-word elements, refinements, index existentials and
type existentials of those.  Declarations: plain blocks (no `device` or
`restricted` declarations).  Everything else is rejected with the construct named.

## Static checks beyond the fragment

* **Stack pointers never escape.**  The source has no stack addresses at all:
  every `Ptr`/`Loc` value is a heap label and offset (`TermRun.alloc`,
  `TermRun.allocBuf` and `TermRun.freshLabel`, TermRun.lean:266 and 288–302),
  and spawn arguments must be copyable (`checkOp`'s `.spawn`, CoreTerm.lean:2232),
  so no owned reference crosses threads.  The lowering keeps it that way:
  every pointer comes from `new`/`newBuf` (the heap arena), from `fld`/`b[i]`
  on such a pointer (a base and an offset word), or from the runtime (the
  thread's TCB, in the pinned region); values live in registers and frame
  slots and no operation takes the address of either.  The check is therefore a documented no-op
  (`stackNoEscape`); it becomes a real check when a construct that can take
  the address of a frame slot enters the fragment.
* **Mixed units do not race** (`regionHomog`, provisional).  Under the
  object layout (`Scc/LAYOUT.md`) a locative's base and offset words live in
  different regions, so a locative may not sit inline in a shared (`pub`)
  cell, where a racing reader could pair the halves of two writes.  Checked on every signature and binding type; to be dropped
  when WeakCore's checker has the rule.
* **Literals fit in 64 bits.**  WeakCore's `Int` literals are any `Nat`; a
  literal of `2^64` or more cannot be represented and is rejected, in a term
  (`bigLit`) and in a type (`tyBig`: an index literal or scaling constant of
  a singleton `Int[i]`, an array length or a refinement, in a signature or
  in the type an operation names).  WeakCore has no negative literals (a
  negation is the operation `fop1 neg`), so there is no lower bound to check.
* **Buffers fit the 32-bit offsets.**  A locative's offset word packs two
  32-bit byte offsets (`Scc/LAYOUT.md` §4), so each region of an object must
  stay below 4 GiB.  A `newBuf` of a literal length whose region would take
  `2^32` bytes or more is rejected (`bufTooBig`); a dynamic length is bounded
  at run time by the allocator (`2^lenBits` elements, and the arena, whose
  size the lowering requires below `2^32`).
* **`Int` addition.**  Plain `Int` is unbounded in WeakCore; scc lowers
  **every** `+` to an addition whose overflow beyond `2^64 - 1` takes the
  abort outcome.  No check is elided: eliding one would need a WeakCore lemma
  (index-typed variables hold their index values in reachable states) that a
  certificate could cite, and none exists yet.  `addSites` still classifies
  each site: *boundable* when both operands are literals or singletons
  `Int[e]` and the sum of their index terms is, by `Lin.leB` under the
  checker's own context, at most the length of an array of non-empty elements
  that some variable in scope refers to (an allocated array has fewer than
  `2^61` elements), so the check could be elided once that lemma exists;
  *unbounded* otherwise.  `--report` lists every site with its class.
-/

open CoreLang CoreTerm

namespace Scc.Frontend

/-- A diagnostic: a message with a `line:col` position (`0` = unknown). -/
structure Diag where
  line : Nat := 0
  col : Nat := 0
  msg : String
  deriving Repr, Inhabited

def Diag.render (file : String) (d : Diag) : String :=
  if d.line == 0 then s!"{file}: error: {d.msg}"
  else s!"{file}:{d.line}:{d.col}: error: {d.msg}"

/-! ## Locating constructs in the source text

The AST carries no positions; diagnostics about a block are placed by finding
the block's `def` line and, inside it, the line that binds the variable
concerned. -/

/-- `s` without leading whitespace. -/
def ltrim (s : String) : String := String.ofList (s.toList.dropWhile Char.isWhitespace)

/-- `s` without its first `n` characters. -/
def sdrop (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)

/-- Lines of the source, numbered from 1. -/
def srcLines (src : String) : Array String := (src.splitOn "\n").toArray

/-- The column (from 1) of the first occurrence of `pat` in `s`. -/
def findCol (s pat : String) : Option Nat :=
  let n := s.length
  let m := pat.length
  let rec go (i : Nat) (fuel : Nat) : Option Nat :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      if i + m > n then none
      else if (sdrop s i).startsWith pat then some (i + 1) else go (i + 1) fuel
  go 0 (n + 1)

/-- The line (from 1) of `def f`, if found. -/
def defLine (ls : Array String) (f : String) : Option Nat := Id.run do
  for h : i in [0:ls.size] do
    let t := ltrim ls[i]
    if t.startsWith "def " then
      let rest := ltrim (sdrop t 4)
      if rest.startsWith f then
        let after := sdrop rest f.length
        if after.isEmpty || after.startsWith "(" || after.startsWith "{" || after.startsWith "[" ||
            after.startsWith " " then
          return some (i + 1)
  return none

/-- Position of the first line at or after block `f`'s `def` containing one
of `pats` (before the next `def`); else the `def` line; else unknown. -/
def locate (src : String) (f : String) (pats : List String) : Nat × Nat := Id.run do
  let ls := srcLines src
  match defLine ls f with
  | none => return (0, 0)
  | some d =>
    let mut j := d
    while j < ls.size do
      let l := ls[j]!
      if (ltrim l).startsWith "def " then break
      for p in pats do
        if let some c := findCol l p then return (j + 1, c)
      j := j + 1
    return (d, 1)

def diagAt (src f : String) (pats : List String) (msg : String) : Diag :=
  let (l, c) := locate src f pats
  { line := l, col := c, msg := msg }

/-- Patterns that find the binding of `x`. -/
def bindPats (x : String) : List String :=
  [s!"let {x} ", s!"let {x}=", s!"let ({x},", s!"let ({x} ,", s!", {x})", s!",{x})", s!", {x}>"]

/-! ## Parsing, with the provisional `spawn` form -/

/-- Rewrite `spawn[ts]{f}(a)` calls into `Op.spawn`. -/
partial def rewriteSpawnE (p : Prog) (src fn : String) : Expr → Except Diag Expr
  | .let_ x (.call "spawn" is a ts) e => do
      let f ← match is with
        | [f] => pure f
        | _ => throw (diagAt src fn (bindPats x) "spawn: write `spawn{f}(a)`, naming exactly one block")
      let d ← match p.find? (·.name == f) with
        | some d => pure d
        | none => throw (diagAt src fn (bindPats x) s!"spawn: unknown block '{f}'")
      if !d.tparams.isEmpty || !d.idx.isEmpty then
        throw (diagAt src fn (bindPats x) s!"spawn: block '{f}' has type or index parameters")
      pure (.let_ x (.spawn f a d.argTy ts) (← rewriteSpawnE p src fn e))
  | .let_ x op e => return .let_ x op (← rewriteSpawnE p src fn e)
  | .split a x y e => return .split a x y (← rewriteSpawnE p src fn e)
  | .unpack a i x e => return .unpack a i x (← rewriteSpawnE p src fn e)
  | .unpackT a al x e => return .unpackT a al x (← rewriteSpawnE p src fn e)
  | .region a r q t e => return .region a r q t (← rewriteSpawnE p src fn e)
  | .openPub a r q c e => return .openPub a r q c (← rewriteSpawnE p src fn e)
  | .case a x e₁ y e₂ => return .case a x (← rewriteSpawnE p src fn e₁) y (← rewriteSpawnE p src fn e₂)
  | .ifnull a e₁ x e₂ => return .ifnull a (← rewriteSpawnE p src fn e₁) x (← rewriteSpawnE p src fn e₂)
  | .parity a k e₁ e₂ => return .parity a k (← rewriteSpawnE p src fn e₁) (← rewriteSpawnE p src fn e₂)
  | .ifeq a b e₁ e₂ => return .ifeq a b (← rewriteSpawnE p src fn e₁) (← rewriteSpawnE p src fn e₂)
  | .cas acq rel w e v t ok fl =>
      return .cas acq rel w e v t (← rewriteSpawnE p src fn ok) (← rewriteSpawnE p src fn fl)
  | .casp acq rel w e0 e1 v0 v1 t ok fl =>
      return .casp acq rel w e0 e1 v0 v1 t (← rewriteSpawnE p src fn ok) (← rewriteSpawnE p src fn fl)
  | e => pure e

/-- Parse a `.w` source text. -/
def parse (src : String) : Except Diag Prog := do
  -- `spawn` is now a WeakCore keyword (native form `spawn f[ts] a : T`); the
  -- provisional `spawn{f}(a)` is read as a call of the escaped name `«spawn»`.
  let p ← match Syntax.parseProg (src.replace "spawn{" "«spawn»{") with
    | .ok p => pure p
    | .error e => throw { line := e.line, col := e.col, msg := e.msg }
  if p.any (·.name == "spawn") then
    throw (diagAt src "spawn" [] "a block may not be named 'spawn' (the provisional spawn form)")
  p.mapM fun d => do pure { d with body := ← rewriteSpawnE p src d.name d.body }

/-- Run WeakCore's checker. -/
def typecheck (src : String) (p : Prog) : Except Diag Unit :=
  p.forM fun d =>
    match checkDecl p d with
    | .ok _ => pure ()
    | .error e => throw (diagAt src d.name [] s!"type error in '{d.name}': {e}")

/-! ## Externs -/

/-- The signature of the provisional output extern `print`. -/
def printSigText : String := "({Loc pub Array[m] LanesU8 | ini >= m} * Int[m]) * Int"

/-- `printSigText` as a term, so that the kernel reduces `externOf` (the
parser is `partial`); the `#guard` below pins it to the text's parse. -/
def printSig : Option Ty :=
  some (.prod (.prod (.refine (.loc .pub (.array (.var 0) (.lanes false .w8))) (.ini (.var 0)))
    (.intS (.var 0))) .int)

#guard printSig == (Syntax.parseTy printSigText {} ["m"]).toOption

/-- The signature of the output extern on an owned slice. -/
def printOwnSigText : String := "({Loc own Array[m] LanesU8 | ini >= m} * Int[m]) * Int"

/-- `printOwnSigText` as a term (as `printSig`), pinned to the text's parse by
the `#guard` below. -/
def printOwnSig : Option Ty :=
  some (.prod (.prod (.refine (.loc .own (.array (.var 0) (.lanes false .w8))) (.ini (.var 0)))
    (.intS (.var 0))) .int)

#guard printOwnSig == (Syntax.parseTy printOwnSigText {} ["m"]).toOption

/-- Which extern a block is, if any. -/
inductive Extern
  | print
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `some e` if block `d` is the extern `e` (name and signature match), or,
for `.print`, the extern's loop (textually `printLoopD` or `printLoopPubD`;
see the module docstring). -/
def externOf (d : Decl) : Option Extern :=
  if d.name == "print" && d.idx.length == 1 && d.tparams.isEmpty &&
      (some d.argTy == printSig || some d.argTy == printOwnSig) &&
      d.retTy == .unit then some .print
  else if d.name == "printL" && (declIs d printLoopD || declIs d printLoopPubD) then some .print
  else none

/-- Is block `d` the output extern's loop (`printLoopD` or `printLoopPubD`, textually)? -/
def isPrintLoop (d : Decl) : Bool := d.name == "printL" && (declIs d printLoopD || declIs d printLoopPubD)

/-- The externs among the program's blocks. -/
def externs (p : Prog) : List (String × Extern) :=
  p.filterMap fun d => (externOf d).map (d.name, ·)

/-! ## The accepted fragment -/

/-- Runtime words of a value of type `t` (as `TermRun.accs`, restricted to
the fragment's types: every access is one word).  `none` off the fragment. -/
def words : Ty → Option Nat
  | .unit | .void => some 0
  | .int | .intS _ | .fix _ _ | .lanes _ _ => some 1
  | .ptr _ _ | .loc _ _ => some 1
  | .prod a b => do pure ((← words a) + (← words b))
  | .refine t _ | .iall t | .mu t => words t
  | .iex t =>
      if t.countI 0 ≥ 2 then
        match (Ty.iex t).rawWords with
        | some 0 => some 0 | some 1 => some 1 | some 2 => none  -- a 16-byte granule
        | _ => words t
      else words t
  | .tex κ t =>
      if t.countT 0 ≥ 2 then
        match (Ty.tex κ t).rawWords with
        | some 0 => some 0 | some 1 => some 1 | some 2 => none
        | _ => words t
      else words t
  | _ => none

/-- `none` if mode `μ` is in the fragment, else what it is. -/
def modeBad : Mode → Option String
  | .own => none
  | .pub => none
  | _ => some "a region mode"

/-- `none` if type `t` is in the fragment, else the offending construct. -/
def tyBad : Ty → Option String
  | .unit | .void | .int | .intS _ | .fix _ _ | .lanes _ _ => none
  | .prod a b => tyBad a <|> tyBad b
  | .ptr μ t | .loc μ t => modeBad μ <|> tyBad t
  | .array _ t =>
      match tyBad t with
      | some s => some s
      | none => if words t == some 1 then none else some "an array of multi-word or empty elements"
  | .refine t _ | .iex t => tyBad t
  | .tex _ t => tyBad t
  | .tvar _ => none
  | .sum _ _ => some "a sum type"
  | .code _ _ _ => some "a code pointer type"
  | .opq _ => some "a device type"
  | .ptrOpt _ _ => some "a nullable pointer type"
  | .share _ => some "a read share"
  | .cap _ _ => some "a capability"
  | .word _ _ | .word2 _ _ | .epair _ _ => some "a protocol word"
  | .tok _ _ | .tok2 _ _ _ _ | .tokE _ _ _ => some "a region token"
  | .mu _ => some "a recursive type"
  | .iall _ => some "an index universal"
  | .tid => none

/-- `none` if operation `op` is in the fragment, else the offending construct. -/
def opBad : Op → Option String
  | .atom _ | .pair _ _ | .add _ _ | .sub _ _ | .new _ _ | .publish _ | .idx _ _ | .fld _ _
  | .fence _ | .xchg _ _ | .nameI _ | .xchgAt _ _ _ | .loadAt _ _ | .bit1 _ _
  | .cvt _ _ _ | .toInt _ | .asLanes _ _ _ | .fop _ _ _ | .fcmp _ _ _ | .fop1 _ _
  | .lane _ _ | .setLane _ _ _ | .bufInit _ _ _ => none
  | .load _ _ => none
  | .store _ _ _ none => none
  | .store _ _ _ (some _) => some "a store with a token (`store … with t`)"
  | .newBuf _ τ => tyBad τ
  | .zero τ => tyBad τ
  | .pack _ _ τ => tyBad τ
  | .packT _ σ τ => tyBad σ <|> tyBad τ
  | .call _ _ _ ts => ts.findSome? tyBad
  | .spawn _ _ T ts => tyBad T <|> (ts.findSome? tyBad)
  | .bits .msb16 _ _ => some "`bits msb16`"
  | .bits _ _ _ => none
  | .inl _ _ | .inr _ _ => some "a sum injection (`inl`/`inr`)"
  | .null _ _ => some "`null`"
  | .fold _ _ => some "`fold`"
  | .intoRgn _ _ => some "`intoRgn`"
  | .mkWord .. => some "`mkWord`"
  | .ext .park _ | .ext .unpark _ => none
  | .ext .. => some "an extern call"
  | .validate _ => some "`validate`"
  | .borrow _ _ => some "`borrow`"
  | .endBorrow _ => some "`endBorrow`"
  | .fnptr _ => some "`fnptr`"
  | .callc _ _ => some "`callc`"
  | .rem _ _ => some "`mod`"
  | .vmatch _ _ _ => some "`vmatch`"
  | .band _ _ => some "`&` (index mask)"
  | .loadAtF _ _ _ => some "a field-path slot load"
  | .xchgAtF _ _ _ _ => some "a field-path slot exchange"
  | .freeze _ => some "`freeze`"
  | .ldl _ _ | .stl _ _ _ | .ldlw _ _ _ | .stlw _ _ _ _ => some "a lane access to a buffer (`ldl`/`stl`/`ldlw`/`stlw`)"
  | .mkWord2 .. => some "`mkWord2`"
  | .ldp .. => some "`ldp`"
  | .stp .. => some "`stp`"
  | .mkEPair .. => some "`mkEPair`"
  | .mkTicket .. => some "`mkTicket`"
  | .claim _ _ => some "`claim`"
  -- `fetch add` on an `Int` cell also grows without bound.  If it enters the
  -- fragment, its checked form must be a CAS loop that never stores on
  -- overflow, never `ldaddal`/`lock xadd`: those publish the wrapped value
  -- before the check could abort.
  | .fetch .. => some "a fetch-op (`fetch`)"
  | .isTy _ _ => some "a type test (`isTy`)"

/-- The atoms an operation of the fragment reads. -/
def opAts : Op → List At
  | .atom a | .new a _ | .publish a | .nameI a | .toInt a | .cvt _ _ a | .asLanes _ _ a
  | .fop1 _ a | .bit1 _ a | .pack a _ _ | .packT a _ _ | .call _ _ a _ | .spawn _ a _ _
  | .newBuf a _ | .fld _ a | .load _ a => [a]
  | .pair a b | .add a b | .sub a b | .idx a b | .xchg a b | .loadAt a b | .fop _ a b
  | .fcmp _ a b | .lane a b | .bits _ a b | .store _ a b _ => [a, b]
  | .xchgAt a b c | .setLane a b c | .bufInit a b c => [a, b, c]
  | _ => []

/-- The first integer literal that does not fit in 64 bits. -/
def bigLit (as : List At) : Option Nat :=
  as.findSome? fun | .lit n => if n ≥ 2 ^ 64 then some n else none | _ => none

def bigLitDiag (src fn : String) (pats : List String) (as : List At) : List Diag :=
  match bigLit as with
  | some n => [diagAt src fn pats s!"the literal {n} does not fit in 64 bits (in '{fn}')"]
  | none => []

/-- The first literal or scaling constant of an index term that does not fit
in 64 bits. -/
def idxBig : Idx → Option Nat
  | .lit n => if n ≥ 2 ^ 64 then some n else none
  | .var _ => none
  | .add i j | .sub i j => idxBig i <|> idxBig j
  | .smul n i => if n ≥ 2 ^ 64 then some n else idxBig i

/-- The first index literal of a refinement predicate that does not fit in
64 bits. -/
def predBig : Pred → Option Nat
  | .tt => none
  | .le i j | .eq i j => idxBig i <|> idxBig j
  | .and p q => predBig p <|> predBig q
  | .ini i => idxBig i

/-- The first index literal of a type that does not fit in 64 bits (the
fragment's types: singletons, arrays, refinements and what contains them). -/
def tyBig : Ty → Option Nat
  | .intS i => idxBig i
  | .array i t => idxBig i <|> tyBig t
  | .prod a b | .sum a b | .code a b _ => tyBig a <|> tyBig b
  | .ptr _ t | .ptrOpt _ t | .loc _ t => tyBig t
  | .mu t | .iall t | .iex t | .tex _ t => tyBig t
  | .refine t ψ => tyBig t <|> predBig ψ
  | _ => none

/-- The types an operation of the fragment names. -/
def opTys : Op → List Ty
  | .newBuf _ τ | .zero τ | .pack _ _ τ => [τ]
  | .packT _ σ τ => [σ, τ]
  | .call _ _ _ ts => ts
  | .spawn _ _ T ts => T :: ts
  | _ => []

def tyBigDiag (src fn : String) (pats : List String) (where_ : String) (ts : List Ty) : List Diag :=
  match ts.findSome? tyBig with
  | some n => [diagAt src fn pats s!"the index literal {n} does not fit in 64 bits ({where_})"]
  | none => []

/-- A `newBuf` of literal length `n` whose regions would take `2^32` bytes or
more: `8·n` bytes per word of the element in a region (`Scc/LAYOUT.md` §3),
beyond what a 32-bit byte offset of the locative's offset word addresses. -/
def bufTooBig : Op → Option Nat
  | .newBuf (.lit n) τ => if 8 * n * ((words τ).getD 1) ≥ 2 ^ 32 then some n else none
  | _ => none

/-- Check one block's body against the fragment. -/
partial def exprDiags (src fn : String) : Expr → List Diag
  | .let_ x op e =>
      let here := match opBad op with
        | some c => [diagAt src fn (bindPats x) s!"{c} is not in the accepted fragment (in '{fn}', binding '{x}')"]
        | none =>
          match bufTooBig op with
          | some n => [diagAt src fn (bindPats x)
              s!"the buffer of {n} elements would take 4 GiB or more in a region, beyond the 32-bit byte offsets of its locatives (in '{fn}', binding '{x}')"]
          | none =>
            bigLitDiag src fn (bindPats x) (opAts op) ++
              tyBigDiag src fn (bindPats x) s!"in '{fn}', binding '{x}'" (opTys op)
      here ++ exprDiags src fn e
  | .split a x _ e => bigLitDiag src fn (bindPats x) [a] ++ exprDiags src fn e
  | .unpack a _ x e | .unpackT a _ x e => bigLitDiag src fn (bindPats x) [a] ++ exprDiags src fn e
  | .ifeq a b e₁ e₂ => bigLitDiag src fn ["if "] [a, b] ++ exprDiags src fn e₁ ++ exprDiags src fn e₂
  | .ret a => bigLitDiag src fn ["ret "] [a]
  | .tail _ _ a _ => bigLitDiag src fn ["tail "] [a]
  | .region _ _ _ _ _ => [diagAt src fn ["region"] s!"`region` is not in the accepted fragment (in '{fn}')"]
  | .openPub _ _ _ _ _ => [diagAt src fn ["openPub"] s!"`openPub` is not in the accepted fragment (in '{fn}')"]
  | .case _ _ _ _ _ => [diagAt src fn ["case "] s!"`case` is not in the accepted fragment (in '{fn}')"]
  | .ifnull _ _ _ _ => [diagAt src fn ["ifnull"] s!"`ifnull` is not in the accepted fragment (in '{fn}')"]
  | .parity _ _ _ _ => [diagAt src fn ["parity"] s!"`parity` is not in the accepted fragment (in '{fn}')"]
  | .cas .. => [diagAt src fn ["cas "] s!"`cas` is not in the accepted fragment (in '{fn}')"]
  | .casp .. => [diagAt src fn ["casp "] s!"`casp` is not in the accepted fragment (in '{fn}')"]

/-- `newBuf`s of zero-word elements in a block's body (their bindings): the
code check's heap counter counts a buffer's words in source units, so such a
buffer is outside what `scc --code` certifies (`codeDiags`). -/
partial def zeroBufs : Expr → List String
  | .let_ x op e =>
      (match op with
       | .newBuf _ τ => if words τ == some 0 then [x] else []
       | _ => []) ++ zeroBufs e
  | .split _ _ _ e | .unpack _ _ _ e | .unpackT _ _ _ e => zeroBufs e
  | .ifeq _ _ e₁ e₂ => zeroBufs e₁ ++ zeroBufs e₂
  | _ => []

/-- **The code check's limits on the source** (`scc --code`, both ISAs):
a `newBuf` of a zero-word element type is refused (`zeroBufs`). The compiler
itself accepts it. -/
def codeDiags (src : String) (p : Prog) : List Diag :=
  let ext := externs p
  p.flatMap fun d =>
    if ext.any (·.1 == d.name) then [] else
    (zeroBufs d.body).map fun x => diagAt src d.name (bindPats x)
      s!"a buffer of zero-word elements is outside the certified fragment of the code check (in '{d.name}', binding '{x}')"

/-- The entry point's shape: what `main` takes. -/
inductive EntryArg
  /-- `main(a : Unit)` -/
  | unit
  /-- `main(a : ThreadId)` (or the older stub `Ptr pub Void`): the main
  thread's `ThreadId`. -/
  | tid
  /-- `main(a : S * ThreadId)` (or `S * Ptr pub Void`), with `S` the result of the setup block
  `rodata(u : Unit) : S`, run as code before `main` (static data by the
  heap-bytes route). -/
  | setupTid
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The entry point's shape: what `main` takes and whether it returns an `Int`. -/
structure Entry where
  arg : EntryArg
  retInt : Bool
  deriving Repr, Inhabited

/-- Check the entry point `main`. -/
def entryOf (src : String) (p : Prog) : Except Diag Entry := do
  let d ← match p.find? (·.name == "main") with
    | some d => pure d
    | none => throw { msg := "no block named 'main'" }
  let bad (m : String) : Diag := diagAt src "main" [] m
  if !d.tparams.isEmpty || !d.idx.isEmpty then throw (bad "'main' may not have type or index parameters")
  let retInt ← match d.retTy with
    | .int => pure true
    | .unit => pure false
    | _ => throw (bad "'main' must return Int (the exit status) or Unit")
  let arg ← match d.argTy with
    | .unit => pure EntryArg.unit
    | .ptr .pub .void | .tid => pure .tid
    | .prod s (.ptr .pub .void) | .prod s .tid =>
        match p.find? (·.name == "rodata") with
        | some r =>
            if r.tparams.isEmpty && r.idx.isEmpty && r.argTy == .unit && r.retTy == s then pure .setupTid
            else throw (bad "'main(a : S * ThreadId)' needs a setup block 'rodata(u : Unit) : S'")
        | none => throw (bad "'main(a : S * ThreadId)' needs a setup block 'rodata(u : Unit) : S'")
    | _ => throw (bad "'main' must take Unit, ThreadId, or S * ThreadId")
  pure ⟨arg, retInt⟩

/-- All fragment diagnostics of a program. -/
def acceptDiags (src : String) (p : Prog) : List Diag :=
  let ext := externs p
  p.flatMap fun d =>
    let sig := match tyBad d.argTy <|> tyBad d.retTy with
      | some c => [diagAt src d.name [] s!"{c} is not in the accepted fragment (in the signature of '{d.name}')"]
      | none => tyBigDiag src d.name [] s!"in the signature of '{d.name}'" [d.argTy, d.retTy]
    let tps := if d.tparams.isEmpty then [] else
      [diagAt src d.name [] s!"type parameters are not in the accepted fragment (block '{d.name}')"]
    -- A device declaration may call device externs, which the backend does not implement.
    let dev := if d.kind == .device then
      [diagAt src d.name [] s!"a device declaration is not in the accepted fragment (block '{d.name}')"]
      else []
    -- A restricted declaration's fuel and stack budgets are not checked or
    -- lowered by scc yet; refuse it here rather than rely on WeakCore's checker.
    let rst := match d.kind with
      | .restricted _ _ _ _ =>
          [diagAt src d.name [] s!"a restricted declaration is not in the accepted fragment (block '{d.name}')"]
      | _ => []
    -- An extern's body is replaced by the runtime; it is not compiled.
    if ext.any (·.1 == d.name) then dev ++ rst ++ sig else dev ++ rst ++ sig ++ tps ++ exprDiags src d.name d.body

/-- The blocks a body calls, tail-calls, spawns or names as a code value
(`fnptr`), in every sub-term (whether or not the fragment admits it). -/
def reachedE : Expr → List String
  | .let_ _ op e =>
      (match op with
       | .call f .. | .spawn f .. | .fnptr f => [f]
       | _ => []) ++ reachedE e
  | .split _ _ _ e => reachedE e
  | .unpack _ _ _ e => reachedE e
  | .unpackT _ _ _ e => reachedE e
  | .region _ _ _ _ e => reachedE e
  | .openPub _ _ _ _ e => reachedE e
  | .case _ _ e₁ _ e₂ => reachedE e₁ ++ reachedE e₂
  | .ifnull _ e₁ _ e₂ => reachedE e₁ ++ reachedE e₂
  | .parity _ _ e₁ e₂ => reachedE e₁ ++ reachedE e₂
  | .ifeq _ _ e₁ e₂ => reachedE e₁ ++ reachedE e₂
  | .cas _ _ _ _ _ _ e₁ e₂ => reachedE e₁ ++ reachedE e₂
  | .casp _ _ _ _ _ _ _ _ e₁ e₂ => reachedE e₁ ++ reachedE e₂
  | .ret _ => []
  | .tail f .. => [f]

/-- **The extern's loop is reached only through the extern**: a compiled
block that calls, tail-calls, spawns or takes a code value of the loop
(`isPrintLoop`, anywhere in its body: `reachedE`) is refused,
since the loop is not compiled (the lowering would read the call as the
extern's). -/
def modelDiags (src : String) (p : Prog) : List Diag :=
  let ext := externs p
  let loops := (p.filter isPrintLoop).map (·.name)
  p.flatMap fun d =>
    if ext.any (·.1 == d.name) then [] else
    ((reachedE d.body).filter loops.contains).eraseDups.map fun f =>
      diagAt src d.name [] s!"the output extern's loop '{f}' may be reached only from the extern (in '{d.name}')"

/-- The stack-pointer no-escape check: a no-op on the fragment (see the module
docstring), kept as the place where the check goes. -/
def stackNoEscape (_p : Prog) : List Diag := []

/-! ## Mixed units do not race (provisional `regionHomog`) -/

/-- The cell types behind the shared (`pub`) references anywhere in `t`; for
a buffer, its element type. -/
def sharedCells : Ty → List Ty
  | .ptr μ u | .ptrOpt μ u | .loc μ u =>
      (if μ == .pub then [elem u] else []) ++ sharedCells u
  | .prod a b | .sum a b | .code a b _ => sharedCells a ++ sharedCells b
  | .array _ u => sharedCells u
  | .mu t | .iall t | .iex t | .tex _ t | .refine t _ => sharedCells t
  | _ => []
where
  elem : Ty → Ty
    | .array _ u => u
    | .refine t _ => elem t
    | t => t

/-- `some u` if a shared cell type `u` in `t` holds a mixed unit inline
(`Scc.Obj.inlineMixed`). -/
def homogBad (t : Ty) : Option Ty := (sharedCells t).find? Obj.inlineMixed

def homogMsg (u : Ty) : String :=
  s!"the shared cell type `{Syntax.showType u}` holds a locative inline, which is not supported: " ++
    "its base and offset words live in different regions and a racing access could tear them"

/-- The `regionHomog` diagnostics of a block body: every binding's type in the
checker's context, at the first place it is found. -/
partial def homogE (p : Prog) (src fn : String) (cx : Option Cx) (e : Expr) : List Diag :=
  let kids : List Expr := match e with
    | .let_ _ _ k | .split _ _ _ k | .unpack _ _ _ k | .unpackT _ _ _ k => [k]
    | .ifeq _ _ y n => [y, n]
    | _ => []
  let here := match cx with
    | some c => c.vars.filterMap fun (x, t, _) =>
        (homogBad t).map fun u => diagAt src fn (bindPats x) s!"{homogMsg u} (in '{fn}', binding '{x}')"
    | none => []
  match here with
  | d :: _ => [d]
  | [] => (kids.zipIdx.flatMap fun (k, i) => homogE p src fn (Scope.nth p cx e i) k).take 1

/-- Provisional `regionHomog`: a mixed unit (in the
fragment: a locative) may live in a frame, an argument or an own cell, but not
inline in a shared cell, where a racing reader could pair the base of one
write with the offset of another.  Checked on every signature and every
binding's type.  To be removed when WeakCore's checker has the rule. -/
def regionHomog (src : String) (p : Prog) : List Diag :=
  let ext := externs p
  p.flatMap fun d =>
    let sig := match homogBad d.argTy <|> homogBad d.retTy with
      | some u => [diagAt src d.name [] s!"{homogMsg u} (in the signature of '{d.name}')"]
      | none => []
    if ext.any (·.1 == d.name) || !sig.isEmpty then sig
    else homogE p src d.name (some (Scope.start d)) d.body

/-! ## `Int` addition sites -/

/-- An `Int` addition.  Every site keeps its overflow check; `boundable`
records whether index facts bound the sum (a candidate for elision once
WeakCore proves that index-typed variables hold their index values). -/
structure AddSite where
  fn : String
  x : String
  a : At
  b : At
  boundable : Bool
  line : Nat
  col : Nat
  deriving Repr

/-- The linear form of an `Int` operand, under the checker's context. -/
def atLin (cx : Cx) : At → Option Lin
  | .lit n => some (Lin.ofConst n)
  | .var x => do
      let (_, t, _) ← cx.vars.find? (·.1 == x)
      let rec intIdx : Ty → Option Idx
        | .intS i => some i
        | .refine t _ => intIdx t
        | _ => none
      cx.norm (← intIdx t)
  | .unit => none

/-- Array lengths visible in a type without crossing a binder. -/
partial def arrayLens : Ty → List Idx
  | .array i t => if words t == some 1 then [i] else []
  | .ptr _ t | .loc _ t | .refine t _ => arrayLens t
  | .prod a b => arrayLens a ++ arrayLens b
  | _ => []

/-- Is `a + b` bounded by an array length in scope (by index facts)? -/
def addBounded (cx : Cx) (a b : At) : Bool :=
  match atLin cx a, atLin cx b with
  | some la, some lb =>
      let s := Lin.add la lb
      cx.vars.any fun (_, t, _) =>
        (arrayLens t).any fun L => match cx.norm L with
          | some l => Lin.leB s l
          | none => false
  | _, _ => false

/-- The `Int` additions of a block, following the checker's context. -/
partial def addSitesE (p : Prog) (src fn : String) (cx : Option Cx) (e : Expr) : List AddSite :=
  let kids : List Expr := match e with
    | .let_ _ _ k | .split _ _ _ k | .unpack _ _ _ k | .unpackT _ _ _ k => [k]
    | .ifeq _ _ y n => [y, n]
    | _ => []
  let here := match e with
    | .let_ x (.add a b) _ =>
        let ok := match cx with | some c => addBounded c a b | none => false
        let (l, c) := locate src fn (bindPats x)
        [{ fn, x, a, b, boundable := ok, line := l, col := c }]
    | _ => []
  here ++ (kids.zipIdx.flatMap fun (k, i) => addSitesE p src fn (Scope.nth p cx e i) k)

/-- All `Int` addition sites of the compiled blocks. -/
def addSites (src : String) (p : Prog) : List AddSite :=
  let ext := externs p
  p.flatMap fun d =>
    if ext.any (·.1 == d.name) then []
    else addSitesE p src d.name (some (Scope.start d)) d.body

def showAt : At → String
  | .var x => x | .lit n => toString n | .unit => "()"

def AddSite.render (file : String) (s : AddSite) : String :=
  s!"{file}:{s.line}:{s.col}: checked `+` ({if s.boundable then "boundable by index facts" else "unbounded"}): " ++
    s!"{s.x} = {showAt s.a} + {showAt s.b} in '{s.fn}'"

/-! ## The whole frontend -/

/-- A program that passed the frontend. -/
structure Checked where
  prog : Prog
  entry : Entry
  externs : List (String × Extern)
  adds : List AddSite

/-- Parse, type-check, and check the fragment.  Errors: all diagnostics. -/
def run (src : String) : Except (List Diag) Checked := do
  let p ← (parse src).mapError ([·])
  (typecheck src p).mapError ([·])
  let ds := acceptDiags src p ++ modelDiags src p ++ stackNoEscape p
  if !ds.isEmpty then throw ds
  let hs := regionHomog src p
  if !hs.isEmpty then throw hs
  let entry ← (entryOf src p).mapError ([·])
  pure { prog := p, entry, externs := externs p, adds := addSites src p }

end Scc.Frontend
