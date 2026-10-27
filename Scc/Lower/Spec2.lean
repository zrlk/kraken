import Scc.Lower.Spec1
import Scc.Frontend
import Scc.PrintModel

/-!
# The fragment `Accepted2`: `Accepted1` with the setup block's buffer, lane stores and output

`Accepted2` widens `Accepted1` (`Scc/Lower/Spec1.lean`) by exactly what
`hello1L.w` needs: a setup block that allocates a buffer of one-word elements
and stores lane words into it, the output extern on the owned slice (its
WeakCore model, the `emit` loop, given textually), and a `main` that takes
the setup block's result. Every `Accepted1` program is in `Accepted2`
(`accepted2_of_accepted1`).

* **The output extern** (`isPrintExt`): a block named `print` with one index
  parameter, the owned-slice signature (`Frontend.printOwnSig`) and result
  `Unit` is the extern (as `Frontend.externOf` decides). It is admitted only
  if it is **textually** `printExtD` (`declIs`, which is equality:
  `declIs_eq`; its body the call of the loop), and
  then the program must also contain the loop `printLoopD`, textually,
  declared before it. scc does not compile either: the runtime's
  `scc_rt_print` stands for them, which is a proof obligation, not part of
  this statement. With the extern present, user code may call neither
  `printL` nor `print` except through the extern call below.
* **The setup block**: when `main` takes `S * Ptr pub Void`, the program has
  the setup block `rodata(u : Unit) : S`, `S` with a runtime layout
  (`Frontend.words`) and not a bare locative (`shapeOf S ≠ .loc`), no type
  or index parameters (`setup2`); otherwise a
  block named `rodata` is an ordinary block (`Int → Int`), so a setup block
  `rodata(u : Unit) : S` is present exactly when `main` takes its result.
  The setup block is run by the runtime: no code calls it, it has no output,
  and it is the only block that allocates.
* **`main`** returns `Int` and takes `Unit` (no setup block) or
  `S * Ptr pub Void` (with the setup block of result `S`).
* **Bodies** (`body2`) are `body1`'s trees, with also:
  - **in the setup block only**:
    - `let x = newBuf[τ] n`, `n` **known before run time** with
      `1 ≤ n < 2 ^ 28`: a literal, or a variable bound by `let`s of atoms and
      `nameI` to one (`constOf`; `hello1L.w` writes `let two = 2`,
      `let m = nameI two`, `newBuf[LanesU8] m`), `τ` a one-word element type
      (`elem2`: `Int`, `fix sg w`, `lanes sg w`);
    - `let x = xchg b[i] v`, `b` bound by a `newBuf` of `n` elements in the
      same body (and not rebound since), `i` a **literal** below `n`, `v` an
      atom;
  - `let x = asLanes sg w a`, `let x = nameI a`, `let x = (a, b)`,
    `let x = pack a at w : τ`, `let (x, y) = a`, `let <i, x> = unpack a`;
  - outside the setup block, `let x = print{i}(a)`: the extern call, with
    exactly one index argument, the extern declared before the caller.
* Atoms are as in `Accepted1` (variables in scope, literals below `2 ^ 63`).
* **Coherent immediates** (`immsCoherent2`), as in `Accepted1` but word by
  word: the lowering keeps a literal as an immediate through `let`s of
  atoms, `nameI`, `asLanes`, pairs, `pack`, `split` and `unpack`, so the walk
  tracks each variable's literal words in its source word layout (`LitV`,
  `opLit`; the setup block's result is a `simpleTy`, so that its layout is
  `shapeOf`'s), over every block's body (the extern's and the loop's
  included). The keys
  (`termKey2`) omit the types of `newBuf`, `asLanes` and `pack` and the index
  names of calls: two points sharing a key must agree on their literals, so
  a coarser key only rejects more (`imms2Of_sub_immsOf` is the gate that
  makes this a theorem). On `Accepted1` programs `imms2Of` is `imms1Of`
  (`imms2Of_eq_imms1Of`).
* **Layouts** (`layoutOk2`), a check on the source alone: every `pack`'s
  operand has the word layout of the package's type (`LitV.erase`,
  `shapeOf`; a locative, `newBuf`'s result, is its own kind of word,
  `LitV.loc`, so that it does not stand for a scalar), that type a
  `simpleTy` with the lowering's layout (`Obj.valWords`, which a coupled
  index package lacks); every `asLanes` operand is one word.
  The lowering places a package's words by its type and a lane word by its
  one operand word, so on a program that passes the check the walk's word
  `k` is the lowering's word `k`.
* **No refined products** (`refOk2`): no block's parameter or result type
  and no `pack`'s type has a refinement of a product inside it (`noRefProd`,
  through products and index packages). The source's `let (x, y) = a` steps
  on a literal product only, while the lowering also splits a refined one
  (`prodOf`), so a refined product would let the target run where the source
  is stuck.
* **Calls and returns agree with the walk** (`callsOk2`): at every point of
  every block, a call's operand has its callee's parameter layout
  (`argShape`) and a `ret`'s operand the block's result layout (`shapeOf`),
  literals dropped. The lowering passes a call's words by its operand's
  layout, and the walk gives a call's result the callee's declared layout
  (`retShape`), so on a program that passes the check the two agree; without
  it, an operand of another kind (a buffer's locative passed to an `Int`
  parameter) reaches source operations that are stuck on it (`if`).
* **A locative is paired with its buffer's count** (`countsOk2`): in every
  block but the extern and its loop, a pair whose left part is a locative
  (`LitV.loc`) pairs a variable bound by a `newBuf` of `n` elements in the
  same body (and not rebound since) with a value known to be `n`
  (`constOf`). The extern reads `8 · m` bytes from a slice whose count word
  is `m` and the lowering writes `min(n, 8 · m)` of them, while the source's
  loop stops at the buffer's end; a larger count would let the target read
  past the buffer where the source is stuck. An alias of the buffer, a
  locative taken out of a pair, or a pair built outside the setup block is
  rejected.
* **`main` does not read its thread word** (`setupArgOk2`): with a setup
  block, `main`'s body starts by splitting its parameter into two distinct
  variables, and neither the parameter nor the second one occurs in the rest
  of the body. That word is the main thread's `Ptr pub Void`: the runtime
  passes its control block's address, allocated at run time, while the
  source start leaves it an arbitrary word (`setupInit`); a branch on it, a
  sum with it or returning it would make the proof pick, at the start, the
  address the runtime will allocate later.

Not in the fragment: allocation or buffer stores outside the setup block;
`newBuf` with a count computed at run time, a count of 0 or `≥ 2 ^ 28`, or elements of
`Ptr`, `Loc`, products or refinements; `xchg` with a variable or
out-of-bounds index; `loadAt`, `lane`, `emit` and `tail` outside the
extern's loop; the other buffer operations; `new`, `publish`, `intoRgn`,
regions, protocol words, atomics; `spawn`, `park`/`unpark`; `case`,
`ifnull`, `parity`, `cas`; literals at or above `2 ^ 63`; output in the setup
block; the `print` extern with the public-slice signature or any other body;
a slice whose count is not its buffer's; any use of `main`'s thread word.
-/

open CoreLang CoreTerm

namespace Scc.Lower

/-! ## The extern's model

`printExtD`, `printLoopD` and `declIs` (equality, `declIs_eq`) are
`Scc/PrintModel.lean`'s, shared with the frontend. -/

open Scc.Frontend (ownSliceTy printLoopD printExtD declIs declIs_eq)

theorem printOwnSig_eq : Frontend.printOwnSig = some ownSliceTy := rfl

/-- **A block that is the output extern** (as `Frontend.externOf` decides,
for the owned slice). -/
def isPrintExt (d : Decl) : Bool :=
  d.name == "print" && d.idx.length == 1 && d.tparams.isEmpty && some d.argTy == Frontend.printOwnSig &&
    d.retTy == .unit

/-! ## Bodies -/

/-- **A one-word element type** for `newBuf`: `Int`, `fix sg w`, `lanes sg w`. -/
def elem2 : Ty → Bool
  | .int | .fix _ _ | .lanes _ _ => true
  | _ => false

/-- What an `Accepted2` body may use besides its scope: `alloc`, it is the
setup block's (buffers and lane stores); `earlier`, the blocks declared
before it; `excl`, the reserved names no ordinary call may name (`rodata`
with a setup block, `print` and `printL` with the extern); `ext`, the
program has the extern. -/
structure Cx2 where
  alloc : Bool
  earlier : List String
  excl : List String
  ext : Bool

/-- An ordinary callee: `callee1`, not reserved. -/
def callee2 (cx : Cx2) (g : String) : Bool := callee1 cx.earlier g && !cx.excl.contains g

/-- Drop the buffer bound to `x` (rebound). -/
def unbuf (x : String) (bufs : List (String × Nat)) : List (String × Nat) := bufs.filter (·.1 != x)

/-- The value of an atom known before run time: a literal, or a variable
bound (in `cs`) to one. -/
def constOf (cs : List (String × Nat)) : At → Option Nat
  | .lit k => some k
  | .var y => cs.lookup y
  | _ => none

/-- Bind `x` to the known value `o` in `cs` (dropping any older binding). -/
def bindC (x : String) (o : Option Nat) (cs : List (String × Nat)) : List (String × Nat) :=
  match o with
  | some k => (x, k) :: unbuf x cs
  | none => unbuf x cs

/-- **An `Accepted2` body** (see the module docstring): `cs` the variables
bound so far to a value known before run time (by `let x = a` or
`let x = nameI a` of a literal or of such a variable), `bufs` the buffers
bound so far with their element counts, `scope` the variables bound so far.
A buffer's size is such a known value `n`, `1 ≤ n < 2 ^ 28`, and a lane
store's index a literal below its buffer's size. -/
def body2 (cx : Cx2) (cs bufs : List (String × Nat)) (scope : List String) : Expr → Bool
  | .let_ x (.atom a) e => atom1 scope a && body2 cx (bindC x (constOf cs a) cs) (unbuf x bufs) (x :: scope) e
  | .let_ x (.add a b) e => atom1 scope a && atom1 scope b && body2 cx (unbuf x cs) (unbuf x bufs) (x :: scope) e
  | .let_ x (.sub a b) e => atom1 scope a && atom1 scope b && body2 cx (unbuf x cs) (unbuf x bufs) (x :: scope) e
  | .let_ x (.call g is a ts) e =>
      (if cx.ext && g == "print" then cx.earlier.contains "print" && is.length == 1 && ts.isEmpty
        else callee2 cx g && is.isEmpty && ts.isEmpty) &&
        atom1 scope a && body2 cx (unbuf x cs) (unbuf x bufs) (x :: scope) e
  | .let_ x (.nameI a) e => atom1 scope a && body2 cx (bindC x (constOf cs a) cs) (unbuf x bufs) (x :: scope) e
  | .let_ x (.newBuf n τ) e =>
      cx.alloc && atom1 scope n && elem2 τ &&
        (match constOf cs n with
          | some k => decide (1 ≤ k) && decide (k < 2 ^ 28) &&
              body2 cx (unbuf x cs) ((x, k) :: unbuf x bufs) (x :: scope) e
          | none => false)
  | .let_ x (.asLanes _ _ a) e => atom1 scope a && body2 cx (unbuf x cs) (unbuf x bufs) (x :: scope) e
  | .let_ x (.xchgAt (.var b) (.lit i) v) e =>
      cx.alloc && (match bufs.lookup b with | some n => decide (i < n) | none => false) && atom1 scope v &&
        body2 cx (unbuf x cs) (unbuf x bufs) (x :: scope) e
  | .let_ x (.pair a b) e => atom1 scope a && atom1 scope b && body2 cx (unbuf x cs) (unbuf x bufs) (x :: scope) e
  | .let_ x (.pack a _ _) e => atom1 scope a && body2 cx (unbuf x cs) (unbuf x bufs) (x :: scope) e
  | .split a x y e =>
      atom1 scope a && body2 cx (unbuf y (unbuf x cs)) (unbuf y (unbuf x bufs)) (y :: x :: scope) e
  | .unpack a i x e =>
      atom1 scope a && body2 cx (unbuf x (unbuf i cs)) (unbuf x (unbuf i bufs)) (x :: scope) e
  | .ifeq a b yes no =>
      atom1 scope a && atom1 scope b && body2 cx cs bufs scope yes && body2 cx cs bufs scope no
  | .ret a => atom1 scope a
  | _ => false

/-! ## Word layouts -/

/-- **The literal words of a value**, in its source word layout: no word
(`nil`, `Unit`), one word with its literal if the lowering keeps it as an
immediate (`leaf`), one locative word, which has no literal (`loc`), or a
pair (`node`). -/
inductive LitV where
  | nil
  | leaf (o : Option Nat)
  | loc
  | node (l r : LitV)
  deriving DecidableEq

/-- The words of a value, left to right, each with its literal if any. -/
def LitV.words : LitV → List (Option Nat)
  | .nil => []
  | .leaf o => [o]
  | .loc => [none]
  | .node l r => l.words ++ r.words

/-- The literal of a one-word value. -/
def LitV.one : LitV → Option Nat
  | .leaf o => o
  | _ => none

/-- **A type's word layout**, no literal: `Unit` no word, a pair its parts,
a refinement or an index package its body, a locative one locative word, any
other type of `simpleTy` one word (as TermRun's values and
`Frontend.words`). -/
def shapeOf : Ty → LitV
  | .unit | .void => .nil
  | .prod a b => .node (shapeOf a) (shapeOf b)
  | .refine t _ | .iex t => shapeOf t
  | .loc _ _ => .loc
  | _ => .leaf none

/-- A layout with its literals dropped. -/
def LitV.erase : LitV → LitV
  | .nil => .nil
  | .leaf _ => .leaf none
  | .loc => .loc
  | .node l r => .node l.erase r.erase

/-- The types whose word layout `shapeOf` gives exactly: one-word scalars,
pointers and locatives, `Unit`, and pairs, refinements and index packages of
them. -/
def simpleTy : Ty → Bool
  | .unit | .void | .int | .intS _ | .fix _ _ | .lanes _ _ | .ptr _ _ | .loc _ _ => true
  | .prod a b => simpleTy a && simpleTy b
  | .refine t _ | .iex t => simpleTy t
  | _ => false

/-! ## Blocks and programs -/

/-- The variables in scope at a body: the parameter, unless it is `Unit`. -/
def params2 (d : Decl) : List String :=
  if d.argTy == .unit then [] else [d.arg]

/-- **The setup block's result** `S`, when `main` takes `S * Ptr pub Void`. -/
def setupOf (p : Prog) : Option Ty :=
  match p.find? (·.name == "main") with
  | some d => match d.argTy with
    | .prod s (.ptr .pub .void) => some s
    | _ => none
  | none => none

/-- **The program has the output extern.** -/
def hasPrint (p : Prog) : Bool := p.any isPrintExt

/-- The names no ordinary call may use. -/
def reserved (setup : Option Ty) (ext : Bool) : List String :=
  (if setup.isSome then ["rodata"] else []) ++ (if ext then ["print", "printL"] else [])

/-- **The setup block** of result `s`: `rodata(u : Unit) : s`, `s` with a
runtime layout and not a bare locative (`main`'s argument pairs `s` with the
thread word, and a pair whose left layout is `.loc` is a slice with its
count), an `Accepted2` body with buffers, no output
(`earlier.erase "print"`). -/
def setup2 (earlier : List String) (excl : List String) (ext : Bool) (s : Ty) (d : Decl) : Bool :=
  d.tparams.isEmpty && d.idx.isEmpty && d.argTy == .unit && d.retTy == s && (Frontend.words s).isSome &&
    (simpleTy s && shapeOf s != .loc) &&
    body2 ⟨true, earlier.erase "print", excl, ext⟩ [] [] [] d.body

/-- **`main`**: `main(u : Unit) : Int` without a setup block, or
`main(a : S * Ptr pub Void) : Int` with the setup block of result `S`. -/
def main2 (earlier : List String) (excl : List String) (ext : Bool) (setup : Option Ty) (d : Decl) : Bool :=
  d.tparams.isEmpty && d.idx.isEmpty && d.retTy == .int &&
    (match setup with
      | some s => d.argTy == .prod s (.ptr .pub .void)
      | none => d.argTy == .unit) &&
    body2 ⟨false, earlier, excl, ext⟩ [] [] (params2 d) d.body

/-- An ordinary block `f(x : Int) : Int`, an `Accepted2` body without buffers. -/
def plain2 (earlier : List String) (excl : List String) (ext : Bool) (d : Decl) : Bool :=
  d.tparams.isEmpty && d.idx.isEmpty && d.retTy == .int && d.argTy == .int &&
    body2 ⟨false, earlier, excl, ext⟩ [] [] (params2 d) d.body

/-- **An `Accepted2` block**, `earlier` the blocks declared before it: the
extern (textually `printExtD`, after the loop), the loop (textually
`printLoopD`, with the extern present), `main`, the setup block (named
`rodata`, when `main` takes its result), or an ordinary block. -/
def decl2 (earlier : List String) (setup : Option Ty) (ext : Bool) (d : Decl) : Bool :=
  let excl := reserved setup ext
  if isPrintExt d then declIs d printExtD && earlier.contains "printL"
  else if ext && d.name == "printL" then declIs d printLoopD
  else if d.name == "main" then main2 earlier excl ext setup d
  else match setup with
    | some s => if d.name == "rodata" then setup2 earlier excl ext s d else plain2 earlier excl ext d
    | none => plain2 earlier excl ext d

/-- The blocks of `p` in order, each `decl2` with the blocks before it. -/
def decls2 (earlier : List String) (setup : Option Ty) (ext : Bool) : Prog → Bool
  | [] => true
  | d :: ds => decl2 earlier setup ext d && decls2 (d.name :: earlier) setup ext ds

/-- **With a setup block, it is there**: when `main` takes `S * Ptr pub
Void`, a block `rodata` exists (`decl2` checks its shape). -/
def setupPresent (p : Prog) : Bool :=
  match setupOf p with
  | some _ => p.any (·.name == "rodata")
  | none => true

/-! ## Coherent immediates -/

/-- A term's key for `Accepted2`: `termKey` on `body1`'s constructors, one
tag per new constructor with its bound names and atoms (types and index
names omitted; see the module docstring). -/
def termKey2 : Expr → List (Nat × String × Nat)
  | .let_ x (.atom a) e => (3, x, 0) :: atKey a ++ termKey2 e
  | .let_ x (.add a b) e => (4, x, 0) :: atKey a ++ atKey b ++ termKey2 e
  | .let_ x (.sub a b) e => (5, x, 0) :: atKey a ++ atKey b ++ termKey2 e
  | .let_ x (.call g _ a _) e => (6, x, 0) :: (7, g, 0) :: atKey a ++ termKey2 e
  | .let_ x (.nameI a) e => (12, x, 0) :: atKey a ++ termKey2 e
  | .let_ x (.newBuf n _) e => (13, x, 0) :: atKey n ++ termKey2 e
  | .let_ x (.asLanes _ _ a) e => (14, x, 0) :: atKey a ++ termKey2 e
  | .let_ x (.xchgAt b i v) e => (15, x, 0) :: atKey b ++ atKey i ++ atKey v ++ termKey2 e
  | .let_ x (.pair a b) e => (16, x, 0) :: atKey a ++ atKey b ++ termKey2 e
  | .let_ x (.pack a _ _) e => (17, x, 0) :: atKey a ++ termKey2 e
  | .split a x y e => (18, x, 0) :: (19, y, 0) :: atKey a ++ termKey2 e
  | .unpack a i x e => (20, x, 0) :: (21, i, 0) :: atKey a ++ termKey2 e
  | .ifeq a b y n => (8, "", (termKey2 y).length) :: atKey a ++ atKey b ++ termKey2 y ++ termKey2 n
  | .ret a => (9, "", 0) :: atKey a
  | _ => [(10, "", 0)]

/-- An atom's literal words, given the bindings `lits`: a variable's (one
word, none, if unbound), a literal's, `()`'s none. -/
def litAt (lits : List (String × LitV)) : At → LitV
  | .var x => (lits.lookup x).getD (.leaf none)
  | .lit n => .leaf (some n)
  | .unit => .nil

/-- A call's result layout: the callee's declared result type. -/
def retShape (p : Prog) (g : String) : LitV :=
  match p.find? (·.name == g) with
  | some d => shapeOf d.retTy
  | none => .leaf none

/-- **The literal words of a `let`'s value**, as the lowering builds its
operands (`lowerOp`): an atom, `nameI` and `pack` copy their operand's,
`asLanes` its one word's, a pair concatenates its parts', a call has its
result's layout with no literal, `newBuf` a locative, and every other
operation one word with no literal (`xchg`'s old element, sums, loads). -/
def opLit (p : Prog) (lits : List (String × LitV)) : Op → LitV
  | .atom a | .nameI a | .pack a _ _ => litAt lits a
  | .asLanes _ _ a => .leaf (litAt lits a).one
  | .pair a b => .node (litAt lits a) (litAt lits b)
  | .call g _ _ _ => retShape p g
  | .newBuf _ _ => .loc
  | _ => .leaf none

/-- The points of a body with the literal words of the variables bound
there (`opLit`); `split` takes a pair's parts, `unpack` its package's words
(its index name is no term variable). -/
def litWalk2 (p : Prog) (lits : List (String × LitV)) : Expr → List (Expr × List (String × LitV))
  | .let_ x op e => (.let_ x op e, lits) :: litWalk2 p ((x, opLit p lits op) :: lits) e
  | .split a x y e =>
      (.split a x y e, lits) ::
        litWalk2 p (match litAt lits a with
          | .node l r => (y, r) :: (x, l) :: lits
          | _ => (y, .leaf none) :: (x, .leaf none) :: lits) e
  | .unpack a i x e => (.unpack a i x e, lits) :: litWalk2 p ((x, litAt lits a) :: lits) e
  | .ifeq a b y n => (.ifeq a b y n, lits) :: (litWalk2 p lits y ++ litWalk2 p lits n)
  | t => [(t, lits)]

/-- The points of every block of `p`, its parameter with its type's layout
and no literal. -/
def litWalks2 (p : Prog) : List (Expr × List (String × LitV)) :=
  p.flatMap fun d => litWalk2 p ((params2 d).map (·, shapeOf d.argTy)) d.body

/-- Word `k` of `x`'s literal words in `lits`. -/
def wordLit (lits : List (String × LitV)) (x : String) (k : Nat) : Option Nat :=
  ((lits.lookup x).bind fun v => v.words[k]?).join

/-- **The immediate table of an `Accepted2` program**: at term `t`, word `k`
of `x`, its literal at the first point with `t`'s key that has one. A
function of the source program only. -/
def imms2Of (p : Prog) (t : Expr) (x : String) (k : Nat) : Option Nat :=
  (litWalks2 p).findSome? fun q => if termKey2 q.1 == termKey2 t then wordLit q.2 x k else none

/-- **Coherent immediates** for `Accepted2`: at every point, every word of
every variable with a literal has that literal in `imms2Of p`. -/
def immsCoherent2 (p : Prog) : Bool :=
  (litWalks2 p).all fun q => q.2.all fun b =>
    (List.range b.2.words.length).all fun k =>
      match wordLit q.2 b.1 k with
      | some n => imms2Of p q.1 b.1 k == some n
      | none => true

/-- **Layouts agree with the walk** (see the module docstring): at every
point, a `pack`'s operand has its type's word layout, the type a `simpleTy`
with the lowering's layout (`Obj.valWords`), and an `asLanes` operand is one
word. A check on the source alone. -/
def layoutOk2 (p : Prog) : Bool :=
  (litWalks2 p).all fun q => match q.1 with
    | .let_ _ (.pack a _ τ) _ => (litAt q.2 a).erase == shapeOf τ && simpleTy τ && (Scc.Obj.valWords τ).isSome
    | .let_ _ (.asLanes _ _ a) _ => match litAt q.2 a with | .leaf _ => true | _ => false
    | _ => true

/-- **No refinement of a product** in `t`, through products, refinements and
index packages: the source splits a literal product only. -/
def noRefProd : Ty → Bool
  | .prod a b => noRefProd a && noRefProd b
  | .refine t _ => (prodOf t).isNone && noRefProd t
  | .iex t => noRefProd t
  | _ => true

/-- **No refined products** (see the module docstring): every block's
parameter and result type, and every `pack`'s type, without a refinement of
a product. -/
def refOk2 (p : Prog) : Bool :=
  p.all (fun d => noRefProd d.argTy && noRefProd d.retTy) &&
    (litWalks2 p).all fun q => match q.1 with
      | .let_ _ (.pack _ _ τ) _ => noRefProd τ
      | _ => true

/-- A call's operand layout: the callee's declared parameter type's. -/
def argShape (p : Prog) (g : String) : LitV :=
  match p.find? (·.name == g) with
  | some d => shapeOf d.argTy
  | none => .leaf none

/-- **Calls and returns agree with the walk** (see the module docstring): at
every point of every block, a call's operand has its callee's parameter
layout and a `ret`'s operand the block's result layout, literals dropped. -/
def callsOk2 (p : Prog) : Bool :=
  p.all fun d => (litWalk2 p ((params2 d).map (·, shapeOf d.argTy)) d.body).all fun q =>
    match q.1 with
    | .let_ _ (.call g _ a _) _ => (litAt q.2 a).erase == argShape p g
    | .ret a => (litAt q.2 a).erase == shapeOf d.retTy
    | _ => true

/-- A pair is fine for `countsOk2`, with known values `cs`, buffers `bufs`
and literal words `lits`: if its left part is a locative, that part is a
buffer of `bufs` and its right part a value known to be the buffer's count. -/
def pairOk (cs bufs : List (String × Nat)) (lits : List (String × LitV)) : Op → Bool
  | .pair l r =>
      match litAt lits l with
      | .loc =>
          match l with
          | .var y =>
              match bufs.lookup y with
              | some n => constOf cs r == some n
              | none => false
          | _ => false
      | _ => true
  | _ => true

/-- The known values after `let x = op`, as `body2` tracks them. -/
def csAfter (x : String) (cs : List (String × Nat)) : Op → List (String × Nat)
  | .atom a | .nameI a => bindC x (constOf cs a) cs
  | _ => unbuf x cs

/-- The buffers after `let x = op`, as `body2` tracks them. -/
def bufsAfter (x : String) (cs bufs : List (String × Nat)) : Op → List (String × Nat)
  | .newBuf n _ =>
      match constOf cs n with
      | some k => (x, k) :: unbuf x bufs
      | none => unbuf x bufs
  | _ => unbuf x bufs

/-- A body's pairs are `pairOk`, walking it with its known values, buffers
and literal words (as `body2` and `litWalk2`). -/
def countsB (p : Prog) : List (String × Nat) → List (String × Nat) → List (String × LitV) → Expr → Bool
  | cs, bufs, lits, .let_ x op e =>
      pairOk cs bufs lits op && countsB p (csAfter x cs op) (bufsAfter x cs bufs op) ((x, opLit p lits op) :: lits) e
  | cs, bufs, lits, .split a x y e =>
      countsB p (unbuf y (unbuf x cs)) (unbuf y (unbuf x bufs))
        (match litAt lits a with
          | .node l r => (y, r) :: (x, l) :: lits
          | _ => (y, .leaf none) :: (x, .leaf none) :: lits) e
  | cs, bufs, lits, .unpack a i x e =>
      countsB p (unbuf x (unbuf i cs)) (unbuf x (unbuf i bufs)) ((x, litAt lits a) :: lits) e
  | cs, bufs, lits, .ifeq _ _ y n => countsB p cs bufs lits y && countsB p cs bufs lits n
  | _, _, _, _ => true

/-- **A locative is paired with its buffer's count** (see the module
docstring): every block but the extern and its loop (fixed text, `declIs`)
is `countsB` from its parameter, with its type's layout. -/
def countsOk2 (p : Prog) : Bool :=
  p.all fun d => isPrintExt d || (hasPrint p && d.name == "printL") ||
    countsB p [] [] ((params2 d).map (·, shapeOf d.argTy)) d.body

/-- Whether `x` occurs as an atom in `e` (by `termKey2`, which records every
atom of a `body2` term; a rebinding of `x` is not looked through, so this
may over-report, which only rejects more). -/
def mentions (x : String) (e : Expr) : Bool := (termKey2 e).contains (0, x, 0)

/-- `main`'s body splits its parameter into two distinct variables first,
and then mentions neither the parameter nor the second one. -/
def mainArgOk (d : Decl) : Bool :=
  match d.body with
  | .split (.var a) x y e => a == d.arg && x != y && !mentions y e && !mentions a e
  | _ => false

/-- **`main` does not read its thread word** (see the module docstring):
with a setup block, `main` is `mainArgOk`. -/
def setupArgOk2 (p : Prog) : Bool :=
  match setupOf p with
  | some _ => p.all fun d => d.name != "main" || mainArgOk d
  | none => true

/-- **The fragment `Accepted2`** (see the module docstring): distinct block
names, one of them `main`, every block `decl2` in program order, the setup
block present when `main` takes its result, coherent immediates, layouts
that agree with the walk, no refined products, calls and returns that
agree with the walk, every locative paired with its buffer's count, and
`main` not reading its thread word. -/
def Accepted2 (p : Prog) : Bool :=
  (p.map (·.name)).Nodup && p.any (·.name == "main") && decls2 [] (setupOf p) (hasPrint p) p &&
    setupPresent p && immsCoherent2 p && layoutOk2 p && refOk2 p && callsOk2 p &&
    countsOk2 p && setupArgOk2 p

/-- **A body ends, on every path, in a call returning its result or a
`print` then a literal**: `let x = call g … in ret b` (a call or `print`,
which lowers from a call) with `b` the result `x` itself, or a literal
after `print` only, reached through `let`s, `split`s and `unpack`s and into
both branches of an `ifeq`. A bare `ret` leaf, a call returning anything
else, and every other construct are rejected. A literal after another
callee is rejected: at the exit the held callee's `ret` may read a
variable whose word no register then holds, whereas `print`'s `ret ()`
reads none. The output extern is told apart from a plain block named
`print` by its one index (`body2`: plain callees take none). -/
def heldRetOk : Expr → Bool
  | .let_ x (.call g is _ _) (.ret b) =>
    match b with
    | .lit _ => g == "print" && is.length == 1
    | .var y => y == x
    | .unit => false
  | .let_ _ _ e => heldRetOk e
  | .split _ _ _ e => heldRetOk e
  | .unpack _ _ _ e => heldRetOk e
  | .ifeq _ _ y n => heldRetOk y && heldRetOk n
  | _ => false

/-- **`main`'s body ends, on every path, in a call returning its result or
a `print` then a literal** (`heldRetOk`; true without a `main`). A proof-coverage
condition, not a semantic restriction: `main`'s `ret` is reached with the
callee's `ret` held one frame up through the return tail, which the
proof covers exactly when the frame's continuation reads nothing but the
call's result (`HeldTail`); a bare `ret` leaf would also meet the
consumer's `W2.noRet` at `(ret k, [])`. -/
def mainRetOk (p : Prog) : Bool :=
  match p.find? (·.name == "main") with
  | some d => heldRetOk d.body
  | none => true

end Scc.Lower

/-! ## `Accepted1` is in `Accepted2` -/

namespace Scc.Lower

/-- An `Accepted1` body is an `Accepted2` body, with no reserved names and
no extern, for any known values and buffers. -/
theorem body2_of_body1 (al : Bool) (E : List String) (e : Expr) :
    ∀ (cs bufs : List (String × Nat)) (scope : List String),
    body1 E scope e = true → body2 ⟨al, E, [], false⟩ cs bufs scope e = true := by
  induction e with
  | let_ x op e ih =>
    intro cs bufs scope h
    cases op <;> simp only [body1, body2, callee2, Bool.and_eq_true, Bool.false_and,
      Bool.false_eq_true, ite_false, List.contains_nil, Bool.not_false, Bool.and_true] at h ⊢
    · exact ⟨h.1, ih _ _ _ h.2⟩
    · exact ⟨h.1, ih _ _ _ h.2⟩
    · exact ⟨h.1, ih _ _ _ h.2⟩
    · exact ⟨h.1, ih _ _ _ h.2⟩
  | ifeq a b y n ihy ihn =>
    intro cs bufs scope h
    simp only [body1, body2, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨h.1.1.1, h.1.1.2⟩, ihy _ _ _ h.1.2⟩, ihn _ _ _ h.2⟩
  | ret a => intro cs bufs scope h; simpa [body1, body2] using h
  | _ => intro cs bufs scope h; simp [body1] at h

/-- On an `Accepted1` body, `termKey2` is `termKey`. -/
theorem termKey2_of_body1 (E : List String) (e : Expr) :
    ∀ scope, body1 E scope e = true → termKey2 e = termKey e := by
  induction e with
  | let_ x op e ih =>
    intro scope h
    cases op <;> simp only [body1, Bool.and_eq_true, Bool.false_eq_true] at h
    all_goals simp only [termKey2, termKey]
    · rw [ih _ h.2]
    · rw [ih _ h.2]
    · rw [ih _ h.2]
    · rw [ih _ h.2]
  | ifeq a b y n ihy ihn =>
    intro scope h
    simp only [body1, Bool.and_eq_true] at h
    simp only [termKey2, termKey, ihy _ h.1.2, ihn _ h.2]
  | ret a => intro _ _; rfl
  | _ => intro scope h; simp [body1] at h

/-- A literal binding of `litWalk` as `litWalk2`'s: one word. -/
def toLV (b : String × Option Nat) : String × LitV := (b.1, .leaf b.2)

theorem lookup_map_toLV (x : String) :
    ∀ lits : List (String × Option Nat), (lits.map toLV).lookup x = (lits.lookup x).map .leaf
  | [] => rfl
  | (y, o) :: l => by
    simp only [List.map_cons, toLV, List.lookup_cons]
    cases x == y
    · exact lookup_map_toLV x l
    · rfl

theorem litAt_map_toLV (lits : List (String × Option Nat)) {a : At} (ha : a ≠ .unit) :
    litAt (lits.map toLV) a = .leaf (litOf lits a) := by
  cases a with
  | var x =>
    simp only [litAt, litOf, lookup_map_toLV]
    cases lits.lookup x <;> rfl
  | lit n => rfl
  | unit => exact absurd rfl ha

theorem atom1_ne_unit {scope : List String} {a : At} (h : atom1 scope a = true) : a ≠ .unit := by
  rintro rfl; simp [atom1, atom0] at h

/-- The result layout of a call in a program whose blocks all return `Int`. -/
theorem retShape_int {p : Prog} (hret : ∀ d ∈ p, d.retTy = .int) (g : String) : retShape p g = .leaf none := by
  unfold retShape
  cases hf : p.find? (·.name == g) with
  | none => rfl
  | some d => simp [hret d (List.mem_of_find?_eq_some hf), shapeOf]

/-- On an `Accepted1` body (in a program whose blocks return `Int`),
`litWalk2` is `litWalk` with one-word literal bindings, and every point is
an `Accepted1` body. -/
theorem litWalk2_of_body1 {p : Prog} (hret : ∀ d ∈ p, d.retTy = .int) (E : List String) (e : Expr) :
    ∀ scope lits, body1 E scope e = true →
      litWalk2 p (lits.map toLV) e = (litWalk lits e).map (fun q => (q.1, q.2.map toLV)) ∧
        ∀ r ∈ litWalk lits e, ∃ s, body1 E s r.1 = true := by
  induction e with
  | let_ x op e ih =>
    intro scope lits h
    have h' := h
    cases op <;> simp only [body1, Bool.and_eq_true, Bool.false_eq_true] at h
    · rename_i a
      have hl := ih _ ((x, litOf lits a) :: lits) h.2
      refine ⟨?_, ?_⟩
      · simp only [litWalk2, litWalk, opLit, List.map_cons]
        rw [litAt_map_toLV lits (atom1_ne_unit h.1)]
        exact congrArg _ hl.1
      · intro r hr
        simp only [litWalk, List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact ⟨scope, h'⟩
        · exact hl.2 r hr
    all_goals
      have hl := ih _ ((x, none) :: lits) h.2
      refine ⟨?_, ?_⟩
      · simp only [litWalk2, litWalk, opLit, List.map_cons, retShape_int hret]
        exact congrArg _ hl.1
      · intro r hr
        simp only [litWalk, List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact ⟨scope, h'⟩
        · exact hl.2 r hr
  | ifeq a b y n ihy ihn =>
    intro scope lits h
    have h' := h
    simp only [body1, Bool.and_eq_true] at h
    obtain ⟨hy, hpy⟩ := ihy _ lits h.1.2
    obtain ⟨hn, hpn⟩ := ihn _ lits h.2
    refine ⟨by simp only [litWalk2, litWalk, hy, hn, List.map_cons, List.map_append], ?_⟩
    intro r hr
    simp only [litWalk, List.mem_cons, List.mem_append] at hr
    rcases hr with rfl | hr | hr
    · exact ⟨scope, h'⟩
    · exact hpy r hr
    · exact hpn r hr
  | ret a =>
    intro scope lits h
    exact ⟨rfl, by intro r hr; simp only [litWalk, List.mem_singleton] at hr; subst hr; exact ⟨scope, h⟩⟩
  | _ => intro scope lits h; simp [body1] at h

/-- Word `k` of a one-word literal binding. -/
theorem wordLit_map_toLV (lits : List (String × Option Nat)) (x : String) (k : Nat) :
    wordLit (lits.map toLV) x k = if k = 0 then (lits.lookup x).join else none := by
  simp only [wordLit, lookup_map_toLV]
  cases lits.lookup x with
  | none => split <;> rfl
  | some o => cases k <;> simp [LitV.words]

/-- An `Accepted1` block: `main` takes `Unit`, every other block `Int`. -/
theorem decl1_argTy {E : List String} {d : Decl} (h : decl1 E d = true) :
    (d.name = "main" → d.argTy = .unit) ∧ (d.name ≠ "main" → d.argTy = .int) := by
  simp only [decl1, Bool.and_eq_true] at h
  obtain ⟨⟨-, hm⟩, -⟩ := h
  refine ⟨fun hn => ?_, fun hn => ?_⟩
  · have hb : (d.name == "main") = true := beq_iff_eq.mpr hn
    simpa [hb] using hm
  · have hb : (d.name == "main") = false := beq_eq_false_iff_ne.mpr hn
    simpa [hb] using hm

theorem decl1_argTy' {E : List String} {d : Decl} (h : decl1 E d = true) : d.argTy = .unit ∨ d.argTy = .int := by
  by_cases hn : d.name = "main"
  · exact .inl ((decl1_argTy h).1 hn)
  · exact .inr ((decl1_argTy h).2 hn)

theorem params2_eq {d : Decl} (h : d.argTy = .unit ∨ d.argTy = .int) : params2 d = params1 d := by
  rcases h with h | h <;> simp [params2, params1, h]

theorem isPrintExt_false {d : Decl} (h : d.argTy = .unit ∨ d.argTy = .int) : isPrintExt d = false := by
  have hne : (some d.argTy == Frontend.printOwnSig) = false := by
    rw [printOwnSig_eq]; rcases h with h | h <;> rw [h] <;> decide
  simp [isPrintExt, hne]

/-- The blocks of an `Accepted1` program are `decl1` with some `earlier`. -/
theorem decl1_of_decls1 : ∀ {E : List String} {p : Prog}, decls1 E p = true → ∀ d ∈ p, ∃ E', decl1 E' d = true
  | _, [], _, d, hd => absurd hd List.not_mem_nil
  | E, d' :: ds, h, d, hd => by
    simp only [decls1, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨E, h.1⟩
    · exact decl1_of_decls1 h.2 d hd

/-- `decls1` is `decls2` without a setup block or the extern. -/
theorem decls2_of_decls1 : ∀ {E : List String} {p : Prog}, decls1 E p = true → decls2 E none false p = true
  | _, [], _ => rfl
  | E, d :: ds, h => by
    simp only [decls1, Bool.and_eq_true] at h
    obtain ⟨hd, hds⟩ := h
    have ha := decl1_argTy' hd
    have hb : body1 E (params1 d) d.body = true := by
      simp only [decl1, Bool.and_eq_true] at hd; exact hd.2
    have hb2 := body2_of_body1 false E d.body [] [] _ hb
    rw [← params2_eq ha] at hb2
    simp only [decls2, decl2, reserved, isPrintExt_false ha, Option.isSome_none, Bool.false_eq_true,
      ite_false, List.nil_append, Bool.false_and, Bool.and_eq_true]
    refine ⟨?_, decls2_of_decls1 hds⟩
    have hd' := hd
    simp only [decl1, Bool.and_eq_true, beq_iff_eq] at hd'
    obtain ⟨⟨⟨⟨ht, hi⟩, hr⟩, -⟩, -⟩ := hd'
    by_cases hn : d.name = "main"
    · have hbn : (d.name == "main") = true := beq_iff_eq.mpr hn
      simp [hbn, main2, ht, hi, hr, (decl1_argTy hd).1 hn, hb2]
    · have hbn : (d.name == "main") = false := beq_eq_false_iff_ne.mpr hn
      simp [hbn, plain2, ht, hi, hr, (decl1_argTy hd).2 hn, hb2]

theorem setupOf_none {p : Prog} (h : decls1 [] p = true) : setupOf p = none := by
  unfold setupOf
  cases hf : p.find? (·.name == "main") with
  | none => rfl
  | some d =>
    have hm := List.mem_of_find?_eq_some hf
    have hn : d.name = "main" := by simpa using List.find?_some hf
    obtain ⟨E, hE⟩ := decl1_of_decls1 h d hm
    simp [(decl1_argTy hE).1 hn]

theorem hasPrint_false {p : Prog} (h : decls1 [] p = true) : hasPrint p = false := by
  unfold hasPrint
  rw [List.any_eq_false]
  intro d hd
  obtain ⟨E, hE⟩ := decl1_of_decls1 h d hd
  simp [isPrintExt_false (decl1_argTy' hE)]

theorem findSome_congr {α β : Type} {f g : α → Option β} :
    ∀ {L : List α}, (∀ q ∈ L, f q = g q) → L.findSome? f = L.findSome? g
  | [], _ => rfl
  | a :: L, h => by
    simp only [List.findSome?_cons, h a List.mem_cons_self,
      findSome_congr (L := L) fun q hq => h q (List.mem_cons_of_mem a hq)]

theorem flatMap_congr' {α β : Type} {f g : α → List β} :
    ∀ {L : List α}, (∀ a ∈ L, f a = g a) → L.flatMap f = L.flatMap g
  | [], _ => rfl
  | a :: L, h => by
    simp only [List.flatMap_cons, h a List.mem_cons_self,
      flatMap_congr' (L := L) fun q hq => h q (List.mem_cons_of_mem a hq)]

/-- The blocks of an `Accepted1` program return `Int`. -/
theorem retTy_of_decls1 {p : Prog} (h : decls1 [] p = true) : ∀ d ∈ p, d.retTy = .int := by
  intro d hd
  obtain ⟨E, hE⟩ := decl1_of_decls1 h d hd
  simp only [decl1, Bool.and_eq_true, beq_iff_eq] at hE
  exact hE.1.1.2

/-- **An `Accepted1` program's walk for `Accepted2`** is its `Accepted1`
walk with one-word literal bindings, at points whose `termKey2` is their
`termKey`. -/
theorem litWalks2_of_decls1 {p : Prog} (h : decls1 [] p = true) :
    litWalks2 p = (litWalks p).map (fun q => (q.1, q.2.map toLV)) ∧
      ∀ q ∈ litWalks p, termKey2 q.1 = termKey q.1 := by
  have hret := retTy_of_decls1 h
  have hd : ∀ d ∈ p, litWalk2 p ((params2 d).map (·, shapeOf d.argTy)) d.body =
        (litWalk ((params1 d).map (·, none)) d.body).map (fun q => (q.1, q.2.map toLV)) ∧
      ∀ q ∈ litWalk ((params1 d).map (·, none)) d.body, termKey2 q.1 = termKey q.1 := by
    intro d hdp
    obtain ⟨E, hE⟩ := decl1_of_decls1 h d hdp
    have hb : body1 E (params1 d) d.body = true := by
      simp only [decl1, Bool.and_eq_true] at hE; exact hE.2
    obtain ⟨hw, hpts⟩ := litWalk2_of_body1 hret E d.body _ ((params1 d).map (·, none)) hb
    have hpar : (params2 d).map (·, shapeOf d.argTy) = ((params1 d).map (·, none)).map toLV := by
      rcases decl1_argTy' hE with ha | ha <;> simp [params2, params1, ha, shapeOf, toLV]
    refine ⟨by rw [hpar, hw], fun q hq => ?_⟩
    obtain ⟨s, hs⟩ := hpts q hq
    exact termKey2_of_body1 E q.1 s hs
  refine ⟨?_, ?_⟩
  · unfold litWalks2 litWalks
    rw [List.map_flatMap]
    exact flatMap_congr' fun d hdp => (hd d hdp).1
  · intro q hq
    simp only [litWalks, List.mem_flatMap] at hq
    obtain ⟨d, hdp, hq⟩ := hq
    exact (hd d hdp).2 q hq

/-- **On an `Accepted1` program, `imms2Of` is `imms1Of`** at every term
whose `termKey2` is its `termKey` (every point of its walk:
`litWalks2_of_decls1`). -/
theorem imms2Of_eq_imms1Of {p : Prog} (h : Accepted1 p = true) {t : Expr} (ht : termKey2 t = termKey t)
    (x : String) (k : Nat) : imms2Of p t x k = imms1Of p t x k := by
  simp only [Accepted1, Bool.and_eq_true] at h
  obtain ⟨hw, hk⟩ := litWalks2_of_decls1 h.1.2
  simp only [imms2Of, imms1Of, hw, List.findSome?_map, ht]
  by_cases hk0 : k = 0
  · simp only [hk0, ite_true]
    exact findSome_congr fun r hr => by simp [Function.comp, hk r hr, wordLit_map_toLV]
  · simp only [hk0, ite_false]
    rw [List.findSome?_eq_none_iff]
    intro r _
    simp [Function.comp, wordLit_map_toLV, hk0]

/-- **An `Accepted1` program's layouts agree with the walk**: no point of
its walk is a `pack` or an `asLanes` (`termKey` has no key for either, so
`termKey2` would differ from it there). -/
theorem layoutOk2_of_decls1 {p : Prog} (h : decls1 [] p = true) : layoutOk2 p = true := by
  obtain ⟨hw, hk⟩ := litWalks2_of_decls1 h
  simp only [layoutOk2, hw, List.all_eq_true, List.mem_map]
  rintro _ ⟨⟨t, l⟩, hq, rfl⟩
  have ht := hk _ hq
  dsimp only at ht ⊢
  split
  · simp [termKey2, termKey] at ht
  · simp [termKey2, termKey] at ht
  · rfl

/-- **An `Accepted1` program has no refined products**: its blocks take
`Unit` or `Int` and return `Int`, and its walk has no `pack`. -/
theorem refOk2_of_decls1 {p : Prog} (h : decls1 [] p = true) : refOk2 p = true := by
  have hret := retTy_of_decls1 h
  obtain ⟨hw, hk⟩ := litWalks2_of_decls1 h
  simp only [refOk2, Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun d hd => ?_, ?_⟩
  · obtain ⟨E, hE⟩ := decl1_of_decls1 h d hd
    rcases decl1_argTy' hE with ha | ha <;> simp [ha, hret d hd, noRefProd]
  · simp only [hw, List.mem_map]
    rintro _ ⟨⟨t, l⟩, hq, rfl⟩
    have ht := hk _ hq
    dsimp only at ht ⊢
    split
    · simp [termKey2, termKey] at ht
    · rfl

/-- **An `Accepted1` program's calls and returns agree with the walk**: every
operand is one word, a callee (never `main`) takes `Int`, and every block
returns `Int`. -/
theorem callsOk2_of_decls1 {p : Prog} (h : decls1 [] p = true) : callsOk2 p = true := by
  have hret := retTy_of_decls1 h
  have harg : ∀ g, g ≠ "main" → argShape p g = .leaf none := by
    intro g hg
    unfold argShape
    cases hf : p.find? (·.name == g) with
    | none => rfl
    | some d =>
      have hn : d.name = g := by simpa using List.find?_some hf
      obtain ⟨E, hE⟩ := decl1_of_decls1 h d (List.mem_of_find?_eq_some hf)
      simp [(decl1_argTy hE).2 (hn ▸ hg), shapeOf]
  simp only [callsOk2, List.all_eq_true]
  intro d hdp q hq
  obtain ⟨E, hE⟩ := decl1_of_decls1 h d hdp
  have hb : body1 E (params1 d) d.body = true := by
    simp only [decl1, Bool.and_eq_true] at hE; exact hE.2
  obtain ⟨hw, hpts⟩ := litWalk2_of_body1 hret E d.body _ ((params1 d).map (·, none)) hb
  have hpar : (params2 d).map (·, shapeOf d.argTy) = ((params1 d).map (·, none)).map toLV := by
    rcases decl1_argTy' hE with ha | ha <;> simp [params2, params1, ha, shapeOf, toLV]
  rw [hpar, hw, List.mem_map] at hq
  obtain ⟨⟨t, l⟩, hr, rfl⟩ := hq
  obtain ⟨s, hs⟩ := hpts _ hr
  dsimp only at hs ⊢
  split
  · rename_i g _ a _ _
    simp only [body1, callee1, Bool.and_eq_true, bne_iff_ne, ne_eq] at hs
    rw [litAt_map_toLV l (atom1_ne_unit hs.1.2), harg g hs.1.1.1.1.2]
    rfl
  · rename_i a
    simp only [body1] at hs
    rw [litAt_map_toLV l (atom1_ne_unit hs), hret d hdp]
    rfl
  · rfl

/-- An `Accepted1` body has no pair: `countsB` holds of it whatever is
tracked. -/
theorem countsB_of_body1 (p : Prog) (E : List String) (e : Expr) :
    ∀ (cs bufs : List (String × Nat)) (lits : List (String × LitV)) (scope : List String),
    body1 E scope e = true → countsB p cs bufs lits e = true := by
  induction e with
  | let_ x op e ih =>
    intro cs bufs lits scope h
    cases op <;> simp only [body1, Bool.and_eq_true, Bool.false_eq_true] at h
    all_goals simp only [countsB, pairOk, Bool.true_and]; exact ih _ _ _ _ h.2
  | ifeq a b y n ihy ihn =>
    intro cs bufs lits scope h
    simp only [body1, Bool.and_eq_true] at h
    simp only [countsB, ihy _ _ _ _ h.1.2, ihn _ _ _ _ h.2, Bool.and_self]
  | ret a => intro _ _ _ _ _; rfl
  | _ => intro cs bufs lits scope h; simp [body1] at h

/-- **An `Accepted1` program pairs nothing**: `countsOk2` holds of it. -/
theorem countsOk2_of_decls1 {p : Prog} (h : decls1 [] p = true) : countsOk2 p = true := by
  simp only [countsOk2, List.all_eq_true, Bool.or_eq_true]
  intro d hdp
  obtain ⟨E, hE⟩ := decl1_of_decls1 h d hdp
  have hb : body1 E (params1 d) d.body = true := by
    simp only [decl1, Bool.and_eq_true] at hE; exact hE.2
  exact .inr (countsB_of_body1 p E d.body _ _ _ _ hb)

/-- **An `Accepted1` program has no setup block**: `setupArgOk2` holds of
it. -/
theorem setupArgOk2_of_decls1 {p : Prog} (h : decls1 [] p = true) : setupArgOk2 p = true := by
  simp [setupArgOk2, setupOf_none h]

/-- **Every `Accepted1` program is in `Accepted2`**: its blocks take `Unit`
or `Int`, so it has neither a setup block nor the extern, and `body2`,
`termKey2` and `litWalk2` agree with `body1`, `termKey` and `litWalk` on
its bodies, which have no `pack` or `asLanes` for `layoutOk2` to check. -/
theorem accepted2_of_accepted1 {p : Prog} (h : Accepted1 p = true) : Accepted2 p = true := by
  have h1 := h
  simp only [Accepted1, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hnd, hm⟩, hds⟩, hc⟩ := h
  obtain ⟨hw, hk⟩ := litWalks2_of_decls1 hds
  have hc2 : immsCoherent2 p = true := by
    simp only [immsCoherent, List.all_eq_true] at hc
    simp only [immsCoherent2, hw, List.all_eq_true]
    intro qq hqq bb hbb k hkr
    rw [List.mem_map] at hqq
    obtain ⟨q, hq, rfl⟩ := hqq
    rw [List.mem_map] at hbb
    obtain ⟨b, hb, rfl⟩ := hbb
    simp only [toLV, LitV.words, List.length_singleton, List.mem_range] at hkr
    have hk0 : k = 0 := by omega
    subst hk0
    have := hc q hq b hb
    simp only [wordLit_map_toLV, ite_true, toLV] at this ⊢
    split
    · rename_i n hn
      rw [hn] at this
      rw [imms2Of_eq_imms1Of h1 (hk q hq)]; exact this
    · rfl
  simp only [Accepted2, hnd, hm, setupOf_none hds, hasPrint_false hds, decls2_of_decls1 hds, setupPresent,
    hc2, layoutOk2_of_decls1 hds, refOk2_of_decls1 hds, callsOk2_of_decls1 hds,
    countsOk2_of_decls1 hds, setupArgOk2_of_decls1 hds, Bool.and_self]

end Scc.Lower
