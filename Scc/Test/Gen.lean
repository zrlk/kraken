import Scc.Test.RefEval

/-!
# A random program generator for differential testing

`program seed k` is the `k`-th program of the stream `seed`: a well-typed,
single-threaded source text in scc's accepted fragment, with `main(u : Unit)
: Int`.  `batch` writes `n` programs to a directory together with their
reference outcomes (`Scc.Test.RefEval`), for `Scc/Test/diff.sh` to compile,
run and compare.

## What a program contains

* **Helpers** `h0 … hN(a : Int * Int) : Int`: straight-line code with nested
  `if a = b`, calls to lower-numbered helpers (so every call graph is
  acyclic) and `tail` calls to them.
* **Loops** over a `U64` counter, called from `main` only:
  `l·(a : U64 * Int)` (a tail-recursive loop, the counter tested with
  `fcmp eq` and decremented with `fop sub`) and `r·(a : U64 * Int)` (the same
  shape with a non-tail self-call, so the frames stay live).
* **Count-downs** `c·{k}(a : Int[k] * Int)`: a tail loop over an `Int` index,
  `if iv = 0 … else let d = iv - 1` (the checked `Int` `-`).
* **Wide tail loops** `w·(a : U64 * Int)` and `w·x` (nine words): each round
  tail-calls the other, passing more stack words than the caller's own
  argument; they must run in constant stack.
* **Statements**: literals (small, byte-sized, near `2^63`, near `2^64` and
  random 64-bit values, so that sums reach the overflow abort), checked `Int`
  `+`, `Int` `-` where the checker can prove the difference nonnegative
  (see below), `bits`/`bit1` on `Int`, fixed-width words (`cvt`, every
  `fop` including `div`/`rem` by zero and `INT_MIN / -1`, `fop1`, `fcmp`,
  `toInt`), lanes (`asLanes`, `lane`), heap cells (`zero`, `new`, `load`,
  `store`) and arrays (`newBuf`, initialising `xchg b[i]`, then `b[i]` with
  `load`/`store`, and `xchg b[i]`).
* **Object layout** (`layoutStmt`): published `Int` cells, pair cells
  `Int * Ptr pub Int` (a scalar and a reference word, in different regions)
  with their field locatives (`fld`, two words each) loaded and stored
  through, a reference loaded from a field and dereferenced, calls of
  `gl(a : Loc pub Int * Int)` (a locative passed in two argument words), and
  buffers of `Ptr pub Int` or `Loc pub Int` elements filled with `bufInit`
  and read with `load b[i]`.
* **Wide arguments**: `gw(a : ((Loc pub Int * Int) * (Loc pub Int * Int)) *
  (Loc pub Int * Int))` takes nine words, more than either target passes in
  registers (x64 six, AArch64 eight), so some travel on the stack.  It is
  called like `gl` and before a block ends, and blocks sometimes end in
  `tail gw(…)`: from a block
  with fewer argument words that is a call and a return
  (`Lower.lowerExpr`).  The fragment has no scalar-only two-word
  unit, so none is generated.

`Int` `-` needs both operands of known index and a provably nonnegative
difference (CoreTerm's `checkOp`, `.sub`), so the generator tracks each
singleton's index as a sum of index variables plus a constant (`Lin`) and
only subtracts `b` from `a` when `b`'s variables are among `a`'s and `b`'s
constant is at most `a`'s.  Hence scc's saturating `-` never saturates in a
well-typed program; a count-down's `iv - 1` relies on the `iv ≠ 0` branch.

Every generated program is meant to pass the frontend; `batch` records a
rejection as a generator bug.
-/

open CoreLang CoreTerm

namespace Scc.Test.Gen

/-! ## Random numbers and output -/

structure GS where
  /-- splitmix64 state -/
  rng : UInt64
  fresh : Nat := 0
  lines : Array String := #[]
  /-- no function of more than six argument words (`gw`, `w·x`): see `program` -/
  narrow : Bool := false

abbrev GM := StateM GS

/-- splitmix64. -/
def nextU64 : GM UInt64 := modifyGet fun s =>
  let z0 : UInt64 := s.rng + 0x9E3779B97F4A7C15
  let z1 : UInt64 := (z0 ^^^ (z0 >>> 30)) * 0xBF58476D1CE4E5B9
  let z2 : UInt64 := (z1 ^^^ (z1 >>> 27)) * 0x94D049BB133111EB
  (z2 ^^^ (z2 >>> 31), { s with rng := z0 })

/-- Uniform in `[0, n)` (`0` when `n = 0`). -/
def below (n : Nat) : GM Nat := do return (← nextU64).toNat % max n 1

def chance (pct : Nat) : GM Bool := do return (← below 100) < pct

def pick {α : Type} [Inhabited α] (xs : Array α) : GM α := do return xs[← below xs.size]!

def fresh (p : String) : GM String :=
  modifyGet fun s => (s!"{p}{s.fresh}", { s with fresh := s.fresh + 1 })

def emit (ind : Nat) (l : String) : GM Unit :=
  modify fun s => { s with lines := s.lines.push ("".pushn ' ' ind ++ l) }

/-! ## Values -/

/-- A singleton's index: a sum of index variables plus a constant. -/
structure Lin where
  vars : List String
  c : Nat
  deriving Inhabited

def Lin.add (a b : Lin) : Lin := ⟨a.vars ++ b.vars, a.c + b.c⟩

/-- `b ≤ a` coefficient-wise (so `a - b` checks), and the difference. -/
def Lin.sub? (a b : Lin) : Option Lin :=
  if b.c ≤ a.c && b.vars.all (fun x => b.vars.count x ≤ a.vars.count x) then
    some ⟨b.vars.foldl List.erase a.vars, a.c - b.c⟩
  else none

/-- An `Int` value in scope: its name (or literal text) and its index, if it
is a singleton. -/
structure IV where
  n : String
  lin : Option Lin := none
  deriving Inhabited

/-- A literal, biased towards the edges. -/
def genLit : GM Nat := do
  let r ← below 100
  if r < 45 then below 21
  else if r < 60 then below 256
  else if r < 70 then do return 2 ^ 64 - 1 - (← below 8)
  else if r < 78 then do return 2 ^ 63 + (← below 5) - 2
  else if r < 86 then do return 2 ^ (← below 64)
  else if r < 92 then do return 2 ^ 32 + (← below 5) - 2
  else do return (← nextU64).toNat

/-- A small literal (operands of most additions, so that not every program
overflows at once). -/
def genSmall : GM Nat := do
  if ← chance 85 then below 50 else genLit

/-! ## Scopes -/

/-- The kind of a callable loop-like block: a tail loop or a non-tail
recursion over a `U64` counter, or a count-down over an `Int` index. -/
inductive LKind | tailU | recU | cd
  deriving Inhabited, BEq

structure Ctx where
  ints : Array IV := #[]
  /-- fixed-width words: name and type (`U64`, `I64`, `U32`, `U8`, `I8`) -/
  words : Array (String × String) := #[]
  /-- owned `Int` cells -/
  cells : Array String := #[]
  /-- fully initialised `Int` arrays and their lengths -/
  bufs : Array (String × Nat) := #[]
  /-- published `Int` cells (`Ptr pub Int`, copyable) -/
  pubs : Array String := #[]
  /-- field locatives into published pair cells: `Loc pub Int` -/
  locs : Array String := #[]
  /-- field locatives into published pair cells: `Loc pub (Ptr pub Int)` -/
  plocs : Array String := #[]
  /-- buffers of references, fully initialised by `bufInit`: name, length,
  and `true` for `Loc pub Int` elements (`false`: `Ptr pub Int`) -/
  rbufs : Array (String × Nat × Bool) := #[]
  /-- `gl` may be called (not inside `gl` itself) -/
  glOk : Bool := true
  /-- `gw` may be called (not inside `gl` or `gw`) -/
  gwOk : Bool := true
  /-- helpers `h0 … h(helpers-1)` may be called -/
  helpers : Nat := 0
  /-- loop-like blocks that may be called, with `true` for a deep-capable one
  (its body calls no helper) -/
  loops : Array (String × LKind × Bool) := #[]
  deriving Inhabited

def Ctx.addInt (cx : Ctx) (n : String) (lin : Option Lin := none) : Ctx :=
  { cx with ints := cx.ints.push { n, lin } }

/-- An `Int` operand: a variable in scope (mostly) or a literal. -/
def operand (cx : Ctx) (small := true) : GM IV := do
  if cx.ints.isEmpty || (← chance 20) then
    let v ← if small then genSmall else genLit
    return { n := toString v, lin := some ⟨[], v⟩ }
  -- prefer recent values
  if ← chance 50 then
    let k := min cx.ints.size 3
    return cx.ints[cx.ints.size - 1 - (← below k)]!
  pick cx.ints

def wordTys : Array String := #["U64", "I64", "U32", "U8", "I8"]
def unsignedTy (t : String) : Bool := t.startsWith "U"
def fopNames : Array String := #["add", "sub", "mul", "div", "rem", "and", "or", "xor", "shl", "shr"]
def bitsNames : Array String := #["and", "or", "xor", "shl", "shr", "wadd", "wsub", "wmul", "mulhi"]

/-! ## Statements -/

/-- A plain `Int` in scope (not a singleton), if any. -/
def plainInt (cx : Ctx) : GM (Option String) := do
  let ps := cx.ints.filter (·.lin.isNone)
  if ps.isEmpty then return none
  return some (← pick ps).n

/-- The nine argument words of `gw`, bound to a fresh name: three locatives
and three plain `Int`s from scope (`none` if there are none). -/
def gwArg (ind : Nat) (cx : Ctx) : GM (Option String) := do
  if cx.locs.isEmpty || !cx.gwOk || (← get).narrow then return none
  let some a ← plainInt cx | return none
  let some b ← plainInt cx | return none
  let some c ← plainInt cx | return none
  let q1 ← fresh "q"
  let q2 ← fresh "q"
  let q3 ← fresh "q"
  let q12 ← fresh "q"
  let q ← fresh "q"
  emit ind s!"let {q1} = ({← pick cx.locs}, {a})"
  emit ind s!"let {q2} = ({← pick cx.locs}, {b})"
  emit ind s!"let {q3} = ({← pick cx.locs}, {c})"
  emit ind s!"let {q12} = ({q1}, {q2})"
  emit ind s!"let {q} = ({q12}, {q3})"
  return some q

/-- Statements on the object layout: published cells, pair cells mixing a
scalar and a reference, field locatives (two words), calls of `gl` with a
locative, and buffers of reference or locative elements. -/
def layoutStmt (ind : Nat) (cx : Ctx) : GM Ctx := do
  let r ← below 6
  -- with no locative yet, make a pair cell (and its locatives) first
  let r := if (r == 2 || r == 3) && cx.locs.isEmpty then 1 else r
  if r == 0 || cx.pubs.isEmpty then
    -- a published `Int` cell
    let z ← fresh "z"
    let c ← fresh "c"
    let s ← fresh "s"
    let p ← fresh "p"
    emit ind s!"let {z} = zero[Int]"
    emit ind s!"let {c} = new {z}"
    emit ind s!"let {s} = store {c} {(← operand cx).n}"
    emit ind s!"let {p} = publish {c}"
    return { cx with pubs := cx.pubs.push p }
  else if r == 1 || r == 5 then
    -- a pair cell (Int, Ptr pub Int), published, and its two field locatives
    let some a ← plainInt cx | return cx
    let q ← fresh "q"
    let c ← fresh "c"
    let cp ← fresh "p"
    let l0 ← fresh "l"
    let l1 ← fresh "l"
    emit ind s!"let {q} = ({a}, {← pick cx.pubs})"
    emit ind s!"let {c} = new {q}"
    emit ind s!"let {cp} = publish {c}"
    emit ind s!"let {l0} = fld 0 {cp}"
    emit ind s!"let {l1} = fld 1 {cp}"
    return { cx with locs := cx.locs.push l0, plocs := cx.plocs.push l1 }
  else if r == 2 then
    -- through a locative: load, store, or a call of `gl`
    if cx.locs.isEmpty then return cx
    let l ← pick cx.locs
    let k ← below 4
    if k == 0 then
      let v ← fresh "v"
      emit ind s!"let {v} = load {l}"
      return cx.addInt v
    else if k == 1 then
      let s ← fresh "s"
      emit ind s!"let {s} = store {l} {(← operand cx).n}"
      return cx
    if k == 3 && cx.gwOk then
      let some q ← gwArg ind cx | return cx
      let v ← fresh "v"
      emit ind s!"let {v} = gw({q})"
      return cx.addInt v
    let some a ← plainInt cx | return cx
    if !cx.glOk then return cx
    let q ← fresh "q"
    let v ← fresh "v"
    emit ind s!"let {q} = ({l}, {a})"
    emit ind s!"let {v} = gl({q})"
    return cx.addInt v
  else if r == 3 then
    -- through a locative to a reference field
    if cx.plocs.isEmpty then return cx
    let l ← pick cx.plocs
    if ← chance 30 then
      let s ← fresh "s"
      emit ind s!"let {s} = store {l} {← pick cx.pubs}"
      return cx
    let p ← fresh "p"
    let v ← fresh "v"
    emit ind s!"let {p} = load {l}"
    emit ind s!"let {v} = load {p}"
    return { cx.addInt v with pubs := cx.pubs.push p }
  else
    -- buffers of references or locatives
    if cx.rbufs.isEmpty || (← chance 40) then
      let isLoc := !cx.locs.isEmpty && (← chance 70)
      let len := (← below 4) + 1
      let k ← fresh "k"
      let m ← fresh "m"
      let b ← fresh "b"
      emit ind s!"let {k} = {len}"
      emit ind s!"let {m} = nameI {k}"
      emit ind s!"let {b} = newBuf[{if isLoc then "Loc pub Int" else "Ptr pub Int"}] {m}"
      let mut cur := b
      for j in [0:len] do
        let nb ← fresh "b"
        let v ← if isLoc then pick cx.locs else pick cx.pubs
        emit ind s!"let {nb} = bufInit {cur} {j} {v}"
        cur := nb
      return { cx with rbufs := cx.rbufs.push (cur, len, isLoc) }
    let (b, len, isLoc) ← pick cx.rbufs
    let j ← below len
    let e ← fresh (if isLoc then "l" else "p")
    let v ← fresh "v"
    emit ind s!"let {e} = load {b}[{j}]"
    emit ind s!"let {v} = load {e}"
    let cx := cx.addInt v
    return if isLoc then { cx with locs := cx.locs.push e } else { cx with pubs := cx.pubs.push e }

/-- One `let` statement (or a short group) at indentation `ind`. -/
def stmt (ind : Nat) (cx : Ctx) : GM Ctx := do
  let r ← below 112
  if r ≥ 100 then layoutStmt ind cx
  else if r < 6 then
    let v ← fresh "v"
    let l ← genLit
    emit ind s!"let {v} = {l}"
    return cx.addInt v (some ⟨[], l⟩)
  else if r < 26 then
    let a ← operand cx
    let b ← operand cx
    let v ← fresh "v"
    emit ind s!"let {v} = {a.n} + {b.n}"
    return cx.addInt v (do Lin.add (← a.lin) (← b.lin))
  else if r < 36 then
    -- a provably nonnegative difference
    let sing := cx.ints.filter (·.lin.isSome)
    let v ← fresh "v"
    if sing.isEmpty || (← chance 20) then
      let x ← genLit
      let y ← below (x + 1)
      emit ind s!"let {v} = {x} - {y}"
      return cx.addInt v (some ⟨[], x - y⟩)
    let a ← pick sing
    let la := a.lin.get!
    let cands := sing.filter fun b => (la.sub? b.lin.get!).isSome
    let b ← if cands.isEmpty || (← chance 40) then do
        let y ← below (la.c + 1)
        pure { n := toString y, lin := some ⟨[], y⟩ }
      else pick cands
    match la.sub? b.lin.get! with
    | some d =>
        emit ind s!"let {v} = {a.n} - {b.n}"
        return cx.addInt v (some d)
    | none => return cx
  else if r < 44 then
    let a ← operand cx (small := false)
    let b ← operand cx
    let v ← fresh "v"
    emit ind s!"let {v} = bits {← pick bitsNames} {a.n} {b.n}"
    return cx.addInt v
  else if r < 47 then
    let a ← operand cx (small := false)
    let v ← fresh "v"
    emit ind s!"let {v} = bit1 {← pick #["not", "ctz", "popcnt"]} {a.n}"
    return cx.addInt v
  else if r < 62 then
    -- fixed-width words
    let t ← pick wordTys
    let same := cx.words.filter (·.2 == t)
    let w ← fresh "w"
    let k ← below 10
    if same.size < 2 || k < 3 then
      let a ← operand cx (small := false)
      emit ind s!"let {w} = cvt {t} {a.n}"
    else if k < 4 then
      emit ind s!"let {w} = fop1 {← pick #["not", "neg"]} {(← pick same).1}"
    else
      emit ind s!"let {w} = fop {← pick fopNames} {(← pick same).1} {(← pick same).1}"
    let cx := { cx with words := cx.words.push (w, t) }
    if ← chance 50 then
      let v ← fresh "v"
      if unsignedTy t then
        emit ind s!"let {v} = toInt {w}"
      else
        let u ← fresh "w"
        emit ind s!"let {u} = cvt U64 {w}"
        emit ind s!"let {v} = toInt {u}"
      return cx.addInt v
    return cx
  else if r < 67 then
    let t ← pick wordTys
    let same := cx.words.filter (·.2 == t)
    if same.isEmpty then return cx
    let v ← fresh "v"
    emit ind s!"let {v} = fcmp {← pick #["eq", "ne", "lt", "le"]} {(← pick same).1} {(← pick same).1}"
    return cx.addInt v
  else if r < 70 then
    let a ← operand cx (small := false)
    let l ← fresh "w"
    let e ← fresh "w"
    let v ← fresh "v"
    emit ind s!"let {l} = asLanes U8 {a.n}"
    emit ind s!"let {e} = lane {l} {← below 8}"
    emit ind s!"let {v} = toInt {e}"
    return cx.addInt v
  else if r < 78 then
    -- heap cells
    if cx.cells.isEmpty || (← chance 30) then
      let z ← fresh "z"
      let c ← fresh "c"
      let s ← fresh "s"
      let a ← operand cx
      emit ind s!"let {z} = zero[Int]"
      emit ind s!"let {c} = new {z}"
      emit ind s!"let {s} = store {c} {a.n}"
      return { cx with cells := cx.cells.push c }
    let c ← pick cx.cells
    if ← chance 50 then
      let v ← fresh "v"
      emit ind s!"let {v} = load {c}"
      return cx.addInt v
    let s ← fresh "s"
    emit ind s!"let {s} = store {c} {(← operand cx).n}"
    return cx
  else if r < 84 then
    -- arrays
    if cx.bufs.isEmpty || (← chance 30) then
      let len := (← below 4) + 1
      let k ← fresh "k"
      let m ← fresh "m"
      let b ← fresh "b"
      emit ind s!"let {k} = {len}"
      emit ind s!"let {m} = nameI {k}"
      emit ind s!"let {b} = newBuf[Int] {m}"
      for j in [0:len] do
        let o ← fresh "o"
        emit ind s!"let {o} = xchg {b}[{j}] {(← operand cx).n}"
      return { cx with bufs := cx.bufs.push (b, len) }
    let (b, len) ← pick cx.bufs
    let j ← below len
    let k ← below 3
    if k == 0 then
      let v ← fresh "v"
      emit ind s!"let {v} = xchg {b}[{j}] {(← operand cx).n}"
      return cx.addInt v
    -- The locative takes the owned buffer (affine); it is then a cell.
    let l ← fresh "p"
    emit ind s!"let {l} = {b}[{j}]"
    let cx := { cx with bufs := cx.bufs.filter (·.1 != b), cells := cx.cells.push l }
    if k == 1 then
      let v ← fresh "v"
      emit ind s!"let {v} = load {l}"
      return cx.addInt v
    let s ← fresh "s"
    emit ind s!"let {s} = store {l} {(← operand cx).n}"
    return cx
  else if r < 93 then
    if cx.helpers == 0 then return cx
    let a ← operand cx
    let b ← operand cx
    let p ← fresh "q"
    let v ← fresh "v"
    emit ind s!"let {p} = ({a.n}, {b.n})"
    emit ind s!"let {v} = h{← below cx.helpers}({p})"
    return cx.addInt v
  else
    if cx.loops.isEmpty then return cx
    let (f, kd, deep) ← pick cx.loops
    -- mostly short; a block whose body calls no helper is sometimes run deep
    -- enough to grow the stack (16 KiB at first)
    let r ← below 100
    let cnt ← if r < 85 then below 40 else if r < 98 || !deep then below 300 else below 20000
    let a ← operand cx
    let p ← fresh "q"
    let v ← fresh "v"
    match kd with
    | .cd =>
        let t ← fresh "t"
        let tn ← fresh "t"
        emit ind s!"let {t} = {cnt}"
        emit ind s!"let {tn} = nameI {t}"
        emit ind s!"let {p} = ({tn}, {a.n})"
        emit ind s!"let {v} = {f}\{{tn}}({p})"
    | _ =>
        let n ← fresh "w"
        emit ind s!"let {n} = cvt U64 {cnt}"
        emit ind s!"let {p} = ({n}, {a.n})"
        emit ind s!"let {v} = {f}({p})"
    return cx.addInt v

/-- `n` statements. -/
def stmts (ind : Nat) : Nat → Ctx → GM Ctx
  | 0, cx => pure cx
  | n + 1, cx => do stmts ind n (← stmt ind cx)

/-- An `Int` value in scope to return or pass on (recent ones preferred). -/
def result (cx : Ctx) : GM String := do
  if cx.ints.isEmpty then return "0"
  if ← chance 70 then return cx.ints.back!.n
  return (← pick cx.ints).n

/-- A value to return or pass on that depends on several values in scope:
up to three of them combined with checked `+` or wrapping `bits` operations,
so that most of a block's computations reach the exit status. -/
def mixResult (ind : Nat) (cx : Ctx) : GM String := do
  if cx.ints.isEmpty then return "0"
  let mut acc ← result cx
  for _ in [0:(← below 4)] do
    let b ← pick cx.ints
    let v ← fresh "v"
    if ← chance 30 then
      emit ind s!"let {v} = {acc} + {b.n}"
    else
      emit ind s!"let {v} = bits {← pick #["wadd", "wsub", "xor", "wmul"]} {acc} {b.n}"
    acc := v
  return acc

/-- A block: statements, then `ret`, a `tail` call to a helper (when
`tailOk`), or an `if a = b` with two blocks (while `depth > 0`). -/
def block (ind : Nat) (tailOk : Bool) : Nat → Ctx → GM Unit
  | depth, cx => do
    let cx ← stmts ind ((← below 7) + 2) cx
    match depth with
    | d + 1 =>
      -- `if` needs a plain `Int` on one side (CoreTerm's `checkExpr`,
      -- `.ifeq`: two singletons need a recordable equality).
      let plain := cx.ints.filter (·.lin.isNone)
      if !plain.isEmpty && (← chance 35) then
        let a ← pick plain
        -- compare with a value in scope or a small literal
        let b ← if ← chance 50 then operand cx else do pure { n := toString (← below 3) }
        emit ind s!"if {a.n} = {b.n} then"
        block (ind + 2) tailOk d cx
        emit ind "else"
        block (ind + 2) tailOk d cx
        return
    | 0 => pure ()
    -- a call of `gw` (nine argument words) before the block ends
    let cx ← if cx.gwOk && !cx.locs.isEmpty && (← chance 40) then do
        match ← gwArg ind cx with
        | some q => do
          let v ← fresh "v"
          emit ind s!"let {v} = gw({q})"
          pure (cx.addInt v)
        | none => pure cx
      else pure cx
    if tailOk && cx.gwOk && !cx.locs.isEmpty && (← chance 25) then
      if let some q ← gwArg ind cx then
        emit ind s!"tail gw({q})"
        return
    if tailOk && cx.helpers > 0 && (← chance 15) then
      let a ← operand cx
      let b ← operand cx
      let p ← fresh "q"
      emit ind s!"let {p} = ({a.n}, {b.n})"
      emit ind s!"tail h{← below cx.helpers}({p})"
    else
      emit ind s!"ret {← mixResult ind cx}"

/-! ## Blocks -/

def helper (j : Nat) : GM Unit := do
  emit 0 s!"def h{j}(a : Int * Int) : Int ="
  emit 2 "let (x, y) = a"
  block 2 true 2 { ints := #[{ n := "x" }, { n := "y" }], helpers := j }
  emit 0 ""

/-- A tail-recursive loop over a `U64` counter. -/
def loopBlk (f : String) (helpers : Nat) : GM Unit := do
  emit 0 s!"def {f}(a : U64 * Int) : Int ="
  emit 2 "let (i, acc) = a"
  emit 2 "let z = cvt U64 0"
  emit 2 "let c = fcmp eq i z"
  emit 2 "if c = 1 then"
  emit 4 "ret acc"
  emit 2 "else"
  emit 4 "let iv = toInt i"
  let cx ← stmts 4 ((← below 4) + 1) { ints := #[{ n := "acc" }, { n := "iv" }], helpers }
  emit 4 s!"let acc1 = {← mixResult 4 cx} + 0"
  emit 4 "let one = cvt U64 1"
  emit 4 "let i1 = fop sub i one"
  emit 4 "let p = (i1, acc1)"
  emit 4 s!"tail {f}(p)"
  emit 0 ""

/-- A non-tail recursion over a `U64` counter. -/
def recBlk (f : String) (helpers : Nat) : GM Unit := do
  emit 0 s!"def {f}(a : U64 * Int) : Int ="
  emit 2 "let (i, x) = a"
  emit 2 "let z = cvt U64 0"
  emit 2 "let c = fcmp eq i z"
  emit 2 "if c = 1 then"
  emit 4 "ret x"
  emit 2 "else"
  emit 4 "let iv = toInt i"
  emit 4 "let one = cvt U64 1"
  emit 4 "let i1 = fop sub i one"
  let cx ← stmts 4 ((← below 3) + 1) { ints := #[{ n := "x" }, { n := "iv" }], helpers }
  emit 4 s!"let p = (i1, {← mixResult 4 cx})"
  emit 4 s!"let r = {f}(p)"
  let cx ← stmts 4 ((← below 3) + 1) (cx.addInt "r")
  emit 4 s!"ret {← mixResult 4 cx}"
  emit 0 ""

/-- A tail loop whose every round passes more stack words than its blocks'
own arguments: `f(a : U64 * Int)` tail-calls `fx` with nine words (a
`U64` and eight `Int`s, more than either target's registers), and `fx`
tail-calls `f` back.  Tail calls are jumps, so a deep run stays in constant
stack (`IR.StackMap.argAreas`). -/
def wideBlk (f : String) (helpers : Nat) : GM Unit := do
  emit 0 s!"def {f}(a : U64 * Int) : Int ="
  emit 2 "let (i, acc) = a"
  emit 2 "let z = cvt U64 0"
  emit 2 "let c = fcmp eq i z"
  emit 2 "if c = 1 then"
  emit 4 "ret acc"
  emit 2 "else"
  emit 4 "let iv = toInt i"
  let cx ← stmts 4 ((← below 3) + 1) { ints := #[{ n := "acc" }, { n := "iv" }], helpers }
  emit 4 s!"let acc1 = {← mixResult 4 cx} + 0"
  emit 4 "let one = cvt U64 1"
  emit 4 "let i1 = fop sub i one"
  emit 4 "let y1 = (i1, acc1)"
  emit 4 "let y2 = (iv, acc1)"
  emit 4 "let y3 = (acc1, iv)"
  emit 4 "let y4 = (iv, iv)"
  emit 4 "let y12 = (y1, y2)"
  emit 4 "let y34 = (y3, y4)"
  emit 4 "let y5 = (y12, y34)"
  emit 4 "let y = (y5, acc1)"
  emit 4 s!"tail {f}x(y)"
  emit 0 ""
  emit 0 s!"def {f}x(a : (((U64 * Int) * (Int * Int)) * ((Int * Int) * (Int * Int))) * Int) : Int ="
  emit 2 "let (y5, xh) = a"
  emit 2 "let (y12, y34) = y5"
  emit 2 "let (y1, y2) = y12"
  emit 2 "let (y3, y4) = y34"
  emit 2 "let (i, xa) = y1"
  emit 2 "let (xb, xc) = y2"
  emit 2 "let (xd, xe) = y3"
  emit 2 "let (xf, xg) = y4"
  let cx ← stmts 2 ((← below 3) + 1)
    { ints := #["xa", "xb", "xc", "xd", "xe", "xf", "xg", "xh"].map fun n => { n }, helpers }
  emit 2 s!"let acc2 = {← mixResult 2 cx} + 0"
  emit 2 "let q = (i, acc2)"
  emit 2 s!"tail {f}(q)"
  emit 0 ""

/-- A tail loop over an `Int` index, counting down with the checked `-`. -/
def cdBlk (f : String) (helpers : Nat) : GM Unit := do
  emit 0 s!"def {f}\{k}(a : Int[k] * Int) : Int ="
  emit 2 "let (iv, acc) = a"
  emit 2 "if iv = 0 then"
  emit 4 "ret acc"
  emit 2 "else"
  emit 4 "let d = iv - 1"
  emit 4 "let dn = nameI d"
  let cx ← stmts 4 ((← below 4) + 1)
    { ints := #[{ n := "acc" }, { n := "iv", lin := some ⟨["k"], 0⟩ }], helpers }
  emit 4 s!"let acc1 = {← mixResult 4 cx} + 0"
  emit 4 "let q = (dn, acc1)"
  emit 4 s!"tail {f}\{dn}(q)"
  emit 0 ""

/-- `gl`: takes a locative (two words) and an `Int`, reads the cell, writes
the `Int` to it, and returns a mix of the old value and its own statements. -/
def glBlk : GM Unit := do
  emit 0 "def gl(a : Loc pub Int * Int) : Int ="
  emit 2 "let (l, x) = a"
  emit 2 "let v = load l"
  emit 2 "let s = store l x"
  let cx ← stmts 2 ((← below 3) + 1)
    { ints := #[{ n := "v" }, { n := "x" }], locs := #["l"], glOk := false, gwOk := false }
  emit 2 s!"ret {← mixResult 2 cx}"
  emit 0 ""

/-- `gw`: nine argument words (three locatives, three `Int`s); reads and
writes through the locatives and returns a mix of its values. -/
def gwBlk : GM Unit := do
  emit 0 "def gw(a : ((Loc pub Int * Int) * (Loc pub Int * Int)) * (Loc pub Int * Int)) : Int ="
  emit 2 "let (gxy, gz) = a"
  emit 2 "let (gx, gy) = gxy"
  emit 2 "let (gk0, ga0) = gx"
  emit 2 "let (gk1, ga1) = gy"
  emit 2 "let (gk2, ga2) = gz"
  emit 2 "let gv0 = load gk0"
  emit 2 "let gs0 = store gk1 ga0"
  emit 2 "let gv2 = load gk2"
  let cx ← stmts 2 ((← below 3) + 1)
    { ints := #[{ n := "gv0" }, { n := "gv2" }, { n := "ga0" }, { n := "ga1" }, { n := "ga2" }],
      locs := #["gk0", "gk1", "gk2"], gwOk := false }
  emit 2 s!"ret {← mixResult 2 cx}"
  emit 0 ""

/-- The whole program text. -/
def genProgram : GM Unit := do
  let narrow := (← get).narrow
  glBlk
  if !narrow then gwBlk
  let nh ← below 4
  for j in [0:nh] do helper j
  let nl ← below 4
  let mut loops : Array (String × LKind × Bool) := #[]
  for j in [0:nl] do
    let kd ← below 4
    -- a deep-capable block calls no helper, so that a deep run stays cheap
    -- for the reference
    let deep ← chance 30
    let hs := if deep then 0 else nh
    if kd == 0 then
      loopBlk s!"l{j}" hs
      loops := loops.push (s!"l{j}", .tailU, deep)
    else if kd == 1 then
      recBlk s!"r{j}" hs
      loops := loops.push (s!"r{j}", .recU, deep)
    else if kd == 2 then
      cdBlk s!"c{j}" hs
      loops := loops.push (s!"c{j}", .cd, deep)
    else if narrow then
      loopBlk s!"l{j}" hs
      loops := loops.push (s!"l{j}", .tailU, deep)
    else
      wideBlk s!"w{j}" hs
      loops := loops.push (s!"w{j}", .tailU, deep)
  emit 0 "def main(u : Unit) : Int ="
  let v0 ← fresh "v"
  let l0 ← genSmall
  emit 2 s!"let {v0} = {l0}"
  block 2 false 3 (({ helpers := nh, loops } : Ctx).addInt v0 (some ⟨[], l0⟩))

/-- The `k`-th program of stream `seed`.  With `narrow`, no function takes
more than six argument words: `gw` is neither defined nor called and a wide
tail loop pair (`w·`, `w·x`) is a plain tail loop instead.  Such functions
spill stack-passed arguments, which `placeOK` does not certify yet (x64's
`fnOk1` `spills`), so `diff.sh --narrow` samples certifiable programs.  The
default stream is unchanged. -/
def program (seed k : Nat) (narrow : Bool := false) : String :=
  let s0 : GS := { rng := (seed * 1000003 + k).toUInt64 * 0x2545F4914F6CDD1D + 1, narrow }
  let ((), s) := genProgram.run s0
  s!"-- generated: seed {seed}, program {k}\n" ++ "\n".intercalate s.lines.toList ++ "\n"

/-! ## Batches -/

/-- `NAME` padded: `g0007`. -/
def progName (k : Nat) : String :=
  let d := toString k
  "g" ++ "".pushn '0' (4 - min 4 d.length) ++ d

/-- Write programs `0 … n-1` of stream `seed` to `dir` as `gNNNN.w`, and
`dir/ref.txt` with one line per program: `NAME CODE OUTCOME`, where `CODE` is
the exit status the binary must produce (`-` for none: rejected, stuck, or out
of fuel or of work, see `RefEval.workBudget`).  Prints a summary. -/
def batch (dir : String) (n seed : Nat) (fuel : Nat := 5_000_000) (work : Nat := RefEval.workBudget)
    (narrow : Bool := false) : IO Unit := do
  IO.FS.createDirAll dir
  let mut out := #[]
  let mut rejected := 0
  let mut ovf := 0
  let mut noVerdict := 0
  for k in [0:n] do
    let name := progName k
    let src := program seed k narrow
    IO.FS.writeFile s!"{dir}/{name}.w" src
    match Frontend.run src with
    | .error ds =>
        rejected := rejected + 1
        out := out.push s!"{name} - rejected {"; ".intercalate (ds.map (·.render s!"{name}.w"))}"
    | .ok c =>
        let o := RefEval.runProg c.prog .arm fuel work
        if o matches .overflow _ then ovf := ovf + 1
        let code := match o.code with | some v => toString v | none => "-"
        if o.code.isNone then noVerdict := noVerdict + 1
        out := out.push s!"{name} {code} {o.render}"
  IO.FS.writeFile s!"{dir}/ref.txt" ("\n".intercalate out.toList ++ "\n")
  let kind := if narrow then " narrow" else ""
  IO.println s!"generated {n}{kind} programs (seed {seed}): {rejected} rejected, {ovf} overflow aborts, \
    {noVerdict} without a verdict"

end Scc.Test.Gen

namespace Scc.Test.Gen

-- The first programs of a stream pass the frontend.
#guard (List.range 20).all fun k => (Frontend.run (program 11 k)).toBool

-- A long allocating loop stops on the work budget, without a verdict (it
-- used to hang `batch dir 300 25`).
#guard match Frontend.run (program 25 256) with
  | .ok c => (RefEval.runProg c.prog .arm 5_000_000 matches .work _)
  | .error _ => false

-- `narrow` leaves the default stream byte-identical: the hash of programs
-- 0 … 39 of streams 11 and 70, as before `narrow` existed.
#guard (List.range 40).foldl (fun h k => mixHash h (program 11 k).hash) 7 = 448067727662517775
#guard (List.range 40).foldl (fun h k => mixHash h (program 70 k).hash) 7 = 13625200795582986081

-- Narrow programs pass the frontend and have no function of more than six argument words.
#guard (List.range 20).all fun k =>
  let p := program 11 k (narrow := true)
  (Frontend.run p).toBool && !(p.splitOn "gw(").length > 1 && !(p.splitOn "x(a :").length > 1

end Scc.Test.Gen
