import WeakCore.CoreLang
import Scc.Config

/-!
# The object layout: regions, the layout map, headers and locatives

The bipartite layout of WeakCore's GC design, as scc lowers
it; `Scc/LAYOUT.md` is the prose version and lists the open items.

* `regE t = (n, m, ext)`: `n` scalar words, `m` trace (reference) words, and
  the number of target words beyond the model's width `wc` (one
  recursion, so `n + m = wc + ext`).  Defined on every closed type with a
  width, sums included (sums only for the width-law test: they are not in the
  accepted fragment).
* `slots t s0 t0`: the layout map `φ_t` on the fragment's types: for each word
  of a value of type `t`, in value order, its region (`true` = trace) and its
  index in that region, the value's regions starting at `s0`/`t0`.  A value
  in registers, frames and arguments is its words in model order with every
  locative expanded to two words `(base, offset)`; `φ_t` is applied only where
  the value meets memory.
* An object at `base` keeps its scalar word `i` at `base + 8·i` and its trace
  word `j` at `base − traceBias − 8·j` (the trace region grows down from the
  base, so a locative's addresses do not depend on the enclosing object's
  `m`); one header word (`header0`, `Scc.ObjLayout`) describes it.
* A locative is `(base, offset)`; the offset word packs the pointee's start in
  both regions as byte offsets (`offWord`): scalar offset in the low 32 bits,
  trace offset in the high 32.  A `Loc` type names only the pointee, not the
  enclosing object, so the model offset alone could not be dereferenced.
-/

open CoreLang

namespace Scc.Obj

/-! ## `reg`, with the extra target words -/

mutual

/-- `(n, m, ext)` of a closed type; `none` for
types with no value width (`array`, type variables). -/
def regE : Ty → Option (Nat × Nat × Nat)
  | .unit | .void | .tok _ _ | .tok2 _ _ _ _ | .tokE _ _ _ | .share _ | .cap _ _ => some (0, 0, 0)
  | .int | .intS _ | .fix _ _ | .lanes _ _ | .code _ _ _ => some (1, 0, 0)
  | .word _ P => some (if P.ghost then (0, 0, 0) else (1, 0, 0))
  | .word2 _ _ | .epair _ _ => some (2, 0, 0)
  | .ptr _ _ | .ptrOpt _ _ | .tid => some (0, 1, 0)
  -- Device handles have no layout: the front end refuses device types.
  | .opq _ => none
  | .loc _ _ => some (1, 1, 1)
  | .prod a b => do
      let (na, ma, ea) ← regE a
      let (nb, mb, eb) ← regE b
      pure (na + nb, ma + mb, ea + eb)
  | .sum a b => do
      let (n1, m1) ← armMax a
      let (n2, m2) ← armMax b
      let mn := max n1 n2
      let mm := max m1 m2
      match (Ty.sum a b).tier with
      -- One shared trace word; a `Loc` arm's offset word beside it.
      | .niche => pure (mn, 1, mn)
      -- Tag and scalar payloads in the scalar region, references in the trace
      -- region: the unit spans both when an arm has a reference.
      | .wide => pure (1 + mn, mm, mn + mm - 1)
      | .boxed => pure (0, 1, 0)
  | .array _ _ | .tvar _ => none
  | .mu t | .iall t | .iex t | .tex _ t | .refine t _ => regE t

/-- The largest `(n, m)` over the arms of a (nested) sum. -/
def armMax : Ty → Option (Nat × Nat)
  | .sum a b => do
      let (n1, m1) ← armMax a
      let (n2, m2) ← armMax b
      pure (max n1 n2, max m1 m2)
  | t => do let (n, m, _) ← regE t; pure (n, m)

end

/-- `(n, m)` of a closed type. -/
def reg (t : Ty) : Option (Nat × Nat) := (regE t).map fun (n, m, _) => (n, m)

/-- Does a value of type `t` contain, inline, a **mixed unit**: a
single-copy-atomic unit with both a scalar and a trace word (a locative, a
niche sum with a `Loc` arm, a wide sum with a reference arm, a coupled package
with both kinds of word)?  Products are not units; what lies behind
a reference is another cell. -/
def inlineMixed : Ty → Bool
  | .loc _ _ => true
  | .prod a b => inlineMixed a || inlineMixed b
  | t@(.sum _ _) =>
      t.tier != .boxed && match reg t with | some (n, m) => n > 0 && m > 0 | none => false
  | .iex b =>
      inlineMixed b || (b.countI 0 ≥ 2 && match reg b with | some (n, m) => n > 0 && m > 0 | none => false)
  | .tex _ b =>
      inlineMixed b || (b.countT 0 ≥ 2 && match reg b with | some (n, m) => n > 0 && m > 0 | none => false)
  | .refine t _ | .iall t | .mu t => inlineMixed t
  | _ => false

/-! ## The layout map on the accepted fragment -/

/-- Is `t` a type-coupled or index-coupled package of two model words (one
16-byte granule, not in the fragment; as `Scc.Frontend.words`)? -/
def coupledPair : Ty → Bool
  | t@(.iex b) => b.countI 0 ≥ 2 && t.rawWords == some 2
  | t@(.tex _ b) => b.countT 0 ≥ 2 && t.rawWords == some 2
  | _ => false

/-- The layout map `φ_t` (see the module docstring): for each word of a value
of type `t`, in value order, `(isTrace, index in its region)`, with the
value's regions starting at scalar index `s` and trace index `r`.  `none` off
the fragment's types. -/
def slots : Ty → Nat → Nat → Option (List (Bool × Nat))
  | .unit, _, _ | .void, _, _ => some []
  | .int, s, _ | .intS _, s, _ | .fix _ _, s, _ | .lanes _ _, s, _ => some [(false, s)]
  | .ptr _ _, _, r | .tid, _, r => some [(true, r)]
  | .loc _ _, s, r => some [(true, r), (false, s)]
  | .prod a b, s, r => do
      let la ← slots a s r
      let lb ← slots b (s + la.countP (!·.1)) (r + la.countP (·.1))
      pure (la ++ lb)
  | .refine t _, s, r | .iall t, s, r | .mu t, s, r => slots t s r
  | t@(.iex b), s, r | t@(.tex _ b), s, r => if coupledPair t then none else slots b s r
  | _, _, _ => none

/-- Words of a value of type `t` in registers (`n + m`). -/
def valWords (t : Ty) : Option Nat := (slots t 0 0).map (·.length)

/-- `(n, m)` of a fragment type, from its layout map. -/
def regOf (t : Ty) : Option (Nat × Nat) :=
  (slots t 0 0).map fun l => (l.countP (!·.1), l.countP (·.1))

/-- Which words of a value of type `t` are trace words (for the stack maps). -/
def traceMask (t : Ty) : Option (List Bool) := (slots t 0 0).map (·.map (·.1))

/-! ## Addresses, locatives and headers -/

/-- The byte distance from an object's base to its trace word 0, downwards:
the trace region ends at `base − 8` with the header before it, or at
`base − 16` with the header at `base − 8`. -/
def traceBias (o : ObjLayout) : Int := if o.headerBeforeTrace then 8 else 16

/-- The two halves of a locative's offset word are 32 bits each. -/
def halfBits : Nat := 32

/-- The offset word of a locative whose pointee starts at scalar byte offset
`sb` and trace byte offset `tb`. -/
def offWord (sb tb : Nat) : Nat := sb + tb * 2 ^ halfBits

/-- The offset-word step of one element (or one component) of layout
`(n, m)`. -/
def stride (n m : Nat) : Nat := offWord (8 * n) (8 * m)

/-- Header kinds. -/
inductive HeaderKind
  /-- An object made by `new`. -/
  | obj
  /-- An array made by `newBuf`: `(n, m)` of the element, `len` elements. -/
  | array
  /-- Reserved: a box (a sum's boxed tier; not in the fragment). -/
  | box
  /-- A runtime block in the pinned region (a TCB). -/
  | pinned
  deriving Repr, BEq, DecidableEq, Inhabited

def HeaderKind.code : HeaderKind → Nat
  | .obj => 0 | .array => 1 | .box => 2 | .pinned => 3

def nShift (o : ObjLayout) : Nat := o.kindBits + o.gcBits
def mShift (o : ObjLayout) : Nat := nShift o + o.nBits
def lenShift (o : ObjLayout) : Nat := mShift o + o.mBits

/-- The header word of kind `k` with counts `(n, m)` and `len = 0` (the
allocator adds the length); `none` if a count does not fit its field. -/
def header0 (o : ObjLayout) (k : HeaderKind) (n m : Nat) : Option Nat :=
  if k.code < 2 ^ o.kindBits ∧ n < 2 ^ o.nBits ∧ m < 2 ^ o.mBits then
    some (k.code + n * 2 ^ nShift o + m * 2 ^ mShift o)
  else none

/-- The fields of a header word: `(kind, gc, n, m, len)`. -/
def decode (o : ObjLayout) (h : Nat) : Nat × Nat × Nat × Nat × Nat :=
  (h % 2 ^ o.kindBits, (h / 2 ^ o.kindBits) % 2 ^ o.gcBits, (h / 2 ^ nShift o) % 2 ^ o.nBits,
   (h / 2 ^ mShift o) % 2 ^ o.mBits, h / 2 ^ lenShift o)

/-- The field widths fill one word. -/
def wellFormed (o : ObjLayout) : Bool :=
  o.kindBits + o.gcBits + o.nBits + o.mBits + o.lenBits == 64

/-! ## 16-byte pairs

A **pair** is a single-copy-atomic access of two words (WeakCore's
`TermRun.Acc.two`): a `word2` protocol pair, an `epair`, a wide sum of two
scalar words, a coupled existential package of two model words.  Under the
bipartite layout a pair is atomic only when both its words lie in one region
and the two form one aligned 16-byte granule, so:

* a pair whose words are both scalars (`word2`, `epair`, a scalar wide sum, a
  package of two scalars) is a **scalar pair**; one of two references (a
  package of two pointers, allowed in shared cells) is a **trace
  pair**; a pair with one word of each kind is a mixed unit (§6 of
  `Scc/LAYOUT.md`) and has no layout here;
* `place` lays a value out unit by unit, like `slots` word by word, and starts
  every pair at an index whose two words form an aligned granule, leaving a
  one-word gap in that region when the next index does not (`pairStart`).
  On types without pairs it leaves no gap and agrees with `slots`;
* an array element's regions are rounded to an even number of words in each
  region that holds a pair (`strideOf`), so every element repeats the first
  one's alignment;
* an object holding a pair needs a 16-byte-aligned base: the allocator skips
  one word when the cursor would misalign it (`allocGap`).  The skipped word
  is never read and needs no header, since nothing walks the heap linearly
  (`Scc/LAYOUT.md` §2).

No pair type is in the accepted fragment yet, so the lowering still uses
`slots` (which has no case for pairs) and the runtime allocator does not
align; `place`, `strideOf` and `allocGap` fix the layout those will use. -/

/-- The region of a pair type's two words: `some false` for a scalar pair,
`some true` for a trace pair; `none` for a type that is not a pair or a
mixed one. -/
def pairRegion (t : Ty) : Option Bool :=
  match t with
  | .word2 _ _ | .epair _ _ => some false
  | .sum _ _ => if t.tier == .wide && reg t == some (2, 0) then some false else none
  | .iex _ | .tex _ _ =>
      if coupledPair t then
        match reg t with
        | some (2, 0) => some false
        | some (0, 2) => some true
        | _ => none
      else none
  | _ => none

/-- Can a pair start at index `i` of its region?  Scalar words `i, i + 1` lie
at `base + 8i` upwards, aligned when `i` is even.  Trace words `j, j + 1` lie
at `base − traceBias − 8j` downwards, so the granule starts at
`base − traceBias − 8(j + 1)`, aligned when `traceBias / 8 + j + 1` is even.
Both assume a 16-byte-aligned base. -/
def pairStart (o : ObjLayout) (trace : Bool) (i : Nat) : Bool :=
  if trace then ((traceBias o).toNat / 8 + i + 1) % 2 == 0 else i % 2 == 0

/-- The first index from `i` at which a pair can start (`i` or `i + 1`). -/
def pairAt (o : ObjLayout) (trace : Bool) (i : Nat) : Nat :=
  if pairStart o trace i then i else i + 1

/-- One memory unit of a value: its region (`true` = trace), the index of its
first word in that region, and whether it is a pair (two words, `idx` and
`idx + 1`). -/
structure MemUnit where
  trace : Bool
  idx : Nat
  pair : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The words of a unit, as `slots` lists them: `(isTrace, index)`. -/
def MemUnit.words (u : MemUnit) : List (Bool × Nat) :=
  if u.pair then [(u.trace, u.idx), (u.trace, u.idx + 1)] else [(u.trace, u.idx)]

/-- The aligned layout of a value of type `t` whose regions start at scalar
index `s` and trace index `r`: its units in value order, and the next free
scalar and trace indices (gaps included).  `none` off the fragment's types
and the pairs. -/
def place (o : ObjLayout) : Ty → Nat → Nat → Option (List MemUnit × Nat × Nat)
  | .unit, s, r | .void, s, r => some ([], s, r)
  | .int, s, r | .intS _, s, r | .fix _ _, s, r | .lanes _ _, s, r =>
      some ([{ trace := false, idx := s }], s + 1, r)
  | .ptr _ _, s, r | .tid, s, r => some ([{ trace := true, idx := r }], s, r + 1)
  | .loc _ _, s, r => some ([{ trace := true, idx := r }, { trace := false, idx := s }], s + 1, r + 1)
  | .prod a b, s, r => do
      let (ua, s1, r1) ← place o a s r
      let (ub, s2, r2) ← place o b s1 r1
      pure (ua ++ ub, s2, r2)
  | .refine t _, s, r | .iall t, s, r | .mu t, s, r => place o t s r
  | t@(.iex b), s, r | t@(.tex _ b), s, r =>
      if coupledPair t then pairUnit (pairRegion t) s r else place o b s r
  | t@(.word2 _ _), s, r | t@(.epair _ _), s, r | t@(.sum _ _), s, r =>
      pairUnit (pairRegion t) s r
  | _, _, _ => none
where
  /-- A pair in region `pr` at the first aligned index. -/
  pairUnit : Option Bool → Nat → Nat → Option (List MemUnit × Nat × Nat)
    | some false, s, r => let i := pairAt o false s; some ([{ trace := false, idx := i, pair := true }], i + 2, r)
    | some true, s, r => let j := pairAt o true r; some ([{ trace := true, idx := j, pair := true }], s, j + 2)
    | none, _, _ => none

/-- The words of `place`, in value order (`slots`' format). -/
def placeWords (o : ObjLayout) (t : Ty) (s r : Nat) : Option (List (Bool × Nat)) :=
  (place o t s r).map fun (us, _, _) => us.flatMap MemUnit.words

/-- An array element's `(n, m)` under `place`: its regions, gaps included,
each rounded up to an even number of words when it holds a pair, so element
`k` at `(k·n, k·m)` is laid out as element 0 shifted. -/
def strideOf (o : ObjLayout) (t : Ty) : Option (Nat × Nat) := do
  let (us, n, m) ← place o t 0 0
  let even (x : Nat) (tr : Bool) := if us.any (fun u => u.pair && u.trace == tr) then (x + 1) / 2 * 2 else x
  pure (even n false, even m true)

/-- **The header's counts** `(n, m)` of an object or of an array element of
type `t`: its regions under `place`, gaps included (`strideOf`).  The object
then takes `1 + len·(n + m)` words with every alignment gap inside it, so the
header alone still gives its size; a gap in the trace region is a trace
word that no unit uses, born null in the zero-filled arena and never
stored.  On types without pairs it is `regOf`. -/
def counts (o : ObjLayout) (t : Ty) : Option (Nat × Nat) := strideOf o t

/-- Words the allocator skips before an object holding a pair, with the
cursor at byte address `c` (a multiple of 8) and `M` trace words: the base
lies `8·(M + 1)` bytes above the object's start under either header
placement, and must be a multiple of 16. -/
def allocGap (c M : Nat) : Nat := if (c / 8 + M + 1) % 2 == 0 then 0 else 1

end Scc.Obj
