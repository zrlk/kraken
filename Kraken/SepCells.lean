import Kraken.SeparationMem

/-!
# Memory cells in separation syntax

A stack frame is a few cells with known contents (the return address, the
saved frame pointer) next to regions whose contents do not matter. `Blocks`
only covers the latter, and a list is awkward once cells of both kinds mix.
This file states memory as a `⋆`-tree of cells:

* `bs =@ a` — the bytes `bs` sit at `a` (contents known);
* `n ?@ a` — some `n` bytes sit at `a` (contents unknown; this is `Block a n`).

A load or store needs to find its cell in the tree. `Split P R H` says that
`H` is `P ⋆ R` once `P` is pulled to the front, and its introduction rules
walk the tree, so `grind` derives a `Split` for every cell of every tree it
sees. The access lemmas take a `Split` and the fact `m =⋆ H`; a store into a
`?@` cell keeps `H`, a store into a `=@` cell, or one that fixes the contents
of a `?@` cell, puts the new cell in front: `m' =⋆ bs' =@ a ⋆ R`.

Addresses are matched exactly against the cell's base (`Split` on the base
term), so the arithmetic `grind` has to do is `a = a'` between two address
terms, which its `ring` module handles for linear bitvector expressions.
-/

open Std.ExtHashMap

namespace Mem

/-- The bytes `bs` sit at `a`, and nothing else is in this part of memory. -/
def Val {w : Nat} (a : BitVec w) (bs : List UInt8) : Mem w → Prop := Eq (bs.At a)

@[inherit_doc Val] notation:75 bs:76 " =@ " a:76 => Val a bs
@[inherit_doc Block] notation:75 n:76 " ?@ " a:76 => Block a n

theorem Val.eq {w : Nat} (a : BitVec w) (bs : List UInt8) : (bs =@ a) = Eq (bs.At a) := rfl

/-- `H` is `P ⋆ R` with `P` pulled to the front. -/
def Split {w : Nat} (P R H : Mem w → Prop) : Prop := H = P ⋆ R

theorem Split.here {w : Nat} (P R : Mem w → Prop) : Split P R (P ⋆ R) := rfl

theorem Split.left {w : Nat} {P R Q : Mem w → Prop} (h : Split P R Q) (S : Mem w → Prop) :
    Split P (R ⋆ S) (Q ⋆ S) := by
  unfold Split at *; rw [h, sep_assoc]

theorem Split.right {w : Nat} {P R S : Mem w → Prop} (h : Split P R S) (Q : Mem w → Prop) :
    Split P (Q ⋆ R) (Q ⋆ S) := by
  unfold Split at *; rw [h, sep_comm_l]

/-- A tree that is one cell splits with the empty rest. -/
theorem Split.val {w : Nat} (a : BitVec w) (bs : List UInt8) :
    Split (bs =@ a) emp (bs =@ a) := (sep_emp _).symm

theorem Split.block {w : Nat} (a : BitVec w) (n : Nat) : Split (n ?@ a) emp (n ?@ a) :=
  (sep_emp _).symm

/-! ### Access lemmas -/

/-- Loading a known cell whole reads its bytes. -/
theorem Val.loadInt {w : Nat} {H R : Mem w → Prop} {m : Mem w} {a : BitVec w}
    {bs : List UInt8} {n : Nat} (h : m =⋆ H) (hs : Split (bs =@ a) R H)
    (hlen : bs.length = n) (hw : n ≤ 2 ^ w) :
    m.loadInt a n = some (Int.ofBytes bs) := by
  rw [hs] at h
  exact loadInt_sep bs a n R m h hlen hw

/-- Storing over a known cell whole replaces its bytes. -/
theorem Val.storeInt {w : Nat} {H R : Mem w → Prop} {m : Mem w} {a : BitVec w}
    {bs : List UInt8} {n : Nat} (h : m =⋆ H) (hs : Split (bs =@ a) R H)
    (hlen : bs.length = n) (v : Int) :
    m.storeInt a n v =⋆ (Int.toBytes n v) =@ a ⋆ R := by
  rw [hs] at h
  exact storeInt_sep a n bs R m ⟨h, hlen⟩ v

/-- Loading inside an unknown cell succeeds. -/
theorem Block.loadInt_isSome_split {w : Nat} {H R : Mem w → Prop} {m : Mem w}
    {a addr : BitVec w} {len n : Nat} (h : m =⋆ H) (hs : Split (len ?@ a) R H)
    (hin : (addr - a).toNat + n ≤ len) :
    (m.loadInt addr n).isSome = true := by
  rw [hs] at h
  exact Block.loadInt_isSome h hin

/-- Storing inside an unknown cell keeps the tree. -/
theorem Block.storeInt_split {w : Nat} {H R : Mem w → Prop} {m : Mem w}
    {a addr : BitVec w} {len n : Nat} (h : m =⋆ H) (hs : Split (len ?@ a) R H)
    (hin : (addr - a).toNat + n ≤ len) (v : Int) :
    m.storeInt addr n v =⋆ H := by
  rw [hs] at h ⊢
  exact Block.storeInt h hin v

/-- Storing over an unknown cell whole fixes its contents. -/
theorem Block.storeInt_val {w : Nat} {H R : Mem w → Prop} {m : Mem w} {a : BitVec w}
    {n : Nat} (h : m =⋆ H) (hs : Split (n ?@ a) R H) (v : Int) :
    m.storeInt a n v =⋆ (Int.toBytes n v) =@ a ⋆ R := by
  rw [hs] at h
  obtain ⟨hw, bs, hlen, h'⟩ := Block.sep_elim h
  exact storeInt_sep a n bs R m ⟨h', hlen⟩ v

/-- Forgetting a known cell's contents. -/
theorem Val.forget {w : Nat} {H R : Mem w → Prop} {m : Mem w} {a : BitVec w}
    {bs : List UInt8} (h : m =⋆ H) (hs : Split (bs =@ a) R H) (hw : bs.length ≤ 2 ^ w) :
    m =⋆ bs.length ?@ a ⋆ R := by
  rw [hs] at h
  exact Block.sep_intro rfl hw h

/-- A block is two adjacent blocks. -/
theorem Block.split {w : Nat} (a : BitVec w) (i j : Nat) (hw : i + j ≤ 2 ^ w) :
    ((i + j) ?@ a) = i ?@ a ⋆ j ?@ (a + .ofNat w i) := by
  funext m
  apply propext
  constructor
  · rintro ⟨-, bs, hlen, rfl⟩
    have h1 : (bs.take i).length = i := by simp only [List.length_take]; omega
    have h2 : (bs.drop i).length = j := by simp only [List.length_drop]; omega
    have hsep : (Eq ((bs.take i ++ bs.drop i).At a)) (bs.At a) := by
      rw [List.take_append_drop]
    rw [At_append_sep _ _ _ (by rw [h1, h2]; exact hw), h1] at hsep
    have hb2 := Block.sep_intro (F := Eq ((bs.take i).At a)) h2 (by omega)
      (by rw [sep_comm]; exact hsep)
    rw [sep_comm] at hb2
    exact Block.sep_intro h1 (by omega) hb2
  · intro h
    obtain ⟨-, bs₁, hlen₁, h₁⟩ := Block.sep_elim h
    rw [sep_comm] at h₁
    obtain ⟨-, bs₂, hlen₂, h₂⟩ := Block.sep_elim h₁
    rw [sep_comm, ← hlen₁, ← At_append_sep _ _ _ (by omega)] at h₂
    exact ⟨hw, bs₁ ++ bs₂, by simp [hlen₁, hlen₂], h₂⟩

/-- A block cut at offset `k`. -/
theorem Block.split_at {w : Nat} (a : BitVec w) (n k : Nat) (hk : k ≤ n) (hw : n ≤ 2 ^ w) :
    (n ?@ a) = k ?@ a ⋆ (n - k) ?@ (a + .ofNat w k) := by
  conv => lhs; rw [show n = k + (n - k) by omega]
  exact Block.split a k (n - k) (by omega)

/-- Reading a memory fact in another arrangement of the same cells: `grind`
does not reassociate `⋆`, `ac_rfl` does. `exact Mem.ac h` against a goal with
the cells permuted. -/
theorem ac {w : Nat} {H₁ H₂ : Mem w → Prop} {m : Mem w} (h : m =⋆ H₁)
    (e : H₁ = H₂ := by ac_rfl) : m =⋆ H₂ := e ▸ h

-- A stored cell's length is the store's width.
attribute [grind =] Int.toBytes_length

/-- `Split.here` at a known cell: the form the patterns below key on, so that
`grind` splits trees at cells only and not at every subtree. -/
theorem Split.here_val {w : Nat} (a : BitVec w) (bs : List UInt8) (R : Mem w → Prop) :
    Split (bs =@ a) R (bs =@ a ⋆ R) := rfl

/-- `Split.here` at an unknown cell. -/
theorem Split.here_block {w : Nat} (a : BitVec w) (n : Nat) (R : Mem w → Prop) :
    Split (n ?@ a) R (n ?@ a ⋆ R) := rfl

/-! ### `grind` patterns

The split rules walk every tree in sight, so they are keyed on cells: a split
is derived for each cell of each tree, `here` at the head and `left`/`right`
through the spine. The access rules are keyed on the memory fact `(X ⋆ Y) m`
itself, the split of its tree at a cell, and the access, so that they fire
for the memories a fact is known about and not for every memory term in the
E-graph; this is what the `_at` variants below are for. An access is matched
against a cell's base exactly; `grind` identifies the two address terms with
its `ring` module. The offset forms `Block.loadInt_isSome_split` and
`Block.storeInt_split` have no pattern: an access inside a larger block is
stated by splitting the block at the proof's start (`Block.split_at`), or
uses `Mem.Blocks`, whose `Inside` rules cover offsets. Keying the offset forms
on every (cell, access) pair exhausts `grind`'s instance budget on a frame of
a few cells. -/

theorem Val.loadInt_at {w : Nat} {X Y R : Mem w → Prop} {m : Mem w} {a : BitVec w}
    {bs : List UInt8} {n : Nat} (h : m =⋆ X ⋆ Y) (hs : Split (bs =@ a) R (X ⋆ Y))
    (hlen : bs.length = n) (hw : n ≤ 2 ^ w) :
    m.loadInt a n = some (Int.ofBytes bs) :=
  Val.loadInt h hs hlen hw

theorem Val.storeInt_at {w : Nat} {X Y R : Mem w → Prop} {m : Mem w} {a : BitVec w}
    {bs : List UInt8} {n : Nat} (h : m =⋆ X ⋆ Y) (hs : Split (bs =@ a) R (X ⋆ Y))
    (hlen : bs.length = n) (v : Int) :
    m.storeInt a n v =⋆ (Int.toBytes n v) =@ a ⋆ R :=
  Val.storeInt h hs hlen v

theorem Block.loadInt_isSome_at {w : Nat} {X Y R : Mem w → Prop} {m : Mem w}
    {a : BitVec w} {n : Nat} (h : m =⋆ X ⋆ Y) (hs : Split (n ?@ a) R (X ⋆ Y)) :
    (m.loadInt a n).isSome = true :=
  Block.loadInt_isSome_split h hs (by rw [BitVec.sub_self, BitVec.toNat_zero]; omega)

theorem Block.storeInt_val_at {w : Nat} {X Y R : Mem w → Prop} {m : Mem w} {a : BitVec w}
    {n : Nat} (h : m =⋆ X ⋆ Y) (hs : Split (n ?@ a) R (X ⋆ Y)) (v : Int) :
    m.storeInt a n v =⋆ (Int.toBytes n v) =@ a ⋆ R :=
  Block.storeInt_val h hs v

grind_pattern Split.here_val => sep (Val a bs) R
grind_pattern Split.here_block => sep (Block a n) R
grind_pattern Split.left => Split P R Q, sep Q S
grind_pattern Split.right => Split P R S, sep Q S
grind_pattern Val.loadInt_at => sep X Y m, Split (Val a bs) R (sep X Y), Mem.loadInt m a n
grind_pattern Val.storeInt_at => sep X Y m, Split (Val a bs) R (sep X Y), Mem.storeInt m a n v
grind_pattern Block.loadInt_isSome_at =>
  sep X Y m, Split (Block a n) R (sep X Y), Mem.loadInt m a n
grind_pattern Block.storeInt_val_at =>
  sep X Y m, Split (Block a n) R (sep X Y), Mem.storeInt m a n v

/-! ### Matching a tree against the goal

A postcondition lists the frame's cells in its own order and usually as `?@`
(their contents at exit do not matter). The memory fact `grind` has at that
point is a tree in the order the stores happened to leave it, with `=@` cells.
`Entails H₁ H₂` is derived by walking `H₂`: pull `H₂`'s head cell out of `H₁`
(a `Split` fact) and continue on the rests, forgetting contents when `H₂`
asks for `?@` where `H₁` has `=@`. -/

/-- Every memory satisfying `H₁` satisfies `H₂`. -/
def Entails {w : Nat} (H₁ H₂ : Mem w → Prop) : Prop := ∀ m, H₁ m → H₂ m

theorem Entails.refl {w : Nat} (R : Mem w → Prop) : Entails R R := fun _ h => h

/-- The goal's head cell is in the tree. -/
theorem Entails.cell {w : Nat} {P R₁ R₂ H₁ : Mem w → Prop} (hs : Split P R₁ H₁)
    (e : Entails R₁ R₂) : Entails H₁ (P ⋆ R₂) := by
  intro m h
  rw [hs] at h
  obtain ⟨m₁, m₂, hd, hm, h₁, h₂⟩ := h
  exact ⟨m₁, m₂, hd, hm, h₁, e m₂ h₂⟩

/-- The goal's head cell is in the tree with known contents. -/
theorem Entails.forget {w : Nat} {R₁ R₂ H₁ : Mem w → Prop} {a : BitVec w} {bs : List UInt8}
    {n : Nat} (hs : Split (bs =@ a) R₁ H₁) (e : Entails R₁ R₂) (hlen : bs.length = n)
    (hw : n ≤ 2 ^ w) : Entails H₁ (n ?@ a ⋆ R₂) := by
  intro m h
  have h' := Val.forget h hs (hlen ▸ hw)
  rw [hlen] at h'
  obtain ⟨m₁, m₂, hd, hm, h₁, h₂⟩ := h'
  exact ⟨m₁, m₂, hd, hm, h₁, e m₂ h₂⟩

theorem entails {w : Nat} {X Y P R : Mem w → Prop} {m : Mem w} (h : m =⋆ X ⋆ Y)
    (e : Entails (X ⋆ Y) (P ⋆ R)) : m =⋆ P ⋆ R := e m h

theorem Entails.trans {w : Nat} {H₁ H₂ H₃ : Mem w → Prop} (e₁ : Entails H₁ H₂)
    (e₂ : Entails H₂ H₃) : Entails H₁ H₃ := fun m h => e₂ m (e₁ m h)

/-- The goal's head is itself a tree: read it flat. -/
theorem Entails.assoc {w : Nat} {H₁ P Q R₂ : Mem w → Prop} (e : Entails H₁ (P ⋆ (Q ⋆ R₂))) :
    Entails H₁ ((P ⋆ Q) ⋆ R₂) := by
  intro m h
  rw [sep_assoc]
  exact e m h

/-- The goal's head cell is the front of a larger block of the tree: the
remainder of the block joins the rest. -/
theorem Entails.split {w : Nat} {R₁ R₂ H₁ : Mem w → Prop} {a : BitVec w} {n i : Nat}
    (hs : Split (n ?@ a) R₁ H₁) (e : Entails ((n - i) ?@ (a + .ofNat w i) ⋆ R₁) R₂)
    (hi : i < n) (hw : n ≤ 2 ^ w) : Entails H₁ (i ?@ a ⋆ R₂) := by
  intro m h
  rw [hs, Block.split_at a n i (Nat.le_of_lt hi) hw, sep_assoc] at h
  obtain ⟨m₁, m₂, hd, hm, h₁, h₂⟩ := h
  exact ⟨m₁, m₂, hd, hm, h₁, e m₂ h₂⟩

/-- The goal's head block starts with a smaller block of the tree: the rest
must supply the remainder, at the address behind it. -/
theorem Entails.join {w : Nat} {R₁ R₂ H₁ : Mem w → Prop} {a : BitVec w} {n i : Nat}
    (hs : Split (i ?@ a) R₁ H₁) (e : Entails R₁ ((n - i) ?@ (a + .ofNat w i) ⋆ R₂))
    (hi : i < n) (hw : n ≤ 2 ^ w) : Entails H₁ (n ?@ a ⋆ R₂) := by
  intro m h
  rw [hs] at h
  obtain ⟨m₁, m₂, hd, hm, h₁, h₂⟩ := h
  have h' : (i ?@ a ⋆ ((n - i) ?@ (a + .ofNat w i) ⋆ R₂)) m := ⟨m₁, m₂, hd, hm, h₁, e m₂ h₂⟩
  rwa [← sep_assoc, ← Block.split_at a n i (Nat.le_of_lt hi) hw] at h'

/-- `join` when the smaller cell has known contents. -/
theorem Entails.join_val {w : Nat} {R₁ R₂ H₁ : Mem w → Prop} {a : BitVec w}
    {bs : List UInt8} {n : Nat} (hs : Split (bs =@ a) R₁ H₁)
    (e : Entails R₁ ((n - bs.length) ?@ (a + .ofNat w bs.length) ⋆ R₂))
    (hi : bs.length < n) (hw : n ≤ 2 ^ w) : Entails H₁ (n ?@ a ⋆ R₂) := by
  refine Entails.trans (H₂ := bs.length ?@ a ⋆ R₁) ?_ (Entails.join (Split.here _ _) e hi hw)
  intro m h
  exact Val.forget h hs (by omega)

/- A head that is not a cell (a frame predicate, say) needs its own `Split.here`
instance, keyed on `sep P R` for that `P`; a generic rule keyed on the goal's
head fires for every head in every tree and exhausts the instance budget. See
`Frame` in the `EvenOdd` examples. -/

/- `entails` fires once per pair of a memory fact and a tree asked of the same
memory (the negated goal), and creates the `Entails` term between the two
trees; the other rules descend from an `Entails` term that exists, pulling the
goal's head out of the tree with the `Split` facts (`cell`, `forget`), carving
it out of a larger block (`split`), and flattening a composite head (`assoc`).
The descent is linear in the goal; each step is one E-matching round and one
generation, so a `finish` or `grind` that walks a frame of several cells needs
`(ematch := 20) (gen := 20)` or so.

### Addresses

Cells are matched by address up to `grind`'s equivalence classes, and `grind`
does *not* put `r - 24 + 8` and `r - 16` in one class by itself: bitvector
terms in argument positions are only identified when a case split asserts
their equation, and `grind` proposes such a split (model-based theory
combination) only between arguments of two applications of the same function
in the same position, with the same other arguments — `Block (r - 16) 16` and
`Block (r - 24 + 8) 16`, say, but never a `Val` against a `Block`, or blocks
of different sizes. It does prove an equation it is *given* (`r - 24 + 8 =
r - 16`, through `toNat`), and merges the classes then.

So `join` and `join_val` carry no pattern: their continuation asks for the
cell at the computed address `a + i`, which is found only by luck. A rule that
takes the adjacency `b = a + i` as a side condition instead (merging the cell
at `a` with any cell `Q` of the tree) fans out over every `Q` before the side
condition is checked, each instance a new tree, which is factorial. The
working discipline is to never need a join inside `grind`: a specification's
block (`24 ?@ (r - 24)`) is related to the cells the code uses by a lemma
proved once with `Block.split` (`Frame_cells` in the `EvenOdd` examples), and
`grind` is given that lemma as a rewrite, so every tree it compares lists the
same cells at the same address terms. -/
grind_pattern entails => sep X Y m, sep P R m
grind_pattern Entails.refl => Entails R R
grind_pattern Entails.cell => Entails H₁ (sep P R₂), Split P R₁ H₁
grind_pattern Entails.forget => Entails H₁ (sep (Block a n) R₂), Split (Val a bs) R₁ H₁
grind_pattern Entails.assoc => Entails H₁ (sep (sep P Q) R₂)
grind_pattern Entails.split => Entails H₁ (sep (Block a i) R₂), Split (Block a n) R₁ H₁

end Mem
