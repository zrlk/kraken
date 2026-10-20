/-
WeakCore's FlatHashMap `lookup` (portable variant, `Int` keys and values):
the pure model, ISA-neutral. Shared by the AArch64 lowering
(`FlatGroupMatch.lean`, `FlatLookup.lean`) and the x64 one
(`FlatGroupMatchX64.lean`, `FlatLookupX64.lean`); it imports no ISA.

* §1 copies the word primitives of WeakCore's `TermRun.lean` (`W64`, `bitN`,
  `bit1N`, …) verbatim, on `Nat`, and the constants and `zb` of
  `FlatHashMap.lean`; `matchN`/`emptyN` are the group match.
* §2 proves that each primitive the group match uses is the `toNat` of a
  `BitVec` operation (`bitN_and`, …, `zbBV_toNat`, `matchBV_toNat`), and that
  `BitVec.ctz` is WeakCore's `bit1 ctz` (`ctz_toNat`, `bit1N_ctz`).
* The model `lookupN` (WeakCore's `lookupD false` / `findD false` /
  `candD false` at `K = V = Int`, `hash = hashInt`, `eq = eqInt`), the
  probe-termination property `ProbeEnds`, the restriction `Tbl.Bounded`, the
  concrete table `tbl1`, and the register-level facts (`rv`, `candN_rv`,
  `findN_step`, `next_lt`, …) both lowerings' proofs use.

What names a machine (the table in memory `Tbl.InMem` over the ISA's
`DataMem`, the hash mix over its `BitVec.unsigned`) stays with each lowering.
-/
import Kraken.WordLemmas

namespace Kraken.Promising.Lower.Flat

/-! ## 1. The pure model: WeakCore's 64-bit word primitives

Copied from WeakCore `TermRun.lean` ("64-bit word primitives (swisstable)")
and `CoreTerm.lean` (`BitOp`, `BitOp1`), and the constants and `zb` of
`FlatHashMap.lean`. Operands are reduced mod 2⁶⁴, as there. -/

def W64 : Nat := 2 ^ 64

/-- WeakCore's `BitOp`. -/
inductive BitOp
  | and | or | xor | shl | shr | wadd | wsub | wmul | mulhi | msb16
  deriving Repr, DecidableEq

/-- WeakCore's `BitOp1`; `ctz 0 = 64`. -/
inductive BitOp1
  | not | ctz | popcnt
  deriving Repr, DecidableEq

/-- Byte `i` of `x`. -/
def byteAt (x i : Nat) : Nat := (x / 2 ^ (8 * i)) % 256

/-- Top bit of each of the 8 bytes of `x`, as an 8-bit mask. -/
def msb8 (x : Nat) : Nat :=
  (List.range 8).foldl (fun acc i => acc + (byteAt x i / 128) * 2 ^ i) 0

def ctz64 (x : Nat) : Nat :=
  let x := x % W64
  ((List.range 64).find? fun i => (x >>> i) % 2 == 1).getD 64

def popcnt64 (x : Nat) : Nat :=
  let x := x % W64
  (List.range 64).foldl (fun acc i => acc + (x >>> i) % 2) 0

def bitN (o : BitOp) (a b : Nat) : Nat :=
  let a := a % W64
  let b := b % W64
  match o with
  | .and => a &&& b
  | .or => a ||| b
  | .xor => a ^^^ b
  | .shl => (a <<< (b % 64)) % W64
  | .shr => a >>> (b % 64)
  | .wadd => (a + b) % W64
  | .wsub => (a + W64 - b) % W64
  | .wmul => (a * b) % W64
  | .mulhi => a * b / W64
  | .msb16 => msb8 a + 256 * msb8 b

def bit1N (o : BitOp1) (a : Nat) : Nat :=
  let a := a % W64
  match o with
  | .not => W64 - 1 - a
  | .ctz => ctz64 a
  | .popcnt => popcnt64 a

def L8 : Nat := 0x0101010101010101
def H8 : Nat := 0x8080808080808080
def Lo7 : Nat := 0x7F7F7F7F7F7F7F7F

/-- The exact zero-byte test, as the portable group code computes it
(WeakCore `FlatHashMap.zbN`). -/
def zbN (y : Nat) : Nat :=
  bit1N .not (bitN .or (bitN .or (bitN .wadd (bitN .and y Lo7) Lo7) y) Lo7)

/-- The lanes of control word `w` whose byte is `h2` (`matchOps false`). -/
def matchN (w h2 : Nat) : Nat := zbN (bitN .xor w (bitN .wmul h2 L8))

/-- The empty lanes of control word `w` (`emptyOps false`). -/
def emptyN (w : Nat) : Nat := zbN w

-- WeakCore's own check of `zbN`: zero bytes at 0, 3, 6, and not at 7.
#guard zbN 0x0100FF8000017F00 == 0x0080000080000080
-- Lanes 1 and 4 hold `0x85`, every other lane is empty: they match, the rest are empty.
#guard matchN 0x0000008500008500 0x85 == 0x0000008000008000
#guard emptyN 0x0000008500008500 == 0x8080800080800080
-- A full group of other bytes and deleted slots: no match, no empty lane.
#guard matchN 0x0101018601018701 0x85 == 0 && emptyN 0x0101018601018701 == 0

/-! ## 2. The model is the machine's arithmetic

Each primitive the leaf uses, at the `toNat` of two 64-bit vectors, is the
`toNat` of the `BitVec` operation. -/

section Bridge
variable (a b : BitVec 64)

private theorem mod_W64 : a.toNat % W64 = a.toNat := Nat.mod_eq_of_lt a.isLt

theorem bitN_and : bitN .and a.toNat b.toNat = (a &&& b).toNat := by
  simp [bitN, mod_W64]
theorem bitN_or : bitN .or a.toNat b.toNat = (a ||| b).toNat := by
  simp [bitN, mod_W64]
theorem bitN_xor : bitN .xor a.toNat b.toNat = (a ^^^ b).toNat := by
  simp [bitN, mod_W64]
theorem bitN_wadd : bitN .wadd a.toNat b.toNat = (a + b).toNat := by
  simp [bitN, BitVec.toNat_add, W64]
theorem bitN_wmul : bitN .wmul a.toNat b.toNat = (a * b).toNat := by
  simp [bitN, BitVec.toNat_mul, W64]
theorem bit1N_not : bit1N .not a.toNat = (~~~a).toNat := by
  simp only [bit1N, W64, BitVec.toNat_mod_cancel, BitVec.toNat_not]

end Bridge

/-- `zb` on 64-bit vectors, as the leaf computes it. -/
def zbBV (y : BitVec 64) : BitVec 64 :=
  ~~~((((y &&& 0x7F7F7F7F7F7F7F7F#64) + 0x7F7F7F7F7F7F7F7F#64) ||| y) ||| 0x7F7F7F7F7F7F7F7F#64)

theorem zbBV_toNat (y : BitVec 64) : (zbBV y).toNat = zbN y.toNat := by
  have h : Lo7 = (0x7F7F7F7F7F7F7F7F#64).toNat := rfl
  simp only [zbN, zbBV, h, bitN_and, bitN_wadd, bitN_or, bit1N_not]

/-- The match on 64-bit vectors, as the leaf computes it. -/
def matchBV (w h2 : BitVec 64) : BitVec 64 := zbBV (w ^^^ h2 * 0x0101010101010101#64)

theorem matchBV_toNat (w h2 : BitVec 64) : (matchBV w h2).toNat = matchN w.toNat h2.toNat := by
  have h : L8 = (0x0101010101010101#64).toNat := rfl
  simp only [matchBV, matchN, zbBV_toNat, h, bitN_wmul, bitN_xor]

private theorem find_range_some (q : Nat → Bool) (t : Nat) (ht : q t = true)
    (hlt : ∀ j, j < t → q j = false) : ∀ n, t < n → (List.range n).find? q = some t
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    rw [List.range_succ, List.find?_append]
    by_cases htn : t < n
    · rw [find_range_some q t ht hlt n htn]; rfl
    · have e : t = n := by omega
      subst e
      rw [List.find?_eq_none.mpr (fun j hj => by
        simp [hlt j (List.mem_range.mp hj)])]
      simp [ht]

theorem ctz_toNat (x : BitVec 64) : x.reverse.clz.toNat = ctz64 x.toNat := by
  have hq : ∀ i, ((x.toNat >>> i) % 2 == 1) = x.getLsbD i := by
    intro i
    rw [← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
    by_cases h : x.toNat / 2 ^ i % 2 = 1 <;> simp [h]
  unfold ctz64
  simp only [W64, BitVec.toNat_mod_cancel]
  by_cases hx : x = 0#64
  · subst hx
    rw [List.find?_eq_none.mpr (fun j _ => by simp)]
    have h0 : (0#64).reverse.clz = (64 : Nat) :=
      BitVec.clz_eq_iff_eq_zero.mpr (BitVec.reverse_eq_zero_iff.mpr rfl)
    rw [h0]; rfl
  · have h1 := BitVec.getLsbD_true_ctz_of_ne_zero hx
    have hlt : x.ctz.toNat < 64 := by
      rcases Nat.lt_or_ge x.ctz.toNat 64 with h | h
      · exact h
      · rw [BitVec.getLsbD_of_ge x _ h] at h1
        exact absurd h1 (by decide)
    rw [find_range_some _ x.ctz.toNat (by rw [hq]; exact h1)
      (fun j hj => by rw [hq]; exact BitVec.getLsbD_false_of_lt_ctz hj) 64 hlt]
    rfl

/-- **`BitVec.ctz` is WeakCore's `bit1 ctz`** (the value of x64 `tzcnt`):
`ctz64` searches for the first set bit, as `BitVec.toNat_ctz_eq_find` reads
`ctz`. -/
theorem bit1N_ctz (x : BitVec 64) : bit1N .ctz x.toNat = x.ctz.toNat := by
  rw [BitVec.toNat_ctz_eq_find]
  simp only [bit1N, ctz64, W64, BitVec.toNat_mod_cancel]

/-! ## 2. The model: WeakCore's `lookup` at `Int` keys and values

`T.ctrl g` is control word `g` (`loadAt cb g`, then `toInt`), `T.key s` and
`T.val s` the two words of slot `s` (`loadAtF sb s [0]`, `[1]`). `findN` takes
WeakCore's tail-recursive `find` with fuel: `none` is "fuel out". `lookupN`
starts it with `m + 1` (the number of groups), so `(lookupN T k).isSome` is
the probe-termination property `ProbeEnds` (WeakCore's `find` stops at the
first group, on the triangular sequence, that has an empty slot). -/

/-- What `lookup` reads of a table, and where the two buffers sit. -/
structure Tbl where
  /-- `m`: groups − 1 (the `band` mask of a group index). -/
  mv : Nat
  /-- `c`: slots − 1 (the `band` mask of a slot index). -/
  cv : Nat
  ctrl : Nat → Nat
  key : Nat → Nat
  val : Nat → Nat
  /-- The control buffer's address (`σ` of its label). -/
  cb : BitVec 64
  /-- The slot buffer's address. -/
  sb : BitVec 64

def Cmix : Nat := 0x9E3779B97F4A7C15

/-- `band a m` (`TermRun`: `(a % W64) &&& m`). -/
def bandN (a m : Nat) : Nat := (a % W64) &&& m

/-- `hashOps` at `hash = hashInt` (the identity): `(h2, pos)`. -/
def hashN (k : Nat) : Nat × Nat :=
  let hm := bitN .xor (bitN .mulhi k Cmix) (bitN .wmul k Cmix)
  (bitN .or (bitN .and hm 0x7F) 0x80, bitN .shr hm 7)

private theorem clearLow_lt (mk : Nat) (h : mk ≠ 0) :
    bitN .and mk (bitN .wsub mk 1) < mk := by
  simp only [bitN]
  have h1 := Nat.mod_le mk W64
  by_cases h0 : mk % W64 = 0
  · have := @Nat.and_le_left (mk % W64) ((mk % W64 + W64 - 1 % W64) % W64 % W64)
    omega
  · have hl : (mk % W64 + W64 - 1 % W64) % W64 % W64 = mk % W64 - 1 := by
      have : mk % W64 < W64 := Nat.mod_lt _ (by decide)
      rw [show 1 % W64 = 1 by decide, Nat.mod_mod,
        show mk % W64 + W64 - 1 = (mk % W64 - 1) + W64 by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [hl]
    have := @Nat.and_le_right (mk % W64) (mk % W64 - 1)
    omega

/-- WeakCore's `cand` [c] at `eq = eqInt`: the candidate lanes `mk` of the
group at slot `base`, lowest first (`lane`, `clearLow`); `some sr` is
`inl sr`, `none` is `inr ()`. -/
def candN (T : Tbl) (k base mk : Nat) : Option Nat :=
  if _h : mk = 0 then none
  else
    let sr := bitN .or base (bitN .shr (bit1N .ctz mk) 3)
    if k = T.key (bandN sr T.cv) then some sr
    else candN T k base (bitN .and mk (bitN .wsub mk 1))
termination_by mk
decreasing_by exact clearLow_lt mk _h

/-- `find`'s answer once `cand` has answered `cr`: found, or (no match) the
next group if this one has no empty slot (`rest`), else absent. -/
def contN (cr : Option Nat) (em : Nat) (rest : Option (Option Nat)) : Option (Option Nat) :=
  match cr with
  | some sr => some (some sr)
  | none => if em = 0 then rest else some none

/-- WeakCore's `find` [m, c] with fuel `n`: `some (some sr)` is `inl sr`,
`some none` is `inr ()`, `none` is fuel out. -/
def findN (T : Tbl) (k h2 : Nat) : Nat → Nat → Nat → Option (Option Nat)
  | 0, _, _ => none
  | n + 1, pos, st =>
    let g := bandN pos T.mv
    let w := T.ctrl g
    contN (candN T k (bitN .shl g 3) (matchN w h2)) (emptyN w)
      (findN T k h2 n (bitN .wadd pos (bitN .wadd st 1)) (bitN .wadd st 1))

/-- WeakCore's `lookup` at `Int` keys and values: `some (some y)` is `inr y`,
`some none` is `inl ()`, `none` is a probe that does not end within `m + 1`
groups. -/
def lookupN (T : Tbl) (k : Nat) : Option (Option Nat) :=
  (findN T k (hashN k).1 (T.mv + 1) (hashN k).2 0).map
    (Option.map fun sr => T.val (bandN sr T.cv))

/-- **The probe-termination hypothesis** (a start-state property of the
table): `lookup`'s probe for `k` ends within `m + 1` groups. -/
def ProbeEnds (T : Tbl) (k : Nat) : Prop := (lookupN T k).isSome

/-- The words are 64-bit (restriction R-INT). -/
structure Tbl.Bounded (T : Tbl) (k : Nat) : Prop where
  mv : T.mv + 1 < W64
  cv : T.cv < W64
  key : ∀ s, T.key s < W64
  val : ∀ s, T.val s < W64
  ctrl : ∀ g, T.ctrl g < W64
  k : k < W64

theorem bitN_shr (a : BitVec 64) (n : Nat) (h : n < 64) :
    bitN .shr a.toNat n = (a >>> n).toNat := by
  simp only [bitN, W64, BitVec.toNat_mod_cancel, BitVec.toNat_ushiftRight,
    Nat.mod_eq_of_lt (show n < 2 ^ 64 from Nat.lt_trans h (by decide)), Nat.mod_eq_of_lt h]

/-- A literal operand, as a 64-bit vector (for `rw`, at one literal). -/
theorem bitN_lit (o : BitOp) (a c : Nat) : bitN o a c = bitN o a (BitVec.ofNat 64 c).toNat := by
  rw [BitVec.toNat_ofNat]; simp only [bitN, W64, Nat.mod_mod]

/-! ### A concrete table: one group, key `5` in lane `2`, value `55` -/

/-- One group (`m = 0`, `c = 7`): lane 2 holds `hashN 5`'s `h2`, the others
are empty. -/
def tbl1 : Tbl where
  mv := 0
  cv := 7
  ctrl := fun _ => (hashN 5).1 * 2 ^ 16
  key := fun s => if s = 2 then 5 else 0
  val := fun s => if s = 2 then 55 else 0
  cb := 0x1000#64
  sb := 0x2000#64

theorem tbl1_lookup5 : lookupN tbl1 5 = some (some 55) := by decide +kernel
theorem tbl1_lookup6 : lookupN tbl1 6 = some none := by decide +kernel
theorem tbl1_probeEnds : ProbeEnds tbl1 5 := by
  show (lookupN tbl1 5).isSome = true
  rw [tbl1_lookup5]; rfl
theorem tbl1_bounded : tbl1.Bounded 5 :=
  ⟨by decide, by decide, fun s => by simp only [tbl1]; split <;> decide,
   fun s => by simp only [tbl1]; split <;> decide,
   fun _ => by show (hashN 5).1 * 2 ^ 16 < W64; decide +kernel, by decide⟩

/-- A register's value as a number: `BitVec.toNat`, sealed so that `simp`
normalises the register under it and leaves the model's arguments alone. -/
def rv (b : BitVec 64) : Nat := b.toNat
theorem rv_def (b : BitVec 64) : rv b = b.toNat := rfl
attribute [irreducible] rv

@[simp] theorem rv_zero : rv 0#64 = 0 := by simp only [rv_def]; rfl

theorem var_le (a : Nat) : (a + 1) * (W64 + 1) + W64 ≤ (a + 2) * (W64 + 1) := by
  rw [Nat.add_mul, Nat.add_mul]; omega

theorem rv_lt (b : BitVec 64) : rv b < W64 := by rw [rv_def]; exact b.isLt
theorem rv_ofNat (n : Nat) (h : n < W64) : rv (BitVec.ofNat 64 n) = n := by
  rw [rv_def, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h
theorem bandN_rv {a b : BitVec 64} {m : Nat} (h : rv b = m) : bandN (rv a) m = rv (a &&& b) := by
  subst h; simp only [bandN, rv_def, W64, BitVec.toNat_mod_cancel, BitVec.toNat_and]
theorem shl3_rv (a : BitVec 64) : bitN .shl (rv a) 3 = rv (a <<< 3) := by
  simp only [bitN, rv_def, W64, BitVec.toNat_mod_cancel, BitVec.toNat_shiftLeft]
theorem matchN_rv {c h2 : Nat} {hb : BitVec 64} (hc : c < W64) (h : rv hb = h2) :
    matchN c h2 = rv (matchBV (BitVec.ofNat 64 c) hb) := by
  subst h; simp only [rv_def, matchBV_toNat, BitVec.toNat_ofNat]
  rw [show (2 : Nat) ^ 64 = W64 from rfl, Nat.mod_eq_of_lt hc]
theorem emptyN_rv {c : Nat} (hc : c < W64) : emptyN c = rv (zbBV (BitVec.ofNat 64 c)) := by
  rw [rv_def, zbBV_toNat, BitVec.toNat_ofNat, show (2 : Nat) ^ 64 = W64 from rfl,
    Nat.mod_eq_of_lt hc, emptyN]
/-- `find` with fuel left, one group unfolded. -/
theorem findN_step (T : Tbl) (k h2 pos st : Nat) (h : st ≤ T.mv) :
    findN T k h2 (T.mv + 1 - st) pos st =
      contN (candN T k (bitN .shl (bandN pos T.mv) 3) (matchN (T.ctrl (bandN pos T.mv)) h2))
        (emptyN (T.ctrl (bandN pos T.mv)))
        (findN T k h2 (T.mv - st) (bitN .wadd pos (bitN .wadd st 1)) (bitN .wadd st 1)) := by
  rw [show T.mv + 1 - st = (T.mv - st) + 1 by omega]; rfl

theorem bitN_wsub (a b : BitVec 64) : bitN .wsub a.toNat b.toNat = (a - b).toNat := by
  have := b.isLt
  simp only [bitN, W64, BitVec.toNat_mod_cancel, BitVec.toNat_sub]
  congr 1; omega

theorem clear_rv (mk : BitVec 64) :
    bitN .and (rv mk) (bitN .wsub (rv mk) 1) = rv (mk &&& (mk - 1#64)) := by
  rw [rv_def, rv_def, ← bitN_and, ← bitN_wsub]; rfl

theorem rv_ne (mk : BitVec 64) (h : mk ≠ 0#64) : rv mk ≠ 0 := by
  rw [rv_def]; intro h'; exact h (BitVec.eq_of_toNat_eq (by simpa using h'))

theorem clear_lt (mk : BitVec 64) (h : mk ≠ 0#64) : rv (mk &&& (mk - 1#64)) < rv mk :=
  clear_rv mk ▸ clearLow_lt _ (rv_ne mk h)

theorem candN_zero (T : Tbl) (k b : Nat) : candN T k b 0 = none := by rw [candN]; rfl

theorem sub_rv (b : BitVec 64) (n : Nat) (hn : n < W64) :
    b - BitVec.ofNat 64 n = 0#64 ↔ rv b = n := by
  rw [rv_def]
  constructor
  · intro h
    have := congrArg (· + BitVec.ofNat 64 n) h
    simp only [BitVec.sub_add_cancel, BitVec.zero_add] at this
    subst this; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  · rintro rfl; simp

@[simp] theorem ofNat_rv (b : BitVec 64) : BitVec.ofNat 64 (rv b) = b := by simp [rv_def]

/-- `cand` with a non-empty mask, one lane unfolded, in register form. -/
theorem candN_rv (T : Tbl) (k : Nat) (base mk : BitVec 64) (h : mk ≠ 0#64) :
    candN T k (rv base) (rv mk) =
      if k = T.key (bandN (rv (base ||| mk.reverse.clz >>> 3)) T.cv)
      then some (rv (base ||| mk.reverse.clz >>> 3))
      else candN T k (rv base) (rv (mk &&& (mk - 1#64))) := by
  rw [candN]; simp only [rv_ne mk h, ↓reduceDIte]
  have e1 : bitN .or (rv base) (bitN .shr (bit1N .ctz (rv mk)) 3)
      = rv (base ||| mk.reverse.clz >>> 3) := by
    simp only [bit1N, rv_def, W64, BitVec.toNat_mod_cancel]
    rw [← ctz_toNat, bitN_shr _ 3 (by decide), bitN_or]
  simp only [e1, clear_rv]

theorem wadd1 (b : BitVec 64) : bitN .wadd (rv b) 1 = rv (b + 1#64) := by
  rw [rv_def, rv_def, ← bitN_wadd]; rfl
theorem wadd_rv (a b : BitVec 64) : bitN .wadd (rv a) (rv b) = rv (a + b) := by
  rw [rv_def, rv_def, rv_def, bitN_wadd]
theorem rv_add1 (b : BitVec 64) (h : rv b + 1 < W64) : rv (b + 1#64) = rv b + 1 := by
  simp only [rv_def, BitVec.toNat_add] at h ⊢; exact Nat.mod_eq_of_lt h
theorem var_lt (m s : Nat) (h : s ≤ m) : (m - s) * (W64 + 1) + W64 < (m + 1 - s) * (W64 + 1) := by
  rw [show m + 1 - s = (m - s) + 1 by omega, Nat.add_mul]; omega

/-- The probe's overall answer. -/
abbrev Rf (T : Tbl) (k : Nat) : Option (Option Nat) :=
  findN T k (hashN k).1 (T.mv + 1) (hashN k).2 0

theorem lookupN_eq (T : Tbl) (k : Nat) :
    lookupN T k = (Rf T k).map (Option.map fun sr => T.val (bandN sr T.cv)) := rfl

/-- The probe has fuel left at every group it reaches. -/
theorem next_lt {T : Tbl} {k st pos st' : Nat} (hpe : ProbeEnds T k) (hst : st ≤ T.mv)
    (hf : findN T k (hashN k).1 (T.mv - st) pos st' = Rf T k) : st < T.mv := by
  rcases Nat.lt_or_ge st T.mv with h | h
  · exact h
  · have e : T.mv - st = 0 := by omega
    rw [e] at hf
    have : (lookupN T k).isSome = true := hpe
    rw [lookupN_eq, ← hf] at this
    exact absurd this (by simp [findN])

end Kraken.Promising.Lower.Flat
