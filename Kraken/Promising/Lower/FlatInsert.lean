/-
**WeakCore's FlatHashMap `insert` (portable, no
growth) at `Int` keys and values, lowered to AArch64.** Sequential
machine-founded wp, total correctness, reusing `FlatLookup.lean`'s model.
§1: a concrete `DataMem` holding `tbl1` (`tbl1Mem`). §2: the model `insertN`
(`gl > 0`; growth not lowered). §3: memory algebra (word stores, `InMem`,
byte frame). §4: the code and `insert_spec`. §5: non-vacuity at `tbl1Mem`
(`lookup_tbl1Mem` closes the FlatHashMap `lookup` lowering's deviation (f); `insert_tbl1_*`).
-/
import Kraken.Promising.Lower.FlatLookup

open Kraken.AArch64.Parser
open Kraken
open Std.WP
open MachineWP
open Lean.Order

set_option mvcgen.warning false
set_option experimental.vcgen true

namespace Kraken.Promising.Lower.Flat

/-! ## 1. Word stores and loads; a concrete memory holding `tbl1` -/

/-- A word store at offset `o₁` from `base` leaves the word at offset `o₂`
alone when the two do not overlap and neither wraps. -/
theorem load_store_apart (m : DataMem) (base : BitVec 64) (o₁ o₂ : Nat) (v : Int)
    (h₁ : o₁ + 8 ≤ W64) (h₂ : o₂ + 8 ≤ W64) (h : o₁ + 8 ≤ o₂ ∨ o₂ + 8 ≤ o₁) :
    (m.storeInt (base + .ofNat 64 o₁) 8 v).loadInt (base + .ofNat 64 o₂) 8
      = m.loadInt (base + .ofNat 64 o₂) 8 := by
  have e : (base + BitVec.ofNat 64 o₂ - (base + BitVec.ofNat 64 o₁)).toNat
      = (W64 - o₁ + o₂) % W64 := by
    rw [show base + BitVec.ofNat 64 o₂ - (base + BitVec.ofNat 64 o₁)
        = BitVec.ofNat 64 o₂ - BitVec.ofNat 64 o₁ by bv_omega,
      BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [W64] at h₁ h₂ ⊢
    rw [Nat.mod_eq_of_lt (a := o₁) (by omega), Nat.mod_eq_of_lt (a := o₂) (by omega)]
  apply Mem.loadInt_storeInt_of_above <;> rw [e] <;> simp only [W64] at h₁ h₂ ⊢ <;> omega

/-- A word load reads back the word stored there (unsigned). -/
theorem load_store_same (m : DataMem) (a : BitVec 64) (v : Int) :
    (m.storeInt a 8 v).loadInt a 8 = some (v % 2 ^ 64) := by
  rw [Mem.loadInt_storeInt _ _ _ _ (by decide), ofBytes_toBytes]

/-- `n` words `f 0, …, f (n-1)` stored at `a, a + 8, …` over `m`. -/
def wordsAt (a : BitVec 64) (f : Nat → Nat) : Nat → DataMem → DataMem
  | 0, m => m
  | n + 1, m => (wordsAt a f n m).storeInt (a + BitVec.ofNat 64 (8 * n)) 8 (f n)

theorem wordsAt_load (a : BitVec 64) (f : Nat → Nat) (m : DataMem) (hf : ∀ i, f i < W64) :
    ∀ n, 8 * n ≤ W64 → ∀ i < n,
      (wordsAt a f n m).loadInt (a + BitVec.ofNat 64 (8 * i)) 8 = some (f i)
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, hn, i, hi => by
    rw [wordsAt]
    rcases Nat.lt_or_ge i n with h | h
    · rw [load_store_apart _ _ _ _ _ (by omega) (by omega) (by omega)]
      exact wordsAt_load a f m hf n (by omega) i h
    · rw [show i = n by omega, load_store_same]
      have := hf n; simp only [W64] at this
      congr 1; omega

theorem wordsAt_load_above (a : BitVec 64) (f : Nat → Nat) (m : DataMem) (o : Nat)
    (ho : o + 8 ≤ W64) : ∀ n, 8 * n ≤ o →
      (wordsAt a f n m).loadInt (a + BitVec.ofNat 64 o) 8 = m.loadInt (a + BitVec.ofNat 64 o) 8
  | 0, _ => rfl
  | n + 1, hn => by
    rw [wordsAt, load_store_apart _ _ _ _ _ (by omega) ho (by omega)]
    exact wordsAt_load_above a f m o ho n (by omega)

/-- `n` words at `a` leave a `k`-byte load at `b` alone when `b` is at an
offset of at least `8` past each word (mod `2^64`) and the load does not wrap. -/
theorem wordsAt_load_off (a b : BitVec 64) (f : Nat → Nat) (m : DataMem) (k : Nat) : ∀ n,
    (∀ i < n, 8 ≤ (b - (a + BitVec.ofNat 64 (8 * i))).toNat ∧ (b - (a + BitVec.ofNat 64 (8 * i))).toNat + k ≤ 2 ^ 64) →
      (wordsAt a f n m).loadInt b k = m.loadInt b k
  | 0, _ => rfl
  | n + 1, h => by
    rw [wordsAt, Mem.loadInt_storeInt_of_above _ _ _ _ _ _ (h n (by omega)).1 (h n (by omega)).2]
    exact wordsAt_load_off a b f m k n fun i hi => h i (by omega)

theorem shl_ofNat (g : BitVec 64) (k : Nat) :
    g <<< k = BitVec.ofNat 64 (2 ^ k * g.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mul_comm]

/-- A table's slot buffer as words: key, value, key, value, … -/
def slotWords (T : Tbl) (i : Nat) : Nat := if i % 2 = 0 then T.key (i / 2) else T.val (i / 2)

/-- **A concrete memory holding `tbl1`**: its control word at `0x1000`, its
eight slots at `0x2000` (from the empty memory). -/
def tbl1Mem : DataMem := wordsAt tbl1.sb (slotWords tbl1) 16 (wordsAt tbl1.cb tbl1.ctrl 1 ∅)

theorem tbl1_inMem : tbl1.InMem tbl1Mem := by
  have hw : ∀ i, slotWords tbl1 i < W64 := fun i => by
    simp only [slotWords, tbl1]; split <;> split <;> decide
  refine ⟨fun g hg => ?_, fun s hs => ?_⟩
  · change g.toNat ≤ 0 at hg
    have e : tbl1.cb + g <<< 3 = tbl1.sb + BitVec.ofNat 64 (W64 - 0x1000) := by
      rw [shl_ofNat]
      simp only [tbl1, W64]; bv_omega
    rw [e, tbl1Mem, wordsAt_load_above _ _ _ _ (by decide) 16 (by decide)]
    rw [show tbl1.sb + BitVec.ofNat 64 (W64 - 0x1000) = tbl1.cb + BitVec.ofNat 64 (8 * 0) by
      simp only [tbl1, W64]; bv_omega, show g.toNat = 0 by omega]
    exact wordsAt_load _ _ _ (fun _ => by show (hashN 5).1 * 2 ^ 16 < W64; decide +kernel)
      1 (by decide) 0 (by decide)
  · change s.toNat ≤ 7 at hs
    rw [shl_ofNat]
    have h1 := wordsAt_load tbl1.sb (slotWords tbl1) (wordsAt tbl1.cb tbl1.ctrl 1 ∅) hw 16
      (by decide) (2 * s.toNat) (by omega)
    have h2 := wordsAt_load tbl1.sb (slotWords tbl1) (wordsAt tbl1.cb tbl1.ctrl 1 ∅) hw 16
      (by decide) (2 * s.toNat + 1) (by omega)
    simp only [slotWords, Nat.mul_mod_right, Nat.mul_add_mod,
      Nat.mul_div_cancel_left _ (by decide : 0 < 2),
      show (2 * s.toNat + 1) / 2 = s.toNat by omega, ↓reduceIte] at h1 h2
    refine ⟨?_, ?_⟩
    · rw [show BitVec.ofNat 64 (2 ^ 4 * s.toNat) = BitVec.ofNat 64 (8 * (2 * s.toNat)) by
        congr 1; omega]
      exact h1
    · rw [show tbl1.sb + BitVec.ofNat 64 (2 ^ 4 * s.toNat) + 8#64
          = tbl1.sb + BitVec.ofNat 64 (8 * (2 * s.toNat + 1)) by
        simp only [W64] at *; bv_omega]
      exact h2

/-! ## 2. The model: WeakCore's `insert` at `Int` keys and values, no growth

From WeakCore `FlatHashMap.lean` (`insertD`, `place`, `freeSlotD`, `setCtrlD`,
`ctrlStore`) and `TermRun.lean` (`laneN`, `setLaneN`, `fenc`, `cvtN` at `w8`;
`stlw` is a word load, `setLaneN` and a word store there too). -/

/-- `fenc .w8` (`TermRun`): the 8-bit pattern of `z`. `cvtN .int .w8 x` is
`fenc8 x` (`srcVal .int x = x`). -/
def fenc8 (z : Int) : Nat := (z % 256).toNat % 256

/-- `laneN .w8 x j`: byte `j` of `x`. -/
def laneN8 (x j : Nat) : Nat := (x / 2 ^ (8 * j)) % 256

/-- `setLaneN .w8 x j v`: `x` with byte `j` replaced by `v`. -/
def setLaneN8 (x j v : Nat) : Nat :=
  let sh := 2 ^ (8 * j)
  let x := x % 2 ^ 64
  x - laneN8 x j * sh + (v % 256) * sh

/-- WeakCore's `freeSlot` [m] with fuel `n`: the first group from `pos`, on the
triangular sequence, with an empty or deleted lane (`freeOps false`: top bit
clear); `some (sr, isE)` is the raw slot of its lowest such lane and whether
that lane is empty; `none` is fuel out. -/
def freeN (T : Tbl) : Nat → Nat → Nat → Option (Nat × Nat)
  | 0, _, _ => none
  | n + 1, pos, st =>
    let g := bandN pos T.mv
    let w := T.ctrl g
    let fr := bitN .and (bit1N .not w) H8
    if fr = 0 then freeN T n (bitN .wadd pos (bitN .wadd st 1)) (bitN .wadd st 1)
    else
      let bz := bit1N .ctz fr
      some (bitN .or (bitN .shl g 3) (bitN .shr bz 3),
        bitN .and (bitN .shr (emptyN w) bz) 1)

/-- `f` with `f i := y`. -/
def upd (f : Nat → Nat) (i y : Nat) : Nat → Nat := fun j => if j = i then y else f j

/-- WeakCore's `setCtrl` [m] (portable): control byte `val` for raw slot `sr`,
a byte store into lane `sr & 7` of word `(sr >> 3) & m` (`stlw`). -/
def setCtrlN (T : Tbl) (sr val : Nat) : Tbl :=
  let g := bandN (bitN .shr sr 3) T.mv
  let b := bitN .and sr 7
  { T with ctrl := upd T.ctrl g (setLaneN8 (T.ctrl g) (b % 8) (fenc8 val)) }

/-- `place`: the fresh key in the free slot `sr` found by `freeSlot` (its
control byte, then key and value), `gl` less `isE`, `n + 1`. -/
def placeN (T : Tbl) (k v gl n : Nat) : Option (Nat × Nat) → Option (Tbl × Nat × Nat × Option Nat)
  | none => none
  | some (sr, isE) =>
    some ({ setCtrlN T sr (hashN k).1 with
        key := upd T.key (bandN sr T.cv) k, val := upd T.val (bandN sr T.cv) v },
      bitN .wsub gl isE, bitN .wadd n 1, none)

/-- `insert`'s `case` on `find`'s answer: replace the value, or (`gl > 0`)
place the key; growth (`gl = 0`) is not lowered. -/
def insContN (T : Tbl) (k v gl n : Nat) :
    Option (Option Nat) → Option (Tbl × Nat × Nat × Option Nat)
  | none => none
  | some (some sr) =>
    some ({ T with val := upd T.val (bandN sr T.cv) v }, gl, n, some (T.val (bandN sr T.cv)))
  | some none => if gl = 0 then none else placeN T k v gl n (freeN T (T.mv + 1) (hashN k).2 0)

/-- WeakCore's `insert` at `Int` keys and values: the new table, `gl`, `n`
and the answer (`some old` is `inr old`, `none` is `inl ()`); `none` overall
is a probe that does not end within `m + 1` groups, or `gl = 0` (growth, not
lowered). The displaced pair `xchgAt` returns on the fresh path is dropped, as
in WeakCore. -/
def insertN (T : Tbl) (k v gl n : Nat) : Option (Tbl × Nat × Nat × Option Nat) :=
  insContN T k v gl n (findN T k (hashN k).1 (T.mv + 1) (hashN k).2 0)

/-! ## 3. Memory algebra: the table under word stores -/

/-- The two buffers neither overlap nor wrap: the slot buffer starts at least
`8(m+1)` bytes above the control buffer and ends at most `2⁶⁴` above it (mod
`2⁶⁴`, so either buffer may be the lower one). -/
structure Tbl.Sep (T : Tbl) : Prop where
  lo : 8 * (T.mv + 1) ≤ (T.sb - T.cb).toNat
  hi : (T.sb - T.cb).toNat + 16 * (T.cv + 1) ≤ W64

/-- The bytes the table owns: its control buffer and its slot buffer. -/
def Tbl.Owns (T : Tbl) (a : BitVec 64) : Prop :=
  (a - T.cb).toNat < 8 * (T.mv + 1) ∨ (a - T.sb).toNat < 16 * (T.cv + 1)

section Mem
variable {T : Tbl} {m : DataMem}

theorem toInt_emod (x : BitVec 64) : x.toInt % 2 ^ 64 = x.toNat := by
  rw [BitVec.toInt_eq_toNat_cond]
  have := x.isLt
  split <;> omega

theorem ctrl_addr (g : BitVec 64) : T.cb + g <<< 3 = T.cb + BitVec.ofNat 64 (8 * g.toNat) := by
  rw [shl_ofNat]

theorem key_addr (s : BitVec 64) (hs : T.Sep) :
    T.sb + s <<< 4 = T.cb + BitVec.ofNat 64 ((T.sb - T.cb).toNat + 16 * s.toNat) := by
  have := hs.hi; rw [shl_ofNat]; simp only [W64] at *; bv_omega

theorem val_addr (s : BitVec 64) (hs : T.Sep) :
    T.sb + s <<< 4 + 8#64 = T.cb + BitVec.ofNat 64 ((T.sb - T.cb).toNat + 16 * s.toNat + 8) := by
  have := hs.hi; rw [shl_ofNat]; simp only [W64] at *; bv_omega

theorem load_store_toNat (a : BitVec 64) (x : BitVec 64) :
    (m.storeInt a 8 x.toInt).loadInt a 8 = some (x.toNat : Int) := by
  rw [load_store_same, toInt_emod]

/-- `InMem` after the store of control word `g`. -/
theorem inMem_ctrl (hm : T.InMem m) (hs : T.Sep) (g x : BitVec 64) (hg : g.toNat ≤ T.mv) :
    { T with ctrl := upd T.ctrl g.toNat x.toNat }.InMem (m.storeInt (T.cb + g <<< 3) 8 x.toInt) := by
  have := hs.lo; have := hs.hi; have hW : W64 = 18446744073709551616 := rfl
  refine ⟨fun g' (hg' : g'.toNat ≤ T.mv) => ?_, fun s (hs' : s.toNat ≤ T.cv) => ?_⟩
  · have h1 := hm.1 g' hg'
    rw [ctrl_addr] at h1 ⊢; rw [ctrl_addr]
    by_cases e : g'.toNat = g.toNat
    · simp only [upd, e, ite_true, load_store_toNat]; rfl
    · rw [load_store_apart _ _ _ _ _ (by omega) (by omega) (by omega)]
      simp only [upd, e, ite_false]; exact h1
  · have h1 := hm.2 s hs'
    rw [val_addr s hs, key_addr s hs] at h1
    rw [val_addr s hs, key_addr s hs, ctrl_addr,
      load_store_apart _ _ _ _ _ (by omega) (by omega) (by omega),
      load_store_apart _ _ _ _ _ (by omega) (by omega) (by omega)]
    exact h1

/-- `InMem` after the store of the key of slot `s`. -/
theorem inMem_key (hm : T.InMem m) (hs : T.Sep) (s x : BitVec 64) (h : s.toNat ≤ T.cv) :
    { T with key := upd T.key s.toNat x.toNat }.InMem (m.storeInt (T.sb + s <<< 4) 8 x.toInt) := by
  have := hs.lo; have := hs.hi; have hW : W64 = 18446744073709551616 := rfl
  refine ⟨fun g' (hg' : g'.toNat ≤ T.mv) => ?_, fun s' (hs' : s'.toNat ≤ T.cv) => ?_⟩
  · have h1 := hm.1 g' hg'
    rw [ctrl_addr] at h1 ⊢; rw [key_addr s hs]
    rw [load_store_apart _ _ _ _ _ (by omega) (by omega) (by omega)]; exact h1
  · have h1 := hm.2 s' hs'
    rw [val_addr s' hs, key_addr s' hs] at h1
    rw [val_addr s' hs, key_addr s' hs, key_addr s hs]
    refine ⟨?_, ?_⟩
    · by_cases e : s'.toNat = s.toNat
      · simp only [upd, e, ite_true, load_store_toNat]; rfl
      · rw [load_store_apart _ _ _ _ _ (by omega) (by omega) (by omega)]
        simp only [upd, e, ite_false]; exact h1.1
    · rw [load_store_apart _ _ _ _ _ (by omega) (by omega) (by omega)]; exact h1.2

/-- `InMem` after the store of the value of slot `s`. -/
theorem inMem_val (hm : T.InMem m) (hs : T.Sep) (s x : BitVec 64) (h : s.toNat ≤ T.cv) :
    { T with val := upd T.val s.toNat x.toNat }.InMem
      (m.storeInt (T.sb + s <<< 4 + 8#64) 8 x.toInt) := by
  have := hs.lo; have := hs.hi; have hW : W64 = 18446744073709551616 := rfl
  refine ⟨fun g' (hg' : g'.toNat ≤ T.mv) => ?_, fun s' (hs' : s'.toNat ≤ T.cv) => ?_⟩
  · have h1 := hm.1 g' hg'
    rw [ctrl_addr] at h1 ⊢; rw [val_addr s hs]
    rw [load_store_apart _ _ _ _ _ (by omega) (by omega) (by omega)]; exact h1
  · have h1 := hm.2 s' hs'
    rw [val_addr s' hs, key_addr s' hs] at h1
    rw [val_addr s' hs, key_addr s' hs, val_addr s hs]
    refine ⟨?_, ?_⟩
    · rw [load_store_apart _ _ _ _ _ (by omega) (by omega) (by omega)]; exact h1.1
    · by_cases e : s'.toNat = s.toNat
      · simp only [upd, e, ite_true, load_store_toNat]; rfl
      · rw [load_store_apart _ _ _ _ _ (by omega) (by omega) (by omega)]
        simp only [upd, e, ite_false]; exact h1.2

/-- A word store inside `[base, base + len)` leaves every byte outside it. -/
theorem get_store_out (base A a : BitVec 64) (len : Nat) (v : Int) (hl : len ≤ W64)
    (hA : (A - base).toNat + 8 ≤ len) (ha : ¬ (a - base).toNat < len) :
    (m.storeInt A 8 v).get? a = m.get? a := by
  apply Mem.get?_storeBytes_of_not_mem
  rw [mem_At_iff, Int.toBytes_length]
  rintro ⟨i, hi, rfl⟩
  apply ha
  rw [show A + BitVec.ofNat 64 i - base = (A - base) + BitVec.ofNat 64 i by bv_omega,
    BitVec.toNat_add, BitVec.toNat_ofNat]
  simp only [W64] at hl; omega

/-! ### Frames of the three stores -/

theorem frame_ctrl (g : BitVec 64) (hs : T.Sep) (hg : g.toNat ≤ T.mv) (v : Int) (a : BitVec 64)
    (ha : ¬ T.Owns a) : (m.storeInt (T.cb + g <<< 3) 8 v).get? a = m.get? a := by
  have := hs.lo; have := hs.hi; have hW : W64 = 18446744073709551616 := rfl
  refine get_store_out T.cb _ a (8 * (T.mv + 1)) v (by omega) ?_ (fun h => ha (Or.inl h))
  rw [ctrl_addr, show T.cb + BitVec.ofNat 64 (8 * g.toNat) - T.cb = BitVec.ofNat 64 (8 * g.toNat)
    by bv_omega, BitVec.toNat_ofNat]; omega

theorem frame_key (s : BitVec 64) (hs : T.Sep) (h : s.toNat ≤ T.cv) (v : Int) (a : BitVec 64)
    (ha : ¬ T.Owns a) : (m.storeInt (T.sb + s <<< 4) 8 v).get? a = m.get? a := by
  have := hs.lo; have := hs.hi; have hW : W64 = 18446744073709551616 := rfl
  refine get_store_out T.sb _ a (16 * (T.cv + 1)) v (by omega) ?_ (fun h => ha (Or.inr h))
  rw [shl_ofNat, show T.sb + BitVec.ofNat 64 (2 ^ 4 * s.toNat) - T.sb
    = BitVec.ofNat 64 (2 ^ 4 * s.toNat) by bv_omega, BitVec.toNat_ofNat]; omega

theorem frame_val (s : BitVec 64) (hs : T.Sep) (h : s.toNat ≤ T.cv) (v : Int) (a : BitVec 64)
    (ha : ¬ T.Owns a) : (m.storeInt (T.sb + s <<< 4 + 8#64) 8 v).get? a = m.get? a := by
  have := hs.lo; have := hs.hi; have hW : W64 = 18446744073709551616 := rfl
  refine get_store_out T.sb _ a (16 * (T.cv + 1)) v (by omega) ?_ (fun h => ha (Or.inr h))
  rw [shl_ofNat, show T.sb + BitVec.ofNat 64 (2 ^ 4 * s.toNat) + 8#64 - T.sb
    = BitVec.ofNat 64 (2 ^ 4 * s.toNat + 8) by bv_omega, BitVec.toNat_ofNat]; omega

end Mem

/-! ### The control-byte store as a word read-modify-write

WC rule 6: no sub-word store. `stlw` is lowered as word load, `setLaneN .w8`'s
formula `x - laneN x j · 2^{8j} + (v mod 256) · 2^{8j}` (`lsr`, `and`, `lsl`,
`sub`, `and`, `lsl`, `add`), word store; sequentially exact on owned bytes. -/

theorem lane_arith (X V J : Nat) (hX : X < 2 ^ 64) (hV : V < 256) (hJ : J < 8) :
    X / 2 ^ (8 * J) % 256 * 2 ^ (8 * J) ≤ X
      ∧ X - X / 2 ^ (8 * J) % 256 * 2 ^ (8 * J) + V * 2 ^ (8 * J) < 2 ^ 64 := by
  obtain _|_|_|_|_|_|_|_|J := J <;> simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd] <;> omega

/-- **The control-byte store, lowered as a word read-modify-write** computes
`setLaneN .w8`: the machine's `x - (((x >> 8j) & 0xff) << 8j) + ((h & 0xff) << 8j)`
is WeakCore's `setLaneN .w8 x j (cvtN .int .w8 h)`, for a lane `j < 8`. -/
theorem setLane_bv (x h j : BitVec 64) (hj : j.toNat < 8) :
    (x - (x >>> ((j <<< 3).toNat % 64) &&& 0xff#64) <<< ((j <<< 3).toNat % 64)
       + (h &&& 0xff#64) <<< ((j <<< 3).toNat % 64)).toNat
      = setLaneN8 x.toNat j.toNat (fenc8 h.toNat) := by
  have hk : (j <<< 3).toNat % 64 = 8 * j.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hX := x.isLt
  have hff : (0xff#64).toNat = 2 ^ 8 - 1 := rfl
  have hL : (x >>> (8 * j.toNat) &&& 0xff#64).toNat = x.toNat / 2 ^ (8 * j.toNat) % 256 := by
    rw [BitVec.toNat_and, hff, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow]
  have hH : (h &&& 0xff#64).toNat = h.toNat % 256 := by
    rw [BitVec.toNat_and, hff, Nat.and_two_pow_sub_one_eq_mod]
  obtain ⟨a1, a2⟩ := lane_arith x.toNat (h.toNat % 256) j.toNat hX (Nat.mod_lt _ (by decide)) hj
  have hsh : ∀ y : BitVec 64, y.toNat * 2 ^ (8 * j.toNat) < 2 ^ 64 →
      (y <<< (8 * j.toNat)).toNat = y.toNat * 2 ^ (8 * j.toNat) := fun y hy => by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hy]
  rw [hk]
  have e1 := hsh _ (by rw [hL]; omega)
  have e2 := hsh _ (by rw [hH]; omega)
  rw [hL] at e1; rw [hH] at e2
  rw [BitVec.toNat_add, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, e1]; exact a1), e1, e2,
    Nat.mod_eq_of_lt a2]
  simp only [setLaneN8, laneN8, fenc8, Nat.mod_eq_of_lt hX]
  congr 2
  omega

/-! ### `freeSlot` ends where `find` ended -/

/-- An empty lane is free: `zb w` lies inside `¬w & H8`. -/
theorem free_of_empty (w : Nat) (h : emptyN w ≠ 0) : bitN .and (bit1N .not w) H8 ≠ 0 := by
  intro h0
  apply h
  have hH : H8 = (~~~0x7F7F7F7F7F7F7F7F#64).toNat := rfl
  have e1 : emptyN w = (zbBV (BitVec.ofNat 64 w)).toNat := by
    rw [zbBV_toNat, BitVec.toNat_ofNat, emptyN]; simp only [zbN, bitN, bit1N, W64, Nat.mod_mod]
  have e2 : bitN .and (bit1N .not w) H8 = (~~~BitVec.ofNat 64 w &&& ~~~0x7F7F7F7F7F7F7F7F#64).toNat := by
    have : bit1N .not w = (~~~BitVec.ofNat 64 w).toNat := by
      rw [← bit1N_not, BitVec.toNat_ofNat]; simp only [bit1N, W64, Nat.mod_mod]
    rw [this, hH, bitN_and]
  have e3 : zbBV (BitVec.ofNat 64 w) &&& (~~~BitVec.ofNat 64 w &&& ~~~0x7F7F7F7F7F7F7F7F#64)
      = zbBV (BitVec.ofNat 64 w) := by
    simp only [zbBV]; ext i; simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_or]
    cases (BitVec.ofNat 64 w)[i] <;> simp
  rw [e2] at h0; rw [e1, ← e3, BitVec.toNat_and, h0, Nat.and_zero]

/-- If `find` answers "absent", `freeSlot` from the same start answers too. -/
theorem freeN_isSome (T : Tbl) (k h2 : Nat) :
    ∀ n pos st, findN T k h2 n pos st = some none → (freeN T n pos st).isSome
  | 0, _, _, h => by simp [findN] at h
  | n + 1, pos, st, h => by
    simp only [findN] at h
    simp only [freeN]
    split
    · apply freeN_isSome T k h2 n
      cases hc : candN T k (bitN .shl (bandN pos T.mv) 3) (matchN (T.ctrl (bandN pos T.mv)) h2)
      · rw [hc] at h; simp only [contN] at h
        split at h
        · exact h
        · exact absurd ‹_› (free_of_empty _ ‹_›)
      · rw [hc] at h; simp [contN] at h
    · rfl

/-! ## 4. The code and its specification

ABI (as `lookup`'s, a deviation from WeakCore's by-value `MapT`): arguments
`x0 = cb`, `x1 = sb`, `x2 = m`, `x3 = c`, `x4 = k`, `x5 = v`, `x6 = gl`,
`x7 = n`; results `x0` = the tag (`0` = `inl ()`, `1` = `inr old`), `x1 = old`,
`x2 = gl'`, `x3 = n'`; the table is updated in place. `x0 = 2` at `grow`:
growth is **not lowered** (`gl = 0`, excluded by `GrowthLeft`). Scratch:
`x8`–`x17`; `x18`–`x30` and `sp` are untouched. -/

/-- `insert`, lowered. Blocks: the hash; `find`/`cand`/`cand_none`/`next` as
in `flatLookup`; `free` (one group of `freeSlot`), `place` (the free lane,
`setCtrl` as a word read-modify-write, the slot); `found` (`xchgAtF` of the
value); `grow`. -/
def flatInsert : Program := parseAArch64("
flat_insert:
  movz x9, #0x7c15
  movk x9, #0x7f4a, lsl #16
  movk x9, #0x79b9, lsl #32
  movk x9, #0x9e37, lsl #48
  umulh x10, x4, x9
  mul x11, x4, x9
  eor x10, x10, x11
  and x11, x10, #0x7f
  orr x8, x11, #0x80
  lsr x9, x10, #7
  mov x11, x9
  movz x10, #0
  mov x15, #0x7f7f7f7f7f7f7f7f
find:
  and x12, x9, x2
  ldr x16, [x0, x12, lsl #3]
  mov x17, #0x0101010101010101
  mul x14, x8, x17
  eor x14, x16, x14
  and x17, x14, x15
  add x17, x17, x15
  orr x17, x17, x14
  orr x17, x17, x15
  mvn x14, x17
  and x17, x16, x15
  add x17, x17, x15
  orr x17, x17, x16
  orr x17, x17, x15
  mvn x13, x17
  lsl x12, x12, #3
cand:
  cbz x14, cand_none
  rbit x16, x14
  clz x16, x16
  lsr x16, x16, #3
  orr x16, x12, x16
  and x17, x16, x3
  lsl x17, x17, #4
  ldr x16, [x1, x17]
  cmp x4, x16
  b.eq found
  sub x16, x14, #1
  and x14, x14, x16
  b cand
cand_none:
  cbz x13, next
  cbz x6, grow
  mov x9, x11
  movz x10, #0
free:
  and x12, x9, x2
  ldr x16, [x0, x12, lsl #3]
  mvn x17, x16
  and x17, x17, #0x8080808080808080
  cbnz x17, place
  add x10, x10, #1
  add x9, x9, x10
  b free
next:
  add x10, x10, #1
  add x9, x9, x10
  b find
place:
  and x13, x16, x15
  add x13, x13, x15
  orr x13, x13, x16
  orr x13, x13, x15
  mvn x13, x13
  rbit x14, x17
  clz x14, x14
  lsr x17, x14, #3
  lsr x13, x13, x14
  and x13, x13, #1
  lsl x12, x12, #3
  orr x16, x12, x17
  lsr x9, x16, #3
  and x9, x9, x2
  and x10, x16, #7
  lsl x10, x10, #3
  ldr x11, [x0, x9, lsl #3]
  lsr x12, x11, x10
  and x12, x12, #0xff
  lsl x12, x12, x10
  sub x11, x11, x12
  and x12, x8, #0xff
  lsl x12, x12, x10
  add x11, x11, x12
  str x11, [x0, x9, lsl #3]
  and x17, x16, x3
  lsl x17, x17, #4
  str x4, [x1, x17]
  add x17, x1, x17
  str x5, [x17, #8]
  sub x2, x6, x13
  add x3, x7, #1
  movz x0, #0
  ret
found:
  add x17, x1, x17
  ldr x1, [x17, #8]
  str x5, [x17, #8]
  mov x2, x6
  mov x3, x7
  movz x0, #1
  ret
grow:
  movz x0, #2
  ret
")

/-- `insert`'s logical arguments. -/
structure InsX where
  T : Tbl
  k : Nat
  v : Nat
  gl : Nat
  n : Nat

/-- The arguments in their registers, and the return address. -/
def InsArgs (x : InsX) (ra : Int64) (s : MachineData) : Prop :=
  s.regs.X0.toBitVec = x.T.cb ∧ s.regs.X1.toBitVec = x.T.sb ∧ rv s.regs.X2.toBitVec = x.T.mv
    ∧ rv s.regs.X3.toBitVec = x.T.cv ∧ rv s.regs.X4.toBitVec = x.k ∧ rv s.regs.X5.toBitVec = x.v
    ∧ rv s.regs.X6.toBitVec = x.gl ∧ rv s.regs.X7.toBitVec = x.n ∧ s.regs.X30.toBitVec = ra.toBitVec

/-- **The no-growth hypothesis** (a start-state property): `growth_left > 0`. -/
def GrowthLeft (x : InsX) : Prop := 0 < x.gl

/-- `insert`'s precondition: arguments, the table in memory (read-write), its
buffers apart, R-INT, the probe-termination property, and `GrowthLeft`. -/
def InsPre (x : InsX) (ra : Int64) (t : MachineData) : Prop :=
  InsArgs x ra t ∧ x.T.InMem t.dmem ∧ x.T.Bounded x.k ∧ x.T.Sep ∧ ProbeEnds x.T x.k ∧ GrowthLeft x

/-- `insert`'s postcondition: the model's answer and `gl`, `n` in the result
registers; the model's new table in memory; every byte outside the table's
two buffers as it was; `sp` and `x19`–`x28` unchanged. -/
def InsPost (x : InsX) (_ra : Int64) (t₀ s : MachineData) : Prop :=
  ∃ T' gl' n' r, insertN x.T x.k x.v x.gl x.n = some (T', gl', n', r) ∧ ResRegs r s
    ∧ rv s.regs.X2.toBitVec = gl' ∧ rv s.regs.X3.toBitVec = n' ∧ T'.InMem s.dmem
    ∧ (∀ a, ¬ x.T.Owns a → s.dmem.get? a = t₀.dmem.get? a) ∧ Callee t₀ s

/-- `freeSlot`'s overall answer. -/
abbrev Rfr (x : InsX) : Option (Nat × Nat) := freeN x.T (x.T.mv + 1) (hashN x.k).2 0

/-- What every block after the hash keeps. -/
def InsCommon (x : InsX) (ra : Int64) (t₀ s : MachineData) : Prop :=
  InsPre x ra s ∧ s.dmem = t₀.dmem ∧ Callee t₀ s ∧ rv s.regs.X8.toBitVec = (hashN x.k).1
    ∧ s.regs.X15.toBitVec = 0x7F7F7F7F7F7F7F7F#64 ∧ rv s.regs.X10.toBitVec ≤ x.T.mv
    ∧ rv s.regs.X11.toBitVec = (hashN x.k).2

/-- `find`'s answer from the next group on. -/
abbrev restI (x : InsX) (s : MachineData) : Option (Option Nat) :=
  findN x.T x.k (hashN x.k).1 (x.T.mv - rv s.regs.X10.toBitVec)
    (bitN .wadd (rv s.regs.X9.toBitVec) (bitN .wadd (rv s.regs.X10.toBitVec) 1))
    (bitN .wadd (rv s.regs.X10.toBitVec) 1)

/-- The spec table. -/
def insTable (x : InsX) (ra : Int64) (t₀ : MachineData) : Label → MachineData → Prop
  | "flat_insert", s => s = t₀ ∧ InsPre x ra t₀
  | "find", s => InsCommon x ra t₀ s ∧ findN x.T x.k (hashN x.k).1
      (x.T.mv + 1 - rv s.regs.X10.toBitVec) (rv s.regs.X9.toBitVec) (rv s.regs.X10.toBitVec)
        = Rf x.T x.k
  | "cand", s => InsCommon x ra t₀ s ∧ contN (candN x.T x.k (rv s.regs.X12.toBitVec)
      (rv s.regs.X14.toBitVec)) (rv s.regs.X13.toBitVec) (restI x s) = Rf x.T x.k
  | "cand_none", s => InsCommon x ra t₀ s
      ∧ contN none (rv s.regs.X13.toBitVec) (restI x s) = Rf x.T x.k
  | "next", s => InsCommon x ra t₀ s ∧ restI x s = Rf x.T x.k
  | "found", s => InsCommon x ra t₀ s ∧ ∃ sr, Rf x.T x.k = some (some sr)
      ∧ s.regs.X17.toBitVec = BitVec.ofNat 64 (bandN sr x.T.cv) <<< 4
  | "free", s => InsCommon x ra t₀ s ∧ Rf x.T x.k = some none ∧ freeN x.T
      (x.T.mv + 1 - rv s.regs.X10.toBitVec) (rv s.regs.X9.toBitVec) (rv s.regs.X10.toBitVec)
        = Rfr x
  | "place", s => InsCommon x ra t₀ s ∧ Rf x.T x.k = some none ∧ freeN x.T
      (x.T.mv + 1 - rv s.regs.X10.toBitVec) (rv s.regs.X9.toBitVec) (rv s.regs.X10.toBitVec)
        = Rfr x ∧ s.regs.X12.toBitVec = s.regs.X9.toBitVec &&& s.regs.X2.toBitVec
      ∧ rv s.regs.X16.toBitVec = x.T.ctrl (rv s.regs.X12.toBitVec)
      ∧ s.regs.X17.toBitVec = ~~~s.regs.X16.toBitVec &&& 0x8080808080808080#64
      ∧ s.regs.X17.toBitVec ≠ 0#64
  | _, _ => False

/-- The variant: the find phase above the free phase (`+ m + 3`); in each, the
remaining fuel, then the candidate mask. -/
def insVar : Label → MachineData → Nat
  | "flat_insert", s => (rv s.regs.X2.toBitVec + 2) * (W64 + 1) + rv s.regs.X2.toBitVec + 3
  | "find", s => (rv s.regs.X2.toBitVec + 1 - rv s.regs.X10.toBitVec) * (W64 + 1) + W64
      + rv s.regs.X2.toBitVec + 3
  | "cand", s => (rv s.regs.X2.toBitVec + 1 - rv s.regs.X10.toBitVec) * (W64 + 1)
      + rv s.regs.X14.toBitVec + rv s.regs.X2.toBitVec + 3
  | "cand_none", s | "next", s => (rv s.regs.X2.toBitVec + 1 - rv s.regs.X10.toBitVec) * (W64 + 1)
      + rv s.regs.X2.toBitVec + 3
  | "free", s => rv s.regs.X2.toBitVec + 2 - rv s.regs.X10.toBitVec
  | _, _ => 0

/-- `freeSlot` with fuel left, one group unfolded. -/
theorem freeN_step (T : Tbl) (pos st : Nat) (h : st ≤ T.mv) :
    freeN T (T.mv + 1 - st) pos st =
      if bitN .and (bit1N .not (T.ctrl (bandN pos T.mv))) H8 = 0 then
        freeN T (T.mv - st) (bitN .wadd pos (bitN .wadd st 1)) (bitN .wadd st 1)
      else some (bitN .or (bitN .shl (bandN pos T.mv) 3)
          (bitN .shr (bit1N .ctz (bitN .and (bit1N .not (T.ctrl (bandN pos T.mv))) H8)) 3),
        bitN .and (bitN .shr (emptyN (T.ctrl (bandN pos T.mv)))
          (bit1N .ctz (bitN .and (bit1N .not (T.ctrl (bandN pos T.mv))) H8))) 1) := by
  rw [show T.mv + 1 - st = (T.mv - st) + 1 by omega]; rfl

theorem fr_rv (w : BitVec 64) :
    bitN .and (bit1N .not (rv w)) H8 = rv (~~~w &&& 0x8080808080808080#64) := by
  rw [rv_def, rv_def, bit1N_not, show H8 = (0x8080808080808080#64).toNat from rfl, bitN_and]

theorem ctz_rv (x : BitVec 64) : bit1N .ctz (rv x) = rv x.reverse.clz := by
  rw [rv_def, rv_def, ctz_toNat]; simp only [bit1N, W64, BitVec.toNat_mod_cancel]

theorem shr_rv (a b : BitVec 64) : bitN .shr (rv a) (rv b) = rv (a >>> (b.toNat % 64)) := by
  simp only [rv_def, bitN, W64, BitVec.toNat_mod_cancel, BitVec.toNat_ushiftRight]

theorem insertN_found {T : Tbl} {k v gl n sr : Nat} (h : Rf T k = some (some sr)) :
    insertN T k v gl n
      = some ({ T with val := upd T.val (bandN sr T.cv) v }, gl, n, some (T.val (bandN sr T.cv))) := by
  show insContN T k v gl n (Rf T k) = _
  rw [h]; rfl

theorem insertN_place {T : Tbl} {k v gl n sr e : Nat} (h : Rf T k = some none) (hg : 0 < gl)
    (hr : freeN T (T.mv + 1) (hashN k).2 0 = some (sr, e)) :
    insertN T k v gl n = some ({ setCtrlN T sr (hashN k).1 with
      key := upd T.key (bandN sr T.cv) k, val := upd T.val (bandN sr T.cv) v },
        bitN .wsub gl e, bitN .wadd n 1, none) := by
  obtain ⟨g, rfl⟩ : ∃ g, gl = g + 1 := ⟨gl - 1, by omega⟩
  show insContN T k v (g + 1) n (Rf T k) = _
  rw [h]
  show (if g + 1 = 0 then none else placeN T k v (g + 1) n (freeN T (T.mv + 1) (hashN k).2 0)) = _
  simp only [Nat.add_one_ne_zero, ↓reduceIte, hr]; rfl

/-- `freeSlot`'s probe has fuel left at every group it reaches. -/
theorem free_lt {T : Tbl} {k pos st : Nat} (hR : (Rfr ⟨T, k, 0, 0, 0⟩).isSome) (hst : st ≤ T.mv)
    (hf : freeN T (T.mv - st) pos (bitN .wadd st 1) = Rfr ⟨T, k, 0, 0, 0⟩) : st < T.mv := by
  rcases Nat.lt_or_ge st T.mv with h | h
  · exact h
  · rw [show T.mv - st = 0 by omega] at hf
    rw [← hf] at hR; exact absurd hR (by simp [freeN])

/-- A store keeps every loadable word loadable. -/
theorem loadInt_store_isSome (m : DataMem) (a b : BitVec 64) (v : Int)
    (h : (m.loadInt b 8).isSome = true) : ((m.storeInt a 8 v).loadInt b 8).isSome = true := by
  simp only [Mem.loadInt, Option.isSome_map, Mem.loadBytes, List.allSome_isSome_iff,
    List.mem_map, List.mem_range, forall_exists_index, and_imp] at h ⊢
  rintro o i hi rfl
  have := h _ i hi rfl
  simp only [Mem.storeInt, Mem.storeBytes, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.union_eq,
    Std.ExtHashMap.getElem?_union] at this ⊢
  cases (List.At (Int.toBytes 8 v) a)[b + BitVec.ofNat 64 i]? <;> simp_all

theorem val_load' {T : Tbl} {m : DataMem} {cm : BitVec 64} (hm : T.InMem m) (h : rv cm = T.cv)
    (a : BitVec 64) :
    Mem.loadInt m (T.sb + (a &&& cm) <<< 4 + 8#64) 8 = some (T.val (rv (a &&& cm))) := by
  rw [rv_def] at h ⊢; exact (hm.2 _ (h ▸ by rw [BitVec.toNat_and]; exact Nat.and_le_right)).2

theorem shr3_rv (a : BitVec 64) : bitN .shr (rv a) 3 = rv (a >>> 3) := by
  rw [rv_def, rv_def, bitN_shr a 3 (by decide)]

theorem and1_rv (a : BitVec 64) : bitN .and (rv a) 1 = rv (a &&& 1#64) := by
  rw [rv_def, rv_def]; exact bitN_and (a := a) (b := 1#64)

theorem or_rv (a b : BitVec 64) : bitN .or (rv a) (rv b) = rv (a ||| b) := by
  rw [rv_def, rv_def, rv_def, bitN_or]

theorem emptyN_rv' (w : BitVec 64) : emptyN (rv w) = rv (zbBV w) := by
  rw [rv_def, rv_def, zbBV_toNat, emptyN]

theorem shr_mod (x : BitVec 64) (n : Nat) :
    x.toNat >>> n % 18446744073709551616 = x.toNat >>> n :=
  Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) x.isLt)

/-- The table `place` leaves: control byte, key and value written. -/
def placeT (T : Tbl) (sr hh kk vv : Nat) : Tbl :=
  { setCtrlN T sr hh with
    key := upd T.key (bandN sr T.cv) kk, val := upd T.val (bandN sr T.cv) vv }

/-- `place`'s three stores: the model's new table in memory, every byte
outside the table as it was. -/
theorem place_mem {T : Tbl} {m : DataMem} (hm : T.InMem m) (hs : T.Sep)
    (hcw : ∀ g, T.ctrl g < W64) (sr mb cm x8 x4 x5 : BitVec 64) (hh kk vv sh : Nat)
    (hmb : rv mb = T.mv) (hcm : rv cm = T.cv) (hk : rv x4 = kk) (hv : rv x5 = vv)
    (h8 : rv x8 = hh) (hsh : sh = ((sr &&& 7#64) <<< 3).toNat % 64) :
    let g := sr >>> 3 &&& mb
    let w := BitVec.ofNat 64 (T.ctrl (rv g))
    let W := w - (w >>> sh &&& 0xff#64) <<< sh + (x8 &&& 0xff#64) <<< sh
    let s := sr &&& cm
    let m' := ((m.storeInt (T.cb + g <<< 3) 8 W.toInt).storeInt (T.sb + s <<< 4) 8
      x4.toInt).storeInt (T.sb + s <<< 4 + 8#64) 8 x5.toInt
    (placeT T (rv sr) hh kk vv).InMem m'
      ∧ ∀ a, ¬ T.Owns a → m'.get? a = m.get? a := by
  intro g w W s m'
  subst hk hv h8 hsh
  have hg : g.toNat ≤ T.mv := by
    rw [← hmb, rv_def, BitVec.toNat_and]; exact Nat.and_le_right
  have hsl : s.toNat ≤ T.cv := by
    rw [← hcm, rv_def, BitVec.toNat_and]; exact Nat.and_le_right
  have hj : (sr &&& 7#64).toNat < 8 := by
    rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hW : W.toNat = setLaneN8 (T.ctrl g.toNat) (sr &&& 7#64).toNat (fenc8 x8.toNat) := by
    have := setLane_bv w x8 (sr &&& 7#64) hj
    rw [show w.toNat = T.ctrl g.toNat by
      rw [BitVec.toNat_ofNat, ← rv_def]; exact Nat.mod_eq_of_lt (hcw _)] at this
    exact this
  have e1 : bandN (bitN .shr sr.toNat 3) T.mv = g.toNat := by
    have := shr3_rv sr; rw [rv_def, rv_def] at this
    rw [this, ← rv_def (sr >>> 3), bandN_rv hmb, rv_def]
  have e2 : bitN .and sr.toNat 7 % 8 = (sr &&& 7#64).toNat := by
    rw [show bitN .and sr.toNat 7 = (sr &&& 7#64).toNat from bitN_and sr 7#64,
      Nat.mod_eq_of_lt hj]
  have e3 : bandN sr.toNat T.cv = s.toNat := by rw [← rv_def sr, bandN_rv hcm, rv_def]
  have h1 := inMem_ctrl hm hs g W hg
  have h2 := inMem_key h1 ⟨hs.lo, hs.hi⟩ s x4 hsl
  have h3 := inMem_val h2 ⟨hs.lo, hs.hi⟩ s x5 hsl
  refine ⟨?_, fun a ha => ?_⟩
  · simp only [placeT, setCtrlN, e1, e2, e3, ← hW, rv_def]
    exact h3
  · rw [frame_val s hs hsl _ a ha, frame_key s hs hsl _ a ha, frame_ctrl g hs hg _ a ha]

/-- `tbl1`'s buffers apart, and its facts at the fresh key `6`. -/
theorem tbl1_sep : tbl1.Sep := ⟨by decide, by decide⟩

theorem tbl1_bounded6 : tbl1.Bounded 6 :=
  ⟨tbl1_bounded.mv, tbl1_bounded.cv, tbl1_bounded.key, tbl1_bounded.val, tbl1_bounded.ctrl,
    by decide⟩

theorem tbl1_probeEnds6 : ProbeEnds tbl1 6 := by
  show (lookupN tbl1 6).isSome = true
  rw [tbl1_lookup6]; rfl

section Spec
variable [CodeEnv]

set_option hygiene false in
/-- Open block `l`'s invariant: the arguments `h0`–`h7`, `hlr`, `hmem` (at
`t₀`'s memory), `hb`, `hsep`, `hpe`, `hgl`, `hdm`, `hcs`, `h8`, `h15`, `hst`,
`h11`, and the block's own facts `hf`. -/
local macro "open_inv" l:str : tactic => `(tactic| (
  have h := ‹insTable _ _ _ $l _ ∧ _›
  simp only [insTable, insVar] at h
  obtain ⟨⟨hc, hf⟩, rfl⟩ := h
  simp only [InsCommon, InsPre, InsArgs, GrowthLeft, Callee] at hc
  obtain ⟨⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, hlr⟩, hmem, hb, hsep, hpe, hgl⟩, hdm, hcs, h8, h15,
    hst, h11⟩ := hc
  try dsimp only at h0 h1 h2 h3 h4 h5 h6 h7 hmem hb hsep hpe hgl h8 hst h11 hf
  rw [hdm] at hmem))

set_option hygiene false in
/-- Jump to a label: its invariant from the opened facts and `ts`. -/
local macro "goto_inv" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  refine Or.inl (Table.ofLabels_at ⟨by decide, ?_⟩)
  simp only [insTable, insVar, InsCommon, InsPre, InsArgs, Callee, GrowthLeft, restI]
  simp [h0, h1, h2, h3, h4, h5, h6, h7, hlr, hmem, hb, hsep, hpe, hgl, hdm, hcs, h8, h15, hst,
    h11, $ts,*]))

set_option linter.unusedSimpArgs false in
theorem insert_spec (hpl : Program.PlacedIn flatInsert) :
    cenv.ProcSpec ((_root_.Executable.labels cenv).label "flat_insert") InsPre InsPost := by
  refine Kraken.Executable.ProcSpec.of_cfg (p := flatInsert) insTable insVar
    (hblocks := ?_) (hpre := fun x ra t h => ⟨rfl, h⟩)
  rintro ⟨T, k, v, gl, n⟩ ra t₀
  cfg_cases [flatInsert]
  · -- the hash
    vcgen
    have h := ‹insTable _ ra _ "flat_insert" _ ∧ _›
    simp only [insTable, insVar, InsPre, InsArgs, GrowthLeft] at h
    obtain ⟨⟨rfl, ⟨h0, h1, h2, h3, rfl, h5, h6, h7, hlr⟩, hmem, hb, hsep, hpe, hgl⟩, rfl⟩ := h
    simp only [insTable, insVar, InsCommon, InsPre, InsArgs, Callee, GrowthLeft]
    simp [h0, h1, h2, h3, h5, h6, h7, hlr, hmem, hb, hsep, hpe, hgl, hashN_rv, hmB, var_le, Rf]
  · -- find: one group
    vcgen
    all_goals
      open_inv "find"
      rw [findN_step _ _ _ _ _ hst] at hf
      simp only [bandN_rv h2, shl3_rv, matchN_rv (hb.ctrl _) h8, emptyN_rv (hb.ctrl _),
        matchBV, zbBV] at hf
      try (rename_i v hv _ _; simp [h0, hdm, ctrl_load hmem h2] at hv; subst hv)
      simp only [insTable, insVar, InsCommon, InsPre, InsArgs, Callee, GrowthLeft, restI]
      simp [h0, h1, h2, h3, h4, h5, h6, h7, hlr, hmem, hb, hsep, hpe, hgl, hdm, hcs, h8, h15, hst,
        h11, ctrl_load hmem h2, hf, Nat.le_of_lt (rv_lt _)]
  · -- cand: one lane
    vcgen
    all_goals open_inv "cand"
    case vc1 => -- no lane left
      rename_i hz _
      simp at hz
      simp only [hz, rv_zero, candN_zero] at hf
      goto_inv [hf, hz]
      decide
    case vc4 => -- the key matches
      rename_i hz _ v hv hc _
      simp [h1, hdm, key_load hmem h3] at hv hz
      subst hv
      simp at hc
      rw [sub_rv _ _ (hb.key _), h4] at hc
      rw [candN_rv _ _ _ _ hz] at hf
      simp only [bandN_rv h3, ← hc, eq_self, ite_true, contN] at hf
      refine Or.inl (Table.ofLabels_at ⟨by decide, ?_⟩)
      simp only [insTable, insVar, InsCommon, InsPre, InsArgs, Callee, GrowthLeft]
      simp [h0, h1, h2, h4, h5, h6, h7, hlr, hmem, hb, hsep, hpe, hgl, hdm, hcs, h8, h15, hst, h11]
      exact ⟨h3, _, hf.symm, by rw [bandN_rv h3, ofNat_rv]⟩
    case vc5 => -- it does not: the next lane
      rename_i hz _ v hv hc _
      simp [h1, hdm, key_load hmem h3] at hv hz
      subst hv
      simp at hc
      rw [sub_rv _ _ (hb.key _), h4] at hc
      rw [candN_rv _ _ _ _ hz] at hf
      simp only [bandN_rv h3, hc, ite_false] at hf
      goto_inv [hf, clear_lt _ hz]
    all_goals simp [h1, hdm, key_load hmem h3]
  · -- cand_none
    vcgen
    all_goals open_inv "cand_none"
    case vc1 => -- no empty lane: the next group
      rename_i hz _
      simp at hz
      simp only [contN, hz, rv_zero, ↓reduceIte] at hf
      goto_inv [hf]
      decide
    case vc2 => -- absent, and `gl = 0`: excluded
      rename_i hz _ hg _
      simp at hg
      rw [hg, rv_zero] at h6; omega
    case vc3 => -- absent: `freeSlot` from the start
      rename_i hz hg _
      simp at hz
      simp only [contN, rv_ne _ hz, ↓reduceIte] at hf
      simp only [insTable, insVar, InsCommon, InsPre, InsArgs, Callee, GrowthLeft]
      simp [h0, h1, h2, h3, h4, h5, h6, h7, hlr, hmem, hb, hsep, hpe, hgl, hdm, hcs, h8, h15,
        h11, hf]
      exact Nat.le_succ_of_le (Nat.le_add_left _ _)
  · -- free: one group
    vcgen
    all_goals
      open_inv "free"
      obtain ⟨hn, hf⟩ := hf
      have hR := freeN_isSome T k _ _ _ _ hn
      have hfr := hf
      rw [freeN_step _ _ _ hst, bandN_rv h2] at hf
    case vc3 => -- a free lane: `place`
      have hv := ‹Mem.loadInt _ _ _ = some _›
      simp [h0, hdm, ctrl_load hmem h2] at hv
      subst hv
      rename_i hz
      simp at hz
      goto_inv [hn, hfr, hz, rv_ofNat _ (hb.ctrl _)]
      omega
    case vc4 => -- none: the next group
      have hv := ‹Mem.loadInt _ _ _ = some _›
      simp [h0, hdm, ctrl_load hmem h2] at hv
      subst hv
      rename_i hz
      simp at hz
      rw [← rv_ofNat (T.ctrl _) (hb.ctrl _), fr_rv, hz, rv_zero] at hf
      simp only [↓reduceIte] at hf
      have hlt := free_lt (k := k) hR hst hf
      have h10 := rv_add1 _ (Nat.lt_trans (Nat.succ_lt_succ hlt) hb.mv)
      simp only [wadd1] at hf
      simp only [wadd_rv] at hf
      simp only [h10] at hf
      goto_inv [hn, hf, h10, Nat.succ_le_of_lt hlt]
      omega
    all_goals simp [h0, hdm, ctrl_load hmem h2]
  · -- next: the triangular step
    vcgen
    all_goals
      open_inv "next"
      have hlt := next_lt hpe hst hf
      have h10 := rv_add1 _ (Nat.lt_trans (Nat.succ_lt_succ hlt) hb.mv)
      simp only [restI, wadd1] at hf
      simp only [wadd_rv] at hf
      simp only [h10] at hf
      goto_inv [hf, h10, var_lt _ _ hst, Nat.succ_le_of_lt hlt]
  · -- place
    vcgen
    all_goals
      open_inv "place"
      obtain ⟨hn, hfr, h12, h16, h17, hz⟩ := hf
    all_goals try (simp [h0, h1, hdm, ctrl_load hmem h2]; done)
    all_goals
      have hv := ‹Mem.loadInt _ _ _ = some _›
      simp [h0, hdm, ctrl_load hmem h2] at hv
      subst hv
    case vc6 =>
      simp [h0, h1, hdm]
      exact loadInt_store_isSome _ _ _ _ (by rw [key_load hmem h3]; rfl)
    case vc8 =>
      simp [h0, h1, hdm]
      exact loadInt_store_isSome _ _ _ _ (loadInt_store_isSome _ _ _ _
        (by rw [val_load' hmem h3]; rfl))
    case vc9 =>
      rw [freeN_step _ _ _ hst, bandN_rv h2, ← h12, ← h16, fr_rv, ← h17] at hfr
      simp only [rv_ne _ hz, ↓reduceIte, shl3_rv, ctz_rv, shr3_rv, emptyN_rv', shr_rv, and1_rv,
        or_rv] at hfr
      refine Or.inr ⟨by simp [hlr], _, _, _, _, insertN_place hn hgl hfr.symm, ?_⟩
      simp [ResRegs, h0, h1, hdm, Callee, hcs, -BitVec.toInt_add, -BitVec.toInt_sub]
      refine ⟨?_, by rw [← h7, wadd1], ?_⟩
      · rw [← h6, rv_def, rv_def, rv_def, bitN_wsub, h15]; rfl
      · refine place_mem hmem hsep hb.ctrl _ _ _ _ _ _ _ _ _ _ h2 h3 h4 h5 h8 ?_
        simp
        rw [shr_mod]
  · -- found: the value replaced
    vcgen
    all_goals
      open_inv "found"
      obtain ⟨sr, hf, h17⟩ := hf
      try have hv := ‹Mem.loadInt _ _ _ = some _›
      have hvl := val_load hmem hb.cv (bandN sr T.cv) Nat.and_le_right
    case vc1 | vc2 | vc3 => simp [h1, h17, hdm, hvl]
    case vc4 => simp [h1, h17, hdm, hvl] at hv ⊢
    case vc5 =>
      simp [h1, h17, hdm, hvl] at hv
      subst hv
      refine Or.inr ⟨by simp [hlr], _, _, _, _, insertN_found hf, ?_⟩
      simp [ResRegs, hdm, Callee, hcs, h6, h7, UInt64.toNat_ofNat,
        Nat.mod_eq_of_lt (show T.val (bandN sr T.cv) < 2 ^ 64 from hb.val _)]
      have hle : bandN sr T.cv ≤ T.cv := Nat.and_le_right
      have hs : (BitVec.ofNat 64 (bandN sr T.cv)).toNat = bandN sr T.cv :=
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hb.cv)
      have hx : _ = v := (rv_def _).symm.trans h5
      rw [h1, h17]
      refine ⟨?_, fun a ha => frame_val _ hsep (by rw [hs]; exact hle) _ a ha⟩
      have key : ∀ x : BitVec 64, x.toNat = v → { T with val := upd T.val (bandN sr T.cv) v }.InMem
          (t₀.dmem.storeInt (T.sb + BitVec.ofNat 64 (bandN sr T.cv) <<< 4 + 8#64) 8 x.toInt) :=
        fun x hx => by
          have := inMem_val hmem hsep (BitVec.ofNat 64 (bandN sr T.cv)) x (by rw [hs]; exact hle)
          rwa [hs, hx] at this
      exact key _ hx
  · -- grow: unreachable
    vcgen
    all_goals
      have h := ‹insTable _ _ _ "grow" _ ∧ _›
      simp [insTable] at h

/-! ## 5. Non-vacuity at `tbl1` in `tbl1Mem` -/

/-- **Non-vacuity of `lookup_spec`, with `Args` as the only hypothesis**: from
any state whose registers hold `tbl1`'s arguments and key `5`, with the memory
replaced by `tbl1Mem`, `lookup` returns to `ra` with `x0 = 1`, `x1 = 55`, the
memory unchanged. (Closes the FlatHashMap `lookup` lowering's deviation (f).) -/
theorem lookup_tbl1Mem (hpl : Program.PlacedIn flatLookup) (ra : Int64) (t : MachineData)
    (ha : Args tbl1 5 ra t) :
    Eventually cenv.instrStep (fun st => st.2 = ra ∧ st.1.regs.X0 = 1 ∧ st.1.regs.X1.toNat = 55
        ∧ st.1.dmem = tbl1Mem)
      ({ t with dmem := tbl1Mem }, (_root_.Executable.labels cenv).label "flat_lookup") :=
  lookup_tbl1 hpl ra { t with dmem := tbl1Mem } ha tbl1_inMem

/-- **Non-vacuity, replace**: from `tbl1` in `tbl1Mem`, `insert 5 77` (with
`gl = 7`, `n = 1`) returns `inr 55` and `gl`, `n` unchanged, and memory then
holds a table in which `5` maps to `77`; bytes outside `tbl1`'s buffers are
untouched. Only the argument registers are assumed. -/
theorem insert_tbl1_replace (hpl : Program.PlacedIn flatInsert) (ra : Int64) (t : MachineData)
    (ha : InsArgs ⟨tbl1, 5, 77, 7, 1⟩ ra t) :
    Eventually cenv.instrStep (fun st => st.2 = ra ∧ st.1.regs.X0 = 1 ∧ st.1.regs.X1.toNat = 55
        ∧ rv st.1.regs.X2.toBitVec = 7 ∧ rv st.1.regs.X3.toBitVec = 1
        ∧ (∃ T', T'.InMem st.1.dmem ∧ lookupN T' 5 = some (some 77))
        ∧ ∀ a, ¬ tbl1.Owns a → st.1.dmem.get? a = tbl1Mem.get? a)
      ({ t with dmem := tbl1Mem }, (_root_.Executable.labels cenv).label "flat_insert") :=
  eventually_weaken _ _ _ _ (fun st ⟨hra, T', gl', n', r, hI, hres, h2, h3, hm, hfr, _⟩ => by
      have hl : (insertN tbl1 5 77 7 1).map (fun r => (lookupN r.1 5, r.2))
          = some (some (some 77), 7, 1, some 55) := by decide +kernel
      rw [hI] at hl
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨hl1, rfl, rfl, rfl⟩ := hl
      exact ⟨hra, hres.1, hres.2, h2, h3, ⟨T', hm, hl1⟩, hfr⟩)
    (insert_spec hpl ⟨tbl1, 5, 77, 7, 1⟩ ra { t with dmem := tbl1Mem }
      ⟨ha, tbl1_inMem, tbl1_bounded, tbl1_sep, tbl1_probeEnds, show 0 < 7 by decide⟩)

/-- **Non-vacuity, fresh key**: from `tbl1` in `tbl1Mem`, `insert 6 66` (with
`gl = 7`, `n = 1`) returns `inl ()`, `gl = 6` (an empty slot was used),
`n = 2`, and memory then holds a table in which `6` maps to `66` and `5` still
maps to `55`; bytes outside `tbl1`'s buffers are untouched. -/
theorem insert_tbl1_fresh (hpl : Program.PlacedIn flatInsert) (ra : Int64) (t : MachineData)
    (ha : InsArgs ⟨tbl1, 6, 66, 7, 1⟩ ra t) :
    Eventually cenv.instrStep (fun st => st.2 = ra ∧ st.1.regs.X0 = 0
        ∧ rv st.1.regs.X2.toBitVec = 6 ∧ rv st.1.regs.X3.toBitVec = 2
        ∧ (∃ T', T'.InMem st.1.dmem ∧ lookupN T' 6 = some (some 66)
          ∧ lookupN T' 5 = some (some 55))
        ∧ ∀ a, ¬ tbl1.Owns a → st.1.dmem.get? a = tbl1Mem.get? a)
      ({ t with dmem := tbl1Mem }, (_root_.Executable.labels cenv).label "flat_insert") :=
  eventually_weaken _ _ _ _ (fun st ⟨hra, T', gl', n', r, hI, hres, h2, h3, hm, hfr, _⟩ => by
      have hl : (insertN tbl1 6 66 7 1).map (fun r => (lookupN r.1 6, lookupN r.1 5, r.2))
          = some (some (some 66), some (some 55), 6, 2, none) := by decide +kernel
      rw [hI] at hl
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨hl1, hl2, rfl, rfl, rfl⟩ := hl
      exact ⟨hra, hres, h2, h3, ⟨T', hm, hl1, hl2⟩, hfr⟩)
    (insert_spec hpl ⟨tbl1, 6, 66, 7, 1⟩ ra { t with dmem := tbl1Mem }
      ⟨ha, tbl1_inMem, tbl1_bounded6, tbl1_sep, tbl1_probeEnds6, show 0 < 7 by decide⟩)

end Spec

end Kraken.Promising.Lower.Flat
