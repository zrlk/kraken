import Scc.Cert.Link

/-!
# The image of a static link's data symbols

The initial value of a word of `.data` is its image entry, else 0
(`Kraken.Promising.Memory.initVal`; `wordOf`), and a byte is a digit of its
word, little-endian (`byteAt`). A data symbol's **item** is what follows its
label up to the next label or alignment (`symItems`): its bytes `itemBytes`,
`itemLen` of them. `imageOk Λ secs code` checks by evaluation that each data
symbol of `.bss` and `.data` but the three regions of their own (`symRanges`)
has its item's bytes at its address in `Λ.image` (`image_symbols`; the words
of an 8-aligned item, `image_word`), inside `Λ.data` (`image_sub`), the
items disjoint (`image_disj`).

`scc_data_secs%` runs the loader's data-section reader on a listing at
elaboration time, for the generated code checks of both ISAs.
-/

namespace Scc.Cert.Link

open Scc.Sem Kraken.DataImage

deriving instance Lean.ToExpr for Kraken.DataImage.Item
deriving instance Lean.ToExpr for DataSecs

open Lean Elab Term Meta in
/-- `scc_data_secs% c`, `c` a string constant: the data sections the
canonical loader reads from its value (`dataSections`), at elaboration
time, as a literal (for either ISA's code check: `Scc/Cert/LinkA64.lean`,
`Scc/Cert/LinkX64.lean`). -/
elab "scc_data_secs% " id:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let text ← unsafe evalConst String n
  match dataSections text with
  | some d => return toExpr d
  | none => throwError "the loader does not read a line of the text's data sections"

/-- The initial word of an image at `w`: its entry, else 0. -/
def wordOf (img : List (Nat × Nat)) (w : Nat) : Nat := ((img.find? (·.1 == w)).map (·.2)).getD 0

/-- The initial byte of an image at `a`: a digit of its word, little-endian. -/
def byteAt (img : List (Nat × Nat)) (a : Nat) : Nat := wordOf img (a / 8 * 8) / 2 ^ (8 * (a % 8)) % 256

/-- A label or an alignment: where an item ends. -/
def isEnd : Item → Bool
  | .label _ | .align _ => true
  | _ => false

/-- Each label with its item: the items after it up to the next label or
alignment. -/
def symItems : List Item → List (String × List Item)
  | [] => []
  | .label x :: is => (x, is.takeWhile (!isEnd ·)) :: symItems is
  | _ :: is => symItems is

/-- The bytes of an item, `code` resolving `.quad` labels. -/
def itemBytes (code : String → Option Nat) : List Item → List Nat
  | [] => []
  | .bytes bs :: is => bs.map UInt8.toNat ++ itemBytes code is
  | .zero n :: is => List.replicate n 0 ++ itemBytes code is
  | .quad v :: is => bytes8 (v % 2 ^ 64).toNat ++ itemBytes code is
  | .quadLabel l :: is => bytes8 ((code l).getD 0 % 2 ^ 64) ++ itemBytes code is
  | _ :: is => itemBytes code is

/-- The size of an item (`itemBytes`' length, without building it). -/
def itemLen : List Item → Nat
  | [] => 0
  | .bytes bs :: is => bs.length + itemLen is
  | .zero n :: is => n + itemLen is
  | .quad _ :: is => 8 + itemLen is
  | .quadLabel _ :: is => 8 + itemLen is
  | _ :: is => itemLen is

theorem itemLen_eq (code : String → Option Nat) : ∀ is : List Item, itemLen is = (itemBytes code is).length
  | [] => rfl
  | .bytes bs :: is => by simp [itemLen, itemBytes, itemLen_eq code is]
  | .zero n :: is => by simp [itemLen, itemBytes, itemLen_eq code is]
  | .quad _ :: is => by simp [itemLen, itemBytes, bytes8, itemLen_eq code is]
  | .quadLabel _ :: is => by simp [itemLen, itemBytes, bytes8, itemLen_eq code is]
  | .label _ :: is => by simp [itemLen, itemBytes, itemLen_eq code is]
  | .align _ :: is => by simp [itemLen, itemBytes, itemLen_eq code is]

/-- Every item is `.zero`. -/
def allZero : List Item → Bool
  | [] => true
  | .zero _ :: is => allZero is
  | _ => false

/-- `bs` is the image's bytes from `a`. -/
def bytesFrom (img : List (Nat × Nat)) : Nat → List Nat → Bool
  | _, [] => true
  | a, b :: bs => byteAt img a == b && bytesFrom img (a + 1) bs

/-- The item `its` at `a` in the image: an all-zero item when no image word
meets it, else byte by byte. -/
def symOk (img : List (Nat × Nat)) (code : String → Option Nat) (a : Nat) (its : List Item) : Bool :=
  if allZero its then img.all fun p => decide (p.1 + 8 ≤ a ∨ a + itemLen its ≤ p.1)
  else bytesFrom img a (itemBytes code its)

/-- One of the three regions of their own. -/
def special (x : String) : Bool := x == heapSym || x == poolSym || x == pinnedSym

/-- The data symbols of `.bss` and `.data` but the regions of their own, with
their addresses and items. -/
def symRanges (Λ : Layout) (secs : DataSecs) : List (String × Nat × List Item) :=
  (symItems (secs.bss ++ secs.data)).filterMap fun (x, its) =>
    if special x then none else (Λ.symbols.lookup x).map fun a => (x, a, its)

/-- **The image holds every data symbol's item**, inside `Λ.data`, the items
disjoint; checked by evaluation. -/
def imageOk (Λ : Layout) (secs : DataSecs) (code : String → Option Nat) : Bool :=
  (symItems (secs.bss ++ secs.data)).all (fun (x, _) => special x || (Λ.symbols.lookup x).isSome) &&
  (symRanges Λ secs).all (fun (_, a, its) => symOk Λ.image code a its &&
    decide (Λ.data.lo ≤ a) && decide (a + itemLen its ≤ Λ.data.lo + Λ.data.size)) &&
  decide ((symRanges Λ secs).Pairwise fun r s => r.2.1 + itemLen r.2.2 ≤ s.2.1 ∨ s.2.1 + itemLen s.2.2 ≤ r.2.1)

theorem allZero_bytes {code : String → Option Nat} : ∀ {its : List Item}, allZero its = true →
    ∀ b ∈ itemBytes code its, b = 0
  | [], _, _, hb => by simp [itemBytes] at hb
  | .zero n :: is, h, b, hb => by
    simp only [itemBytes, List.mem_append, List.mem_replicate] at hb
    rcases hb with ⟨-, rfl⟩ | hb
    · rfl
    · exact allZero_bytes (its := is) (show allZero is = true from h) b hb
  | .label _ :: _, h, _, _ => by simp [allZero] at h
  | .align _ :: _, h, _, _ => by simp [allZero] at h
  | .bytes _ :: _, h, _, _ => by simp [allZero] at h
  | .quad _ :: _, h, _, _ => by simp [allZero] at h
  | .quadLabel _ :: _, h, _, _ => by simp [allZero] at h

theorem bytesFrom_spec {img : List (Nat × Nat)} : ∀ {a : Nat} {bs : List Nat}, bytesFrom img a bs = true →
    ∀ i (h : i < bs.length), byteAt img (a + i) = bs[i]
  | _, [], _, i, h => absurd h (by simp)
  | a, b :: bs, hb, i, h => by
    simp only [bytesFrom, Bool.and_eq_true, beq_iff_eq] at hb
    cases i with
    | zero => simpa using hb.1
    | succ i =>
      have := bytesFrom_spec hb.2 i (by simpa using h)
      rw [show a + (i + 1) = a + 1 + i by omega, this]
      rfl

/-- No image word meets `[a, a + n)`: every byte there is 0. -/
theorem byteAt_clear {img : List (Nat × Nat)} {a n : Nat}
    (h : img.all (fun p => decide (p.1 + 8 ≤ a ∨ a + n ≤ p.1)) = true) {p : Nat} (hp : a ≤ p) (hpn : p < a + n) :
    byteAt img p = 0 := by
  have hnone : img.find? (·.1 == p / 8 * 8) = none := by
    rw [List.find?_eq_none]
    intro q hq hqe
    have := List.all_eq_true.mp h q hq
    simp only [beq_iff_eq, decide_eq_true_eq] at hqe this
    omega
  simp [byteAt, wordOf, hnone]

theorem symOk_spec {img : List (Nat × Nat)} {code : String → Option Nat} {a : Nat} {its : List Item}
    (h : symOk img code a its = true) :
    ∀ i (hi : i < (itemBytes code its).length), byteAt img (a + i) = (itemBytes code its)[i] := by
  unfold symOk at h
  split at h
  next hz =>
    intro i hi
    rw [byteAt_clear h (Nat.le_add_right a i) (by rw [itemLen_eq code]; omega)]
    exact (allZero_bytes hz _ (List.getElem_mem hi)).symm
  next => exact bytesFrom_spec h

theorem mem_symRanges {Λ : Layout} {secs : DataSecs} {x : String} {a : Nat} {its : List Item} :
    (x, a, its) ∈ symRanges Λ secs ↔
      (x, its) ∈ symItems (secs.bss ++ secs.data) ∧ special x = false ∧ Λ.symbols.lookup x = some a := by
  unfold symRanges
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨y, js⟩, hy, he⟩
    by_cases hs : special y = true
    · simp [hs] at he
    · simp only [hs, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at he
      obtain ⟨b, hb, he⟩ := he
      cases he
      exact ⟨hy, by simpa using hs, hb⟩
  · rintro ⟨hx, hs, ha⟩
    exact ⟨(x, its), hx, by simp [hs, ha]⟩

/-- **Every data symbol's item is in the image** (`imageOk`): at the
symbol's address, the item's bytes (the regions of their own excepted). -/
theorem image_symbols {Λ : Layout} {secs : DataSecs} {code : String → Option Nat}
    (h : imageOk Λ secs code = true) {x : String} {its : List Item}
    (hx : (x, its) ∈ symItems (secs.bss ++ secs.data)) (hs : special x = false) :
    ∃ a, Λ.symbols.lookup x = some a ∧
      ∀ i (hi : i < (itemBytes code its).length), byteAt Λ.image (a + i) = (itemBytes code its)[i] := by
  simp only [imageOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hres, hok⟩, -⟩ := h
  have := hres _ hx
  simp only [hs, Bool.false_or, Option.isSome_iff_exists] at this
  obtain ⟨a, ha⟩ := this
  have hr := hok _ (mem_symRanges.mpr ⟨hx, hs, ha⟩)
  exact ⟨a, ha, symOk_spec hr.1.1⟩

/-- **The items lie in `Λ.data`** (`imageOk`). -/
theorem image_sub {Λ : Layout} {secs : DataSecs} {code : String → Option Nat}
    (h : imageOk Λ secs code = true) {x : String} {a : Nat} {its : List Item}
    (hr : (x, a, its) ∈ symRanges Λ secs) :
    Λ.data.lo ≤ a ∧ a + (itemBytes code its).length ≤ Λ.data.lo + Λ.data.size := by
  simp only [imageOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  have := h.1.2 _ hr
  rw [← itemLen_eq code]
  exact ⟨this.1.2, this.2⟩

/-- **The items are disjoint** (`imageOk`): two data symbols' items, at
distinct places of `symRanges`, do not overlap. -/
theorem image_disj {Λ : Layout} {secs : DataSecs} {code : String → Option Nat}
    (h : imageOk Λ secs code = true) :
    (symRanges Λ secs).Pairwise fun r s =>
      r.2.1 + (itemBytes code r.2.2).length ≤ s.2.1 ∨ s.2.1 + (itemBytes code s.2.2).length ≤ r.2.1 := by
  simp only [imageOk, Bool.and_eq_true, decide_eq_true_eq] at h
  simpa only [itemLen_eq code] using h.2

/-- A word is its 8 little-endian bytes. -/
theorem word_bytes (v : Nat) (hv : v < 2 ^ 64) :
    v = v % 256 + v / 2 ^ 8 % 256 * 2 ^ 8 + v / 2 ^ 16 % 256 * 2 ^ 16 + v / 2 ^ 24 % 256 * 2 ^ 24 +
      v / 2 ^ 32 % 256 * 2 ^ 32 + v / 2 ^ 40 % 256 * 2 ^ 40 + v / 2 ^ 48 % 256 * 2 ^ 48 +
      v / 2 ^ 56 % 256 * 2 ^ 56 := by
  omega

/-- The little-endian word `k` of a byte list (0 past its end). -/
def leWord (bs : List Nat) (k : Nat) : Nat :=
  bs.getD (8 * k) 0 + bs.getD (8 * k + 1) 0 * 2 ^ 8 + bs.getD (8 * k + 2) 0 * 2 ^ 16 +
    bs.getD (8 * k + 3) 0 * 2 ^ 24 + bs.getD (8 * k + 4) 0 * 2 ^ 32 + bs.getD (8 * k + 5) 0 * 2 ^ 40 +
    bs.getD (8 * k + 6) 0 * 2 ^ 48 + bs.getD (8 * k + 7) 0 * 2 ^ 56

/-- The words of a well-formed layout's image fit in 64 bits. -/
theorem wordOf_lt {Λ : Layout} (hwf : Λ.WF) (w : Nat) : wordOf Λ.image w < 2 ^ 64 := by
  unfold wordOf
  cases hf : Λ.image.find? (·.1 == w) with
  | none => simp
  | some p => exact (hwf.image p (List.mem_of_find?_eq_some hf)).2.2

/-- **A word of an 8-aligned item**: the image's word at `a + 8k` is the
item's little-endian word `k`, for a word inside the item. -/
theorem image_word {Λ : Layout} (hwf : Λ.WF) {a : Nat} {bs : List Nat} (ha : a % 8 = 0)
    (hb : ∀ i (hi : i < bs.length), byteAt Λ.image (a + i) = bs[i]) {k : Nat} (hk : 8 * k + 8 ≤ bs.length) :
    wordOf Λ.image (a + 8 * k) = leWord bs k := by
  have hbyte (j : Nat) (hj : j < 8) :
      bs.getD (8 * k + j) 0 = wordOf Λ.image (a + 8 * k) / 2 ^ (8 * j) % 256 := by
    have hi : 8 * k + j < bs.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, ← hb _ hi, byteAt,
      ← Nat.add_assoc,
      show (a + 8 * k + j) / 8 * 8 = a + 8 * k by omega, show (a + 8 * k + j) % 8 = j by omega]
  have hv := wordOf_lt hwf (a + 8 * k)
  have h0 := hbyte 0 (by omega)
  rw [Nat.add_zero] at h0
  rw [leWord, h0, hbyte 1 (by omega), hbyte 2 (by omega), hbyte 3 (by omega), hbyte 4 (by omega),
    hbyte 5 (by omega), hbyte 6 (by omega), hbyte 7 (by omega)]
  generalize wordOf Λ.image (a + 8 * k) = v at hv ⊢
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  exact word_bytes v hv

end Scc.Cert.Link
