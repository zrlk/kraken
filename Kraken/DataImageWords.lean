/-
**A data image as 8-byte words**: the form of a static image of shared
memory, a list of `(address, value)` words (Scc's `Layout.image`).

`words base img` cuts the bytes `img` of an image at `base`
(`DataImage.image`) into consecutive 8-byte little-endian words, the last one
zero-padded. For an 8-aligned section every word is 8-aligned and below
`2 ^ 64` (`words_aligned`), and the word at `base + 8 * j` is what an 8-byte
load at that address reads from the byte image stored in memory
(`loadInt_dataMem_of_lookup`), for every word that lies inside the image.
-/
import Kraken.DataImage

namespace Kraken.DataImage

/-- Up to 8 bytes padded with zeros to 8. -/
def pad8 (bs : List UInt8) : List UInt8 := bs ++ List.replicate (8 - bs.length) 0

/-- `k` consecutive words from address `a`. -/
def wordsN : Nat → Nat → List UInt8 → List (Nat × Nat)
  | 0, _, _ => []
  | k + 1, a, bs => (a, Nat.ofBytes (pad8 (bs.take 8))) :: wordsN k (a + 8) (bs.drop 8)

/-- **The image as 8-byte words** `(address, value)` from `base`, the last
word zero-padded. -/
def words (base : Nat) (img : List UInt8) : List (Nat × Nat) :=
  wordsN ((img.length + 7) / 8) base img

theorem intOfBytes_eq_natOfBytes : ∀ bs : List UInt8, Int.ofBytes bs = (Nat.ofBytes bs : Int)
  | [] => rfl
  | b :: bs => by
    rw [Int.ofBytes_cons, Nat.ofBytes_cons, intOfBytes_eq_natOfBytes bs, Int.natCast_add, Int.natCast_mul]
    rfl

theorem pad8_length {bs : List UInt8} (h : bs.length ≤ 8) : (pad8 bs).length = 8 := by
  simp [pad8]; omega

theorem natOfBytes_pad8_lt {bs : List UInt8} (h : bs.length ≤ 8) : Nat.ofBytes (pad8 bs) < 2 ^ 64 := by
  have := Int.ofBytes_lt (pad8 bs)
  rw [pad8_length h, intOfBytes_eq_natOfBytes] at this
  have h2 : ((256 : Int) ^ 8) = ((2 ^ 64 : Nat) : Int) := by decide
  rw [h2] at this
  exact Int.ofNat_lt.mp this

theorem wordsN_mem : ∀ (k a : Nat) (bs : List UInt8) (p : Nat × Nat), p ∈ wordsN k a bs →
    (∃ j, j < k ∧ p.1 = a + 8 * j) ∧ p.2 < 2 ^ 64
  | 0, _, _, _, h => by simp [wordsN] at h
  | k + 1, a, bs, p, h => by
    simp only [wordsN, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨⟨0, by omega, by simp⟩, natOfBytes_pad8_lt (by rw [List.length_take]; exact Nat.min_le_left _ _)⟩
    · obtain ⟨⟨j, hj, he⟩, hv⟩ := wordsN_mem k (a + 8) (bs.drop 8) p h
      exact ⟨⟨j + 1, by omega, by rw [he]; omega⟩, hv⟩

/-- **Words of an 8-aligned image** are 8-aligned 64-bit values. -/
theorem words_aligned {base : Nat} (hb : base % 8 = 0) (img : List UInt8) :
    ∀ p ∈ words base img, p.1 % 8 = 0 ∧ p.2 < 2 ^ 64 := by
  intro p hp
  obtain ⟨⟨j, -, he⟩, hv⟩ := wordsN_mem _ _ _ p hp
  exact ⟨by rw [he]; omega, hv⟩

theorem lookup_wordsN : ∀ (k a : Nat) (bs : List UInt8) (j : Nat), j < k → 8 * j + 8 ≤ bs.length →
    (wordsN k a bs).lookup (a + 8 * j) = some (Nat.ofBytes ((bs.drop (8 * j)).take 8))
  | 0, _, _, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | k + 1, a, bs, 0, _, hl => by
    have : (bs.take 8).length = 8 := by simp; omega
    simp [wordsN, pad8, this]
  | k + 1, a, bs, j + 1, hj, hl => by
    have ih := lookup_wordsN k (a + 8) (bs.drop 8) j (by omega) (by rw [List.length_drop]; omega)
    have hne : (a + 8 * (j + 1) == a) = false := by simp
    simp only [wordsN, List.lookup, hne]
    have e : List.drop (8 * j) (List.drop 8 bs) = List.drop (8 * (j + 1)) bs := by
      rw [List.drop_drop]; congr 1; omega
    rw [e] at ih
    rw [show a + 8 * (j + 1) = a + 8 + 8 * j by omega, ih]

/-- **The word at `base + 8 * j`** of an image whose bytes cover it. -/
theorem lookup_words {base : Nat} {img : List UInt8} {j : Nat} (hl : 8 * j + 8 ≤ img.length) :
    (words base img).lookup (base + 8 * j) = some (Nat.ofBytes ((img.drop (8 * j)).take 8)) :=
  lookup_wordsN _ _ _ _ (by omega) hl

/-- **An 8-byte load from the stored byte image reads the converted word**:
the value at `base + 8 * j` of `words base img` is what `loadInt` reads at
that address from `dataMem m base img`, for a word inside the image. -/
theorem loadInt_dataMem_of_lookup (m : Mem 64) {base : Nat} {img : List UInt8} {j : Nat}
    (hl : 8 * j + 8 ≤ img.length) (hw : img.length ≤ 2 ^ 64) {v : Nat}
    (hv : (words base img).lookup (base + 8 * j) = some v) :
    (dataMem m base img).loadInt (BitVec.ofNat 64 (base + 8 * j)) 8 = some (v : Int) := by
  rw [lookup_words hl, Option.some.injEq] at hv
  rw [Mem.loadInt, loadBytes_dataMem_off m base img (8 * j) 8 hl hw, Option.map_some,
    intOfBytes_eq_natOfBytes, hv]

-- Nine bytes at 16: one full word and a zero-padded one.
#guard_msgs in
#guard words 16 [1, 2, 3, 4, 5, 6, 7, 8, 9] == [(16, 0x0807060504030201), (24, 9)]

end Kraken.DataImage
