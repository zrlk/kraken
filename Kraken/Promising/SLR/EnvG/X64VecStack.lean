/-
**The private stack slot of `treiber_aba_tagged.kl`.**

Each load of `head` in `treiber_aba_tagged.kl` goes through the thread's
private stack: `movdqa %xmm0,-16(%rsp)` writes the 16 bytes to `dmem`, and
`movq -16(%rsp),%rax` / `movq -8(%rsp),%rdx` read back its low and high 8
bytes (`loadInt_store16_lo`, `loadInt_store16_hi`, little-endian:
`toBytes16`). The stack is the `.kl` runner's `stack 64`: `dmem` holds the
64 bytes below `rsp` and nothing else, and stores into `dmem` keep its
domain (`DomIn`, `DomIn.storeInt`), so an address outside it is shared
(`DomIn.loadInt_none`) and one inside it is in the stack range
(`DomIn.mem_of_loadInt`).
-/
import Kraken.Promising.EnvWPX64

namespace Kraken.Promising.X64.EnvG.VecABA

open Kraken Std

/-- `movdqa`'s 16 bytes are the bytes of the low 8, then of the high 8. -/
theorem toBytes16 (x : BitVec 128) :
    Int.toBytes 16 x.toInt = Int.toBytes 8 (x.extractLsb' 0 64).toInt ++ Int.toBytes 8 (x.extractLsb' 64 64).toInt := by
  have h := Kraken.Promising.X64.toBytes_toPieces (m := 128) (n := 2) rfl x
  simpa [toPieces, List.range_succ] using h

/-- A load of `k` bytes at offset `off` into a store of the bytes `bs` reads
those bytes back. -/
theorem loadBytes_storeBytes_off (m : Mem 64) (a : BitVec 64) (bs : List UInt8) (off k : Nat)
    (h : off + k ≤ bs.length) (hw : bs.length ≤ 2 ^ 64) :
    (m.storeBytes a bs).loadBytes (a + BitVec.ofNat 64 off) k = some ((bs.drop off).take k) := by
  have hget : ∀ i, i < k → (m.storeBytes a bs).get? (a + BitVec.ofNat 64 off + BitVec.ofNat 64 i) =
      ((bs.drop off).take k)[i]? := by
    intro i hi
    have hlt : off + i < 2 ^ 64 := by omega
    have hbs : (bs.At a).get? (a + BitVec.ofNat 64 (off + i)) = bs[off + i]? := get?_At_idx bs a (off + i) hlt hw
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Mem.storeBytes, ExtHashMap.get?_eq_getElem?, ExtHashMap.union_eq,
      ExtHashMap.getElem?_union, ← ExtHashMap.get?_eq_getElem?, hbs, List.getElem?_eq_getElem (by omega)]
    rw [List.getElem?_take_of_lt hi, List.getElem?_drop, List.getElem?_eq_getElem (by omega)]
    rfl
  have hlen : ((bs.drop off).take k).length = k := by simp; omega
  rw [Mem.loadBytes, show (List.range k).map (fun i => (m.storeBytes a bs).get? (a + BitVec.ofNat 64 off + .ofNat _ i))
    = (List.range k).map (fun i => ((bs.drop off).take k)[i]?) from
      List.map_congr_left (fun i hi => hget i (List.mem_range.mp hi))]
  have hm := List.map_range_getElem? ((bs.drop off).take k)
  rw [hlen] at hm
  rw [hm, List.allSome_map_some]

/-- **The low 8 bytes of a 16-byte store** read back as its low half. -/
theorem loadInt_store16_lo (d : Mem 64) (a : BitVec 64) (x : BitVec 128) :
    (d.storeInt a 16 x.toInt).loadInt a 8 = some (Int.ofBytes (Int.toBytes 8 (x.extractLsb' 0 64).toInt)) := by
  have h := loadBytes_storeBytes_off d a (Int.toBytes 16 x.toInt) 0 8 (by simp [Int.toBytes_length])
    (by simp [Int.toBytes_length])
  simp only [BitVec.add_zero, List.drop_zero] at h
  rw [Mem.storeInt, Mem.loadInt, h, toBytes16, List.take_append_of_le_length (by simp [Int.toBytes_length]),
    List.take_of_length_le (by simp [Int.toBytes_length])]
  rfl

/-- **The high 8 bytes of a 16-byte store** read back as its high half. -/
theorem loadInt_store16_hi (d : Mem 64) (a : BitVec 64) (x : BitVec 128) :
    (d.storeInt a 16 x.toInt).loadInt (a + 8) 8 = some (Int.ofBytes (Int.toBytes 8 (x.extractLsb' 64 64).toInt)) := by
  have h := loadBytes_storeBytes_off d a (Int.toBytes 16 x.toInt) 8 8 (by simp [Int.toBytes_length])
    (by simp [Int.toBytes_length])
  rw [Mem.storeInt, Mem.loadInt, show a + 8 = a + BitVec.ofNat 64 8 from rfl, h, toBytes16,
    List.drop_append_of_le_length (by simp [Int.toBytes_length]),
    List.drop_of_length_le (l := Int.toBytes 8 _) (by simp [Int.toBytes_length]), List.nil_append,
    List.take_of_length_le (by simp [Int.toBytes_length])]
  rfl

/-- Reading back 8 bytes of a 64-bit value. -/
theorem ofInt_ofBytes8 (y : BitVec 64) : BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 y.toInt)) = y :=
  BitVec.ofInt_ofBytes_toBytes 64 8 rfl y

/-! ## The domain of the private memory -/

/-- Every mapped byte of `d` is in `S`. -/
def DomIn (S : BitVec 64 → Prop) (d : Mem 64) : Prop := ∀ k, (d.get? k).isSome → S k

theorem get?_isSome_of_loadInt {d : Mem 64} {a : BitVec 64} {n : Nat} (hs : (d.loadInt a n).isSome) {i : Nat}
    (hi : i < n) : (d.get? (a + BitVec.ofNat 64 i)).isSome := by
  unfold Mem.loadInt at hs
  rw [Option.isSome_map] at hs
  unfold Mem.loadBytes at hs
  exact (List.allSome_isSome_iff _).mp hs _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)

/-- **A store to mapped bytes keeps the domain.** -/
theorem DomIn.storeInt {S : BitVec 64 → Prop} {d : Mem 64} (h : DomIn S d) {a : BitVec 64} {n : Nat}
    (hs : (d.loadInt a n).isSome) (v : Int) : DomIn S (d.storeInt a n v) := by
  intro k hk
  unfold Mem.storeInt Mem.storeBytes at hk
  rw [ExtHashMap.get?_eq_getElem?, ExtHashMap.union_eq, ExtHashMap.getElem?_union] at hk
  by_cases hm : k ∈ (Int.toBytes n v).At a
  · obtain ⟨i, hi, rfl⟩ := (mem_At_iff _ _ _).mp hm
    rw [Int.toBytes_length] at hi
    exact h _ (get?_isSome_of_loadInt hs hi)
  · rw [ExtHashMap.getElem?_eq_none hm] at hk
    simp only [Option.none_or] at hk
    exact h k (by rw [ExtHashMap.get?_eq_getElem?]; exact hk)

/-- **Mapped is in the stack.** -/
theorem DomIn.mem_of_loadInt {S : BitVec 64 → Prop} {d : Mem 64} (h : DomIn S d) {a : BitVec 64} {n : Nat}
    (hs : (d.loadInt a n).isSome) (hn : 0 < n) : S a := by
  have := h _ (get?_isSome_of_loadInt hs hn)
  simpa using this

/-- **Outside the stack is unmapped.** -/
theorem DomIn.loadInt_none {S : BitVec 64 → Prop} {d : Mem 64} (h : DomIn S d) {a : BitVec 64} (ha : ¬ S a)
    {n : Nat} (hn : 0 < n) : d.loadInt a n = none := by
  cases hl : d.loadInt a n with
  | none => rfl
  | some _ => exact absurd (h.mem_of_loadInt (by rw [hl]; rfl) hn) ha

end Kraken.Promising.X64.EnvG.VecABA
