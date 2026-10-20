/-
Word-level facts for proofs about lowered code, ISA-neutral and generic in
the address width: a load depends only on the bytes it reads
(`Mem.loadInt_congr`), a load inside the range of a store is mapped
(`Mem.loadInt_isSome_storeInt`), a word at an offset of a region lies inside it
(`BitVec.toNat_offset_sub_lt`), `cmp`'s zero flag read as values
(`BitVec.toNat_eq_of_sub_eq_zero`, `toNat_ne_of_sub_ne_zero`), or as add on
disjoint bits (`BitVec.shiftLeft_or_eq_add`) and clearing the lowest set bit
(`Nat.and_pred_lt`), and the trailing zero count as the first set bit
(`BitVec.toNat_ctz_eq_find`).
-/
import Kraken.Mem

/-! ## Loads -/

/-- **A load depends only on the bytes it reads**: two memories that agree on
the `n` bytes at `a` give the same `loadInt a n`. -/
theorem Mem.loadInt_congr {w : Nat} {m m' : Mem w} {a : BitVec w} {n : Nat}
    (h : ∀ i < n, m'.get? (a + BitVec.ofNat w i) = m.get? (a + BitVec.ofNat w i)) :
    m'.loadInt a n = m.loadInt a n := by
  unfold Mem.loadInt Mem.loadBytes
  congr 2
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- **A load inside the range of a store is mapped**: after storing `n`
bytes at `a`, the first `k ≤ n` bytes at `a` load. -/
theorem Mem.loadInt_isSome_storeInt {w : Nat} (m : Mem w) (a : BitVec w) {n k : Nat} (v : Int) (hk : k ≤ n)
    (hn : n ≤ 2 ^ w) : (Mem.loadInt (Mem.storeInt m a n v) a k).isSome = true := by
  have hlen : (Int.toBytes n v).length = n := Int.toBytes_length n v
  simp only [Mem.loadInt, Option.isSome_map, Mem.loadBytes, List.allSome_isSome_iff, List.mem_map,
    List.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro i hi
  rw [Mem.storeInt, Mem.storeBytes, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.union_eq,
    Std.ExtHashMap.getElem?_union, ← Std.ExtHashMap.get?_eq_getElem?, get?_At_idx _ _ _ (by omega) (by omega),
    List.getElem?_eq_getElem (by omega)]
  rfl

/-! ## Offsets -/

/-- **Byte `o + i` of a region of `len` bytes at `x` lies inside it**: its
distance from `x` is below `len` (no bound on `len` is needed: the distance is
at most `o + i`). -/
theorem BitVec.toNat_offset_sub_lt {w : Nat} (x : BitVec w) (o len i : Nat) (h : o + i < len) :
    (x + BitVec.ofNat w o + BitVec.ofNat w i - x).toNat < len := by
  rw [BitVec.add_assoc, BitVec.add_comm x, BitVec.add_sub_cancel, ← BitVec.ofNat_add, BitVec.toNat_ofNat]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) h

/-! ## Compare as values -/

/-- `a - b = 0` (the zero flag of `cmp a, b`) means equal values. -/
theorem BitVec.toNat_eq_of_sub_eq_zero {w : Nat} {a b : BitVec w} (h : a - b = 0#w) : a.toNat = b.toNat := by
  have := congrArg (· + b) h
  simp only [BitVec.sub_add_cancel, BitVec.zero_add] at this
  rw [this]

/-- `a - b ≠ 0` (the zero flag of `cmp a, b` clear) means different values. -/
theorem BitVec.toNat_ne_of_sub_ne_zero {w : Nat} {a b : BitVec w} (h : ¬ a - b = 0#w) : a.toNat ≠ b.toNat := by
  intro e; apply h
  rw [BitVec.eq_of_toNat_eq e]; simp

/-! ## Masks -/

/-- **Or as add on disjoint bits**: a constant below `2^k` fits in the `k`
cleared low bits of `x <<< k`. -/
theorem BitVec.shiftLeft_or_eq_add {w : Nat} (x : BitVec w) (k : Nat) (c : BitVec w) (hc : c.toNat < 2 ^ k) :
    x <<< k ||| c = x <<< k + c := by
  rw [BitVec.add_eq_or_of_and_eq_zero]; ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft, BitVec.getElem_zero, Bool.and_eq_false_imp,
    Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
  intro h1
  rw [BitVec.getElem_eq_testBit_toNat]
  exact Nat.testBit_lt_two_pow
    (Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt h1.1)))

/-- **Clearing the lowest set bit decreases**: `n &&& (n - 1) < n` for
`n ≠ 0`. -/
theorem Nat.and_pred_lt (n : Nat) (h : n ≠ 0) : n &&& (n - 1) < n :=
  Nat.lt_of_le_of_lt Nat.and_le_right (Nat.pred_lt h)

/-! ## Bit counts -/

private theorem List.find?_range_eq_some_of_first (q : Nat → Bool) (t : Nat) (ht : q t = true)
    (hlt : ∀ j, j < t → q j = false) : ∀ n, t < n → (List.range n).find? q = some t
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    rw [List.range_succ, List.find?_append]
    by_cases htn : t < n
    · rw [List.find?_range_eq_some_of_first q t ht hlt n htn]; rfl
    · have e : t = n := by omega
      subst e
      rw [List.find?_eq_none.mpr (fun j hj => by
        simp [hlt j (List.mem_range.mp hj)])]
      simp [ht]

/-- **The trailing zero count is the index of the first set bit**, or the
width when there is none: `BitVec.ctz` (the value of x64 `tzcnt`, and of
AArch64 `rbit; clz`) as a search over the bits of `toNat`. -/
theorem BitVec.toNat_ctz_eq_find {w : Nat} (x : BitVec w) :
    x.ctz.toNat = ((List.range w).find? fun i => (x.toNat >>> i) % 2 == 1).getD w := by
  have hq : ∀ i, ((x.toNat >>> i) % 2 == 1) = x.getLsbD i := by
    intro i
    rw [← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
    by_cases h : x.toNat / 2 ^ i % 2 = 1 <;> simp [h]
  by_cases hx : x = 0#w
  · subst hx
    rw [List.find?_eq_none.mpr (fun j _ => by simp)]
    have h0 : (0#w).ctz = BitVec.ofNat w w :=
      BitVec.clz_eq_iff_eq_zero.mpr (BitVec.reverse_eq_zero_iff.mpr rfl)
    rw [h0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt Nat.lt_two_pow_self]
    rfl
  · have h1 := BitVec.getLsbD_true_ctz_of_ne_zero hx
    have hlt : x.ctz.toNat < w := by
      rcases Nat.lt_or_ge x.ctz.toNat w with h | h
      · exact h
      · rw [BitVec.getLsbD_of_ge x _ h] at h1
        exact absurd h1 (by decide)
    rw [List.find?_range_eq_some_of_first _ x.ctz.toNat (by rw [hq]; exact h1)
      (fun j hj => by rw [hq]; exact BitVec.getLsbD_false_of_lt_ctz hj) w hlt]
    rfl
