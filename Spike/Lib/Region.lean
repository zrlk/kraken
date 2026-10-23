/-
**Stack regions and static offsets**, independent of the ISA: the part of
`Spike/Lib/X64Block.lean` and `Spike/Lib/A64Flow.lean` that is about
addresses, not instructions.

* `Region`: a base address and a range `[lo, hi)` of byte offsets from it;
  `R.addr k = base + k`, `R.Off k` an 8-aligned cell inside the range.
  Under `R.OK` (no wrap-around) distinct cells are disjoint
  (`Region.addr_sep`) and fit in the address space (`Region.addr_fit`).
* `lk`/`rm`: lookup and removal in an association list of registers to
  offsets (the static offsets of each ISA's `SO`).
* `upd`: the cells of a region as a function `Int → BitVec 64`, updated at
  one offset.
* `offOk`: the decidable form of `Region.Off` for a range `[lo, hi)`.
* `Region.callee`: a callee's region, based at the caller's offset `kc`;
  inside the caller's region when `R.lo ≤ kc + lo'` and `kc + hi' ≤ R.hi`
  (`Region.callee_ok`, `Region.callee_off`, `Region.callee_sep`).
-/

namespace Spike.Lib

/-! ## Regions -/

/-- **A stack region**: the 8-byte cells at `base + k` for `lo ≤ k < hi`
(on x64 the frame, the saved `%rbp` and return address above it, and
whatever the code pushes below it; on AArch64 the frame below the entry
`sp`). -/
structure Region where
  base : BitVec 64
  lo : Int
  hi : Int

/-- The address `base + k`. -/
def Region.addr (R : Region) (k : Int) : BitVec 64 := R.base + BitVec.ofInt 64 k

/-- A region that does not wrap around the address space. -/
structure Region.OK (R : Region) : Prop where
  lo : 0 ≤ (R.base.toNat : Int) + R.lo
  hi : (R.base.toNat : Int) + R.hi ≤ 2 ^ 64

/-- An offset of the region: 8-aligned, the 8 bytes inside. -/
def Region.Off (R : Region) (k : Int) : Prop := k % 8 = 0 ∧ R.lo ≤ k ∧ k + 8 ≤ R.hi

theorem Region.addr_add (R : Region) (k d : Int) : R.addr (k + d) = R.addr k + BitVec.ofInt 64 d := by
  simp only [Region.addr, BitVec.ofInt_add, BitVec.add_assoc]

theorem Region.addr_sub (R : Region) (k d : Int) : R.addr (k - d) = R.addr k - BitVec.ofInt 64 d := by
  rw [Int.sub_eq_add_neg, Region.addr_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

theorem Region.addr_toNat {R : Region} (hR : R.OK) {k : Int} (hk : R.Off k) :
    ((R.addr k).toNat : Int) = R.base.toNat + k := by
  have h1 := hR.lo
  have h2 := hR.hi
  obtain ⟨-, h3, h4⟩ := hk
  have he : R.addr k = BitVec.ofInt 64 ((R.base.toNat : Int) + k) := by
    rw [Region.addr, BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [he, BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide)),
    Int.emod_eq_of_lt (by omega) (by omega)]

theorem Region.addr_fit {R : Region} (hR : R.OK) {k : Int} (hk : R.Off k) : (R.addr k).toNat + 8 ≤ 2 ^ 64 := by
  have := R.addr_toNat hR hk
  have := hR.hi
  obtain ⟨-, -, h4⟩ := hk
  omega

theorem Region.addr_sep {R : Region} (hR : R.OK) {k k' : Int} (hk : R.Off k) (hk' : R.Off k') (hne : k ≠ k') :
    (R.addr k).toNat + 8 ≤ (R.addr k').toNat ∨ (R.addr k').toNat + 8 ≤ (R.addr k).toNat := by
  have h1 := R.addr_toNat hR hk
  have h2 := R.addr_toNat hR hk'
  obtain ⟨a0, -, -⟩ := hk
  obtain ⟨b0, -, -⟩ := hk'
  omega

theorem Region.addr_sub8 (R : Region) (k : Int) : R.addr k - 8#64 = R.addr (k - 8) := by
  rw [Region.addr_sub]; rfl

theorem Region.addr_add8 (R : Region) (k : Int) : R.addr k + 8#64 = R.addr (k + 8) := by
  rw [Region.addr_add]; rfl

/-- An address of a 16-aligned base at a 16-aligned offset is 16-aligned. -/
theorem Region.addr_align16 (R : Region) (hb : R.base.toNat % 16 = 0) {k : Int} (hk : k % 16 = 0) :
    R.addr k % 16#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [Region.addr, BitVec.toNat_umod, BitVec.toNat_add, BitVec.toNat_ofInt]
  have h16 : (16#64).toNat = 16 := rfl
  rw [h16, Nat.mod_mod_of_dvd _ (⟨2 ^ 60, by decide⟩ : 16 ∣ 2 ^ 64)]
  have ht : 0 ≤ k % ((2 ^ 64 : Nat) : Int) ∧ k % ((2 ^ 64 : Nat) : Int) % 16 = 0 := by
    rw [show ((2 ^ 64 : Nat) : Int) = 18446744073709551616 from rfl]; omega
  show _ = 0
  omega

/-- A cell offset inside `[lo, hi)`. -/
def offOk (lo hi : Int) (k : Int) : Bool := decide (k % 8 = 0 ∧ lo ≤ k ∧ k + 8 ≤ hi)

theorem offOk_off {lo hi : Int} {R : Region} {k : Int} (h : offOk lo hi k = true) (hlo : R.lo ≤ lo)
    (hhi : hi ≤ R.hi) : R.Off k := by
  simp only [offOk, decide_eq_true_eq] at h
  exact ⟨h.1, by omega, by omega⟩

/-! ## Offset lists -/

/-- Look a register up in an offset list (registers of any type `ρ`). -/
def lk {ρ : Type} [DecidableEq ρ] : List (ρ × Int) → ρ → Option Int
  | [], _ => none
  | (r, k) :: l, r' => if r' = r then some k else lk l r'

/-- Remove a register from an offset list. -/
def rm {ρ : Type} [DecidableEq ρ] : List (ρ × Int) → ρ → List (ρ × Int)
  | [], _ => []
  | (r, k) :: l, r' => if r = r' then rm l r' else (r, k) :: rm l r'

theorem lk_rm {ρ : Type} [DecidableEq ρ] (l : List (ρ × Int)) (r r' : ρ) :
    lk (rm l r) r' = if r' = r then none else lk l r' := by
  induction l with
  | nil => simp [lk, rm]
  | cons e l ih =>
    obtain ⟨a, k⟩ := e
    by_cases h : a = r
    · subst h
      by_cases h' : r' = a
      · subst h'; simpa [rm] using ih
      · simp [rm, lk, ih, h']
    · by_cases h' : r' = a
      · subst h'; simp [rm, lk, h]
      · simp [rm, lk, h, h', ih]

/-! ## Cells -/

/-- Update a cell file at one offset. -/
def upd (f : Int → BitVec 64) (k : Int) (v : BitVec 64) : Int → BitVec 64 :=
  fun k' => if k' = k then v else f k'

theorem upd_apply (f : Int → BitVec 64) (k : Int) (v : BitVec 64) (k' : Int) :
    upd f k v k' = if k' = k then v else f k' := rfl

theorem ofInt_toNat (x : BitVec 64) : BitVec.ofInt 64 (x.toNat : Int) = x := by
  simp

theorem int64_ofInt_toInt (n : Int64) : BitVec.ofInt 64 n.toInt = n.toBitVec := by
  rw [show n.toInt = n.toBitVec.toInt from rfl, BitVec.ofInt_toInt]

/-! ## A callee's region -/

/-- **The callee's region**: based at the caller's offset `kc`, range
`[lo', hi')`. -/
def Region.callee (R : Region) (kc lo' hi' : Int) : Region := ⟨R.addr kc, lo', hi'⟩

theorem Region.addr_toNat_of {R : Region} (hR : R.OK) {k : Int} (h1 : R.lo ≤ k) (h2 : k < R.hi) :
    ((R.addr k).toNat : Int) = R.base.toNat + k := by
  have ha := hR.lo
  have hb := hR.hi
  have he : R.addr k = BitVec.ofInt 64 ((R.base.toNat : Int) + k) := by
    rw [Region.addr, BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [he, BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide)),
    Int.emod_eq_of_lt (by omega) (by omega)]

section Callee

variable {R : Region} {kc lo' hi' : Int}

theorem Region.callee_addr (R : Region) (kc lo' hi' k : Int) :
    (R.callee kc lo' hi').addr k = R.addr (kc + k) := by
  rw [Region.callee, Region.addr, Region.addr_add]

theorem Region.callee_base (hR : R.OK) (hlo : R.lo ≤ kc + lo') (hlo0 : lo' ≤ 0) (hkc : kc < R.hi) :
    ((R.callee kc lo' hi').base.toNat : Int) = R.base.toNat + kc :=
  Region.addr_toNat_of hR (by omega) hkc

theorem Region.callee_ok (hR : R.OK) (hlo : R.lo ≤ kc + lo') (hlo0 : lo' ≤ 0) (hkc : kc < R.hi)
    (hhi : kc + hi' ≤ R.hi) :
    (R.callee kc lo' hi').OK := by
  have hb := Region.callee_base (hi' := hi') hR hlo hlo0 hkc
  have h1 := hR.lo
  have h2 := hR.hi
  exact ⟨by simp only [Region.callee] at hb ⊢; omega, by simp only [Region.callee] at hb ⊢; omega⟩

theorem Region.callee_off (hlo : R.lo ≤ kc + lo') (hhi : kc + hi' ≤ R.hi) (hk8 : kc % 8 = 0) {k : Int}
    (hk : (R.callee kc lo' hi').Off k) : R.Off (kc + k) := by
  obtain ⟨h1, h2, h3⟩ := hk
  simp only [Region.callee] at h2 h3
  exact ⟨by omega, by omega, by omega⟩

/-- A cell of the caller outside the callee's region is outside it as an
address range (all offsets 8-aligned). -/
theorem Region.callee_sep (hR : R.OK) (hlo : R.lo ≤ kc + lo') (hlo0 : lo' ≤ 0) (hkc : kc < R.hi)
    (hk8 : kc % 8 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0) {k : Int} (hk : R.Off k)
    (hn : ¬ (R.callee kc lo' hi').Off (k - kc)) :
    ((R.addr k).toNat : Int) + 8 ≤ (R.callee kc lo' hi').base.toNat + (R.callee kc lo' hi').lo ∨
      ((R.callee kc lo' hi').base.toNat : Int) + (R.callee kc lo' hi').hi ≤ (R.addr k).toNat := by
  have hb := Region.callee_base (hi' := hi') hR hlo hlo0 hkc
  have ha := R.addr_toNat hR hk
  obtain ⟨k8, -, -⟩ := hk
  simp only [Region.Off, Region.callee] at hn hb ⊢
  omega

end Callee

end Spike.Lib
