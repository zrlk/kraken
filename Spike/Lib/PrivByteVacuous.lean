/-
**A lone private byte is invisible to 8-byte loads** (any ISA): the guard
against stating "no buffer byte is in the thread's private memory" as a
frame condition.

Frame conditions are kept by `FStable R F` (`Spike/Lib/A64Cfg.lean`,
`Spike/Lib/X64Cfg.lean`): `F` survives every change `DFrame R` allows, and
`DFrame` only fixes the 8-byte loads (`Mem.loadInt m.dmem a 8`) outside the
region. The kernel's byte read (`Kernel.readByte`) checks one byte. If eight
consecutive bytes `x … x + 7` are absent, adding a byte at `x + 3` changes
no 8-byte load anywhere: every window through `x + 3` still contains `x` or
`x + 7` (`loadInt_insert_hole`). So an `FStable` frame that says those eight
bytes are absent is empty (`hbuf_vacuous` in `Spike/Lib/A64PrintByteOut.lean`
and `Spike/Lib/X64PrintByteOut.lean`); such a premise on `print`'s buffer
(any `print` of 8 bytes or more) is why the private-memory fact is the
consumer's `hpriv` (`ByteOut.byteOut_emit`), not a frame premise.
-/
import Kraken.Mem

namespace Spike.Lib.PrivByteVacuous

/-- A list of options with a `none` has no `allSome`. -/
theorem allSome_of_none_mem {α : Type} : ∀ {l : List (Option α)}, none ∈ l → l.allSome = none
  | [], h => by cases h
  | o :: l, h => by
    simp only [List.allSome, List.mapM_cons, id] at *
    rcases List.mem_cons.mp h with rfl | h
    · rfl
    · have ih : l.mapM id = none := allSome_of_none_mem h
      cases o <;> simp [ih]

/-- **A byte inside eight absent bytes changes no 8-byte load**: with
`x … x + 7` absent from `dm`, inserting a byte at `x + 3` leaves
`Mem.loadInt _ a 8` unchanged at every `a`. -/
theorem loadInt_insert_hole {dm : _root_.Mem 64} {x : BitVec 64}
    (h : ∀ i < 8, dm[x + BitVec.ofNat 64 i]? = none) (v : UInt8) (a : BitVec 64) :
    Mem.loadInt (dm.insert (x + 3#64) v) a 8 = Mem.loadInt dm a 8 := by
  unfold Mem.loadInt Mem.loadBytes
  by_cases hy : ∃ j < 8, a + BitVec.ofNat 64 j = x + 3#64
  · obtain ⟨j, hj, hy⟩ := hy
    -- another byte of the window is `x` or `x + 7`, absent on both sides
    obtain ⟨k, hk, i, hi, hki, hne⟩ : ∃ k < 8, ∃ i < 8, a + BitVec.ofNat 64 k = x + BitVec.ofNat 64 i ∧
        x + 3#64 ≠ x + BitVec.ofNat 64 i := by
      by_cases h3 : 3 ≤ j
      · refine ⟨j - 3, by omega, 0, by omega, ?_, ?_⟩
        · have : BitVec.ofNat 64 j = BitVec.ofNat 64 (j - 3) + 3#64 := by
            apply BitVec.eq_of_toNat_eq; simp; omega
          rw [this, ← BitVec.add_assoc] at hy
          have := congrArg (· - 3#64) hy
          simpa using this
        · intro he; bv_omega
      · refine ⟨j + 4, by omega, 7, by omega, ?_, ?_⟩
        · have : BitVec.ofNat 64 (j + 4) = BitVec.ofNat 64 j + 4#64 := by
            apply BitVec.eq_of_toNat_eq; simp
          rw [this, ← BitVec.add_assoc, hy, BitVec.add_assoc]
          rfl
        · intro he; bv_omega
    have hn : ∀ m : _root_.Mem 64, m[a + BitVec.ofNat 64 k]? = none →
        ((List.range 8).map fun i => m.get? (a + BitVec.ofNat 64 i)).allSome = none := by
      intro m hm
      apply allSome_of_none_mem
      simp only [List.mem_map, List.mem_range]
      exact ⟨k, hk, by simpa using hm⟩
    have h0 : dm[a + BitVec.ofNat 64 k]? = none := by rw [hki]; exact h i hi
    rw [hn dm h0, hn _ (by
      rw [Std.ExtHashMap.getElem?_insert]
      simp only [beq_iff_eq, hki, hne, ↓reduceIte]
      exact h i hi)]
  · refine congrArg (fun l => Option.map _ (List.allSome l)) (List.map_congr_left ?_)
    intro i hi
    simp only [List.mem_range] at hi
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
    have hne : ¬ x + 3#64 = a + BitVec.ofNat 64 i := fun he => hy ⟨i, hi, he.symm⟩
    simp only [hne, ↓reduceIte]

/-- The byte inserted is there. -/
theorem getElem?_insert_self (dm : _root_.Mem 64) (y : BitVec 64) (v : UInt8) : (dm.insert y v)[y]? = some v := by
  simp

end Spike.Lib.PrivByteVacuous
