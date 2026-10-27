/-
**The marshalling block's states before each instruction** (AArch64): at
every prefix of `marshal sw fn` short of its `bl`, the frame offsets as at
its entry, the argument registers `x0`…`x(sw-1)` as there, and the frame's
base cell (the TCB) kept (`marshal_take`). The stores write `8`…`8 sw`, the
loads read those cells back into their registers, and only the last load
(`x(sw)`) and the `bl` change a register outside them. The prefix states'
facts a placement at `mainS0`'s block needs (`hPlS` of
`Spike/Lib/LowerA64/RtMainXR.lean`).
-/
import Spike.Lib.Rt.A64MainS

namespace Spike.Lib.A64.Rt

open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Flow

/-- The argument registers below the ninth are distinct. -/
theorem argX_inj : ∀ i < 8, ∀ j < 8, argX i = argX j → i = j := by decide

/-- **The marshalling block's prefixes**: before each instruction of
`marshal sw fn` (`hk`), at `sw ≤ 7` words, the frame offsets as at its entry,
`x0`…`x(sw-1)` as there and the frame's base cell kept. -/
theorem marshal_take (lab : Label → Int64) {sw : Nat} (hsw : sw ≤ 7) (fn : Label) (pc : Int64) (sp : Int)
    (σ : Flow.AS) {k : Nat} (hk : k < (marshal sw fn).length) :
    (Flow.arun lab ((marshal sw fn).take k) ⟨pc, ⟨sp, []⟩, σ⟩).so = ⟨sp, []⟩ ∧
      (∀ i < sw, (Flow.arun lab ((marshal sw fn).take k) ⟨pc, ⟨sp, []⟩, σ⟩).σ.regs.getXReg (argX i) =
        σ.regs.getXReg (argX i)) ∧
      (Flow.arun lab ((marshal sw fn).take k) ⟨pc, ⟨sp, []⟩, σ⟩).σ.slot sp = σ.slot sp := by
  have h1 : (mshSt sw).length = sw := by simp [mshSt]
  have h2 : (mshLd sw).length = sw + 1 := by simp [mshLd]
  have hlen : (marshal sw fn).length = 2 * sw + 2 := by
    rw [marshal_eq]; simp [wordDirs, h1, h2]; omega
  have hof : ∀ i < sw, (Int64.ofNat (8 * (i + 1))).toInt = 8 * ((i : Int) + 1) := fun i hi => by
    rw [Int64.toInt_ofNat_of_lt (Nat.lt_of_lt_of_le (show 8 * (i + 1) < 64 by omega) (by decide))]; omega
  -- the stores never write the base cell
  have hst0 : ∀ (ps : List (XReg × Int64)), ps ⊆ mshSt sw → ∀ regs sl,
      stSlots sp regs ps sl sp = sl sp := fun ps hps regs sl =>
    stSlots_of_not_mem _ _ _ _ fun p hp he => by
      have := hps hp
      simp only [mshSt, List.mem_map, List.mem_range] at this
      obtain ⟨i, hi, rfl⟩ := this
      rw [hof i hi] at he; omega
  rw [hlen] at hk
  rw [marshal_eq]
  by_cases hks : k ≤ sw
  · rw [List.append_assoc, List.take_append_of_le_length (by simp [h1]; omega), ← List.map_take,
      arun_spStrs]
    exact ⟨rfl, fun _ _ => rfl, hst0 _ (List.take_subset _ _) _ _⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = sw + j := ⟨k - sw, by omega⟩
    have hj : j ≤ sw + 1 := by omega
    rw [List.append_assoc, List.take_append, List.take_of_length_le (by simp [h1] <;> omega),
      show sw + j - ((mshSt sw).map fun p => spStr p.1 p.2).length = j by simp [h1],
      List.take_append_of_le_length (by simp [wordDirs, h2]; omega), wordDirs, ← List.map_take, ← wordDirs,
      arun_cat, arun_spStrs, arun_words]
    refine ⟨rfl, fun i hi => ?_, hst0 _ (List.Subset.refl _) _ _⟩
    have hnd : (((mshLd sw).take j).map Prod.fst).Nodup := by
      rw [List.map_take]
      exact (List.take_sublist _ _).nodup (by rw [mshLd_fst]; exact argX_nodup sw (by omega))
    by_cases hm : argX i ∈ ((mshLd sw).take j).map Prod.fst
    · obtain ⟨⟨r, w⟩, hrw, hr⟩ := List.mem_map.1 hm
      simp only at hr
      subst hr
      have hmem := List.mem_of_mem_take hrw
      simp only [mshLd, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton, Prod.mk.injEq] at hmem
      rcases hmem with ⟨i', hi', he, rfl⟩ | ⟨he, rfl⟩
      · have : i' = i := argX_inj i' (by omega) i (by omega) he
        subst this
        rw [setWords_get _ _ _ _ hnd hrw]
        simp only [RW.val]
        have hsnd : ((mshSt sw).map fun p => sp + p.2.toInt).Nodup := by
          have e : ((mshSt sw).map fun p => sp + p.2.toInt) =
              (List.range sw).map fun i : Nat => sp + 8 * ((i : Int) + 1) := by
            simp only [mshSt, List.map_map]
            exact List.map_congr_left fun i hi => by
              show sp + (Int64.ofNat (8 * (i + 1))).toInt = _
              rw [hof i (List.mem_range.1 hi)]
          rw [e]
          exact List.Pairwise.map _
            (fun a b hab (h : sp + 8 * ((a : Int) + 1) = sp + 8 * ((b : Int) + 1)) => hab (by omega))
            List.nodup_range
        rw [stSlots_get _ _ _ _ hsnd (r := argX i')
          (by simp only [mshSt, List.mem_map, List.mem_range]; exact ⟨i', hi', rfl⟩), UInt64.ofBitVec_toBitVec]
      · exact absurd (argX_inj sw (by omega) i (by omega) he.symm) (by omega)
    · exact setWords_get_of_not_mem _ _ _ _ hm

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64.Rt.marshal_take' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms marshal_take

end Spike.Lib.A64.Rt
