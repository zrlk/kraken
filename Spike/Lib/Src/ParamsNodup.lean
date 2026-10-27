/-
**A code block's parameter registers are distinct** (ISA-neutral):
`paramsR d na` (`Spike/Lib/LowerShapeC2.lean`), the registers `arg.k`, for
the prologue's spill (`stSlots_paramN` on each ISA).

- `regIdx_inj`: `a.j = a.k` only at `j = k`;
- `paramsR_nodup`: `paramsR d na` has no duplicate.
-/
import Spike.Lib.LowerShapeC2

namespace Spike.Lib.LowerShape

/-- The register names `a.j` and `a.k` agree only at `j = k`. -/
theorem regIdx_inj (a : String) {j k : Nat} (h : s!"{a}.{j}" = s!"{a}.{k}") : j = k := by
  have e := congrArg String.toList h
  simp only [String.toList_append, toString, Nat.repr, String.toList_ofList] at e
  have e' := List.append_cancel_left e
  rw [← Nat.ofDigitChars_ten_toDigits (n := j), e', Nat.ofDigitChars_ten_toDigits]

/-- **A code block's parameter registers are distinct.** -/
theorem paramsR_nodup (d : CoreTerm.Decl) (na : Nat) : (paramsR d na).Nodup := by
  unfold paramsR
  rw [List.Nodup, List.pairwise_map]
  exact List.nodup_range.imp fun h e => h (regIdx_inj _ e)

end Spike.Lib.LowerShape

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerShape.paramsR_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerShape.paramsR_nodup
