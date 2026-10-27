/-
**The setup block is a compiled block** (ISA-neutral): `rodata` is no
extern (the externs are `print` and `printL` only), so a declaration named
`rodata` of the program is one of its compiled blocks (`compiled2`); with a
setup block (`setupOf p = some s`) of an `Accepted2` program, there is one
(`rodata_of_setupOf`). The index premise of `setupPro_ofPlaceOK`
(`Spike/Lib/LowerA64/SetupProOf.lean`, `Spike/Lib/LowerX64/SetupProOf.lean`).

- `rodata_compiled2`: `rodata`'s declaration at an index of `compiled2 p`;
- `rodata_compiled2_ofSetupOf`: the same from `setupOf p = some s`.
-/
import Spike.Lib.Src.NumQLower

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm

/-- **`rodata` is a compiled block**: the program's declaration named
`rodata` (`p.find?`) is at some index of `compiled2 p`, no extern being
named `rodata`. -/
theorem rodata_compiled2 {p : Prog} {dr : Decl} (hf : p.find? (·.name == "rodata") = some dr) :
    ∃ j : Nat, (compiled2 p)[j]? = some dr ∧ dr.name = "rodata" := by
  have hn : dr.name = "rodata" := by simpa using List.find?_some hf
  have hm : dr ∈ compiled2 p := by
    refine List.mem_filter.mpr ⟨List.mem_of_find?_eq_some hf, ?_⟩
    simp only [Bool.not_eq_true', List.any_eq_false]
    intro e he
    obtain ⟨d, -, hd⟩ := List.mem_filterMap.mp he
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hd
    unfold Scc.Frontend.externOf at hx
    rw [hn]
    split at hx
    · rename_i h; simp only [Bool.and_eq_true, beq_iff_eq] at h; simp [h.1.1.1.1]
    · split at hx
      · rename_i h; simp only [Bool.and_eq_true, beq_iff_eq, Scc.Frontend.declIs] at h; simp [h.1]
      · cases hx
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
  exact ⟨j, hj, hn⟩

/-- **With a setup block, `rodata` is a compiled block** (`rodata_of_setupOf`,
`rodata_compiled2`). -/
theorem rodata_compiled2_ofSetupOf {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {s : Ty}
    (hs : Scc.Lower.setupOf p = some s) : ∃ (j : Nat) (d : Decl), (compiled2 p)[j]? = some d ∧ d.name = "rodata" :=
  let ⟨_, hf, _⟩ := rodata_of_setupOf hp hs
  let ⟨j, hj, hn⟩ := rodata_compiled2 hf
  ⟨j, _, hj, hn⟩

end Spike.Lib.LowerNode

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerNode.rodata_compiled2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.rodata_compiled2

/--
info: 'Spike.Lib.LowerNode.rodata_compiled2_ofSetupOf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.LowerNode.rodata_compiled2_ofSetupOf
