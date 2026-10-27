/-
**`main` is a compiled block** (ISA-neutral; the twin of
`Spike/Lib/SetupRodata.lean`): `main` is no extern (the externs are
`print` and `printL` only), so the declaration named `main` of the program
is one of its compiled blocks (`compiled2`); an `Accepted2` program has one.
The index premise of `mainHead_ofPlaceOK` / `mainPro_ofPlaceOK`
(`Spike/Lib/LowerX64/SetupCodeOf.lean`, `Spike/Lib/LowerA64/SetupCodeOf.lean`).

- `main_compiled2`: `main`'s declaration at an index of `compiled2 p`;
- `main_compiled2_ofAccepted2`: the same for an `Accepted2` program.
-/
import Spike.Lib.SetupRodata

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm

/-- **`main` is a compiled block**: the program's declaration named `main`
(`p.find?`) is at some index of `compiled2 p`, no extern being named
`main`. -/
theorem main_compiled2 {p : Prog} {dm : Decl} (hf : p.find? (·.name == "main") = some dm) :
    ∃ j : Nat, (compiled2 p)[j]? = some dm ∧ dm.name = "main" := by
  have hn : dm.name = "main" := by simpa using List.find?_some hf
  have hm : dm ∈ compiled2 p := by
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

/-- **An `Accepted2` program's `main` is a compiled block** (`Accepted2`'s
`main` present, `main_compiled2`). -/
theorem main_compiled2_ofAccepted2 {p : Prog} (hp : Scc.Lower.Accepted2 p = true) :
    ∃ (j : Nat) (d : Decl), (compiled2 p)[j]? = some d ∧ d.name = "main" := by
  have hm : p.any (·.name == "main") = true := by
    simp only [Scc.Lower.Accepted2, Bool.and_eq_true] at hp; exact hp.1.1.1.1.1.1.1.1.2
  obtain ⟨dm, hf⟩ := Option.isSome_iff_exists.mp
    (List.find?_isSome.mpr (List.any_eq_true.mp hm) : (p.find? (·.name == "main")).isSome)
  obtain ⟨j, hj, hn⟩ := main_compiled2 hf
  exact ⟨j, dm, hj, hn⟩

end Spike.Lib.LowerNode

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerNode.main_compiled2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.main_compiled2

/-- info: 'Spike.Lib.LowerNode.main_compiled2_ofAccepted2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.main_compiled2_ofAccepted2
