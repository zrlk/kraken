/-
**`main` allocates no buffer** (ISA-neutral): the compiled block named
`main` of an `Accepted2` program passes `body2` at a context without
allocations (`main2`'s body check), so no tail on its walk allocates a
buffer.

- `main_body2N`: `main`'s body passes `body2` at a context without
  allocations;
- `main_noNewBufT`: no tail of `main`'s walk is a buffer allocation.
-/
import Spike.Lib.Src.CallOrder2
import Spike.Lib.Src.ImmIn2
import Spike.Lib.Src.Walk2Facts

namespace Spike.Lib.LowerNode

set_option autoImplicit false

open CoreLang CoreTerm

/-- **`main`'s body passes `body2` without allocations** (`main2`): the
`j`th compiled block named `main` of an `Accepted2` program. -/
theorem main_body2N {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) (hn : d.name = "main") :
    ∃ (E excl : List String) (ext : Bool) (cs bufs : List (String × Nat)) (scope : List String),
      Scc.Lower.body2 ⟨false, E, excl, ext⟩ cs bufs scope d.body = true := by
  have hdp := (List.mem_filter.1 (List.mem_of_getElem? hd)).1
  have hds : Scc.Lower.decls2 [] (Scc.Lower.setupOf p) (Scc.Lower.hasPrint p) p = true := by
    simp only [Scc.Lower.Accepted2, Bool.and_eq_true] at hp; exact hp.1.1.1.1.1.1.1.2
  obtain ⟨E, hE⟩ := decl2_of_decls2 hds d hdp
  have hpe : Scc.Lower.isPrintExt d = false := by simp [Scc.Lower.isPrintExt, hn]
  have hpl : (Scc.Lower.hasPrint p && d.name == "printL") = false := by simp [hn]
  unfold Scc.Lower.decl2 at hE
  simp only [hpe, hpl, Bool.false_eq_true, ↓reduceIte, hn, beq_self_eq_true] at hE
  have hmp : ("main" == "printL") = false := by decide
  rw [hmp, if_neg (by simp)] at hE
  unfold Scc.Lower.main2 at hE
  simp only [Bool.and_eq_true] at hE
  exact ⟨_, _, _, _, _, _, hE.2⟩

/-- **No tail of `main`'s walk allocates a buffer** (`main_body2N`, the
tail's check by `body2_tail`). -/
theorem main_noNewBufT {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) (hn : d.name = "main") :
    ∀ x cn τ e, ¬ TailAt2 p j (.let_ x (.newBuf cn τ) e) := by
  intro y cn τ e ht
  obtain ⟨_, _, _, _, _, _, hb⟩ := main_body2N hp hd hn
  obtain ⟨_, _, _, hb'⟩ := body2_tail (ht d hd) hb
  simp [Scc.Lower.body2] at hb'

end Spike.Lib.LowerNode

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerNode.main_body2N' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.main_body2N

/-- info: 'Spike.Lib.LowerNode.main_noNewBufT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.main_noNewBufT
