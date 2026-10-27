/-
**The theorem's immediates at a compiled block's points** (ISA-neutral):
neither key at which `imms2Me` differs from `imms2Of p` (`SrcSem.setupTerm`,
`setupK`) is a term of an `Accepted2` body (`body2` has no `.tail` case), so
at every point of a compiled block's walk (`TailAt2 p j`) the two tables
agree.

- `body2_setupK`, `body2_setupTerm`: neither key is a `body2` term;
- `tailAt2_ne_setup`: no `TailAt2` point of a compiled block is either key;
- `immIn_congr`: `ImmIn` at a term only reads the table there;
- `imms2Me_tailAt2`: at such a point `imms2Me Λ p` is `imms2Of p`.
-/
import Spike.Lib.Src.ImmsMe
import Spike.Lib.Src.Walk2Facts

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.Lower (body2 Accepted2)
open Spike.Lib.Form (SEnv)

/-- The setup start's continuation is no `body2` term (it ends in a `.tail`). -/
theorem body2_setupK {c2 : Scc.Lower.Cx2} {cs bufs : List (String × Nat)} {scope : List String}
    (h : body2 c2 cs bufs scope setupK = true) : False := by
  simp [setupK, body2] at h

/-- The setup start's term is no `body2` term (its continuation `setupK` is none). -/
theorem body2_setupTerm {c2 : Scc.Lower.Cx2} {cs bufs : List (String × Nat)} {scope : List String}
    (h : body2 c2 cs bufs scope Scc.Sem.SrcSem.setupTerm = true) : False := by
  simp [Scc.Sem.SrcSem.setupTerm, body2] at h

/-- **No point of a compiled block is a setup key**: a `TailAt2 p j` term of
an `Accepted2` program's `j`th compiled block is a `body2` term
(`body2_of_compiled`, `body2_tail`), so neither `setupTerm` nor `setupK`. -/
theorem tailAt2_ne_setup {p : Prog} (hacc : Accepted2 p = true) {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) {t : Expr} (ht : TailAt2 p j t) :
    t ≠ Scc.Sem.SrcSem.setupTerm ∧ t ≠ setupK := by
  obtain ⟨hdp, hdc⟩ := List.mem_filter.1 (List.mem_of_getElem? hd)
  have hdc' : ((Scc.Frontend.externs p).any (·.1 == d.name)) = false := by simpa using hdc
  obtain ⟨A, B, hp⟩ := List.append_of_mem hdp
  obtain ⟨c2, cs, bufs, scope, hb, -, -⟩ := body2_of_compiled hacc hp hdc'
  obtain ⟨_, _, _, hb'⟩ := body2_tail (ht d hd) hb
  exact ⟨fun h => body2_setupTerm (h ▸ hb'), fun h => body2_setupK (h ▸ hb')⟩

/-- **`ImmIn` depends only on the table's entries at the term.** -/
theorem immIn_congr {i i' : Expr → String → Nat → Option Nat} {s : SEnv} {t : Expr} (h : ImmIn i s t)
    (hi : ∀ x k, i t x k = i' t x k) : ImmIn i' s t :=
  fun x k v hv => hi x k ▸ h x k v hv

/-- **At a compiled block's point the theorem's table is `imms2Of p`**
(`imms2Me_of_ne`, `tailAt2_ne_setup`). -/
theorem imms2Me_tailAt2 {Λ : Scc.Sem.Layout} {p : Prog} (hacc : Accepted2 p = true) {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) {t : Expr} (ht : TailAt2 p j t) (x : String) (k : Nat) :
    imms2Me Λ p t x k = Scc.Lower.imms2Of p t x k :=
  imms2Me_of_ne fun _ h _ _ => h.elim (tailAt2_ne_setup hacc hd ht).1 (tailAt2_ne_setup hacc hd ht).2

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerNode.tailAt2_ne_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tailAt2_ne_setup

/-- info: 'Spike.Lib.LowerNode.imms2Me_tailAt2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms imms2Me_tailAt2

end Spike.Lib.LowerNode
