import Spike.Lib.Src.LowerMarksImm2

/-!
# The pipeline's externs return `Unit`

The lowering's externs are the frontend's (`Scc.Lower.checkedOf`:
`Frontend.externs p`), and an extern block returns `Unit` (`externOf`). With
distinct block names (`Accepted2`) the block a name finds is the block itself
(`externs_unit`), the premise `hext` of `immIn_imms2Of` and
`lowerDeclMarks_immIn2`; `lowerDeclMarks_immIn2F` is the latter on the
frontend's externs.
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.IR
open Scc.Lower

/-- An extern block returns `Unit`. -/
theorem retTy_of_externOf {d : Decl} {e : Scc.Frontend.Extern} (h : Scc.Frontend.externOf d = some e) :
    d.retTy = .unit := by
  unfold Scc.Frontend.externOf at h
  split at h
  · rename_i hc; simp only [Bool.and_eq_true, beq_iff_eq] at hc; exact hc.2
  · split at h
    · rename_i _ hc; simp only [Bool.and_eq_true, Bool.or_eq_true] at hc
      rcases hc.2 with h | h <;> rw [Scc.Frontend.declIs_eq h] <;> rfl
    · cases h

/-- With distinct names, a name determines the block. -/
theorem eq_of_name_nodup {p : Prog} (hn : (p.map (·.name)).Nodup) {a b : Decl} (ha : a ∈ p) (hb : b ∈ p)
    (h : a.name = b.name) : a = b := by
  induction p with
  | nil => cases ha
  | cons c p ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    rcases List.mem_cons.1 ha with ha' | ha' <;> rcases List.mem_cons.1 hb with hb' | hb'
    · rw [ha', hb']
    · subst ha'; exact absurd ⟨b, hb', h.symm⟩ hn.1
    · subst hb'; exact absurd ⟨a, ha', h⟩ hn.1
    · exact ih hn.2 ha' hb'

/-- **With distinct block names, the frontend's externs return `Unit`.** -/
theorem externs_unit {p : Prog} (hn : (p.map (·.name)).Nodup) :
    ∀ d ∈ p, ((Scc.Frontend.externs p).find? (·.1 == d.name)).isSome = true → d.retTy = .unit := by
  intro d hd hf
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hf
  have hxm := List.mem_of_find?_eq_some hx
  have hxn : x.1 = d.name := by simpa using List.find?_some hx
  unfold Scc.Frontend.externs at hxm
  obtain ⟨d', hd', he⟩ := List.mem_filterMap.1 hxm
  obtain ⟨e, he', rfl⟩ := Option.map_eq_some_iff.1 he
  have : d' = d := eq_of_name_nodup hn hd' hd hxn
  subst this
  exact retTy_of_externOf he'

theorem nodup_of_accepted2 {p : Prog} (hp : Scc.Lower.Accepted2 p = true) : (p.map (·.name)).Nodup := by
  simp only [Scc.Lower.Accepted2, Bool.and_eq_true] at hp
  exact of_decide_eq_true hp.1.1.1.1.1.1.1.1.1

/-- `lowerDeclMarks_immIn2` on the frontend's externs: no `hext` premise. -/
theorem lowerDeclMarks_immIn2F {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
    {d : Decl} (hd : d ∈ p) (hne : Scc.Lower.isPrintExt d = false)
    (hnl : ¬(Scc.Lower.hasPrint p = true ∧ d.name = "printL"))
    {obj : Scc.ObjLayout} {frames : Option Nat} {f : Func} {marks : Array (Node × Point)}
    (h : lowerDeclMarks p (Scc.Frontend.externs p) d obj frames = .ok (f, marks)) :
    ∀ mk ∈ marks, ImmIn2 (imms2Of p) mk.2.1 mk.2.2 :=
  lowerDeclMarks_immIn2 hp (externs_unit (nodup_of_accepted2 hp)) hd hne hnl h

/-- The output extern is an extern (`externOf`). -/
theorem externOf_of_isPrintExt {d : Decl} (h : Scc.Lower.isPrintExt d = true) :
    Scc.Frontend.externOf d = some .print := by
  unfold Scc.Lower.isPrintExt at h
  unfold Scc.Frontend.externOf
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  simp [h]

/-- **A block the lowering compiles** (not among the frontend's externs,
`lowerWithMarks`) is not the output extern. -/
theorem isPrintExt_false_of_compiled {p : Prog} {d : Decl} (hd : d ∈ p)
    (hc : ((Scc.Frontend.externs p).any (·.1 == d.name)) = false) :
    Scc.Lower.isPrintExt d = false := by
  cases hpe : Scc.Lower.isPrintExt d
  · rfl
  · have hm : (d.name, Scc.Frontend.Extern.print) ∈ Scc.Frontend.externs p :=
      List.mem_filterMap.2 ⟨d, hd, by rw [externOf_of_isPrintExt hpe]; rfl⟩
    have : ((Scc.Frontend.externs p).any (·.1 == d.name)) = true := List.any_eq_true.2 ⟨_, hm, by simp⟩
    rw [hc] at this; cases this

end Spike.Lib.LowerNode
