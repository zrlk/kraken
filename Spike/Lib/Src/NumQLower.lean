/-
**`numQ` from a successful lowering** (`numQ_of_lowerIR`): every point of an
`Accepted2` program's walk has `numQ` when `lowerIR` succeeds on it. The
checked program is `checked2 p` (`checkedOf_accepted2`), whose program is `p`
and whose externs are the frontend's, so `numQ_of_lowerWithMarks` applies to
the `lowerWithMarks` step. This is the premise `hn` of `srcNumS_of_accepted2`
and `srcRd_isNum`, discharged from the compiler's success (the ISA-specific
`numQ_of_placeOK` in `Spike.Lib.LowerX64.NumQOfPlaceOK` /
`Spike.Lib.LowerA64.NumQOfPlaceOKA` get that success from `placeOKAt`).
-/
import Spike.Lib.Src.SrcNum
import Spike.Lib.LowerProgC2Core

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.Lower (litWalks2)

/-- **Every point of an `Accepted2` program's walk has `numQ`** when
`lowerIR` succeeds on it. -/
theorem numQ_of_lowerIR {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {cfg : Scc.Config}
    {l : Scc.Lower.Lowered} (hl : Scc.Lower.lowerIR cfg p = .ok l) :
    ∀ q ∈ litWalks2 p, numQ q = true := by
  unfold Scc.Lower.lowerIR at hl
  rw [checkedOf_accepted2 hp] at hl
  simp only [bind, Except.bind] at hl
  cases hb : Scc.Lower.stackBudget cfg (checked2 p) with
  | error e => rw [hb] at hl; cases hl
  | ok b =>
    rw [hb] at hl
    cases hw : Scc.Lower.lowerWithMarks cfg (checked2 p) with
    | error e => simp only [hw] at hl; cases hl
    | ok x => exact numQ_of_lowerWithMarks hp rfl rfl hw

/-- **The setup block `rodata` of an `Accepted2` program with a setup block
of result `s`**: `rodata`'s result type is `s`. -/
theorem rodata_of_setupOf {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {s : Ty}
    (hs : Scc.Lower.setupOf p = some s) : ∃ dr, p.find? (·.name == "rodata") = some dr ∧ dr.retTy = s := by
  have hds : Scc.Lower.decls2 [] (Scc.Lower.setupOf p) (Scc.Lower.hasPrint p) p = true := by
    simp only [Scc.Lower.Accepted2, Bool.and_eq_true] at hp; exact hp.1.1.1.1.1.1.1.2
  have hsp : Scc.Lower.setupPresent p = true := by
    simp only [Scc.Lower.Accepted2, Bool.and_eq_true] at hp; exact hp.1.1.1.1.1.1.2
  have hrm : p.any (·.name == "rodata") = true := by simpa [Scc.Lower.setupPresent, hs] using hsp
  obtain ⟨dr, hfr⟩ := Option.isSome_iff_exists.mp
    (List.find?_isSome.mpr (List.any_eq_true.mp hrm) : (p.find? (·.name == "rodata")).isSome)
  have hrn : dr.name = "rodata" := by simpa using List.find?_some hfr
  obtain ⟨E', hE'⟩ := decl2_of_decls2 hds dr (List.mem_of_find?_eq_some hfr)
  have hpe' : Scc.Lower.isPrintExt dr = false := by simp [Scc.Lower.isPrintExt, hrn]
  have hnl' : (Scc.Lower.hasPrint p && "rodata" == "printL") = false := by simp
  simp only [Scc.Lower.decl2, hpe', hrn, hnl', hs, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true] at hE'
  have hmr : ("rodata" == "main") = false := by decide
  simp only [hmr, Bool.false_eq_true, ↓reduceIte] at hE'
  unfold Scc.Lower.setup2 at hE'
  simp only [Bool.and_eq_true, beq_iff_eq] at hE'
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hrr⟩, -⟩, -⟩, -⟩ := hE'
  exact ⟨dr, hfr, hrr⟩

/-- **The setup block's result is not a bare locative** (`setup2`), for an
`Accepted2` program. -/
theorem hloc_of_accepted2 {p : Prog} (hp : Scc.Lower.Accepted2 p = true) :
    ∀ s, Scc.Lower.setupOf p = some s → Scc.Lower.shapeOf s ≠ .loc := by
  intro s hs
  have hds : Scc.Lower.decls2 [] (Scc.Lower.setupOf p) (Scc.Lower.hasPrint p) p = true := by
    simp only [Scc.Lower.Accepted2, Bool.and_eq_true] at hp; exact hp.1.1.1.1.1.1.1.2
  obtain ⟨dr, hfr, -⟩ := rodata_of_setupOf hp hs
  have hrn : dr.name = "rodata" := by simpa using List.find?_some hfr
  obtain ⟨E', hE'⟩ := decl2_of_decls2 hds dr (List.mem_of_find?_eq_some hfr)
  have hpe' : Scc.Lower.isPrintExt dr = false := by simp [Scc.Lower.isPrintExt, hrn]
  have hnl' : (Scc.Lower.hasPrint p && "rodata" == "printL") = false := by simp
  simp only [Scc.Lower.decl2, hpe', hrn, hnl', hs, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true] at hE'
  have hmr : ("rodata" == "main") = false := by decide
  simp only [hmr, Bool.false_eq_true, ↓reduceIte] at hE'
  unfold Scc.Lower.setup2 at hE'
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hE'
  exact hE'.1.2.2

/-- **The setup block's result is a simple type** (`setup2`), for an
`Accepted2` program: its word layout is exactly `shapeOf`'s. -/
theorem simpleTy_of_accepted2 {p : Prog} (hp : Scc.Lower.Accepted2 p = true) :
    ∀ s, Scc.Lower.setupOf p = some s → Scc.Lower.simpleTy s = true := by
  intro s hs
  have hds : Scc.Lower.decls2 [] (Scc.Lower.setupOf p) (Scc.Lower.hasPrint p) p = true := by
    simp only [Scc.Lower.Accepted2, Bool.and_eq_true] at hp; exact hp.1.1.1.1.1.1.1.2
  obtain ⟨dr, hfr, -⟩ := rodata_of_setupOf hp hs
  have hrn : dr.name = "rodata" := by simpa using List.find?_some hfr
  obtain ⟨E', hE'⟩ := decl2_of_decls2 hds dr (List.mem_of_find?_eq_some hfr)
  have hpe' : Scc.Lower.isPrintExt dr = false := by simp [Scc.Lower.isPrintExt, hrn]
  have hnl' : (Scc.Lower.hasPrint p && "rodata" == "printL") = false := by simp
  simp only [Scc.Lower.decl2, hpe', hrn, hnl', hs, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true] at hE'
  have hmr : ("rodata" == "main") = false := by decide
  simp only [hmr, Bool.false_eq_true, ↓reduceIte] at hE'
  unfold Scc.Lower.setup2 at hE'
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hE'
  exact hE'.1.2.1

/-- **The setup block's result has a runtime layout** when `lowerIR`
succeeds on an `Accepted2` program: the lowering's `setupWords` step throws
unless `rodata`'s result has `Obj.valWords`. -/
theorem setupValWords_of_lowerIR {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {cfg : Scc.Config}
    {l : Scc.Lower.Lowered} (hl : Scc.Lower.lowerIR cfg p = .ok l) :
    ∀ s, Scc.Lower.setupOf p = some s → ∃ k, Scc.Obj.valWords s = some k := by
  intro s hs
  obtain ⟨dr, hfr, hrt⟩ := rodata_of_setupOf hp hs
  unfold Scc.Lower.lowerIR at hl
  rw [checkedOf_accepted2 hp] at hl
  simp only [bind, Except.bind] at hl
  cases hb : Scc.Lower.stackBudget cfg (checked2 p) with
  | error e => rw [hb] at hl; cases hl
  | ok b =>
    rw [hb] at hl
    cases hw : Scc.Lower.lowerWithMarks cfg (checked2 p) with
    | error e => simp only [hw] at hl; cases hl
    | ok x =>
      cases hn : Scc.Obj.valWords dr.retTy with
      | some k => exact ⟨k, hrt ▸ hn⟩
      | none =>
        exfalso
        unfold Scc.Lower.lowerWithMarks at hw
        simp only [checked2, bind, Except.bind, pure, Except.pure] at hw
        split at hw
        · cases hw
        split at hw
        · cases hw
        rw [spawned_accepted2 hp] at hw
        have harg : (entry2 p).arg = .setupTid := by simp [entry2, hs]
        simp only [List.eraseDups_nil, List.mapM_nil, pure, Except.pure, harg, hfr, hn, throw, throwThe,
          MonadExceptOf.throw] at hw
        cases hw

/--
info: 'Spike.Lib.LowerNode.numQ_of_lowerIR' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms numQ_of_lowerIR

/--
info: 'Spike.Lib.LowerNode.setupValWords_of_lowerIR' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms setupValWords_of_lowerIR

/--
info: 'Spike.Lib.LowerNode.hloc_of_accepted2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hloc_of_accepted2

/--
info: 'Spike.Lib.LowerNode.simpleTy_of_accepted2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms simpleTy_of_accepted2

end Spike.Lib.LowerNode
