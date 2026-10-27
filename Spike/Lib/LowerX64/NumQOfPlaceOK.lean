/-
**`numQ` from the x86-64 placement check** (`numQ_of_placeOK`): when the
lowering's output passes `placeOKAt` at some layout, `lowerAll?` succeeds
(`lowerAll?_ok_of_placeOKC`), so its `lowerIR` step does, and every point of
an `Accepted2` program's walk has `numQ` (`numQ_of_lowerIR`): the premise
`hn` of `srcNumS_of_accepted2` / `srcRd_isNum` from `placeOKAt`.
-/
import Spike.Lib.LowerX64.CorrectC
import Spike.Lib.Src.NumQLower

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Lower (litWalks2)

/-- **The x86-64 lowering's `lowerIR` step succeeds** on an output passing
`placeOKAt`. -/
theorem lowerIR_ok_of_placeOK {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog}
    {sizes : List Nat} {labelOffs : List (String × Nat)} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true) :
    ∃ l, Scc.Lower.lowerIR cfg p = .ok l := by
  obtain ⟨em, hem⟩ := lowerAll?_ok_of_placeOKC h
  unfold Scc.Lower.X64.lowerAll? at hem
  cases hl : Scc.Lower.lowerIR cfg p with
  | ok l => exact ⟨l, rfl⟩
  | error e => rw [hl] at hem; cases hem

/-- **Every point of an `Accepted2` program's walk has `numQ`** when the
x86-64 lowering's output passes `placeOKAt` at some layout. -/
theorem numQ_of_placeOK {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog}
    {sizes : List Nat} {labelOffs : List (String × Nat)} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (hp : Scc.Lower.Accepted2 p = true) :
    ∀ q ∈ litWalks2 p, Spike.Lib.LowerNode.numQ q = true := by
  obtain ⟨l, hl⟩ := lowerIR_ok_of_placeOK h
  exact Spike.Lib.LowerNode.numQ_of_lowerIR hp hl

/-- **The setup block's result has a runtime layout** when the x86-64
lowering's output passes `placeOKAt` at some layout. -/
theorem setupValWords_of_placeOK {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog}
    {sizes : List Nat} {labelOffs : List (String × Nat)} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (hp : Scc.Lower.Accepted2 p = true) :
    ∀ s, Scc.Lower.setupOf p = some s → ∃ k, Scc.Obj.valWords s = some k := by
  obtain ⟨l, hl⟩ := lowerIR_ok_of_placeOK h
  exact Spike.Lib.LowerNode.setupValWords_of_lowerIR hp hl

/--
info: 'Spike.Lib.LowerX64.numQ_of_placeOK' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms numQ_of_placeOK

/--
info: 'Spike.Lib.LowerX64.setupValWords_of_placeOK' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms setupValWords_of_placeOK

end Spike.Lib.LowerX64
