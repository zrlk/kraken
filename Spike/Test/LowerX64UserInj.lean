import Spike.Lib.LowerX64.UserInj

/-!
# Distinct code block symbols from `PlaceOK` on x86-64

`Spike/Lib/LowerX64/UserInj.lean` at work: a call site's callee by its name
at `fnPh1_ofPlaceOK`'s witnesses, with no `UserInj` hypothesis, and the
axioms of the pieces.
-/

namespace Spike.Test.LowerX64UserInj

open Scc.Lower Scc.Lower.Inv
open Spike.Lib.LowerShape (allInsts)
open Spike.Lib.LowerX64

/-- The callee of a call of a code block's name at `fnPh1_ofPlaceOK`'s
witnesses is the earlier code block of that name. -/
example {cfg : Scc.Config} {p : CoreTerm.Prog} (hp : Accepted1 p = true)
    {em : Scc.Lower.X64.Emitted} (hlow : Scc.Lower.X64.lowerAll? cfg p = .ok em)
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.X64.placeOKAt pcfg Λ
      (Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true) :
    ∃ rs : List Res1, ∀ (j : Nat) (d : CoreTerm.Decl) (r : Res1) ds (g : String) ws, p[j]? = some d →
      rs[j]? = some r → Scc.IR.Inst.call ds (Names.user g) ws ∈ allInsts r → g ∈ p.map (·.name) →
      ∃ j' dg, j' < j ∧ p[j']? = some dg ∧ dg.name = g := by
  obtain ⟨rs, rt, hrs, hir, -⟩ := fnPh1_ofPlaceOK hp hlow h (fun _ _ _ => none)
  refine ⟨rs, fun j d r ds g ws hd hr hg hgp => ?_⟩
  obtain ⟨j', dg, -, hlt, hdg, -, hn, -⟩ := calleeRow_name_of_placeOK hp h hrs hir hd hr hg hgp
  exact ⟨j', dg, hlt, hdg, hn⟩

/-- info: 'Spike.Lib.LowerX64.emitFuncs_labels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms emitFuncs_labels

/-- info: 'Spike.Lib.LowerX64.lowerAll_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowerAll_cells

/-- info: 'Spike.Lib.LowerX64.labs_nodup_of_labelsNodupL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms labs_nodup_of_labelsNodupL

/-- info: 'Spike.Lib.LowerX64.user_inj_of_placeOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms user_inj_of_placeOK

/-- info: 'Spike.Lib.LowerX64.userInj_of_placeOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms userInj_of_placeOK

/-- info: 'Spike.Lib.LowerX64.calleeRow_name_of_placeOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms calleeRow_name_of_placeOK

end Spike.Test.LowerX64UserInj
