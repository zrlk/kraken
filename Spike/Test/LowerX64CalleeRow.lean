import Spike.Lib.LowerX64.CalleeRow

/-!
# A call site's rows of the stack need table on x86-64

`Spike/Lib/LowerX64/CalleeRow.lean` at work: the call site's rows composed
with `fnPh1_ofPlaceOK`'s witnesses, and the axioms of the pieces.
-/

namespace Spike.Test.LowerX64CalleeRow

open Scc.Lower Scc.Lower.Inv
open Spike.Lib.LowerShape (allInsts)
open Spike.Lib.LowerX64

/-- The call site's rows at `fnPh1_ofPlaceOK`'s witnesses: the callee comes
earlier, and the caller's need covers its frame, the return address and the
callee's need. -/
example {cfg : Scc.Config} {p : CoreTerm.Prog} (hp : Accepted1 p = true)
    {em : Scc.Lower.X64.Emitted} (hlow : Scc.Lower.X64.lowerAll? cfg p = .ok em)
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.X64.placeOKAt pcfg Λ
      (Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true) :
    ∃ rs : List Res1, ∀ (j : Nat) (d : CoreTerm.Decl) (r : Res1) ds (g : String) ws, p[j]? = some d →
      rs[j]? = some r → Scc.IR.Inst.call ds (Names.user g) ws ∈ allInsts r →
      ∃ j' dg, j' < j ∧ p[j']? = some dg := by
  obtain ⟨rs, rt, hrs, hir, -⟩ := fnPh1_ofPlaceOK hp hlow h (fun _ _ _ => none)
  refine ⟨rs, fun j d r ds g ws hd hr hg => ?_⟩
  obtain ⟨j', dg, -, hlt, hdg, -⟩ := calleeRow_of_fnPh1 hp h hrs hir hd hr hg
  exact ⟨j', dg, hlt, hdg⟩

/-- info: 'Spike.Lib.LowerX64.needOk1_row' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms needOk1_row

/-- info: 'Spike.Lib.LowerX64.mem_callees_func1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mem_callees_func1

/-- info: 'Spike.Lib.LowerX64.needOk1_of_fnPh1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms needOk1_of_fnPh1

/-- info: 'Spike.Lib.LowerX64.calleeRow_of_fnPh1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms calleeRow_of_fnPh1

/-- info: 'Spike.Lib.LowerX64.calleeRow_name_of_fnPh1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms calleeRow_name_of_fnPh1

/-- info: 'Spike.Lib.LowerX64.hasAddChk_func1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hasAddChk_func1

end Spike.Test.LowerX64CalleeRow
