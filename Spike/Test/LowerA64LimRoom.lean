import Spike.Lib.LowerA64.LimRoom

/-!
# The stack limit's room on AArch64

`Spike/Lib/LowerA64/LimRoom.lean` at work: from a caller's limit room, its
own stack check and a callee's limit room at `fnPh1_ofPlaceOK`'s witnesses;
`main`'s limit room at the default budget; and the axioms of the pieces.
-/

namespace Spike.Test.LowerA64LimRoom

open Scc.Lower Scc.Lower.Inv
open Spike.Lib.LowerShape (allInsts)

/-- A caller with limit room at its entry `sp` passes its own stack check,
and each named callee has limit room at its entry `sp`, right below the
caller's frame. -/
example {cfg : Scc.Config} {p : CoreTerm.Prog} (hp : Accepted1 p = true)
    {em : Scc.Lower.A64.Emitted} (hlow : Scc.Lower.A64.lowerAll? cfg p = .ok em)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.A64.placeOKAt pcfg Λ
      (Scc.Cert.PlaceOK.A64.Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (G : Kraken.Promising.Val → Prop) :
    ∃ (rs : List Res1) (rt : List Scc.IR.Func), ∀ (j : Nat) (d : CoreTerm.Decl) (r : Res1) ds (g : String) ws
      (sp : Nat), p[j]? = some d → rs[j]? = some r → Scc.IR.Inst.call ds (Names.user g) ws ∈ allInsts r →
      g ∈ p.map (·.name) →
      Spike.Lib.LowerA64.LimRoomA (Scc.Cert.PlaceOK.A64.Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need
        (Names.user d.name) G sp →
      let fd := (Scc.Cert.Code1A64.ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir (rt.length + j)
        (func1 (Names.user d.name) (params1R d) r)).frame
      (∀ v, G v → (v.setWidth 64).toNat + fd ≤ sp) ∧
      ∀ sp' : Nat, sp' + fd = sp → ∃ (j' : Nat) (dg : CoreTerm.Decl), j' < j ∧ p[j']? = some dg ∧ dg.name = g ∧
        Spike.Lib.LowerA64.LimRoomA (Scc.Cert.PlaceOK.A64.Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need
          (Names.user g) G sp' := by
  obtain ⟨rs, rt, hrs, hir, -⟩ := Spike.Lib.LowerA64.fnPh1_ofPlaceOK hp hlow h (fun _ _ _ => none)
  refine ⟨rs, rt, fun j d r ds g ws sp hd hr hg hgp hL =>
    ⟨Spike.Lib.LowerA64.ownLim_of_placeOK h hrs hir hd hr hL, fun sp' hsp => ?_⟩⟩
  obtain ⟨j', dg, -, hlt, hdg, -, hn, hL'⟩ :=
    Spike.Lib.LowerA64.calleeLim_of_placeOK hp h hrs hir hd hr hg hgp hsp hL
  exact ⟨j', dg, hlt, hdg, hn, hL'⟩

/-- `main`'s limit room at the default budget `12288`: the limit
`stacksA + 4096`, the first stack's top `stacksA + 16384`, `scc_rt_main`'s
frame `48`. -/
example {G : Kraken.Promising.Val → Prop} {stacks sp n : Nat}
    (hG : ∀ v, G v → (v.setWidth 64).toNat ≤ stacks + 4096) (hrow : 48 + n ≤ 12288)
    (hsp : sp + 48 = stacks + 16384) :
    ∀ v, G v → (v.setWidth 64).toNat + n ≤ sp :=
  Spike.Lib.LowerA64.mainLim_of_rows hG hrow (by omega) hsp

/-- info: 'Spike.Lib.LowerA64.ownLim_of_placeOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.ownLim_of_placeOK

/-- info: 'Spike.Lib.LowerA64.calleeLim_of_placeOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.calleeLim_of_placeOK

/-- info: 'Spike.Lib.LowerA64.mainRow_of_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.mainRow_of_placeOKAt

/-- info: 'Spike.Lib.LowerA64.mainLim_of_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.mainLim_of_rows

end Spike.Test.LowerA64LimRoom
