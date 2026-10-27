import Spike.Lib.LowerA64.CalleeRoom

/-!
# The stack room of a function and of its callees on AArch64

`Spike/Lib/LowerA64/CalleeRoom.lean` at work: from a caller's room, its
own frame's and a callee's room at `fnPh1_ofPlaceOK`'s witnesses, `main`'s
room at its depth, and the axioms of the pieces.
-/

namespace Spike.Test.LowerA64CalleeRoom

open Scc.Lower Scc.Lower.Inv
open Spike.Lib.LowerShape (allInsts)

/-- AArch64: a caller with room at an 8-aligned `lo` (slack `48`) covers its
frame and the overflow abort's `48` bytes, and each named callee has room
at an explicit 8-aligned depth `D` below the caller's frame. -/
example {cfg : Scc.Config} {p : CoreTerm.Prog} (hp : Accepted1 p = true)
    {em : Scc.Lower.A64.Emitted} (hlow : Scc.Lower.A64.lowerAll? cfg p = .ok em)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.A64.placeOKAt pcfg Λ
      (Scc.Cert.PlaceOK.A64.Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true) :
    ∃ rs : List Res1, ∀ (j : Nat) (d : CoreTerm.Decl) (r : Res1) ds (g : String) ws (lo : Int), p[j]? = some d →
      rs[j]? = some r → Scc.IR.Inst.call ds (Names.user g) ws ∈ allInsts r → g ∈ p.map (·.name) →
      lo % 8 = 0 →
      Spike.Lib.LowerA64.NeedRoomA (Scc.Cert.PlaceOK.A64.Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need
        (Names.user d.name) 48 lo →
      lo ≤ -48 ∧ ∃ (j' : Nat) (dg : CoreTerm.Decl) (D : Int), j' < j ∧ p[j']? = some dg ∧ dg.name = g ∧
        D % 8 = 0 ∧ lo ≤ -D ∧
        Spike.Lib.LowerA64.NeedRoomA (Scc.Cert.PlaceOK.A64.Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need
          (Names.user g) 48 (-D) := by
  obtain ⟨rs, rt, hrs, hir, -⟩ := Spike.Lib.LowerA64.fnPh1_ofPlaceOK hp hlow h (fun _ _ _ => none)
  refine ⟨rs, fun j d r ds g ws lo hd hr hg hgp h8 hR => ⟨?_, ?_⟩⟩
  · have := Spike.Lib.LowerA64.ownRoom_of_placeOK h hrs hir hd hr hR
    omega
  · obtain ⟨j', dg, -, hlt, hdg, -, hn, D, hD0, hD8, hlo, hR'⟩ :=
      Spike.Lib.LowerA64.calleeRoom_of_placeOK hp h hrs hir hd hr hg hgp h8 hR
    exact ⟨j', dg, D, hlt, hdg, hn, hD8, by omega, hR'⟩

example (tbl : List Scc.Cert.NeedA64.Row) (a : String) (f n : Nat)
    (hr : Scc.Cert.NeedA64.row? tbl "wc_main" = some (a, f, n)) :
    Spike.Lib.LowerA64.NeedRoomA tbl "wc_main" 48 (-Spike.Lib.LowerA64.needDA n) :=
  Spike.Lib.LowerA64.mainRoom_of_row hr

/-- info: 'Spike.Lib.LowerA64.frame16_of_fnPh1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.frame16_of_fnPh1

/-- info: 'Spike.Lib.LowerA64.ownRoom_of_placeOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.ownRoom_of_placeOK

/-- info: 'Spike.Lib.LowerA64.calleeRoom_of_placeOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.calleeRoom_of_placeOK

/-- info: 'Spike.Lib.LowerA64.mainRoom_of_row' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.mainRoom_of_row

end Spike.Test.LowerA64CalleeRoom
