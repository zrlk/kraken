import Spike.Lib.LowerX64.CalleeRoom

/-!
# The stack room of a function and of its callees on x86-64

`Spike/Lib/LowerX64/CalleeRoom.lean` at work: from a caller's room, its
own frame's and a callee's room at `fnPh1_ofPlaceOK`'s witnesses, `main`'s
room at its depth, and the axioms of the pieces.
-/

namespace Spike.Test.LowerX64CalleeRoom

open Scc.Lower Scc.Lower.Inv
open Spike.Lib.LowerShape (allInsts)

/-- x86-64: a caller with room at `lo` (slack `40`) covers its frame and
the overflow abort's `48` bytes, and each named callee has room past the
caller's frame, saved `%rbp` and return address. -/
example {cfg : Scc.Config} {p : CoreTerm.Prog} (hp : Accepted1 p = true)
    {em : Scc.Lower.X64.Emitted} (hlow : Scc.Lower.X64.lowerAll? cfg p = .ok em)
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.X64.placeOKAt pcfg Λ
      (Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true) :
    ∃ rs : List Res1, ∀ (j : Nat) (d : CoreTerm.Decl) (r : Res1) ds (g : String) ws (lo : Int), p[j]? = some d →
      rs[j]? = some r → Scc.IR.Inst.call ds (Names.user g) ws ∈ allInsts r → g ∈ p.map (·.name) →
      Spike.Lib.LowerX64.NeedRoomX (Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes
        labelOffs).place.need (Names.user d.name) 40 lo →
      lo ≤ -48 ∧ ∃ j' dg lo', j' < j ∧ p[j']? = some dg ∧ dg.name = g ∧ lo + 16 ≤ lo' ∧
        Spike.Lib.LowerX64.NeedRoomX (Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes
          labelOffs).place.need (Names.user g) 40 lo' := by
  obtain ⟨rs, rt, hrs, hir, -⟩ := Spike.Lib.LowerX64.fnPh1_ofPlaceOK hp hlow h (fun _ _ _ => none)
  refine ⟨rs, fun j d r ds g ws lo hd hr hg hgp hR => ⟨?_, ?_⟩⟩
  · have := Spike.Lib.LowerX64.ownRoom_of_placeOK h hrs hir hd hr hR
    omega
  · obtain ⟨j', dg, -, hlt, hdg, -, hn, hR'⟩ := Spike.Lib.LowerX64.calleeRoom_of_placeOK hp h hrs hir hd hr hg hgp hR
    exact ⟨j', dg, _, hlt, hdg, hn, by omega, hR'⟩

example (fr : Scc.Emit.X64.Frame) (tbl : List Scc.Cert.NeedX64.Row) (a : String) (f n : Nat)
    (hr : Scc.Cert.NeedX64.row? tbl "wc_main" = some (a, f, n)) :
    Spike.Lib.LowerX64.NeedRoomX tbl "wc_main" 40 (-Spike.Lib.LowerX64.needD fr n) :=
  Spike.Lib.LowerX64.mainRoom_of_row fr hr

/-- info: 'Spike.Lib.LowerX64.ownRoom_of_placeOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.ownRoom_of_placeOK

/-- info: 'Spike.Lib.LowerX64.calleeRoom_of_placeOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.calleeRoom_of_placeOK

/-- info: 'Spike.Lib.LowerX64.mainRoom_of_row' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.mainRoom_of_row

end Spike.Test.LowerX64CalleeRoom
