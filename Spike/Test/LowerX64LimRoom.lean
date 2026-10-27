import Spike.Lib.LowerX64.LimRoom

/-!
# The stack limit's room on x86-64

`Spike/Lib/LowerX64/LimRoom.lean` at work: from a caller's limit room, its
own stack check in the prologue's form and a callee's limit room at
`fnPh1_ofPlaceOK`'s witnesses; `main`'s limit room at the default budget;
and the axioms of the pieces.
-/

namespace Spike.Test.LowerX64LimRoom

open Scc.Lower Scc.Lower.Inv
open Spike.Lib.LowerShape (allInsts)

/-- A caller with limit room at its entry `%rsp` passes its own stack check
(for 16-aligned limit values) in the prologue's form, and each named callee
has limit room at its entry `%rsp`, past the caller's frame, saved `%rbp`
and return address. -/
example {cfg : Scc.Config} {p : CoreTerm.Prog} (hp : Accepted1 p = true)
    {em : Scc.Lower.X64.Emitted} (hlow : Scc.Lower.X64.lowerAll? cfg p = .ok em)
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.X64.placeOKAt pcfg Λ
      (Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (G : Kraken.Promising.Val → Prop) (hG16 : ∀ v, G v → (v.setWidth 64).toNat % 16 = 0) :
    ∃ rs : List Res1, ∀ (j : Nat) (d : CoreTerm.Decl) (r : Res1) ds (g : String) ws (rsp : BitVec 64),
      p[j]? = some d → rs[j]? = some r → Scc.IR.Inst.call ds (Names.user g) ws ∈ allInsts r →
      g ∈ p.map (·.name) → rsp.toNat % 16 = 8 →
      Spike.Lib.LowerX64.LimRoomX (Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes
        labelOffs).place.need (Names.user d.name) G rsp.toNat →
      (∀ v, G v → (v.setWidth 64).toNat ≤ (rsp - 8#64 - (Int64.ofInt ((Spike.Lib.LowerX64.frOf
        (Scc.Lower.X64.lowerAll cfg p).low.ir (func1 (Names.user d.name) (params1R d) r)).size : Int)).toBitVec
          ).toNat) ∧
      ∀ rsp' : Nat, rsp' + (Spike.Lib.LowerX64.frOf (Scc.Lower.X64.lowerAll cfg p).low.ir
          (func1 (Names.user d.name) (params1R d) r)).size + 16 = rsp.toNat →
        ∃ (j' : Nat) (dg : CoreTerm.Decl), j' < j ∧ p[j']? = some dg ∧ dg.name = g ∧ rsp' % 16 = 8 ∧
          Spike.Lib.LowerX64.LimRoomX (Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes
            labelOffs).place.need (Names.user g) G rsp' := by
  obtain ⟨rs, rt, hrs, hir, -⟩ := Spike.Lib.LowerX64.fnPh1_ofPlaceOK hp hlow h (fun _ _ _ => none)
  refine ⟨rs, fun j d r ds g ws rsp hd hr hg hgp h8 hL =>
    ⟨Spike.Lib.LowerX64.ownLimBv_of_placeOK h hrs hir hd hr h8 hG16 hL, fun rsp' hrsp => ?_⟩⟩
  obtain ⟨j', dg, -, hlt, hdg, -, hn, h8', hL'⟩ :=
    Spike.Lib.LowerX64.calleeLim_of_placeOK hp h hrs hir hd hr hg hgp (by omega) hrsp hL
  exact ⟨j', dg, hlt, hdg, hn, h8', hL'⟩

/-- `main`'s limit room at the default budget `12288`: the limit
`stacksA + 4096`, the first stack's top `stacksA + 16384`. -/
example {G : Kraken.Promising.Val → Prop} {stacks rsp sg n : Nat}
    (hG : ∀ v, G v → (v.setWidth 64).toNat ≤ stacks + 4096) (hrow : sg + 8 + 8 + n ≤ 12288)
    (hrsp : rsp + sg + 16 + 8 = stacks + 16384) :
    ∀ v, G v → (v.setWidth 64).toNat + n ≤ rsp + 8 :=
  Spike.Lib.LowerX64.mainLim_of_rows hG hrow (by omega) hrsp

/-- info: 'Spike.Lib.LowerX64.frame_of_fnPh1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.frame_of_fnPh1

/-- info: 'Spike.Lib.LowerX64.ownLimBv_of_placeOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.ownLimBv_of_placeOK

/-- info: 'Spike.Lib.LowerX64.calleeLim_of_placeOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.calleeLim_of_placeOK

/-- info: 'Spike.Lib.LowerX64.mainRow_of_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.mainRow_of_placeOKAt

/-- info: 'Spike.Lib.LowerX64.mainLim_of_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.mainLim_of_rows

end Spike.Test.LowerX64LimRoom
