/-
**A plain call's blocks inside `W2` at a base context** (AArch64):
`wCallG2 : WCallG2` (`Spike/Lib/LowerA64/G1CallG2.lean`), the premises
`hWB`, `hWR`, `hWBl`, `hWC` of `CallC2FW` at the `j`th compiled block's
code facts under a base context with its records, from the producers at
`W2` (`Spike/Lib/LowerA64/G1CallW2.lean`).

The base context gives the region's facts, its frame condition's stack
and frames, and `FrOk2` at its ghosts (`CxCore2`); the frame lies inside
the region by the block's room (`Room2OwnStmt`). A callee `g` of the
block's lowering context called on its walk is an earlier compiled block
(`hord_ofAccepted2`), whose code facts place its prologue with the
prologue's phase facts (`fnCode2OfPMe_spec`, `ProOK`).

- `callee_fnCode2G`: the callee's code facts;
- `wCallG2`: the statement.
-/
import Spike.Lib.LowerA64.G1CallG2
import Spike.Lib.LowerA64.G1CallW2
import Spike.Lib.LowerA64.HordC2

namespace Spike.Lib.LowerA64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region FrameRunM)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (StackOff limA pinA)
open Spike.Lib.A64.Rt (rS0)
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2 imms2Me IsNum SlotRepAt)

section G1WCallG2

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates. -/
local notation "LY0" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output. -/
local notation "OUT" => Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))

set_option hygiene false in
/-- The `j`th compiled block's code facts at the theorem's immediates. -/
local notation "FC" j:max d:max hd:max => fnCode2OfPMe hp h Λ j d hd

/-- **A callee's code facts** at a plain call of the `j`th compiled block:
a callee `g` of the block's lowering context called at a point of its walk
is an earlier compiled block `dg` named `g` (`hord_ofAccepted2`), its code
facts at the theorem's immediates with its function index none of the
runtime's and its prologue's phase facts (`ProOK`). -/
theorem callee_fnCode2G (hp : Scc.Lower.Accepted2 p = true) {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) :
    ∀ (g : String), Spike.Lib.LowerCall.Callee (FC j d hd).lcx g →
      (∃ x a e, TailAt2 p j (.let_ x (.call g [] a []) e)) →
      ∃ (dg' : Decl) (RaOk : BitVec 64 → Prop) (Cd' : BitVec 64 → Int64 → List Directive → Prop)
        (i' : Expr → String → Nat → Option Nat) (T' : Expr → Prop)
        (c' : FnCode2 (LY0).exe OP (LY0).endPc RaOk Cd' i' T' dg'),
        dg'.name = g ∧ (c'.cx.fi ≠ 9 ∧ c'.cx.fi ≠ 12 ∧ c'.cx.fi ≠ 16) ∧
        ProPh (Spike.Lib.A64.PhRec.okPc LY0) (Spike.Lib.A64.PhRec.ph LY0) (LY0).lab (c'.cx.local "stack_check")
          (Int64.ofInt c'.cx.frame) (proL c'.cx) c'.ps := by
  rintro g ⟨hxe, dd, hfd, -⟩ ⟨x, a, e, hT⟩
  have hfd' : p.find? (·.name == g) = some dd := by
    rw [(fnCode2OfPMe_spec hp h Λ j d hd).1] at hfd; exact hfd
  have hext : ∀ (j : Nat) d (hd : (compiled2 p)[j]? = some d),
      (FC j d hd).lcx.externs = Scc.Frontend.externs p := fun j d hd => by
    rw [(fnCode2OfPMe_spec hp h Λ j d hd).1]
  obtain ⟨j', -, hd'⟩ := hord_ofAccepted2 hp (T := fun j => TailAt2 p j) (fun j d hd => FC j d hd) hext j d hd
    g dd ⟨x, [], a, [], e, hT d hd, hxe⟩ hfd'
  have hP := (fnCode2OfPMe_spec hp h Λ j' dd hd').2.2
  exact ⟨dd, _, _, _, _, FC j' dd hd', by simpa using List.find?_some hfd', hP.1, hP.2.1⟩

/-- **A plain call's blocks inside `W2` at a base context** (`WCallG2`):
`callW2_hWB`, `callW2_hWR`, `callW2_hWBl`, `callW2_hWC` at the instance's
`InstOk`, the base context's facts (`CxCore2`), the frame inside the region
by the block's room (`hown`), the code predicate `CdCLE` and the call
predicate inside `BlC` (`fnCode2OfPMe_spec`), the callees' code facts
(`callee_fnCode2G`). -/
theorem wCallG2 (hp : Scc.Lower.Accepted2 p = true) (hown : Room2OwnStmt h hp) : WCallG2 h hp := by
  intro Dt J j d hd R F fs fp ra tp G0 Ab hcx hra
  have hc := hcx.1
  have hf := (FC j d hd).hf
  have h1 := (FC j d hd).h1
  have h16 := (FC j d hd).h16
  have hlo : R.lo ≤ -((FC j d hd).cx.frame : Int) := by
    have := hown j d hd 256 R.lo (hc.room d hd)
    omega
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (imms2Me Λ p) (rS := rS0 (Ly))
  have hpN := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
  have hfit := Spike.Lib.A64.Rt.fitS_of_sub (Ly) hsub
  have hBl : ∀ pc g k, (FC j d hd).Bl ra pc g k →
      BlC OP (Spike.Lib.A64.PhRec.okPc LY0) (Spike.Lib.A64.PhRec.ph LY0) (LY0).lab (FC j d hd).cx
        (Int64.ofBitVec ra) pc g k := fun pc g k hb => by
    rw [(fnCode2OfPMe_spec hp h Λ j d hd).2.1] at hb
    exact hb.1.1
  have hcf := callee_fnCode2G h hp hd
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact callW2_hWB (rd := IsNum)
      (G := Spike.Lib.A64.PhRec.GOf (Ly) (Spike.Lib.A64.PhRec.m0Of (Ly).Λ OP (OUT).secs))
      (ar := Spike.Lib.A64.Rt.arOf (Ly).Λ)
      (Jv := Spike.Lib.AllocReach.IN (Spike.Lib.A64.Rt.arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) (Dt := Dt)
      (lbl := fun _ => none) (lsize := fun _ => 0) (fp := fp) (ra := ra)
      hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hf h1 h16 hc.hFS hc.hR hc.hal hlo hc.hhi hc.hl hc.hh
      hsub hfit hc.hFO hpN hc.hfp hc.hG0F (fun _ _ h => h)
  · exact callW2_hWR (rd := IsNum)
      (G := Spike.Lib.A64.PhRec.GOf (Ly) (Spike.Lib.A64.PhRec.m0Of (Ly).Λ OP (OUT).secs))
      (ar := Spike.Lib.A64.Rt.arOf (Ly).Λ)
      (Jv := Spike.Lib.AllocReach.IN (Spike.Lib.A64.Rt.arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) (Dt := Dt)
      (lbl := fun _ => none) (lsize := fun _ => 0) (fp := fp) (ra := ra)
      hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hf h1 h16 hc.hFS hc.hR hc.hal hlo hc.hhi hc.hl hc.hh
      hsub hfit hc.hFO hpN hc.hfp hc.hG0F (fun _ _ h => h)
  · exact callW2_hWBl (rd := IsNum)
      (G := Spike.Lib.A64.PhRec.GOf (Ly) (Spike.Lib.A64.PhRec.m0Of (Ly).Λ OP (OUT).secs))
      (ar := Spike.Lib.A64.Rt.arOf (Ly).Λ)
      (Jv := Spike.Lib.AllocReach.IN (Spike.Lib.A64.Rt.arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) (Dt := Dt)
      (lbl := fun _ => none) (lsize := fun _ => 0) (fp := fp) (ra := ra)
      hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hf h16 hc.hFS hc.hR hc.hal hlo hc.hhi hc.hl hc.hh
      hsub hfit hc.hFO hpN hc.hfp hc.hG0F hBl hcf
  · exact callW2_hWC (rd := IsNum)
      (G := Spike.Lib.A64.PhRec.GOf (Ly) (Spike.Lib.A64.PhRec.m0Of (Ly).Λ OP (OUT).secs))
      (ar := Spike.Lib.A64.Rt.arOf (Ly).Λ)
      (Jv := Spike.Lib.AllocReach.IN (Spike.Lib.A64.Rt.arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) (Dt := Dt)
      (lbl := fun _ => none) (lsize := fun _ => 0) (fp := fp) (ra := ra)
      hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hf h16 hc.hR hc.hal hlo hc.hhi hc.hl hc.hh
      hsub hfit hc.hFO hpN hc.hfp hc.hG0F hcf

end G1WCallG2

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.callee_fnCode2G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.callee_fnCode2G

/-- info: 'Spike.Lib.LowerA64.wCallG2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.wCallG2
