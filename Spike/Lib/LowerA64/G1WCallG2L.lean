/-
**A plain call's blocks inside `W2` at a base context at a reachable
placement** (AArch64): `wCallG2L : WCallG2L`
(`Spike/Lib/LowerA64/G1CallG2L.lean`), `wCallG2`
(`Spike/Lib/LowerA64/G1WCallG2.lean`) at the placement `L`, `ls`: the
producers at `W2` (`Spike/Lib/LowerA64/G1CallW2.lean`) at `lbl := L`,
`lsize := ls`, from the base context's facts at the placement
(`CxCore2L`, field for field `CxCore2`'s).

- `wCallG2L`: the statement.
-/
import Spike.Lib.LowerA64.G1WCallG2
import Spike.Lib.LowerA64.G1CallG2L

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

section G1WCallG2L

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

/-- **A plain call's blocks inside `W2` at a base context at a reachable
placement** (`WCallG2L`): `wCallG2`'s producers at `lbl := L`, `lsize :=
ls`, the base context's facts at the placement (`CxCore2L`). -/
theorem wCallG2L (hp : Scc.Lower.Accepted2 p = true) (hown : Room2OwnStmt h hp) : WCallG2L h hp := by
  intro Dt J L ls j d hd R F fs fp ra tp G0 Ab hcx hra
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
      (lbl := L) (lsize := ls) (fp := fp) (ra := ra)
      hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hf h1 h16 hc.hFS hc.hR hc.hal hlo hc.hhi hc.hl hc.hh
      hsub hfit hc.hFO hpN hc.hfp hc.hG0F (fun _ _ h => h)
  · exact callW2_hWR (rd := IsNum)
      (G := Spike.Lib.A64.PhRec.GOf (Ly) (Spike.Lib.A64.PhRec.m0Of (Ly).Λ OP (OUT).secs))
      (ar := Spike.Lib.A64.Rt.arOf (Ly).Λ)
      (Jv := Spike.Lib.AllocReach.IN (Spike.Lib.A64.Rt.arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) (Dt := Dt)
      (lbl := L) (lsize := ls) (fp := fp) (ra := ra)
      hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hf h1 h16 hc.hFS hc.hR hc.hal hlo hc.hhi hc.hl hc.hh
      hsub hfit hc.hFO hpN hc.hfp hc.hG0F (fun _ _ h => h)
  · exact callW2_hWBl (rd := IsNum)
      (G := Spike.Lib.A64.PhRec.GOf (Ly) (Spike.Lib.A64.PhRec.m0Of (Ly).Λ OP (OUT).secs))
      (ar := Spike.Lib.A64.Rt.arOf (Ly).Λ)
      (Jv := Spike.Lib.AllocReach.IN (Spike.Lib.A64.Rt.arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) (Dt := Dt)
      (lbl := L) (lsize := ls) (fp := fp) (ra := ra)
      hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hf h16 hc.hFS hc.hR hc.hal hlo hc.hhi hc.hl hc.hh
      hsub hfit hc.hFO hpN hc.hfp hc.hG0F hBl hcf
  · exact callW2_hWC (rd := IsNum)
      (G := Spike.Lib.A64.PhRec.GOf (Ly) (Spike.Lib.A64.PhRec.m0Of (Ly).Λ OP (OUT).secs))
      (ar := Spike.Lib.A64.Rt.arOf (Ly).Λ)
      (Jv := Spike.Lib.AllocReach.IN (Spike.Lib.A64.Rt.arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) (Dt := Dt)
      (lbl := L) (lsize := ls) (fp := fp) (ra := ra)
      hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hf h16 hc.hR hc.hal hlo hc.hhi hc.hl hc.hh
      hsub hfit hc.hFO hpN hc.hfp hc.hG0F hcf

end G1WCallG2L

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.wCallG2L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.wCallG2L
