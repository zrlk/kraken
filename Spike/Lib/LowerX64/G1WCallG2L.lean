/-
**A plain call's blocks inside `W2` at a base context at a reachable
placement** (x86-64; the twin of `Spike/Lib/LowerA64/G1WCallG2L.lean`):
`wCallG2L : WCallG2L` (`Spike/Lib/LowerX64/G1CallG2L.lean`), `wCallG2`
(`Spike/Lib/LowerX64/G1WCallG2.lean`) at the placement `L`, `ls`: the
producers at `W2` (`Spike/Lib/LowerX64/G1CallW2.lean`) at `lbl := L`,
`lsize := ls`, from the base context's facts at the placement
(`CxCore2L`, field for field `CxCore2`'s).

- `wCallG2L`: the statement.
-/
import Spike.Lib.LowerX64.G1WCallG2
import Spike.Lib.LowerX64.G1CallG2L

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region FrameRunM)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (StackOff limA pinA)
open Spike.Lib.X64.Rt (rS0)
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2 imms2Me IsNum SlotRepAt)

section G1WCallG2L

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates. -/
local notation "LY0" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)

set_option hygiene false in
/-- The `j`th compiled block's code facts at the theorem's immediates. -/
local notation "FC" j:max d:max hd:max => fnCode2OfPMe hp h Λ j d hd

/-- **A plain call's blocks inside `W2` at a base context at a reachable
placement** (`WCallG2L`): `wCallG2`'s producers at `lbl := L`, `lsize :=
ls`: `callW2_hWB`, `callW2_hWR`, `callW2_hWBl`, `callW2_hWC` at the instance's
`InstOk`, the base context's facts at the placement (`CxCore2L`, in the rebased region), the
frame, the saved `%rbp` and the return address inside the region by the
block's room (`hown`), the code predicate `CdCLE` and the call predicate
inside `BlC` (`fnCode2OfPMe_spec`), the callees' code facts
(`callee_fnCode2G`). -/
theorem wCallG2L (hp : Scc.Lower.Accepted2 p = true) (hown : Room2OwnStmt h hp) : WCallG2L h hp := by
  intro Dt J L ls j d hd R F fs fp ra tp G0 Ab hcx hra
  have hc := hcx.1
  have hf := (FC j d hd).hf
  have h1 := (FC j d hd).h1
  have h16 := (FC j d hd).h16
  have hrow := hown j d hd 256 ((rbR R).lo - 8) (hc.room d hd)
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (imms2Me Λ p) (rS := rS0 (Ly))
  have hpN := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  have hsub := Spike.Lib.X64.Rt.rS0_sub (Ly)
  have hfit := Spike.Lib.X64.Rt.fitS_of_sub (Ly) hsub
  have hBl : ∀ pc zc g k, (FC j d hd).Bl ra pc zc g k →
      BlC OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab (FC j d hd).fr
        (Int64.ofBitVec ra) pc zc g k := fun pc zc g k hb => by
    rw [(fnCode2OfPMe_spec hp h Λ j d hd).2.1] at hb
    exact hb.1.1
  have hcf := callee_fnCode2G h hp hd
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact callW2_hWB hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hf h1 hc.hFS hc.hR hc.hal
      (by omega) hc.hhi hc.hl hc.hh hsub hfit hc.hFO hpN hc.hfp hc.hG0F (fun _ _ h => h)
  · exact callW2_hWR hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hf h1 hc.hFS hc.hR hc.hal
      (by omega) hc.hhi hc.hl hc.hh hsub hfit hc.hFO hpN hc.hfp hc.hG0F (fun _ _ h => h)
  · exact callW2_hWBl hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hf h16 hc.hFS hc.hR hc.hal
      (by omega) hc.hhi hc.hl hc.hh hsub hfit hc.hFO hpN hc.hfp hc.hG0F hBl hcf
  · exact callW2_hWC hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hf h16 hc.hR hc.hal
      (by omega) hc.hhi hc.hl hc.hh hsub hfit hc.hFO hpN hc.hfp hc.hG0F hcf

end G1WCallG2L

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.wCallG2L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.wCallG2L
