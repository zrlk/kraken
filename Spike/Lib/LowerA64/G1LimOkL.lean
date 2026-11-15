/-
**The prologue's limit facts at a reachable placement** (AArch64):
`LimOk2StmtL` (`Spike/Lib/LowerA64/G1CallG2L.lean`), `limOk2`
(`Spike/Lib/LowerA64/G1Room2.lean`) at a placement reachable from the
start's, the runtime's words free of the placed labels
(`rtFree_lvl_ofPlaceOK`).

- `limOk2L`: `LimOk2StmtL`.
-/
import Spike.Lib.LowerA64.G1CallG2L
import Spike.Lib.LowerA64.G1Room2
import Spike.Lib.LowerA64.LimLvl2

namespace Spike.Lib.LowerA64

set_option autoImplicit false

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.LowerNode (IsNum imms2Me)
open Spike.Lib.A64.Flow.Ret0 (limA pinA)

section G1LimOkL

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The output. -/
local notation "OUT" => Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The canonical load's memory of the output. -/
local notation "M0" => Spike.Lib.A64.PhRec.m0Of (Ly).Λ (Scc.Cert.PlaceOK.Out.prog (OUT)) (OUT).secs

/-- **The prologue's limit facts inside `MSAtL`** (`limOk2` at a reachable
placement `L`, `ls`: the runtime's limit facts at `L`, `ls` from the
runtime's words free of its labels, `rtFree_lvl_ofPlaceOK`). -/
theorem limOk2L (hp : Scc.Lower.Accepted2 p = true) : LimOk2StmtL h hp := by
  intro J L ls hre F fs σ fsz htp hun hroom
  refine limOk_tpidr htp ?_
  have e : UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64) = UInt64.ofBitVec ((Ly).pinA + 0#64 + 8#64) := by
    rw [Spike.Lib.A64.Rt.pinA_lab0 (Ly)]
  have h0 := Spike.Lib.A64.Rt.rt_limOk (L := Ly) (μ := Spike.Lib.A64.PhRec.μ (Ly)) (rd := IsNum)
    (G := Spike.Lib.A64.PhRec.GOf Ly M0) (own := Spike.Lib.A64.PhRec.own (Ly)) (lbl := L)
    (lsize := ls) (rtFree_lvl_ofPlaceOK h (imms2Me Λ p) hre) (Z := BitVec.allOnes 64)
    (fun v _ => by have := (v.setWidth 64).isLt; simp only [BitVec.toNat_allOnes]; omega)
  have h1 := limOk_toAX (p := p) (ar := Spike.Lib.A64.Rt.arOf (Ly).Λ)
    (J := Spike.Lib.AllocReach.IN (Spike.Lib.A64.Rt.arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J)
    (ab := ab2 p (Ly).lab) h0
  rw [← e] at h1
  revert hroom
  generalize ab2 p (Ly).lab = ab at h1 ⊢
  cases ab <;> exact fun hroom => ⟨h1.rt, h1.mp, hun, hroom⟩

end G1LimOkL

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.limOk2L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.limOk2L
