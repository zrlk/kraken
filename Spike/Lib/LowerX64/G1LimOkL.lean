/-
**The prologue's limit facts at a reachable placement** (x86-64; the twin
of `Spike/Lib/LowerA64/G1LimOkL.lean`): `LimOk2StmtL`
(`Spike/Lib/LowerX64/G1CallG2L.lean`), `limOk2`
(`Spike/Lib/LowerX64/G1Room2.lean`) at a placement reachable from the
start's, the runtime's words free of the placed labels
(`rtFree_lvl_ofPlaceOK`).

- `limOk2L`: `LimOk2StmtL`.
-/
import Spike.Lib.LowerX64.G1CallG2L
import Spike.Lib.LowerX64.G1Room2
import Spike.Lib.LowerX64.LimLvl2

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.LowerNode (IsNum imms2Me)
open Spike.Lib.X64.Flow.Ret0 (limA pinA tpOf)

section G1LimOkL

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The output. -/
local notation "OUT" => Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The canonical load's memory of the output. -/
local notation "M0" => Spike.Lib.X64.PhRec.m0Of (Ly).Λ (Scc.Cert.PlaceOK.Out.prog (OUT)) (OUT).secs

/-- **The prologue's limit facts inside `MSAtL`** (`limOk2` at a reachable
placement `L`, `ls`: the runtime's limit facts at `L`, `ls` from the
runtime's words free of its labels, `rtFree_lvl_ofPlaceOK`). -/
theorem limOk2L (hp : Scc.Lower.Accepted2 p = true) : LimOk2StmtL h hp := by
  intro J L ls hre F fs σ fsz htp hun hroom
  refine limOk_fsBase htp ?_
  have e : tpOf (pinA (Ly).lab + 0#64 + 8#64) = tpOf ((Ly).pinA + 0#64 + 8#64) := by
    rw [Spike.Lib.X64.Rt.pinA_lab0 (Ly)]
  have h0 := Spike.Lib.X64.Rt.rt_limOk (L := Ly) (μ := Spike.Lib.X64.PhRec.μ (Ly)) (rd := IsNum)
    (G := Spike.Lib.X64.PhRec.GOf Ly M0) (own := Spike.Lib.X64.PhRec.own (Ly)) (lbl := L)
    (lsize := ls) (rtFree_lvl_ofPlaceOK h (imms2Me Λ p) hre) (Z := BitVec.allOnes 64)
    (fun v _ => by have := (v.setWidth 64).isLt; simp only [BitVec.toNat_allOnes]; omega)
  have h1 := limOk_toAX (p := p) (ar := Spike.Lib.X64.Rt.arOf (Ly).Λ)
    (J := Spike.Lib.AllocReach.IN (Spike.Lib.X64.Rt.arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J)
    (ab := ab2 p (Ly).lab) h0
  rw [← e] at h1
  revert hroom
  generalize ab2 p (Ly).lab = ab at h1 ⊢
  cases ab <;> exact fun hroom => ⟨h1.rt, h1.mp, hun, hroom⟩

end G1LimOkL

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.limOk2L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.limOk2L
