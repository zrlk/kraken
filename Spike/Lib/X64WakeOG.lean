/-
**wake's guarantee `G` in `X64WakeO.OData`** (x86-64, the twin of
`Spike/Lib/WakeOG.lean`, same names): at the runtime's layout
`L := RuntimeLayout.ofPlaceWX hp i` of an output with wake's placement facts
(`PlaceWX`), the pre-spawn data's value invariant is
`gW hp i cT := wakeG (GOf2 L m0) cT`, `m0` the canonical load's memory and
`cT` the flag's word.

- `hGpl_ofPlaceW2`: `GOf2` holds of any value at a placed word of `.data` or
  the heap, given the second limit word in the pinned region (`hpin2`):
  `PlaceWX.hGpl_ofPlaceWX` off the second limit word.
- `gW`, `hGpl_gW`: the guarantee, and `X64WakeO.OPrem.hGpl` at it.

**Unlike AArch64**: the layout is `RuntimeLayout.ofPlaceWX` at `PlaceWX`
(A64: `ofPlaceW` at `PlaceW`); the memory is `X64.PhRec.m0Of` of the cells.
-/
import Spike.Lib.X64PlaceWRt
import Spike.Lib.X64WakeO
import Spike.Lib.X64WakeGOf2
import Spike.Lib.WakeG

namespace Spike.Lib.X64WakeOG

open Kraken Kraken.Promising
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.PhRec (GOf m0Of)
open Spike.Lib.X64WakeGOf2 (GOf2 gOf2_of lim2A lim2Off)
open Spike.Lib.PlaceWX

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
    (h : Spike.Lib.PlaceWX pcfg Λ o)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX h i

set_option hygiene false in
/-- The canonical load's memory of the output. -/
local notation "M0" => m0Of (RuntimeLayout.ofPlaceWX h i).Λ o.prog o.secs

/-- **wake's guarantee** at the layout of `ofPlaceWX`, the flag at `cT`. -/
def gW (cT : Loc) : Loc → Val → Prop := Spike.Lib.WakeG.wakeG (GOf2 Ly M0) cT

include h

/-- **The value invariant at a placed word** of `.data` or the heap, given
the second limit word lies in the pinned region (`hpin2`). -/
theorem hGpl_ofPlaceW2 (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) :
    ∀ a v, (Ly).Λ.heap.contains a ∨ (Ly).Λ.data.contains a → GOf2 Ly M0 (Scc.Sem.wordLoc a) v := by
  intro a v ha
  refine gOf2_of (hGpl_ofPlaceWX h i a v ha) fun he => ?_
  have hwf := wf_link_of_placeWX i h
  have hd : Λ.data.InSpace := hwf.inSpace _ (by simp [Scc.Sem.Layout.regions] : (Ly).Λ.data ∈ (Ly).Λ.regions)
  have hh : Λ.heap.InSpace := hwf.inSpace _ (by simp [Scc.Sem.Layout.regions] : (Ly).Λ.heap ∈ (Ly).Λ.regions)
  obtain ⟨-, -, -, -, -, -, -, hdp, hhp, -⟩ := hwf.disjoint
  have hdp' : Λ.data.Disjoint Λ.pinned := hdp
  have hhp' : Λ.heap.Disjoint Λ.pinned := hhp
  have hp : (Ly).pinA.toNat = Λ.pinned.lo := pinA_toNat_ofPlaceWX h i
  change (Ly).pinA.toNat + 168 ≤ Λ.pinned.lo + Λ.pinned.size at hpin2
  change Λ.heap.contains a ∨ Λ.data.contains a at ha
  have hx := congrArg (fun l : Loc => l.addr.toNat) he
  simp only [Scc.Sem.wordLoc, lim2A, lim2Off, BitVec.toNat_ofNat, BitVec.toNat_add] at hx
  simp only [Scc.Sem.Range.InSpace] at hd hh
  simp only [Scc.Sem.Range.contains] at ha
  simp only [Scc.Sem.Range.Disjoint] at hdp' hhp'
  have hsm := (Ly).words_small _ (Ly).pin_mem
  have ha64 : a < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt ha64, Nat.mod_eq_of_lt (by omega : (Ly).pinA.toNat + 112 < 2 ^ 64)] at hx
  omega

/-- **`OPrem.hGpl` at wake's guarantee.** -/
theorem hGpl_gW (cT : Loc) (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) :
    ∀ a v, (Ly).Λ.heap.contains a ∨ (Ly).Λ.data.contains a → gW h i cT (Scc.Sem.wordLoc a) v :=
  fun a v ha => .inr (hGpl_ofPlaceW2 h i hpin2 a v ha)

end Place

end Spike.Lib.X64WakeOG

/-- info: 'Spike.Lib.X64WakeOG.hGpl_ofPlaceW2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOG.hGpl_ofPlaceW2

/-- info: 'Spike.Lib.X64WakeOG.hGpl_gW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOG.hGpl_gW
