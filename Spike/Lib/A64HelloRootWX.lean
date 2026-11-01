/-
**A candidate for the root's third level and `H1GAH.hWX` at it** (AArch64;
row hP-hWX). `HelloRootPrem.W2` is a free field (nothing instantiates it
yet); `W2H` is `Wf` at `H1GAH`'s own parameters (the start's own, abort and
`clone` phases, the same `Ctx`), at no frames, so the level lift from the
start's level `WSH` at main's frame is a projection. The fence's extra fact
`X2H` at the take site `siteL` follows from `X0TH`: off the clone's pc its
clone clause is vacuous, its take clause is `X0TH`'s.

- `W2H`: `fs = [] ∧ Wf …` at `ownGH L a`, `WriteAb.Ab`, `AcH … pfxM`.
- `hWX_W2H`: `H1GAH.hWX`'s statement at `W := W2H …`, `X := X2H L siteL …`
  (any `endPc`, X's placement and sizes).

No absolute address appears in this file.
-/
import Spike.Lib.A64HelloH1A
import Spike.Lib.A64HelloH2Inv

namespace Spike.Lib.A64.HelloPh.RootWX

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib (Arena FragS Ctl)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.WakeWf (Wf)
open Spike.Lib.A64.Flow.WakeWc (MidG)
open Spike.Lib.A64.Flow.Ret0.StackTake (siteL)
open Spike.Lib.A64.Flow.Worker.Hello.Child (pfxM)
open Spike.Lib.HelloHMid (SBH)
open Spike.Lib.A64.HelloPh.StartWf (WSH)
open Spike.Lib.A64.HelloPh.Ti2 (X0TH)
open Spike.Lib.HelloH2Inv (X2H)

/-- **The third level** (candidate for `HelloRootPrem.W2`): `Wf` at the
start's own (`ownGH L a`), the write abort's and the `clone`'s phases, the
context `Ctx`, the placement `lbl` and sizes `lsize`, at no frames. -/
def W2H (L : RuntimeLayout) (a : BitVec 64) (ar : Arena) (p : Prog) (Dt Cl : State → Prop) (Ctx : FragS isaLSE2)
    (lbl : Lbl) (lsize : Lsize) : FragS isaLSE2 := fun s c fs =>
  fs = [] ∧ Wf L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) ar p Dt (Spike.Lib.A64.WriteAb.Ab L.lab) Cl
    (Spike.Lib.A64.HelloWf.AcH L.lab pfxM) Ctx lbl lsize s c fs

/-- **`H1GAH.hWX` at `W2H` and `X2H`**: `WSH` at main's frame and `X0TH`
at the take site gives `W2H` (`W0`'s `Wf` at no frames) and `X2H` at the
take site (`X0TH` is off the clone's pc, and its take clause is `X2H`'s). -/
theorem hWX_W2H {L : RuntimeLayout} {a : BitVec 64} {ar : Arena} {p : Prog} {Dt Cw : State → Prop}
    {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize} {frM : Ctl → TermRun.Frame} {l : WeakMem.AllocLabel}
    {b : Nat} {ws : List TermRun.Word} (endPc : Int64) (lbl' : Lbl) (lsize' : Lsize) :
    ∀ c0 cA, MidG (SBH l b ws) c0 cA → ∀ s c,
      WSH L a ar p Dt Cw Ctx lbl lsize (frM c0) (X0TH L (L.lab siteL)) s c →
      W2H L a ar p Dt Cw Ctx lbl lsize s c [] ∧ X2H L (L.lab siteL) endPc lbl' lsize' s c [] :=
  fun _ _ _ _ _ ⟨_, hX, hW⟩ => ⟨⟨rfl, hW⟩, fun h => absurd h hX.1, hX.2⟩

end Spike.Lib.A64.HelloPh.RootWX

/-- info: 'Spike.Lib.A64.HelloPh.RootWX.hWX_W2H' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootWX.hWX_W2H
