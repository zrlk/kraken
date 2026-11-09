/-
**A candidate for the root's third level and the level lift at it** (x86-64; the twin of
`Spike/Lib/A64HelloRootWX.lean`). `W2H` is `Wf` at the start's own parameters (the start's own, abort and `clone`
phases, the same `Ctx`), at no frames, so the level lift from the start's level `WSH` at main's frame is a
projection. The fence's extra fact `X2H` at the take site `siteL` follows from `X0TH`: off the clone's pc its
clone clause is vacuous, its take clause is `X0TH`'s.

- `W2Hg`: `fs = [] ∧ Wf …` at any owned words `own`, `WriteAb.Ab`, `AcH … pfxM`; `W2H`: at `ownGH L a`.
- `hWX_W2Hg`: the level lift at `W := W2Hg own …`, `X := X2H L siteL …` (any `endPc`, X's placement and sizes),
  at any source facts `MidG S`, from `StartWf.WSHg own`.

No absolute address appears in this file.

**Unlike AArch64**: the lift is stated at any source facts `S` (AArch64: at `SBH`), since x86-64's
`Ti2Hat.hti_H` / `Ti2HatO.hti_HOX` ask it at `QBH`; the phases are x86-64's (`X64.WriteAb.Ab`,
`X64.Hello.ThreadsAb.AcH … StartWf.pfxM`); the level is generic in the owned words (`W2Hg`), so that `ownGHXW`
shares it.
-/
import Spike.Lib.X64HelloH2Inv
import Spike.Lib.X64HelloStartWf
import Spike.Lib.X64HelloTi2HatG
import Spike.Lib.X64HelloW2Weak
import Spike.Lib.X64HelloHMid

namespace Spike.Lib.X64.HelloPh.RootWX

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib (Arena FragS Ctl)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64.WakeWf (Wf)
open Spike.Lib.X64.Flow.WakeWc (MidG)
open Spike.Lib.X64.Flow.Ret0.StackTake (siteL)
open Spike.Lib.X64.HelloPh.Ti2 (X0TH)
open Spike.Lib.X64HelloH2Inv (X2H)

/-- **The third level at any owned words `own`**: `Wf` at `own`, the write abort's and the `clone`'s phases, the
context `Ctx`, the placement `lbl` and sizes `lsize`, at no frames. -/
def W2Hg (own : Spike.Lib.X64Consumer.Own) (L : RuntimeLayout) (ar : Arena) (p : Prog) (Dt Cl : State → Prop)
    (Ctx : FragS isa) (lbl : Lbl) (lsize : Lsize) : FragS isa := fun s c fs =>
  fs = [] ∧ Wf L.Λ (Spike.Lib.X64.PhRec.μ L) own ar p Dt
    (Spike.Lib.X64.WriteAb.Ab L.lab) Cl (Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab Spike.Lib.X64.HelloPh.StartWf.pfxM)
    Ctx lbl lsize s c fs

/-- **The third level** (candidate for the root's `W2`): `W2Hg` at the start's own (`ownGH L a`). -/
abbrev W2H (L : RuntimeLayout) (a : BitVec 64) (ar : Arena) (p : Prog) (Dt Cl : State → Prop) (Ctx : FragS isa)
    (lbl : Lbl) (lsize : Lsize) : FragS isa :=
  W2Hg (Spike.Lib.X64.HelloPh.ownGH L a) L ar p Dt Cl Ctx lbl lsize

/-- **The level lift at `W2Hg` and `X2H` at any owned words `own`**: `WSHg own` at main's frame and `X0TH` at the
take site gives `W2Hg own` (`W0`'s `Wf` at no frames) and `X2H` at the take site (`X0TH` is off the clone's pc,
and its take clause is `X2H`'s). -/
theorem hWX_W2Hg {own : Spike.Lib.X64Consumer.Own} {L : RuntimeLayout} {ar : Arena} {p : Prog}
    {Dt Cw : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize} {frM : Ctl → TermRun.Frame}
    {S : WeakMem.AllocLabel → Nat → Ctl → Prop} (endPc : Int64) (lbl' : Lbl) (lsize' : Lsize) :
    ∀ c0 cA, MidG S c0 cA → ∀ s c,
      Spike.Lib.X64.HelloPh.StartWf.WSHg own L ar p Dt Cw Ctx lbl lsize (frM c0) (X0TH L (L.lab siteL)) s c →
      W2Hg own L ar p Dt Cw Ctx lbl lsize s c [] ∧ X2H L (L.lab siteL) endPc lbl' lsize' s c [] :=
  fun _ _ _ _ _ ⟨_, hX, hW⟩ => ⟨⟨rfl, hW⟩, fun h => absurd h hX.1, hX.2⟩

end Spike.Lib.X64.HelloPh.RootWX

/-- info: 'Spike.Lib.X64.HelloPh.RootWX.hWX_W2Hg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootWX.hWX_W2Hg
