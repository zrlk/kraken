/-
**hello's level after `wc_rodata`'s allocation** (AArch64; the twin of
`WakeOPremW.W1W`): the start's level `HelloWf.WSHF` (`WakeWf.W0` at `ownGH`, `WriteAb.Ab`, `HelloWf.AcH … pfxM`)
at the labels after the allocation of `l` at `b`, `n` cells (`upd L0 l b`, `updN ls0 l n`).

It differs from wake's `W1W` (`WakeWf.W1`, the context empty, no frame clause):
- the counter context is a family `Ctx1 l b n`: hello's box allocation (its counter add and the box's
  initialising store) runs inside this level, its rows stated at the level's labels (level-1 `CtxR1H`);
- the frames are `[]` or `[frM]` (`W0`'s clause): the level starts at `wc_rodata`'s landing under `rodata`'s frame
  and pops it at `wc_rodata`'s `ret` (at the root `frM := HelloRdCf.frH c0S.env`);
- the per-state facts `X1` (at the root `StartGlue.X0WH … (lab take_site)`, as at level 0: the clone comes at
  level 2).

At h1 (`HelloO.OPremH.h1`) the outside move is `TakeCKS a Cl`, as at h0/h2.

- `W1H`: the level.
- `w1H_def`: its unfolding to `W0` (by definition).
-/
import Spike.Lib.A64HelloAllocWSF

namespace Spike.Lib.A64.HelloWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.WakeWf (W0)
open Spike.Lib (Arena FragS)

/-- **hello's level after `wc_rodata`'s allocation** of `l` at `b`, `n` cells: `WSHF` at `upd L0 l b` /
`updN ls0 l n`, the counter context `Ctx1 l b n`, the frames `[]` or `[frM]`, the per-state facts `X1`. -/
def W1H (L : RuntimeLayout) (a : BitVec 64) (ar : Arena) (p : Prog) (Dt Cl : State → Prop)
    (Ctx1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) (L0 : Lbl) (ls0 : Lsize) (frM : TermRun.Frame)
    (X1 : State → Prop) : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2 :=
  fun l b n s c fs => WSHF L a ar p Dt Cl (Ctx1 l b n) (Spike.Lib.A64ConsumerA.upd L0 l b)
    (Spike.Lib.A64ConsumerA.updN ls0 l n) frM X1 fs s c

/-- **`W1H` is `W0` at the level's labels** (by definition). -/
theorem w1H_def {L : RuntimeLayout} {a : BitVec 64} {ar : Arena} {p : Prog} {Dt Cl : State → Prop}
    {Ctx1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {L0 : Lbl} {ls0 : Lsize} {frM : TermRun.Frame}
    {X1 : State → Prop} (l : WeakMem.AllocLabel) (b n : Nat) (s : State) (c : Ctl) (fs : List TermRun.Frame) :
    W1H L a ar p Dt Cl Ctx1 L0 ls0 frM X1 l b n s c fs ↔
      W0 L.Λ (Spike.Lib.A64.PhRec.μ L) (Spike.Lib.A64.HelloPh.ownGH L a) ar p Dt (Spike.Lib.A64.WriteAb.Ab L.lab)
        Cl (AcH L.lab Spike.Lib.A64.Flow.Worker.Hello.Child.pfxM) (Ctx1 l b n)
        (Spike.Lib.A64ConsumerA.upd L0 l b) (Spike.Lib.A64ConsumerA.updN ls0 l n) frM X1 s c fs :=
  Iff.rfl

end Spike.Lib.A64.HelloWf

/-- info: 'Spike.Lib.A64.HelloWf.w1H_def' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloWf.w1H_def
