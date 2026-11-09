/-
**hello's level after `wc_rodata`'s allocation** (x86-64; the twin of `Spike/Lib/A64HelloW1H.lean`, itself the
twin of `WakeOPremW.W1W`): the start's level `HelloWf.WSHFg own` (`WakeWf.W0` at `own`, `WriteAb.Ab`,
`ThreadsAb.AcH … pfxM`) at the labels after the allocation of `l` at `b`, `n` cells (`upd L0 l b`, `updN ls0 l n`).

It differs from wake's `W1W` (`WakeWf.W1`, the context empty, no frame clause):
- the counter context is a family `Ctx1 l b n`: hello's box allocation (its counter add and the box's
  initialising store) runs inside this level, its rows stated at the level's labels (the level-1 `CtxR1H`);
- the frames are `[]` or `[frM]` (`W0`'s clause): the level starts at `wc_rodata`'s landing under `rodata`'s frame
  and pops it at `wc_rodata`'s `ret` (at the root `frM := HelloRdCf.frH c0S.env`);
- the per-state facts `X1` (at the root `StartGlue.X0WH … (lab take_site)`, as at level 0: the clone comes at
  level 2).

At h1 (`HelloO.OPremH.h1`) the outside move is `TakeCKS a Cl`, as at h0/h2.

- `W1Hg`: the level at any owned words `own` (`WSHFg own`).
- `w1Hg_def`: its unfolding to `W0` (by definition).

Unlike AArch64 (`isaLSE2`, the threads abort's phase `HelloWf.AcH` at `Child.pfxM`), the level is over x86-64's `isa`
and the threads abort's phase is `Hello.ThreadsAb.AcH` at `StartWf.pfxM` (`X64HelloAllocWSF.WSHFg`'s). The level is
generic in the owned words (`W1Hg`, over `WSHFg`; AArch64's `W1H` and `w1H_def` are at `ownGH` only); the root's is
at `ownGHXW`, which carries main's and the worker's TCB words.
-/
import Spike.Lib.X64HelloAllocWSF

namespace Spike.Lib.X64.HelloWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64.WakeWf (W0)
open Spike.Lib (Arena FragS)

/-- **hello's level after `wc_rodata`'s allocation** of `l` at `b`, `n` cells, at the owned words `own`:
`WSHFg own` at `upd L0 l b` / `updN ls0 l n`, the counter context `Ctx1 l b n`, the frames `[]` or `[frM]`, the
per-state facts `X1`. -/
def W1Hg (own : Spike.Lib.X64Consumer.Own) (L : RuntimeLayout) (ar : Arena) (p : Prog) (Dt Cl : State → Prop)
    (Ctx1 : WeakMem.AllocLabel → Nat → Nat → FragS isa) (L0 : Lbl) (ls0 : Lsize) (frM : TermRun.Frame)
    (X1 : State → Prop) : WeakMem.AllocLabel → Nat → Nat → FragS isa :=
  fun l b n s c fs => WSHFg own L ar p Dt Cl (Ctx1 l b n) (Spike.Lib.X64ConsumerA.upd L0 l b)
    (Spike.Lib.X64ConsumerA.updN ls0 l n) frM X1 fs s c

/-- **`W1Hg own` is `W0` at `own` and the level's labels** (by definition). -/
theorem w1Hg_def {own : Spike.Lib.X64Consumer.Own} {L : RuntimeLayout} {ar : Arena} {p : Prog}
    {Dt Cl : State → Prop} {Ctx1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {L0 : Lbl} {ls0 : Lsize}
    {frM : TermRun.Frame} {X1 : State → Prop} (l : WeakMem.AllocLabel) (b n : Nat) (s : State) (c : Ctl)
    (fs : List TermRun.Frame) :
    W1Hg own L ar p Dt Cl Ctx1 L0 ls0 frM X1 l b n s c fs ↔
      W0 L.Λ (Spike.Lib.X64.PhRec.μ L) own ar p Dt (Spike.Lib.X64.WriteAb.Ab L.lab)
        Cl (Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab Spike.Lib.X64.HelloPh.StartWf.pfxM) (Ctx1 l b n)
        (Spike.Lib.X64ConsumerA.upd L0 l b) (Spike.Lib.X64ConsumerA.updN ls0 l n) frM X1 s c fs :=
  Iff.rfl

end Spike.Lib.X64.HelloWf

/-- info: 'Spike.Lib.X64.HelloWf.w1Hg_def' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloWf.w1Hg_def
