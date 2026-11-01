/-
**hello.w's level-2 fragment** (AArch64; the level-2 twin of `WakeWf.W1` /
`hW1F`): the fragment `W2` of `HelloO.ODataH` after the box's allocation, and `OPremH.hW2` at it.

After the box (`l'` at `b'`, `n'` cells, at the level-1 placement `upd L0 l b`) no state writes the counter word:
the level's states are the reserve's, the second TCB's, `scc_rt_thread_init`'s take, the `clone` and the refusal's
threads abort, none an arena allocation (`wc_main` allocates twice, both before). So the level is `Wf` at the twice
extended placement with the empty context, which is `WakeWf.W1` at the level-1 placement and sizes, and its
per-state facts need no counter row or store premise (`WakeWf.hW1F`).

- `W2H`: the level (`WakeWf.W1` at `upd L0 l b`, `updN ls0 l n`, the box `l' b' n'`).
- `w2H_def`: it is `Wf` at the twice extended placement and sizes, the empty context.
- `hW2H`: `OPremH.hW2`'s `SFactsACH` at every state of `W2H`, with no premise.
-/
import Spike.Lib.A64WakeWf

namespace Spike.Lib.A64.HelloW2

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks)
open Spike.Lib (Arena FragS)
open Spike.Lib.A64Consumer (Lbl Lsize Own)
open Spike.Lib.A64ConsumerS (InvS)
open Spike.Lib.A64ConsumerA (SFactsACH)

variable (Λ : Scc.Sem.Layout) (μ : Marks) (own : Own) (ar : Arena) (p : Prog) (Dt Ab Cl Ac : State → Prop)
  (Ctx : FragS isaLSE2) (L0 : Lbl) (ls0 : Lsize)

/-- **The level after the box** (`HelloO.ODataH.W2`): `WakeWf.W1` at the level-1 placement `upd L0 l b` and sizes
`updN ls0 l n`, at the box `l'` placed at `b'` with `n'` cells (writing no counter). -/
def W2H (l : WeakMem.AllocLabel) (b n : Nat) (l' : WeakMem.AllocLabel) (b' n' : Nat) : FragS isaLSE2 :=
  Spike.Lib.A64.WakeWf.W1 Λ μ own ar p Dt Ab Cl Ac Ctx (Spike.Lib.A64ConsumerA.upd L0 l b)
    (Spike.Lib.A64ConsumerA.updN ls0 l n) l' b' n'

/-- **`W2H` is `Wf` at the twice extended placement**, the empty context. -/
theorem w2H_def (l : WeakMem.AllocLabel) (b n : Nat) (l' : WeakMem.AllocLabel) (b' n' : Nat) :
    W2H Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 l b n l' b' n' =
      Spike.Lib.A64.WakeWf.Wf Λ μ own ar p Dt Ab Cl Ac (fun _ _ _ => False)
        (Spike.Lib.A64ConsumerA.upd (Spike.Lib.A64ConsumerA.upd L0 l b) l' b')
        (Spike.Lib.A64ConsumerA.updN (Spike.Lib.A64ConsumerA.updN ls0 l n) l' n') :=
  rfl

/-- **`OPremH.hW2` at `W2H`**, with no premise (`WakeWf.hW1F` at the level-1 placement): `SFactsACH` at every state
of `W2H … l b n l' b' n'` at the twice extended placement and sizes, for any `rd`, `G`, fragment `J`. -/
theorem hW2H {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {J : InvS} :
    ∀ l b n l' b' n' s c fs, W2H Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 l b n l' b' n' s c fs →
      SFactsACH Λ μ p rd G (fun s _ => own s) ar J
        (Spike.Lib.A64ConsumerA.upd (Spike.Lib.A64ConsumerA.upd L0 l b) l' b')
        (Spike.Lib.A64ConsumerA.updN (Spike.Lib.A64ConsumerA.updN ls0 l n) l' n') s c fs Dt Ab Cl Ac :=
  fun l b n l' b' n' s c fs h =>
    Spike.Lib.A64.WakeWf.hW1F (L0 := Spike.Lib.A64ConsumerA.upd L0 l b) (ls0 := Spike.Lib.A64ConsumerA.updN ls0 l n)
      l' b' n' s c fs h

end Spike.Lib.A64.HelloW2

/-- info: 'Spike.Lib.A64.HelloW2.w2H_def' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloW2.w2H_def

/-- info: 'Spike.Lib.A64.HelloW2.hW2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloW2.hW2H
