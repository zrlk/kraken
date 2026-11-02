/-
**hello.w's level-2 fragment** (x86-64; the twin of `Spike/Lib/A64HelloW2H.lean`, the level-2 twin of `WakeWf.W1` /
`hW1F`): the fragment `W2` of `X64HelloO.ODataH` after the box's allocation, and `OPremH.hW2` at it.

After the box (`l'` at `b'`, `n'` cells, at the level-1 placement `upd L0 l b`) no state writes the counter word:
the level's states are the reserve's, the second TCB's, `scc_rt_thread_init`'s take, the `clone` and the refusal's
threads abort, none an arena allocation (`wc_main` allocates twice, both before). So the level is `Wf` at the twice
extended placement with the empty context, which is `WakeWf.W1` at the level-1 placement and sizes, and its
per-state facts need no counter row or store premise (`WakeWf.hW1F`).

- `W2H`: the level (`WakeWf.W1` at `upd L0 l b`, `updN ls0 l n`, the box `l' b' n'`).
- `w2H_def`: it is `Wf` at the twice extended placement and sizes, the empty context.
- `hW2H`: `OPremH.hW2`'s `SFactsACH` at every state of `W2H`, with no premise.

## Differences from the AArch64 version

None beyond the ISA: the same names, in namespaces with the `X64` prefix, over x86-64's `WakeWf.W1`.
-/
import Spike.Lib.X64WakeWf

namespace Spike.Lib.X64.HelloW2

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks)
open Spike.Lib (Arena FragS)
open Spike.Lib.X64Consumer (Lbl Lsize Own)
open Spike.Lib.X64ConsumerS (InvS)
open Spike.Lib.X64ConsumerA (SFactsACH)

variable (Λ : Scc.Sem.Layout) (μ : Marks) (own : Own) (ar : Arena) (p : Prog) (Dt Ab Cl Ac : State → Prop)
  (Ctx : FragS isa) (L0 : Lbl) (ls0 : Lsize)

/-- **The level after the box** (`X64HelloO.ODataH.W2`): `WakeWf.W1` at the level-1 placement `upd L0 l b` and sizes
`updN ls0 l n`, at the box `l'` placed at `b'` with `n'` cells (writing no counter). -/
def W2H (l : WeakMem.AllocLabel) (b n : Nat) (l' : WeakMem.AllocLabel) (b' n' : Nat) : FragS isa :=
  Spike.Lib.X64.WakeWf.W1 Λ μ own ar p Dt Ab Cl Ac Ctx (Spike.Lib.X64ConsumerA.upd L0 l b)
    (Spike.Lib.X64ConsumerA.updN ls0 l n) l' b' n'

/-- **`W2H` is `Wf` at the twice extended placement**, the empty context. -/
theorem w2H_def (l : WeakMem.AllocLabel) (b n : Nat) (l' : WeakMem.AllocLabel) (b' n' : Nat) :
    W2H Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 l b n l' b' n' =
      Spike.Lib.X64.WakeWf.Wf Λ μ own ar p Dt Ab Cl Ac (fun _ _ _ => False)
        (Spike.Lib.X64ConsumerA.upd (Spike.Lib.X64ConsumerA.upd L0 l b) l' b')
        (Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64ConsumerA.updN ls0 l n) l' n') :=
  rfl

/-- **`OPremH.hW2` at `W2H`**, with no premise (`WakeWf.hW1F` at the level-1 placement): `SFactsACH` at every state
of `W2H … l b n l' b' n'` at the twice extended placement and sizes, for any `rd`, `G`, fragment `J`. -/
theorem hW2H {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {J : InvS} :
    ∀ l b n l' b' n' s c fs, W2H Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 l b n l' b' n' s c fs →
      SFactsACH Λ μ p rd G (fun s _ => own s) ar J
        (Spike.Lib.X64ConsumerA.upd (Spike.Lib.X64ConsumerA.upd L0 l b) l' b')
        (Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64ConsumerA.updN ls0 l n) l' n') s c fs Dt Ab Cl Ac :=
  fun l b n l' b' n' s c fs h =>
    Spike.Lib.X64.WakeWf.hW1F (L0 := Spike.Lib.X64ConsumerA.upd L0 l b) (ls0 := Spike.Lib.X64ConsumerA.updN ls0 l n)
      l' b' n' s c fs h

end Spike.Lib.X64.HelloW2

/-- info: 'Spike.Lib.X64.HelloW2.w2H_def' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloW2.w2H_def

/-- info: 'Spike.Lib.X64.HelloW2.hW2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloW2.hW2H
