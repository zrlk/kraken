/-
**hello.w's level-2 lift from the start's level** (x86-64; the twin of `Spike/Lib/A64HelloW2Weak.lean`): a state of
`WakeWf.Wf` at any context and sizes whose instruction writes neither the arena's counter nor a word of the arena's
cells is `Wf` at the empty context and any sizes at the same placement. After hello's box no state writes the counter
or allocates (the level's states are the reserve's, the second TCB's, `scc_rt_thread_init`'s take, the `clone` and
the refusal's threads abort, which write the TCBs, the stack lock and cursor, the stacks and `scc_rt_nthreads`, all
off the arena), so the start's level `WSH` at the twice extended placement lifts to the level-2 fragment
`X64HelloW2H.W2H` (empty context, sizes `updN (updN ls0 l n) l' n'`), wake's shape after its one allocation
(`WakeWf.W1`, empty context).

- `OffW ar s`: every word the instruction at `s` writes is off the counter and off the arena's cells.
- `wf_offW`: `Wf … Ctx lbl lsize` and `OffW` give `Wf … ∅ lbl lsize'` (the `ArenaWr` conjunct by `ArenaW`'s
  off-arena disjunct, the counter conjunct vacuous; the other conjuncts do not read the context or the sizes).
- `w2H_of_wshg`: `W0` at any owned words `own` (e.g. `ownGHXW`) gives `W2H` at `own`.
- `w2H_of_wsh`: `WSH` at `lbl2H L0 l b l' b'` and `OffW` give `W2H … l b n l' b' n'` at no frames
  (`StartWf.WSH`'s `W0` projected to its `Wf`).

Unlike AArch64, the level's write abort and threads abort are x86-64's (`X64.WriteAb.Ab`,
`X64.Hello.ThreadsAb.AcH` at main's prefix `.Lwc_main`), and `WSH` takes no separate refusal `Cw` beyond its `Cl`;
the proofs are otherwise the same. The lift is generic in the owned words (`w2H_of_wshg`; AArch64's is at `ownGH`
only), so the level at `ownGHXW` shares it.
-/
import Spike.Lib.X64HelloW2H
import Spike.Lib.X64HelloStartWf
import Spike.Lib.X64HelloClH

namespace Spike.Lib.X64.HelloW2

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks)
open Spike.Lib (Arena FragS)
open Spike.Lib.X64Consumer (Lbl Lsize Own)
open Spike.Lib.X64ConsumerA (WrAt)
open Spike.Lib.X64.WakeWf (Wf)

/-- **The instruction writes off the arena**: every word it writes is not the counter and not in the arena's
cells (`ArenaW`'s second disjunct). -/
def OffW (ar : Arena) (s : State) : Prop :=
  ∀ L, WrAt s L → L ≠ ar.ctrLoc ∧ ¬ (ar.heap ≤ L.addr.toNat ∧ L.addr.toNat < ar.heap + 16 * ar.cells)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {ar : Arena} {p : Prog} {Dt Ab Cl Ac : State → Prop}

/-- **`Wf` at the empty context**, from `Wf` at any context and sizes, at a state writing off the arena: the arena's
writes are off its cells (`ArenaW`'s second disjunct, at any sizes), the counter is not written. -/
theorem wf_offW {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize} (lsize' : Lsize) {s : State} {c : Spike.Lib.Ctl}
    {fs : List TermRun.Frame} (h : Wf Λ μ own ar p Dt Ab Cl Ac Ctx lbl lsize s c fs) (hoff : OffW ar s) :
    Wf Λ μ own ar p Dt Ab Cl Ac (fun _ _ _ => False) lbl lsize' s c fs := by
  obtain ⟨hst, hab, hac, hcl, hnr, hpl, -, -, hr, habt⟩ := h
  exact ⟨hst, hab, hac, hcl, hnr, hpl, fun _ _ _ L hL _ => .inl (.inr (.inl (hoff L hL).2)),
    fun hw => ((hoff _ hw).1 rfl).elim, hr, habt⟩

/-- **The start's level at any owned words lifts to the level-2 fragment**: `W0` at `own` at the twice
extended placement `lbl2H L0 l b l' b'` gives `W2H` at `own` at no frames. -/
theorem w2H_of_wshg {L : Spike.Lib.X64.Rt.RuntimeLayout} {Cw : State → Prop}
    {Ctx Ctx' : FragS isa} {L0 : Lbl} {lsize ls0 : Lsize} {frM : TermRun.Frame} {X0 : State → Prop}
    {l : WeakMem.AllocLabel} {b n : Nat} {l' : WeakMem.AllocLabel} {b' n' : Nat} {s : State} {c : Spike.Lib.Ctl}
    (h : Spike.Lib.X64.WakeWf.W0 L.Λ (Spike.Lib.X64.PhRec.μ L) own ar p Dt (Spike.Lib.X64.WriteAb.Ab L.lab) Cw
      (Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab Spike.Lib.X64.HelloPh.StartWf.pfxM) Ctx
      (Spike.Lib.X64.HelloPh.lbl2H L0 l b l' b') lsize frM X0 s c [])
    (hoff : OffW ar s) :
    W2H L.Λ (Spike.Lib.X64.PhRec.μ L) own ar p Dt (Spike.Lib.X64.WriteAb.Ab L.lab) Cw
      (Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab Spike.Lib.X64.HelloPh.StartWf.pfxM) Ctx' L0 ls0 l b n l' b' n' s c [] :=
  wf_offW _ h.2.2 hoff

/-- **The start's level lifts to the level-2 fragment** at a state writing off the arena: `WSH` at the twice
extended placement `lbl2H L0 l b l' b'` (any context `Ctx`, sizes `lsize`, main frame `frM`, per-state facts
`X0`) gives `W2H` at no frames, at the sizes `updN (updN ls0 l n) l' n'`. -/
theorem w2H_of_wsh {L : Spike.Lib.X64.Rt.RuntimeLayout} {a : BitVec 64} {Cw : State → Prop}
    {Ctx Ctx' : FragS isa} {L0 : Lbl} {lsize ls0 : Lsize} {frM : TermRun.Frame} {X0 : State → Prop}
    {l : WeakMem.AllocLabel} {b n : Nat} {l' : WeakMem.AllocLabel} {b' n' : Nat} {s : State} {c : Spike.Lib.Ctl}
    (h : Spike.Lib.X64.HelloPh.StartWf.WSH L a ar p Dt Cw Ctx (Spike.Lib.X64.HelloPh.lbl2H L0 l b l' b') lsize frM
      X0 s c)
    (hoff : OffW ar s) :
    W2H L.Λ (Spike.Lib.X64.PhRec.μ L) (Spike.Lib.X64.HelloPh.ownGH L a) ar p Dt (Spike.Lib.X64.WriteAb.Ab L.lab) Cw
      (Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab Spike.Lib.X64.HelloPh.StartWf.pfxM) Ctx' L0 ls0 l b n l' b' n' s c [] :=
  w2H_of_wshg h hoff

/-- Inhabitation: a state writing nothing (`WrAt` false at every word) writes off every arena. -/
example (ar : Arena) (s : State) (h : ∀ L, ¬ WrAt s L) : OffW ar s := fun L hL => (h L hL).elim

end Spike.Lib.X64.HelloW2

/-- info: 'Spike.Lib.X64.HelloW2.wf_offW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloW2.wf_offW

/-- info: 'Spike.Lib.X64.HelloW2.w2H_of_wshg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloW2.w2H_of_wshg

/-- info: 'Spike.Lib.X64.HelloW2.w2H_of_wsh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloW2.w2H_of_wsh
