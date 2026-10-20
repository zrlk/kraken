/-
Open statements of (the no-fault theorem, the O11 hook), stated
as `Prop`s so that nothing here is axiomatised and the file builds without
`sorry`. Nothing imports this file.

## The no-fault theorem

`NoFaultTheorem A fuel`: under Theorem 1′'s hypotheses with the per-thread
`NPSafe` given by rules (`NoFaultHyps`), if every thread's rule excludes
faults (`NoFaultRule`, `SLR/Sim/NoFault.lean`), no reachable configuration
has a faulting step (`Config.FaultFree`, `Promising/Faults.lean`).

**Status: reduced, not proved.** `noFaultTheorem_of_erasedWitness` proves it
from one lemma, `ErasedWitness`: at every reachable configuration, for every
thread, the hypotheses of the rule's `wp` (an instance `Inv`, an
environment extension, an erasure, the machine invariants, the own-pending
transport) hold at *some* configuration with that thread's real state and the
real memory. `NoFaultRule.not_faultStep` then excludes the fault, because a
step depends only on the thread and the memory.

`ErasedWitness` is where the work is, and where B2 is consumed:

- Theorem 1′'s invariant (`Theorem1Proof.Inv`, along a `Path` to a *final*
  configuration) does not supply it. It exists only for live configurations,
  and in its virtual configuration the threads with outstanding non-pending
  promises are *advanced* along their path future (`Config.VirtualOf`): the
  real state of such a thread sits in no erased configuration.
- The carrier must therefore be an invariant over `Reachable` itself: for
  each thread `tid`, an erased configuration at the real memory with `tid`
  *not* advanced and every other thread with non-pending promises advanced
  along a certification run rather than its path future. The other threads'
  real steps append messages between the replayed steps of those runs; B2
  (`Sim.certOk_extAppend`, `Sim.SchedSF`) is exactly what keeps an advanced
  thread's certification run valid across them, so its virtual run stays a
  successful (`ThreadNP`, `.ok`-only) run: the faulting successors `succsL`
  drops are never needed to build the witness.
- The missing pieces are (i) the `StaleFree` side condition of B2 for those
  certification runs, which is not derivable (counterexample in
  `Sim/CertExt.lean`) and so must come from the program or be avoided by
  choosing which threads to advance, and (ii) the erasure of the configuration
  so advanced, i.e. Theorem 1′'s `cond3` / case (d1) machinery redone for a
  run that is a certification run rather than the path's future.

## The O11 hook

`Config.VirtualOfNTs`: the multi-thread virtual configuration with pending
non-temporal stores, stated with one
simulation map per thread: each thread's virtual state is the target of a
`Sim.SimState` whose source is a solo run of the thread from the real
memory, the virtual memory holding every thread's replayed messages (each
foreign for the others). `O11Embed`: the existing single-appender
`Config.VirtualOfNT` is an instance (statement only).
-/
import Kraken.Promising.SLR.Sim.NoFault
import Kraken.Promising.SLR.Sim.CertExt
import Kraken.Promising.SLR.Theorem1Final
import Kraken.Promising.SLR.Adequacy

namespace Kraken.Promising.SLR

variable {I : ISA}

/-! ## The no-fault theorem -/

/-- The hypotheses of the no-fault theorem: Theorem 1′'s (`Theorem1IIPure`),
with the per-thread `NPSafe` given by rules `R` whose invariants hold at the
initial configuration. -/
structure NoFaultHyps (A : Arch) (fuel : Nat) [I.LawfulState] (B : Config I → Res → Ghost → Prop)
    (states : List I.State) (initMem : List (Loc × Val)) (rF : Nat → Res) (g : Ghost)
    (R : (tid : Nat) → ThreadRuleRX A B tid) : Prop where
  ntFree : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A
  erase : Erase rF g (fun _ => False) (Config.init states initMem)
  noPend : ∀ ts, ts ∉ g.pend
  pure : PromisePure A fuel states initMem g.rel
  inv : ∀ tid, tid < states.length → (R tid).Inv True (Config.init states initMem) (rF tid) g

/-- **The no-fault theorem** (statement): rules that exclude faults give a
fault-free program. -/
def NoFaultTheorem (A : Arch) (fuel : Nat) [I.LawfulState] : Prop :=
  ∀ (B : Config I → Res → Ghost → Prop) (states : List I.State) (initMem : List (Loc × Val)) (rF : Nat → Res)
    (g : Ghost) (R : (tid : Nat) → ThreadRuleRX A B tid),
    NoFaultHyps A fuel B states initMem rF g R → (∀ tid, tid < states.length → NoFaultRule (R tid)) →
    Config.FaultFree A fuel (Config.init states initMem)

/-- **The open lemma** (statement): at every reachable configuration, for
every thread, the hypotheses of the rule's `wp` hold at a configuration with
the thread's real state and the real memory. -/
def ErasedWitness (A : Arch) (fuel : Nat) [I.LawfulState] : Prop :=
  ∀ (B : Config I → Res → Ghost → Prop) (states : List I.State) (initMem : List (Loc × Val)) (rF : Nat → Res)
    (g : Ghost) (R : (tid : Nat) → ThreadRuleRX A B tid),
    NoFaultHyps A fuel B states initMem rF g R →
    ∀ c, Reachable A fuel (Config.init states initMem) c → ∀ tid t, c.threads[tid]? = some t →
      ∃ (cl : Prop) (c₀ c₁ : Config I) (r : Res) (g₀ g₁ : Ghost) (rF₁ : Nat → Res),
        (R tid).Inv cl c₀ r g₀ ∧ EnvExt tid c₀ c₁ ∧ g₀.Le g₁ ∧ c₁.threads[tid]? = some t ∧ c₁.mem = c.mem ∧
        Erase (setRes rF₁ tid r) g₁ (fun _ => True) c₁ ∧ c₁.MachInv ∧ c₁.WfProm tid ∧
        (∀ ts ∈ t.prom, ts ∈ g₁.pend → ts ∈ g₀.pend)

/-- **The no-fault theorem from the open lemma** (proved). -/
theorem noFaultTheorem_of_erasedWitness [I.LawfulState] {A : Arch} {fuel : Nat} (h : ErasedWitness (I := I) A fuel) :
    NoFaultTheorem (I := I) A fuel := by
  intro B states initMem rF g R H hR c hc tid m hf
  have hlt : tid < states.length := by
    have := hf.lt_size
    rwa [Reachable.size_eq hc, Config.init_size] at this
  obtain ⟨outs, hs, ho⟩ := hf
  obtain ⟨t, ht, hs1⟩ := stepThread_eq_some hs
  obtain ⟨cl, c₀, c₁, r, g₀, g₁, rF₁, hI, he, hg, ht₁, hm, E, hinv, hwf, hnp⟩ := h B states initMem rF g R H c hc tid t ht
  refine (hR tid hlt).not_faultStep rF₁ hI he hg ht₁ E hinv hwf hnp m ⟨outs, ?_, ho⟩
  simp only [stepThread, ht₁, hm, Option.bind_eq_bind, Option.bind_some]
  exact hs1

/-! ## The O11 hook -/

/-- **Multi-thread virtual configuration with pending non-temporal stores**
(statement of the O11 design, one simulation map per thread). `v.mem`
extends `c.mem`; each thread `i` of `c` is either unchanged or advanced to a
pending release: its virtual state `t'` is the target of a `Sim.SimState`
(map `ρ`, thresholds `N`, every location watched) whose source is a solo run
of `i` from `(t, c.mem)`, against the virtual memory `v.mem`, with the base
`[0, |c.mem|]` mapped identically. The messages of `v.mem` that are not
images of the source run (the other threads' replayed messages) are the
foreign ones of `i`'s map. -/
def _root_.Kraken.Promising.Config.VirtualOfNTs (A : Arch) (c v : Config I) : Prop :=
  c.mem.Prefix v.mem ∧ v.threads.size = c.threads.size ∧
    ∀ i t, c.threads[i]? = some t → ∃ (t' : Thread I) (p : Thread I × Memory) (ρ : Sim.TMap) (N : Nat → Prop),
      v.threads[i]? = some t' ∧ ThreadNP A i (t, c.mem) p ∧ Sim.SimState ρ N (fun _ => True) p (t', v.mem) ∧
      (∀ s ≤ c.mem.last, ρ.dom s ∧ ρ.f s = s) ∧
      ((t' = t ∧ p = (t, c.mem)) ∨ ∃ ts ∈ t'.prom, t'.RelFulfils A i ts v.mem)

/-- **O11 hook** (statement): the single-appender `Config.VirtualOfNT` of
bounded threads is an instance of `Config.VirtualOfNTs`. -/
def O11Embed (A : Arch) : Prop :=
  ∀ (c v : Config I), c.VirtualOfNT A v → (∀ (i : Nat) (t : Thread I), c.threads[i]? = some t → t.Bnd c.mem.last) →
    (∀ (i : Nat) (t : Thread I), c.threads[i]? = some t → ∀ s ∈ t.prom, s ≤ c.mem.last) → c.VirtualOfNTs A v

end Kraken.Promising.SLR
