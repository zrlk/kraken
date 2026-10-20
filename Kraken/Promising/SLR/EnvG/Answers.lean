/-
Whole-thread environment (`EnvG`): **the no-fault rule without
`EnvGAnswersAt`**. ISA-neutral; the AArch64 instance is
`EnvG/A64Answers.lean`.

`noFaultRule_ofEnvG` (`EnvG/RuleNoFault.lean`) derives `NoFaultRule` from
the env judgment (`LinkNF`) and the missing fact `EnvGAnswersAt`: the
judgment speaks about a store's continuation only through an env outcome, so
every actual write outcome needs an env answer. With an own pending promise
`ts` at `l` and a store of a different value to `l`, every actual write
outcome overtakes `ts` and `EnvG` has none (`StoreOut` asks `¬ Overtaken`,
and `SnapLe` keeps `ts` in every re-anchor's promise list), so
`EnvGAnswersAt` is not a general fact.

It is also not needed. `NoFaultRule` asks for no faulting run of the
thread's tree, and a run faults only at a `.fault` leaf
(`EvTree.NoFault.run`): faults are a property of the tree, not of the memory.
The AArch64 link already requires fault-free trees (`DirsNoFault`, behind
`TreeJLiveNF.onNoFault`), so the tree at every invariant state is
structurally fault-free and `NoFaultRule.ofNoFault` applies directly:

- `noFaultRule_ofEnvG_struct`: `NoFaultRule (ThreadRuleRX.ofEnvG H hB)` from
  fault-free trees at every `Q`-state (no `LinkNF`, no `EnvGAnswersAt`).
-/
import Kraken.Promising.SLR.EnvG.RuleNoFault

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

section Rule

variable {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}

/-- At the rule's invariant, transported to the current configuration
(`CoreAt.transport`, as in `InvG.noFault`), the thread's state is a `Q`-state. -/
theorem InvG.q_at {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t : Thread I)
    (h : InvG A tid pl Q cl c₀ r g₀) (he : EnvExt tid c₀ c) (hg : g₀.Le g) (ht : c.threads[tid]? = some t)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hnp : ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) :
    ∃ σ, Q t.st σ := by
  obtain ⟨σ, t₀, hC₀, hQ₀⟩ := h
  obtain ⟨hst, -⟩ := hC₀.transport he hg ht hnp E
  exact ⟨σ, hst ▸ hQ₀⟩

/-- **The no-fault rule from fault-free trees**: if every tree the thread can
run from a `Q`-state is fault-free (`EvTree.NoFault`), the rule of the link
is a no-fault rule. Unconditional in the thread's promises: no `LinkNF`, no
`EnvGAnswersAt` (compare `noFaultRule_ofEnvG`). -/
theorem noFaultRule_ofEnvG_struct {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHyps A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    (HS : ∀ st σ tree, Q st σ → I.exec st = some tree → tree.NoFault) :
    NoFaultRule (ThreadRuleRX.ofEnvG H hB) :=
  NoFaultRule.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp => by
    obtain ⟨σ, hQ⟩ := InvG.q_at rF t h he hg ht E hnp
    exact HS t.st σ tree hQ hex

end Rule

end Kraken.Promising.SLR.EnvG

#print axioms Kraken.Promising.SLR.EnvG.noFaultRule_ofEnvG_struct
