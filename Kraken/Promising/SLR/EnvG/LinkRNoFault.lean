/-
Whole-thread environment (`EnvG`), shared helpers:
**the no-fault rules of the release-RMW rule links from fault-free trees**.
ISA-neutral (no `Syntax` import), so both the AArch64 and the x64 links use
the same lemmas.

- `InvGR.q_at`, `noFaultRule_ofEnvGR_struct` (`ThreadRuleRX.ofEnvGR`),
  moved verbatim from `A64LinkR.lean`;
- `noFaultRule_ofEnvGRC_struct` (`ThreadRuleRX.ofEnvGRC`, the
  claim-conditional environment `EnvGC`), moved verbatim from
  `RmwGhostA64.lean`.

The x64 copies `InvGR.q_atX`, `noFaultRule_ofEnvGR_structX`
(`X64Link.lean`) and `noFaultRule_ofEnvGRC_structX`
(`X64RmwGhostLink.lean`) are statement-preserving aliases of these.
-/
import Kraken.Promising.SLR.EnvG.RmwGhostRule
import Kraken.Promising.SLR.EnvG.RuleNoFault

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-! ## The no-fault rule with release-kind RMWs (ISA-neutral) -/

section Rule

variable {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}

/-- At the rule's invariant with release-kind RMWs, transported to the
current configuration, the thread's state is a `Q`-state (`InvG.q_at`). -/
theorem InvGR.q_at {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t : Thread I)
    (h : InvGR tid pl Q cl c₀ r g₀) (he : EnvExt tid c₀ c) (hg : g₀.Le g) (ht : c.threads[tid]? = some t)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hnp : ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) :
    ∃ σ, Q t.st σ := by
  obtain ⟨σ, t₀, hC₀, hQ₀⟩ := h
  obtain ⟨hst, -⟩ := hC₀.transport he hg ht hnp E
  exact ⟨σ, hst ▸ hQ₀⟩

/-- **The no-fault rule with release-kind RMWs from fault-free trees**
(`noFaultRule_ofEnvG_struct`). -/
theorem noFaultRule_ofEnvGR_struct {B : Config I → (model I).R → (model I).Ghost → Prop}
    (H : LinkHypsR A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    (HS : ∀ st σ tree, Q st σ → I.exec st = some tree → tree.NoFault) :
    NoFaultRule (ThreadRuleRX.ofEnvGR H hB) :=
  NoFaultRule.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp => by
    obtain ⟨σ, hQ⟩ := InvGR.q_at rF t h he hg ht E hnp
    exact HS t.st σ tree hQ hex

end Rule

/-! ## The no-fault rule of `EnvGC` (ISA-neutral) -/

/-- **The no-fault rule of `EnvGC` from fault-free trees**
(`noFaultRule_ofEnvGR_struct`). -/
theorem noFaultRule_ofEnvGRC_struct {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop}
    (H : LinkHypsRC A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    (HS : ∀ st σ tree, Q st σ → I.exec st = some tree → tree.NoFault) :
    NoFaultRule (ThreadRuleRX.ofEnvGRC H hB) :=
  NoFaultRule.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp => by
    obtain ⟨σ, hQ⟩ := InvGR.q_at rF t h he hg ht E hnp
    exact HS t.st σ tree hQ hex

end Kraken.Promising.SLR.EnvG
