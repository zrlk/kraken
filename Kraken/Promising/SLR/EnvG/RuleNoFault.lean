/-
Whole-thread environment (`EnvG`): **the no-fault rule from the
rule link** (`NoFaultRule (ThreadRuleRX.ofEnvG H hB)`). ISA-neutral; the
AArch64 instance is `EnvG/A64NoFault.lean`.

`NoFaultRule` asks, under the hypotheses of the rule's `wp`, that no run of
the thread's tree from the instruction's start context faults. From the
rule's invariant (`InvG`) the core transports to the current configuration
(`CoreAt.transport`), `EnvRel.toNodeRel` relates the env state to the start
context, and `treeJ_envG_noFaultRun` (`EnvG/NoFault.lean`) concludes
for the (phase-1, hence single-access) tree, given

- `LinkNF`: the no-fault twin of `LinkHyps.link`, for `TreeJLiveNF` (the
  live tree judgment **without** a `fault` law: the env treats a fault leaf
  as `False`);
- `EnvGAnswers` (the no-fault track's missing fact) at the thread: holds for a thread
  without outstanding promises (`envGAnswers_of_promFree`), so the
  promise-free form `noFault_ofEnvG_promFree` needs no further hypothesis.

- `EnvGAnswersAt`: `EnvGAnswers` at every configuration's thread `tid`
  (**the remaining missing fact** for threads with promises).
- `noFault_ofEnvG_promFree`: the `NoFaultRule.noFault` conclusion for a
  thread with no outstanding promise.
- `noFaultRule_ofEnvG`: `NoFaultRule` under `EnvGAnswersAt`.

`EnvGAnswersAt` is believed false for threads with a pure own
promise; `EnvG/Answers.lean` proves `NoFaultRule` from fault-free trees
alone (`noFaultRule_ofEnvG_struct`).
-/
import Kraken.Promising.SLR.EnvG.RuleLink
import Kraken.Promising.SLR.EnvG.NoFault

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- **The no-fault link hypothesis** for a thread-local invariant `Q`:
every no-fault live tree judgment of `EnvG` whose postcondition contains `Q`
holds of the thread's tree from a `Q`-related env state (`LinkHyps.link`
with `TreeJLiveNF`: no fault leaf is reachable through `EnvG`). -/
def LinkNF (A : Arch) (tid : Nat) (pl : Plan) (Q : I.State → State I → Prop) : Prop :=
  ∀ (J : TreeJLiveNF (EnvG I A tid pl) I.State) st σ tree, Q st σ → I.exec st = some tree →
    (∀ st' σ', Q st' σ' → J.Post st' σ') → J.W tree σ

/-- **The missing fact for threads with promises**: `EnvGAnswers` at
thread `tid` of every configuration. Believed **false** in general (a thread
with a pure own promise to `l` storing another value to `l`; see
`EnvGAnswers`), so theorems assuming it may be vacuous there; the `_struct`
forms (`EnvG/Answers.lean`) do without it. -/
def EnvGAnswersAt (A : Arch) (tid : Nat) (pl : Plan) : Prop :=
  ∀ (iv : InstrViews) (rF : Nat → Res) (c : Config I) (t : Thread I), c.threads[tid]? = some t →
    EnvGAnswers A tid pl iv rF c t

section Rule

variable {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}

/-- The no-fault conclusion at the rule's invariant, given `EnvGAnswers` at
the current thread. -/
theorem InvG.noFault (H : LinkHyps A tid pl Q) (HN : LinkNF A tid pl Q) {cl : Prop} {c₀ c : Config I} {r : Res}
    {g₀ g : Ghost} (rF : Nat → Res) (t : Thread I) (tree : EvTree I.State) (h : InvG A tid pl Q cl c₀ r g₀)
    (he : EnvExt tid c₀ c) (hg : g₀.Le g) (ht : c.threads[tid]? = some t) (hex : I.exec t.st = some tree)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv)
    (hnp : ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend)
    (hans : EnvGAnswers A tid pl (instrViews t (I.deps t.st)) rF c t) :
    tree.NoFaultRun A tid (instrViews t (I.deps t.st)) (ctx₀ t tid c.mem) := by
  obtain ⟨σ, t₀, hC₀, hQ₀⟩ := h
  obtain ⟨hst, hC⟩ := hC₀.transport he hg ht hnp E
  have hQ : Q t.st σ := hst ▸ hQ₀
  have hW := HN (TreeJLiveNF.envG (rv₀ := σ.r) (g₀ := g) (cl₀ := cl) hans I.State) t.st σ tree hQ hex
    (fun _ _ _ => trivial)
  exact treeJ_envG_noFaultRun hans hW (hC.rel.toNodeRel rF (I.deps t.st) E hm) (hm.ctxInv ht _)
    (H.shape _ _ hQ tree hex).2.singleAccess

/-- **No fault for a promise-free thread**: the conclusion of
`NoFaultRule.noFault` for `ThreadRuleRX.ofEnvG`, under its hypotheses and
`t.prom = []` (`EnvGAnswers` by `envGAnswers_of_promFree`). -/
theorem noFault_ofEnvG_promFree {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHyps A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    (HN : LinkNF A tid pl Q) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res)
    (t : Thread I) (tree : EvTree I.State) (h : (ThreadRuleRX.ofEnvG H hB).Inv cl c₀ r g₀)
    (he : EnvExt tid c₀ c) (hg : g₀.Le g) (ht : c.threads[tid]? = some t) (hex : I.exec t.st = some tree)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv) (hp : t.prom = []) :
    tree.NoFaultRun A tid (instrViews t (I.deps t.st)) (ctx₀ t tid c.mem) :=
  InvG.noFault H HN rF t tree h he hg ht hex E hm (fun _ hts _ => absurd (hp ▸ hts) List.not_mem_nil)
    (envGAnswers_of_promFree hp)

/-- **The no-fault rule from the rule link**, under `LinkNF` and the missing
fact `EnvGAnswersAt` (for promise-free threads see
`noFault_ofEnvG_promFree`). `EnvGAnswersAt` is believed false for threads
with a pure own promise (see its docstring), so this may be vacuous; prefer
`noFaultRule_ofEnvG_struct` (`EnvG/Answers.lean`), which needs only
fault-free trees. -/
theorem noFaultRule_ofEnvG {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHyps A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    (HN : LinkNF A tid pl Q) (hans : EnvGAnswersAt (I := I) A tid pl) : NoFaultRule (ThreadRuleRX.ofEnvG H hB) :=
  ⟨fun rF t tree h he hg ht hex E hm _ hnp =>
    InvG.noFault H HN rF t tree h he hg ht hex E hm hnp (hans _ rF _ t ht)⟩

end Rule

end Kraken.Promising.SLR.EnvG
