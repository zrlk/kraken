/-
**No fault for rules whose loads may take, ISA-neutral part**.

- `NoFaultRuleS R`: `NoFaultRule` (`SLR/Sim/NoFault.lean`, stated for
  `ThreadRuleRX`) for a rule whose loads may take (`ThreadRuleRXGS`), same
  field. `NoFaultRuleS.ofNoFault`: from fault-free trees.

Users: `EnvG/TakeA64Rule.lean` (`noFaultRule_ofSafelyEnvGT_struct`) and
`EnvG/TakeX64Link.lean` (whose `NoFaultRuleSX` is now an alias of
`NoFaultRuleS`).
-/
import Kraken.Promising.SLR.TakeRuleThread
import Kraken.Promising.SLR.Sim.NoFault

namespace Kraken.Promising.SLR

open Kraken Kraken.Promising

variable {I : ISA}

/-! ## No fault for rules whose loads may take -/

/-- **A no-fault rule whose loads may take** (`NoFaultRule` for
`ThreadRuleRXGS`): at every instance of the invariant the thread's next tree
has no fault from its instruction-start context. -/
structure NoFaultRuleS {G : PrepayGuard I} {A : Arch} {B : Config I → (model I).R → (model I).Ghost → Prop}
    {tid : Nat} (R : ThreadRuleRXGS G A B tid) : Prop where
  noFault : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t : Thread I)
    (tree : EvTree I.State), R.Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g →
    c.threads[tid]? = some t → I.exec t.st = some tree →
    Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv → c.WfProm tid →
    (∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    tree.NoFaultRun A tid (instrViews t (I.deps t.st)) (ctx₀ t tid c.mem)

/-- `NoFaultRuleS` from fault-free trees (`NoFaultRule.ofNoFault`). -/
theorem NoFaultRuleS.ofNoFault {G : PrepayGuard I} {A : Arch}
    {B : Config I → (model I).R → (model I).Ghost → Prop} {tid : Nat} {R : ThreadRuleRXGS G A B tid}
    (h : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t : Thread I)
      (tree : EvTree I.State), R.Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g →
      c.threads[tid]? = some t → I.exec t.st = some tree →
      Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv → c.WfProm tid →
      (∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) → tree.NoFault) :
    NoFaultRuleS R :=
  ⟨fun rF t tree hI he hg ht hex E hinv hwf hnp =>
    (h rF t tree hI he hg ht hex E hinv hwf hnp).run A tid _ _⟩

end Kraken.Promising.SLR
