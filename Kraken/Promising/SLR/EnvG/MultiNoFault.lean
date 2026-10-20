/-
Whole-thread environment (`EnvG`), phase 2: **the no-fault rule for
code with load-prefix trees** (`ThreadRuleRX.ofEnvG2`, `ofSafelyEnvG2`).

The phase-1 route (`EnvG/Answers.lean`, `EnvG/A64Answers.lean`) proves
`NoFaultRule` from fault-free trees alone: a run faults only at a `.fault`
leaf, so a structurally fault-free tree at every invariant state suffices
(`NoFaultRule.ofNoFault`). The argument never looks at the tree's shape, and
`ofEnvG2` keeps the existing invariant `InvG`, so it carries over verbatim:

- `noFaultRule_ofEnvG2_struct` (ISA-neutral): `NoFaultRule (ofEnvG2 H hB)`
  from fault-free trees at every `Q`-state;
- `noFaultRule_ofSafelyEnvG2_struct` (AArch64): `NoFaultRule (ofSafelyEnvG2 …)`
  for fault-free code (`DirsNoFault e`, decided by `dirs_no_fault`), with or
  without promises.
-/
import Kraken.Promising.SLR.EnvG.MultiA64
import Kraken.Promising.SLR.EnvG.A64Answers

-- `noFaultRule_ofEnvG2_struct`: `EnvG/MultiCommon.lean` (moved there).

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

variable {A : Arch} {tid : Nat} {pl : Plan} {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
  {endPc : Int64} {post : MachineState × EStateA → Prop}

/-- **The AArch64 phase-2 no-fault rule**: `NoFaultRule (ofSafelyEnvG2 …)` for
fault-free code (`DirsNoFault e`), with or without promises. Same arguments
as `noFaultRule_ofSafelyEnvG_struct` with `Phase2Tree` for `Phase1Tree`. -/
theorem noFaultRule_ofSafelyEnvG2_struct {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase2Tree A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRule (ThreadRuleRX.ofSafelyEnvG2 hpl hlive hshape hpost hstuck hB) :=
  noFaultRule_ofEnvG2_struct _ _ (noFault_QA64 hnf hpost)

end Kraken.Promising.AArch64.EnvG
