/-
Whole-thread environment (`EnvG`): **the AArch64 no-fault rule
without `EnvGAnswersAt`** (`EnvG/Answers.lean`).

`noFaultRule_ofSafelyEnvG` (`EnvG/A64NoFault.lean`) takes fault-free code
(`DirsNoFault e`) *and* the missing fact `EnvGAnswersAt`. Fault-free code
alone suffices: at every `QA64`-state the thread's tree is fault-free
(`noFault_of_codeAt`, or there is no tree at the end), so
`noFaultRule_ofEnvG_struct` applies. This covers threads with promises.

- `noFault_QA64`: every tree from a `QA64`-state is fault-free, given
  `DirsNoFault e`.
- `noFaultRule_ofSafelyEnvG_struct`: `NoFaultRule (ofSafelyEnvG …)` with the
  arguments of `noFaultRule_ofSafelyEnvG` minus `EnvGAnswersAt`.
-/
import Kraken.Promising.SLR.EnvG.A64NoFault
import Kraken.Promising.SLR.EnvG.Answers

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
  {endPc : Int64} {post : MachineState × EStateA → Prop}

/-- **Every tree from a `QA64`-state is fault-free**, for fault-free code
(`DirsNoFault e`): at the end there is no tree (`exec_eq_none_of_end`),
elsewhere the pc's directive is in the code (`noFault_of_codeAt`). -/
theorem noFault_QA64 (hnf : DirsNoFault e) (hpost : ∀ y, post y → y.1.2 = endPc) :
    ∀ st σ tree, QA64 A tid pl e endPc post st σ → isa.exec st = some tree → tree.NoFault := by
  intro st σ tree h hex
  obtain ⟨he, hds, hend, hsafe⟩ := h
  rcases hsafe.unfold with hp | ⟨R, hR, -⟩
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · obtain ⟨d, z, rest, hcode, -⟩ := id hR
    exact noFault_of_codeAt he hds hcode (hnf d z (mem_of_codeAt hcode)) tree hex

/-- **The AArch64 no-fault rule, unconditional in the thread's promises**:
`NoFaultRule (ofSafelyEnvG …)` for fault-free code (`DirsNoFault e`). Same
arguments as `noFaultRule_ofSafelyEnvG` without `EnvGAnswersAt`. -/
theorem noFaultRule_ofSafelyEnvG_struct {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRule (ThreadRuleRX.ofSafelyEnvG hpl hlive hshape hpost hstuck hB) :=
  noFaultRule_ofEnvG_struct _ _ (noFault_QA64 hnf hpost)

end Link

end Kraken.Promising.AArch64.EnvG

#print axioms Kraken.Promising.AArch64.EnvG.noFault_QA64
#print axioms Kraken.Promising.AArch64.EnvG.noFaultRule_ofSafelyEnvG_struct
