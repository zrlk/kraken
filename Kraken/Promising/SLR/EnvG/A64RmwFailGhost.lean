/-
Part 3: **the AArch64 link of the claim-conditional
environment with failing in-flight release RMWs** (F × C,
`ThreadRuleRXF.ofSafelyEnvGFC`). Additive beside
`ThreadRuleRX.ofSafelyEnvGRC` (`EnvG/RmwGhostA64.lean`: `EnvGC`, but an
in-flight release RMW never fails) and `ThreadRuleRXF.ofSafelyEnvGF`
(`EnvG/A64RmwFail.lean`: failing release RMWs, but on `EnvG` with
`RelRmwGiveOk`).

It is `ofSafelyEnvGRC` with `Phase1TreeF` (RMWs of any kind and operation,
`casal` included; `dirs_phase1F`) and the `F` rule (`ThreadRuleRXF`, giving
`NPSafeF`; Theorem 1′ for it is `theorem1FChain`). The judgment is
`Safely (e.instrStepEnv (EnvGCA A tid pl)) post` (`QA64C`), as for
`ofSafelyEnvGRC`; no release predicates are fixed (no `rel₀`).

This covers release RMWs that **give something away and may fail**: a
Treiber push (`casal` publishing a node) and a Treiber pop (`casal` writing a
loaded value), `treiber_pp.kl`.

Phase-1 limits otherwise: single-access trees, read-side acquire only; a
release RMW cannot forward what it claims.

Contents: `linkHypsFC_QA64C`, `ThreadRuleRXF.ofSafelyEnvGFC`,
`npSafeF_of_safelyEnvGFC`, `noFaultRuleF_ofSafelyEnvGFC_struct` (from
`DirsNoFault`), `invGFC_init`.
-/
import Kraken.Promising.SLR.EnvG.RmwFailGhostRule
import Kraken.Promising.SLR.EnvG.RmwGhostA64
import Kraken.Promising.SLR.EnvG.A64RmwFail

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
  {endPc : Int64} {post : MachineState × EStateA → Prop}

/-- **The link hypotheses of `EnvGC` with failing release RMWs at `QA64C`**
(`linkHypsRC_QA64C` with `Phase1TreeF`). -/
theorem linkHypsFC_QA64C (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeF e)
    (hpost : ∀ y, post y → y.1.2 = endPc) : LinkHypsFC (I := isa) A tid pl (QA64C A tid pl e endPc post) where
  valid := hpl
  shape st _ h tree hex := hshape st h.1 h.2.1 tree hex
  link J st σ tree h hex hJ := by
    obtain ⟨he, hds, hend, hsafe⟩ := h
    rcases hsafe.unfold with hp | ⟨R, hR, hk⟩
    · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
      rw [this] at hex; cases hex
    · exact exec_treeJLive_of_instrStepEnv' J he hds hR (fun m g' hz => hJ _ _ ⟨he, hds, hend, hk _ hz⟩) hlive
        tree hex

/-- **`ThreadRuleRXF.ofSafelyEnvGFC`**: the AArch64 rule link of `EnvGC` with
failing release RMWs (`ofSafelyEnvGRC` with `Phase1TreeF` and the `F`
rule). -/
def _root_.Kraken.Promising.SLR.EnvG.ThreadRuleRXF.ofSafelyEnvGFC
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeF e)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGCA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXF A B tid :=
  ThreadRuleRXF.ofEnvGFC (linkHypsFC_QA64C (tid := tid) hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64C hstuck hQ hh) hp hrel hcl

/-- **`NPSafeF` from a `Safely` judgment of `EnvGC` with failing release
RMWs** (`NPSafeF.of_ruleRXF` at `ofSafelyEnvGFC`). -/
theorem npSafeF_of_safelyEnvGFC {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeF e)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGCA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvGF (I := isa) tid pl (QA64C A tid pl e endPc post) cl c r g) :
    NPSafeF (model isa) A B tid n m cl c r g :=
  NPSafeF.of_ruleRXF (ThreadRuleRXF.ofSafelyEnvGFC hpl hlive hshape hpost hstuck hB) n m cl c r g h

/-- **The AArch64 no-fault rule of the `FC` link**, unconditional in the
thread's promises, for fault-free code (`DirsNoFault e`). -/
theorem noFaultRuleF_ofSafelyEnvGFC_struct {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeF e)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGCA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRuleF (ThreadRuleRXF.ofSafelyEnvGFC hpl hlive hshape hpost hstuck hB) :=
  noFaultRuleF_ofEnvGFC_struct _ _ fun st σ tree hQ hex => by
    obtain ⟨he, hds, hend, hsafe⟩ := hQ
    rcases hsafe.unfold with hp | ⟨R, hR, -⟩
    · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
      rw [this] at hex; cases hex
    · obtain ⟨d, z, rest, hcode, -⟩ := id hR
      exact noFault_of_codeAt he hds hcode (hnf d z (mem_of_codeAt hcode)) tree hex

end Link

/-- **The rule's invariant of the `FC` link at the initial configuration**,
from `QA64C` at `σInit`. -/
theorem invGFC_init {A : Arch} {tid : Nat} {pl : Plan} {ss : List isa.State} {m : List (Loc × Val)}
    {s : isa.State} (hs : ss[tid]? = some s) {r : Res} {g : Ghost} (hpend : g.pend = [])
    {e : Kraken.Executable Directive} {endPc : Int64} {post : MachineState × EStateA → Prop}
    (hQ : QA64C A tid pl e endPc post s (σInit (Config.init ss m) r g)) :
    InvGF (I := isa) tid pl (QA64C A tid pl e endPc post) True (Config.init ss m) r g :=
  ⟨σInit (Config.init ss m) r g, Thread.init s, coreAtF_init hs hpend, hQ⟩

end Kraken.Promising.AArch64.EnvG
