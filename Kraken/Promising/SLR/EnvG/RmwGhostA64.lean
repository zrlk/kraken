/-
Whole-thread environment, **Claim-conditional RMWs** part 4: the **AArch64 link** of the
claim-conditional environment `EnvGC` (`ThreadRuleRX.ofSafelyEnvGRC`),
additively beside `ThreadRuleRX.ofSafelyEnvGR` (`EnvG/A64LinkR.lean`).
Nothing imports this file.

It is `ofSafelyEnvGR` with `EnvGC` for `EnvG` in the `Safely` judgment
(`QA64C`) and **without** `RelRmwGiveOk` (so without fixing the release
predicates: `QA64C` needs no `rel₀`). Release-only RMWs (`swpl`, `ldaddl`)
and RMW releases that give something away are covered: a release-only RMW
does not claim (`claimOk_rel_false`), and a release gives from the thread's
own resource (`RmwOkC`).

Phase-1 limits otherwise as `ofSafelyEnvGR`: single-access trees
(`Phase1TreeR`), read-side acquire only, an in-flight release RMW never fails.

Contents: `EnvGCA`, `QA64C`, `linkHypsRC_QA64C`, `post_of_halted_QA64C`,
`ThreadRuleRX.ofSafelyEnvGRC`, `npSafe_of_safelyEnvGRC`,
`noFaultRule_ofSafelyEnvGRC_struct` (unconditional in promises, from
`DirsNoFault`), `invGRC_init`.
-/
import Kraken.Promising.SLR.EnvG.RmwGhostRule
import Kraken.Promising.SLR.EnvG.A64LinkR
import Kraken.Promising.SLR.EnvG.LinkRNoFault

-- `noFaultRule_ofEnvGRC_struct`: `EnvG/LinkRNoFault.lean` (moved there).

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-- `EnvGC` for AArch64. -/
abbrev EnvGCA (A : Arch) (tid : Nat) (pl : Plan) : SharedEnv := Kraken.Promising.SLR.EnvGC isa A tid pl

/-- **The thread-local invariant of `EnvGC`**: `QA64` with the `Safely`
judgment of `EnvGC`. -/
def QA64C (A : Arch) (tid : Nat) (pl : Plan) (e : Kraken.Executable Directive) (endPc : Int64)
    (post : MachineState × EStateA → Prop) (st : State) (σ : EStateA) : Prop :=
  st.exe = e ∧ st.decls = {} ∧ st.endPc = endPc ∧ Safely (e.instrStepEnv (EnvGCA A tid pl)) post (st.st, σ)

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
  {endPc : Int64} {post : MachineState × EStateA → Prop}

/-- **The link hypotheses of `EnvGC` at `QA64C`** (as `linkHyps_QA64`). -/
theorem linkHypsRC_QA64C (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e)
    (hpost : ∀ y, post y → y.1.2 = endPc) : LinkHypsRC (I := isa) A tid pl (QA64C A tid pl e endPc post) where
  valid := hpl
  shape st _ h tree hex := hshape st h.1 h.2.1 tree hex
  link J st σ tree h hex hJ := by
    obtain ⟨he, hds, hend, hsafe⟩ := h
    rcases hsafe.unfold with hp | ⟨R, hR, hk⟩
    · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
      rw [this] at hex; cases hex
    · exact exec_treeJLive_of_instrStepEnv' J he hds hR (fun m g' hz => hJ _ _ ⟨he, hds, hend, hk _ hz⟩) hlive
        tree hex

omit [Kraken.Executable.ValidLayout e] in
/-- **`done` at `QA64C`** (`post_of_halted_QA64`). -/
theorem post_of_halted_QA64C (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGCA A tid pl) x R)
    {t : Thread isa} {σ : EStateA} (hQ : QA64C A tid pl e endPc post t.st σ) (hh : t.halted = true) :
    post (t.st.st, σ) := by
  obtain ⟨he, -, hend, hsafe⟩ := hQ
  exact post_of_halted_env hstuck he hend hsafe hh

/-- **`ThreadRuleRX.ofSafelyEnvGRC`**: the AArch64 rule link of `EnvGC`
(`ofSafelyEnvGR` without the give-away side condition). -/
def _root_.Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvGRC
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGCA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRX A B tid :=
  ThreadRuleRX.ofEnvGRC (linkHypsRC_QA64C (tid := tid) hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64C hstuck hQ hh) hp hrel hcl

/-- **`NPSafe` from a `Safely` judgment of `EnvGC`**. -/
theorem npSafe_of_safelyEnvGRC {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGCA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvGR (I := isa) tid pl (QA64C A tid pl e endPc post) cl c r g) :
    NPSafe (model isa) A B tid n m cl c r g :=
  NPSafe.of_ruleRX (ThreadRuleRX.ofSafelyEnvGRC hpl hlive hshape hpost hstuck hB) n m cl c r g h

/-- **The AArch64 no-fault rule of `EnvGC`**, unconditional in the thread's
promises, for fault-free code (`DirsNoFault e`). -/
theorem noFaultRule_ofSafelyEnvGRC_struct {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGCA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRule (ThreadRuleRX.ofSafelyEnvGRC hpl hlive hshape hpost hstuck hB) :=
  noFaultRule_ofEnvGRC_struct _ _ fun st σ tree hQ hex => by
    obtain ⟨he, hds, hend, hsafe⟩ := hQ
    rcases hsafe.unfold with hp | ⟨R, hR, -⟩
    · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
      rw [this] at hex; cases hex
    · obtain ⟨d, z, rest, hcode, -⟩ := id hR
      exact noFault_of_codeAt he hds hcode (hnf d z (mem_of_codeAt hcode)) tree hex

end Link

/-- **The rule's invariant of `EnvGC` at the initial configuration**, from
`QA64C` at `σInit`. -/
theorem invGRC_init {A : Arch} {tid : Nat} {pl : Plan} {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State}
    (hs : ss[tid]? = some s) {r : Res} {g : Ghost} (hpend : g.pend = []) {e : Kraken.Executable Directive}
    {endPc : Int64} {post : MachineState × EStateA → Prop}
    (hQ : QA64C A tid pl e endPc post s (σInit (Config.init ss m) r g)) :
    InvGR (I := isa) tid pl (QA64C A tid pl e endPc post) True (Config.init ss m) r g :=
  ⟨σInit (Config.init ss m) r g, Thread.init s, coreAtR_init hs hpend, hQ⟩

end Kraken.Promising.AArch64.EnvG
