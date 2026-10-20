/-
**Part 6: the AArch64 link with taking
loads**, `ThreadRuleRXGS.ofSafelyEnvGT` (`EnvG/A64Link.lean`'s
`ThreadRuleRX.ofSafelyEnvG`, frozen and unchanged, for `EnvGT`).

A thread proved by a `Safely` judgment of `instrStepEnv (EnvGT isa A tid pl)`
(non-forwarded acquire loads take their exposed slots, `EnvG/TakeEnv.lean`)
gives a `ThreadRuleRXGS G₀`, hence `NPSafeP … G₀ (K2Scope (model isa)
AllocIds)` (`npSafeP_of_safelyEnvGT`), the input of Theorem 1′ with option
(S)'s frame (`theorem1IIPure_G₀_S`). The link hypotheses come from
`exec_treeJLive_of_instrStepEnv'` exactly as for `EnvG` (it is generic in
the environment).

Phase-1 limits: as `ofSafelyEnvG` (single-access trees, releases are stores,
`Phase1Tree` a stated hypothesis), plus: only non-forwarded acquire loads
take, no fence-node take, the take and the use of what is taken are in
different instructions.
-/
import Kraken.Promising.SLR.EnvG.TakeRuleLink
import Kraken.Promising.SLR.EnvG.A64Link

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-- `EnvGT` for AArch64. -/
abbrev EnvGTA (A : Arch) (tid : Nat) (pl : Plan) : SharedEnv := Kraken.Promising.SLR.EnvGT isa A tid pl

/-- **The thread-local invariant with taking loads** (`QA64` for `EnvGT`). -/
def QA64T (A : Arch) (tid : Nat) (pl : Plan) (e : Kraken.Executable Directive) (endPc : Int64)
    (post : MachineState × EStateA → Prop) (st : State) (σ : EStateA) : Prop :=
  st.exe = e ∧ st.decls = {} ∧ st.endPc = endPc ∧ Safely (e.instrStepEnv (EnvGTA A tid pl)) post (st.st, σ)

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
  {endPc : Int64} {post : MachineState × EStateA → Prop}

/-- **The link hypotheses at `QA64T`** (`linkHyps_QA64` for `EnvGT`). -/
theorem linkHypsT_QA64T (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e)
    (hpost : ∀ y, post y → y.1.2 = endPc) : LinkHypsT (I := isa) A tid pl (QA64T A tid pl e endPc post) where
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
/-- **`done` at `QA64T`** (`post_of_halted_QA64` for `EnvGT`). -/
theorem post_of_halted_QA64T (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTA A tid pl) x R)
    {t : Thread isa} {σ : EStateA} (hQ : QA64T A tid pl e endPc post t.st σ) (hh : t.halted = true) :
    post (t.st.st, σ) := by
  obtain ⟨he, -, hend, hsafe⟩ := hQ
  exact post_of_halted_env hstuck he hend hsafe hh

/-- **`ThreadRuleRXGS.ofSafelyEnvGT`**: the AArch64 rule link with taking
loads (hypotheses as `ThreadRuleRX.ofSafelyEnvG`, for `EnvGT`). -/
def _root_.Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGT
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGS G₀ A B tid :=
  ThreadRuleRXGS.ofEnvGT (linkHypsT_QA64T (tid := tid) hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64T hstuck hQ hh) hp hrel hcl

/-- **`NPSafeP` (frame `K2Scope AllocIds`) from a `Safely` judgment of
`EnvGT`** (`NPSafeP.of_ruleRXGS` at `ofSafelyEnvGT`). -/
theorem npSafeP_of_safelyEnvGT {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvG (I := isa) A tid pl (QA64T A tid pl e endPc post) cl c r g) :
    NPSafeP (model isa) A B tid G₀ (K2Scope (model isa) AllocIds) n m cl c r g :=
  NPSafeP.of_ruleRXGS (ThreadRuleRXGS.ofSafelyEnvGT hpl hlive hshape hpost hstuck hB) n m cl c r g h

end Link

#print axioms ThreadRuleRXGS.ofSafelyEnvGT
#print axioms npSafeP_of_safelyEnvGT

end Kraken.Promising.AArch64.EnvG
