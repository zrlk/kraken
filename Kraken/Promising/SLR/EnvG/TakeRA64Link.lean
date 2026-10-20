/-
**Part 2: the AArch64 link with taking loads
and release-kind RMWs**, `ThreadRuleRXGS.ofSafelyEnvGTR` (the combination of
`ThreadRuleRXGS.ofSafelyEnvGT`, `EnvG/TakeA64Link.lean`, and
`ThreadRuleRX.ofSafelyEnvGR`, `EnvG/A64LinkR.lean`; both unchanged).

A thread proved by a `Safely` judgment of `instrStepEnv (EnvGT isa A tid pl)`
whose code is phase-1 with release-kind RMWs (`Phase1TreeR`) and whose plan
satisfies the give-away side condition at the release predicates `rel₀`
(`RelRmwGiveOk isa pl rel₀`) gives a `ThreadRuleRXGS G₀`, hence `NPSafeP …
G₀ (K2Scope (model isa) AllocIds)` (`npSafeP_of_safelyEnvGTR`), the input of
Theorem 1′ with option (S)'s frame (`theorem1IIPure_G₀_S`,
`final_of_relPureSafelyS`).

- `QA64TR` (`QA64T` with fixed release predicates), `linkHypsTR_QA64TR`,
  `ThreadRuleRXGS.ofSafelyEnvGTR`, `npSafeP_of_safelyEnvGTR`.
- No-fault: `noFaultRule_ofSafelyEnvGTR_struct` (`NoFaultRuleS`, for
  fault-free code, unconditional in the thread's promises).
- Start: `qa64TR_of_partialTripleEnv`, `invGTR_init`.

Phase-1 limits: as `EnvG/TakeRLink.lean` (in particular, a planned-release
RMW forwards nothing it claims, `RelRmwGiveOk`).
-/
import Kraken.Promising.SLR.EnvG.TakeRLink
import Kraken.Promising.SLR.EnvG.TakeA64Rule
import Kraken.Promising.SLR.EnvG.A64LinkR

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-- **The thread-local invariant with taking loads and fixed release
predicates**: `QA64T` and `σ.g.rel = rel₀`. -/
def QA64TR (A : Arch) (tid : Nat) (pl : Plan) (e : Kraken.Executable Directive) (endPc : Int64)
    (post : MachineState × EStateA → Prop) (rel₀ : Loc → Pred) (st : State) (σ : EStateA) : Prop :=
  QA64T A tid pl e endPc post st σ ∧ σ.g.rel = rel₀

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
  {endPc : Int64} {post : MachineState × EStateA → Prop} {rel₀ : Loc → Pred}

/-- **The link hypotheses at `QA64TR`** (`linkHypsT_QA64T` with
`Phase1TreeR` and the give-away side condition, through `link_relFixT`). -/
theorem linkHypsTR_QA64TR (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e)
    (hG : RelRmwGiveOk isa pl rel₀) (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsTR (I := isa) A tid pl (QA64TR A tid pl e endPc post rel₀) where
  valid := hpl
  shape st _ h tree hex := hshape st h.1.1 h.1.2.1 tree hex
  giveOk _ _ h := h.2 ▸ hG
  link := link_relFixT rel₀ fun J st σ tree h hex hJ => by
    obtain ⟨he, hds, hend, hsafe⟩ := h
    rcases hsafe.unfold with hp | ⟨R, hR, hk⟩
    · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
      rw [this] at hex; cases hex
    · exact exec_treeJLive_of_instrStepEnv' J he hds hR (fun m g' hz => hJ _ _ ⟨he, hds, hend, hk _ hz⟩) hlive
        tree hex

/-- **`ThreadRuleRXGS.ofSafelyEnvGTR`**: the AArch64 rule link with taking
loads and release-kind RMWs (hypotheses as `ThreadRuleRX.ofSafelyEnvGR`,
for `EnvGT`). -/
def _root_.Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTR
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e) (hG : RelRmwGiveOk isa pl rel₀)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGS G₀ A B tid :=
  ThreadRuleRXGS.ofEnvGTR (linkHypsTR_QA64TR (tid := tid) hpl hlive hshape hG hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64T hstuck hQ.1 hh) hp hrel hcl

/-- **`NPSafeP` (frame `K2Scope AllocIds`) from a `Safely` judgment of
`EnvGT` with release-kind RMWs** (`NPSafeP.of_ruleRXGS` at
`ofSafelyEnvGTR`). -/
theorem npSafeP_of_safelyEnvGTR {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e) (hG : RelRmwGiveOk isa pl rel₀)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvGR (I := isa) tid pl (QA64TR A tid pl e endPc post rel₀) cl c r g) :
    NPSafeP (model isa) A B tid G₀ (K2Scope (model isa) AllocIds) n m cl c r g :=
  NPSafeP.of_ruleRXGS (ThreadRuleRXGS.ofSafelyEnvGTR hpl hlive hshape hG hpost hstuck hB) n m cl c r g h

/-- **The AArch64 no-fault rule with taking loads and release-kind RMWs**,
unconditional in the thread's promises: `NoFaultRuleS (ofSafelyEnvGTR …)`
for fault-free code (`DirsNoFault e`). -/
theorem noFaultRule_ofSafelyEnvGTR_struct {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e) (hG : RelRmwGiveOk isa pl rel₀)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRuleS (ThreadRuleRXGS.ofSafelyEnvGTR hpl hlive hshape hG hpost hstuck hB) :=
  NoFaultRuleS.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp => by
    obtain ⟨σ, hQ⟩ := InvGR.q_at rF t h he hg ht E hnp
    exact noFault_QA64T hnf hpost t.st σ tree hQ.1 hex

end Link

/-! ## The initial state -/

section Init

variable {A : Arch} {tid : Nat} {pl : Plan}

/-- **`QA64TR` from a partial triple** in `EnvGT` at a thread state at the
start of `p` (`qa64T_of_partialTripleEnv` with the release predicates of the
initial env state). -/
theorem qa64TR_of_partialTripleEnv [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Kraken.Executable.ValidLayout (layout p)] {P Q : MachineData → EStateA → Prop}
    {E : Int64 → MachineData → EStateA → Prop} (ht : MachineWP.PartialTripleEnv (EnvGTA A tid pl) P p Q E)
    (henv : cenv = layout p) {st : State} (he : st.exe = layout p) (hds : st.decls = {})
    (hend : st.endPc = (layout p).addrOf p.length) (hpc : st.st.2 = (layout p).addrOf 0) {σ : EStateA}
    (hP : P st.st.1 σ) (hE : ∀ a s g, ¬ E a s g := by simp) :
    QA64TR A tid pl (layout p) ((layout p).addrOf p.length) (postOf p Q) σ.g.rel st σ :=
  ⟨qa64T_of_partialTripleEnv ht henv he hds hend hpc hP hE, rfl⟩

/-- **The rule's invariant with taking loads and release-kind RMWs at the
initial configuration** from `QA64T` at `σInit` (the release predicates are
the ghost's). -/
theorem invGTR_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = []) {e : Kraken.Executable Directive} {endPc : Int64}
    {post : MachineState × EStateA → Prop} (hQ : QA64T A tid pl e endPc post s (σInit (Config.init ss m) r g)) :
    InvGR (I := isa) tid pl (QA64TR A tid pl e endPc post g.rel) True (Config.init ss m) r g :=
  ⟨σInit (Config.init ss m) r g, Thread.init s, coreAtR_init hs hpend, hQ, rfl⟩

end Init

#print axioms ThreadRuleRXGS.ofSafelyEnvGTR
#print axioms npSafeP_of_safelyEnvGTR
#print axioms noFaultRule_ofSafelyEnvGTR_struct
#print axioms invGTR_init

end Kraken.Promising.AArch64.EnvG
