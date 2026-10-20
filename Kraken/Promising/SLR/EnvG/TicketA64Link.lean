/-
**Layer L, part 5: the AArch64 ticket link**,
`ThreadRuleRXGSXE.ofSafelyEnvGTD` (`EnvG/TakeA64Link.lean` and
`EnvG/TakeA64Rule.lean` for `EnvGTD`; both unchanged).

A thread proved by a `Safely` judgment of `instrStepEnv (EnvGTD isa A tid pl
D)` (the ticket environment, `EnvG/TicketEnv.lean`) gives a
`ThreadRuleRXGSXE G₀ D.TX`, hence `NPSafeP (modelX isa D.TX) … G₀
(K2Scope (model isa) AllocIds)` (`npSafeP_of_safelyEnvGTD`), the per-thread
input of `theorem1IIPureX_G₀_S`.

- `QA64TD`, `linkHypsTD_QA64TD`, `post_of_halted_QA64TD`: `QA64T` and its
  link hypotheses for `EnvGTD` (by `exec_treeJLive_of_instrStepEnv'`, generic
  in the environment).
- `qa64TD_of_partialTripleEnv`, `invGTD_init`: `QA64TD` from a `vcgen`
  partial triple, and the rule's invariant at the initial configuration
  (`coreAt_init`; the `coh x` transfer holds since the initial views are
  `0`).
- `noFault_QA64TD`, **`noFaultRule_ofSafelyEnvGTD_struct`**: the no-fault rule
  (`NoFaultRuleSXE`) for fault-free code.
-/
import Kraken.Promising.SLR.EnvG.TicketRuleLink
import Kraken.Promising.SLR.EnvG.TakeA64Rule

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-- `EnvGTD` for AArch64. -/
abbrev EnvGTDA (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser) : SharedEnv :=
  Kraken.Promising.SLR.EnvGTD isa A tid pl D

/-- **The thread-local invariant of the ticket environment** (`QA64T` for
`EnvGTD`). -/
def QA64TD (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser) (e : Kraken.Executable Directive) (endPc : Int64)
    (post : MachineState × EStateA → Prop) (st : State) (σ : EStateA) : Prop :=
  st.exe = e ∧ st.decls = {} ∧ st.endPc = endPc ∧ Safely (e.instrStepEnv (EnvGTDA A tid pl D)) post (st.st, σ)

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {D : Dispenser} {e : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateA → Prop}

/-- **The link hypotheses at `QA64TD`** (`linkHypsT_QA64T` for `EnvGTD`). -/
theorem linkHypsTD_QA64TD (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e)
    (hpost : ∀ y, post y → y.1.2 = endPc) : LinkHypsTD (I := isa) A tid pl D (QA64TD A tid pl D e endPc post) where
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
/-- **`done` at `QA64TD`** (`post_of_halted_QA64T` for `EnvGTD`). -/
theorem post_of_halted_QA64TD (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTDA A tid pl D) x R)
    {t : Thread isa} {σ : EStateA} (hQ : QA64TD A tid pl D e endPc post t.st σ) (hh : t.halted = true) :
    post (t.st.st, σ) := by
  obtain ⟨he, -, hend, hsafe⟩ := hQ
  exact post_of_halted_env hstuck he hend hsafe hh

/-- **`ThreadRuleRXGSXE.ofSafelyEnvGTD`**: the AArch64 ticket rule link
(hypotheses as `ThreadRuleRXGS.ofSafelyEnvGT`, for `EnvGTD`). -/
def _root_.Kraken.Promising.SLR.ThreadRuleRXGSXE.ofSafelyEnvGTD
    {B : Config isa → (modelX isa D.TX).R → (modelX isa D.TX).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTDA A tid pl D) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGSXE G₀ D.TX A B tid :=
  ThreadRuleRXGSXE.ofEnvGTD (linkHypsTD_QA64TD (tid := tid) hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64TD hstuck hQ hh) hp hrel hcl

/-- **`NPSafeP` over `Erase ∧ TX` (frame `K2Scope AllocIds`) from a `Safely`
judgment of `EnvGTD`** (`NPSafeP.of_ruleRXGSXE` at `ofSafelyEnvGTD`). -/
theorem npSafeP_of_safelyEnvGTD {B : Config isa → (modelX isa D.TX).R → (modelX isa D.TX).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTDA A tid pl D) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvGTD (I := isa) A tid pl D (QA64TD A tid pl D e endPc post) cl c r g) :
    NPSafeP (modelX isa D.TX) A B tid G₀ (K2Scope (model isa) AllocIds) n m cl c r g :=
  NPSafeP.of_ruleRXGSXE (ThreadRuleRXGSXE.ofSafelyEnvGTD hpl hlive hshape hpost hstuck hB) n m cl c r g h

/-- **Every tree from a `QA64TD`-state is fault-free**, for fault-free code
(`noFault_QA64T` for `EnvGTD`). -/
theorem noFault_QA64TD (hnf : DirsNoFault e) (hpost : ∀ y, post y → y.1.2 = endPc) :
    ∀ st σ tree, QA64TD A tid pl D e endPc post st σ → isa.exec st = some tree → tree.NoFault := by
  intro st σ tree h hex
  obtain ⟨he, hds, hend, hsafe⟩ := h
  rcases hsafe.unfold with hp | ⟨R, hR, -⟩
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · obtain ⟨d, z, rest, hcode, -⟩ := id hR
    exact noFault_of_codeAt he hds hcode (hnf d z (mem_of_codeAt hcode)) tree hex

/-- **The AArch64 ticket no-fault rule**, unconditional in the thread's
promises: `NoFaultRuleSXE (ofSafelyEnvGTD …)` for fault-free code
(`noFaultRule_ofSafelyEnvGT_struct` for `EnvGTD`). -/
theorem noFaultRule_ofSafelyEnvGTD_struct
    {B : Config isa → (modelX isa D.TX).R → (modelX isa D.TX).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTDA A tid pl D) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRuleSXE (ThreadRuleRXGSXE.ofSafelyEnvGTD hpl hlive hshape hpost hstuck hB) :=
  NoFaultRuleSXE.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp => by
    obtain ⟨σ, hQ⟩ := InvGTD.q_at rF t h he hg ht E hnp
    exact noFault_QA64TD hnf hpost t.st σ tree hQ hex

end Link

/-! ## Start -/

section Triple

variable {A : Arch} {tid : Nat} {pl : Plan} {D : Dispenser}

/-- **`QA64TD` from a partial triple** in `EnvGTD` at a thread state at the
start of `p`, whose exceptional exit `E` never holds. -/
theorem qa64TD_of_partialTripleEnv [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Kraken.Executable.ValidLayout (layout p)] {P Q : MachineData → EStateA → Prop}
    {E : Int64 → MachineData → EStateA → Prop} (ht : MachineWP.PartialTripleEnv (EnvGTDA A tid pl D) P p Q E)
    (henv : cenv = layout p) {st : State} (he : st.exe = layout p) (hds : st.decls = {})
    (hend : st.endPc = (layout p).addrOf p.length) (hpc : st.st.2 = (layout p).addrOf 0) {σ : EStateA}
    (hP : P st.st.1 σ) (hE : ∀ a s g, ¬ E a s g := by simp) :
    QA64TD A tid pl D (layout p) ((layout p).addrOf p.length) (postOf p Q) st σ := by
  refine ⟨he, hds, hend, ?_⟩
  have hst : st.st = (st.st.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hpc, Executable.addrOf_zero, Layout.apply_fst]
  rw [hst]
  exact (Program.instrStepEnv_of_partialTripleEnv ht hP henv).mono fun _ h => h.imp id (hE _ _ _)

/-- **The ticket rule's invariant at the initial configuration** from
`QA64TD` at `σInit` (the initial views are `0`). -/
theorem invGTD_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = []) {e : Kraken.Executable Directive} {endPc : Int64}
    {post : MachineState × EStateA → Prop}
    (hQ : QA64TD A tid pl D e endPc post s (σInit (Config.init ss m) r g)) :
    InvGTD (I := isa) A tid pl D (QA64TD A tid pl D e endPc post) True (Config.init ss m) r g :=
  ⟨_, _, coreAt_init hs hpend, hQ, fun _ => by simp [Thread.init, Views.getCoh]⟩

end Triple

end Kraken.Promising.AArch64.EnvG

#print axioms Kraken.Promising.SLR.ThreadRuleRXGSXE.ofSafelyEnvGTD
#print axioms Kraken.Promising.AArch64.EnvG.npSafeP_of_safelyEnvGTD
#print axioms Kraken.Promising.AArch64.EnvG.noFaultRule_ofSafelyEnvGTD_struct
#print axioms Kraken.Promising.AArch64.EnvG.invGTD_init
