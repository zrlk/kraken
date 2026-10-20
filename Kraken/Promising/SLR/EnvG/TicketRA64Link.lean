/-
**Part 4: the AArch64 ticket link with a
release-kind ticket RMW**, `ThreadRuleRXGSXE.ofSafelyEnvGTDR`
(`EnvG/TicketA64Link.lean` for `EnvGTDR`, with `Phase1TreeR` from
`EnvG/A64LinkR.lean`; all unchanged).

A thread proved by a `Safely` judgment of `instrStepEnv (EnvGTDR isa A tid pl
D)` (`EnvG/TicketREnv.lean`: the ticket environment whose ticket RMW may be
release-kind, e.g. `ldaddal`) gives a `ThreadRuleRXGSXE G₀ D.TX`, hence
`NPSafeP (modelX isa D.TX) … G₀ (K2Scope (model isa) AllocIds)`
(`npSafeP_of_safelyEnvGTDR`), the per-thread input of `theorem1IIPureX_G₀_S`.

- `QA64TDR`, `linkHypsTDR_QA64TDR`, `post_of_halted_QA64TDR`.
- `ThreadRuleRXGSXE.ofSafelyEnvGTDR`, `npSafeP_of_safelyEnvGTDR`,
  `noFaultRule_ofSafelyEnvGTDR_struct`.
- Start: `qa64TDR_of_partialTripleEnv`, `invGTDR_init` (`coreAtR_init`).
-/
import Kraken.Promising.SLR.EnvG.TicketRRuleLink
import Kraken.Promising.SLR.EnvG.TicketA64Link
import Kraken.Promising.SLR.EnvG.A64LinkR

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-- `EnvGTDR` for AArch64. -/
abbrev EnvGTDRA (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser) : SharedEnv :=
  Kraken.Promising.SLR.EnvGTDR isa A tid pl D

/-- **The thread-local invariant of the ticket environment with a
release-kind ticket RMW** (`QA64TD` for `EnvGTDR`). -/
def QA64TDR (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser) (e : Kraken.Executable Directive) (endPc : Int64)
    (post : MachineState × EStateA → Prop) (st : State) (σ : EStateA) : Prop :=
  st.exe = e ∧ st.decls = {} ∧ st.endPc = endPc ∧ Safely (e.instrStepEnv (EnvGTDRA A tid pl D)) post (st.st, σ)

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {D : Dispenser} {e : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateA → Prop}

/-- **The link hypotheses at `QA64TDR`** (`linkHypsTD_QA64TD` with
`Phase1TreeR`). -/
theorem linkHypsTDR_QA64TDR (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e)
    (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsTDR (I := isa) A tid pl D (QA64TDR A tid pl D e endPc post) where
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
/-- **`done` at `QA64TDR`**. -/
theorem post_of_halted_QA64TDR (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTDRA A tid pl D) x R)
    {t : Thread isa} {σ : EStateA} (hQ : QA64TDR A tid pl D e endPc post t.st σ) (hh : t.halted = true) :
    post (t.st.st, σ) := by
  obtain ⟨he, -, hend, hsafe⟩ := hQ
  exact post_of_halted_env hstuck he hend hsafe hh

/-- **`ThreadRuleRXGSXE.ofSafelyEnvGTDR`**: the AArch64 ticket rule link with
a release-kind ticket RMW. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRXGSXE.ofSafelyEnvGTDR
    {B : Config isa → (modelX isa D.TX).R → (modelX isa D.TX).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTDRA A tid pl D) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGSXE G₀ D.TX A B tid :=
  ThreadRuleRXGSXE.ofEnvGTDR (linkHypsTDR_QA64TDR (tid := tid) hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64TDR hstuck hQ hh) hp hrel hcl

/-- **`NPSafeP` over `Erase ∧ TX` (frame `K2Scope AllocIds`) from a `Safely`
judgment of `EnvGTDR`** (`NPSafeP.of_ruleRXGSXE` at `ofSafelyEnvGTDR`). -/
theorem npSafeP_of_safelyEnvGTDR {B : Config isa → (modelX isa D.TX).R → (modelX isa D.TX).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTDRA A tid pl D) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvGTDR (I := isa) tid pl D (QA64TDR A tid pl D e endPc post) cl c r g) :
    NPSafeP (modelX isa D.TX) A B tid G₀ (K2Scope (model isa) AllocIds) n m cl c r g :=
  NPSafeP.of_ruleRXGSXE (ThreadRuleRXGSXE.ofSafelyEnvGTDR hpl hlive hshape hpost hstuck hB) n m cl c r g h

/-- **Every tree from a `QA64TDR`-state is fault-free**, for fault-free code. -/
theorem noFault_QA64TDR (hnf : DirsNoFault e) (hpost : ∀ y, post y → y.1.2 = endPc) :
    ∀ st σ tree, QA64TDR A tid pl D e endPc post st σ → isa.exec st = some tree → tree.NoFault := by
  intro st σ tree h hex
  obtain ⟨he, hds, hend, hsafe⟩ := h
  rcases hsafe.unfold with hp | ⟨R, hR, -⟩
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · obtain ⟨d, z, rest, hcode, -⟩ := id hR
    exact noFault_of_codeAt he hds hcode (hnf d z (mem_of_codeAt hcode)) tree hex

/-- **The AArch64 ticket no-fault rule with a release-kind ticket RMW**,
unconditional in the thread's promises. -/
theorem noFaultRule_ofSafelyEnvGTDR_struct
    {B : Config isa → (modelX isa D.TX).R → (modelX isa D.TX).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTDRA A tid pl D) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRuleSXE (ThreadRuleRXGSXE.ofSafelyEnvGTDR hpl hlive hshape hpost hstuck hB) :=
  NoFaultRuleSXE.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp => by
    obtain ⟨σ, hQ⟩ := InvGTDR.q_at rF t h he hg ht E hnp
    exact noFault_QA64TDR hnf hpost t.st σ tree hQ hex

end Link

/-! ## Start -/

section Triple

variable {A : Arch} {tid : Nat} {pl : Plan} {D : Dispenser}

/-- **`QA64TDR` from a partial triple** in `EnvGTDR` at a thread state at the
start of `p`, whose exceptional exit `E` never holds. -/
theorem qa64TDR_of_partialTripleEnv [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Kraken.Executable.ValidLayout (layout p)] {P Q : MachineData → EStateA → Prop}
    {E : Int64 → MachineData → EStateA → Prop} (ht : MachineWP.PartialTripleEnv (EnvGTDRA A tid pl D) P p Q E)
    (henv : cenv = layout p) {st : State} (he : st.exe = layout p) (hds : st.decls = {})
    (hend : st.endPc = (layout p).addrOf p.length) (hpc : st.st.2 = (layout p).addrOf 0) {σ : EStateA}
    (hP : P st.st.1 σ) (hE : ∀ a s g, ¬ E a s g := by simp) :
    QA64TDR A tid pl D (layout p) ((layout p).addrOf p.length) (postOf p Q) st σ := by
  refine ⟨he, hds, hend, ?_⟩
  have hst : st.st = (st.st.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hpc, Executable.addrOf_zero, Layout.apply_fst]
  rw [hst]
  exact (Program.instrStepEnv_of_partialTripleEnv ht hP henv).mono fun _ h => h.imp id (hE _ _ _)

/-- **The rule's invariant at the initial configuration** from `QA64TDR` at
`σInit` (`coreAtR_init`; the initial views are `0`). -/
theorem invGTDR_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = []) {e : Kraken.Executable Directive} {endPc : Int64}
    {post : MachineState × EStateA → Prop}
    (hQ : QA64TDR A tid pl D e endPc post s (σInit (Config.init ss m) r g)) :
    InvGTDR (I := isa) tid pl D (QA64TDR A tid pl D e endPc post) True (Config.init ss m) r g :=
  ⟨_, _, coreAtR_init hs hpend, hQ, fun _ => by simp [Thread.init, Views.getCoh]⟩

end Triple

end Kraken.Promising.AArch64.EnvG

#print axioms Kraken.Promising.SLR.ThreadRuleRXGSXE.ofSafelyEnvGTDR
#print axioms Kraken.Promising.AArch64.EnvG.npSafeP_of_safelyEnvGTDR
#print axioms Kraken.Promising.AArch64.EnvG.noFaultRule_ofSafelyEnvGTDR_struct
#print axioms Kraken.Promising.AArch64.EnvG.invGTDR_init
