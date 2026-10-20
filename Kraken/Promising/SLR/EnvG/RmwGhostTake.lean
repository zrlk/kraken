/-
Whole-thread environment, **Claim-conditional RMWs** part 6: the claim-conditional
environment **with taking loads**, `EnvGTC` (`EnvGC`, `EnvG/RmwGhost.lean`,
with `EnvGT`'s taking load step, `EnvG/TakeEnv.lean`), and its link
(`ThreadRuleRXGS.ofEnvGTRC`, `ThreadRuleRXGS.ofSafelyEnvGTRC`). Additive:
it composes `EnvG/TakeRLink.lean` with `EnvG/RmwGhostRule.lean`;
nothing else changes and nothing imports this file.

This is the link a relay `ldar` (take) … `swpl` (release-only, gives what it
took) needs: `ofEnvGTR` has `LinkHypsTR.giveOk` (`RelRmwGiveOk`), which a
release-only RMW giving anything away cannot satisfy; `LinkHypsTRC` has no
such field.

- `EnvGTC`: state, permissions and store/RMW/fence steps of `EnvGC`
  (definitionally), load step `LoadOutT`.
- `nodeSimT2_envGTC`: the load field is `nodeSimT_envGT`'s, the others are
  `nodeSimS2_envGC`'s (the fields agree definitionally);
  `treeJ_envGTC_eraseWPRDSR(_start)`.
- `LinkHypsTRC`, `InvGR.wpTRC`, `InvGR.prepayTRC` (from
  `InvGR.prepay_of_okAtC`), **`ThreadRuleRXGS.ofEnvGTRC : ThreadRuleRXGS G₀`**,
  `npSafeP_of_envGTRC` (frame `K2Scope AllocIds`).
- AArch64: `EnvGTCA`, `QA64TC`, `linkHypsTRC_QA64TC`, `post_of_halted_QA64TC`,
  `ThreadRuleRXGS.ofSafelyEnvGTRC`, `npSafeP_of_safelyEnvGTRC`,
  `noFaultRule_ofSafelyEnvGTRC_struct`, `invGTRC_init`.

Phase-1 limits: as `EnvG/TakeRLink.lean` except that release RMWs may give
away (from the thread's own resource) and release-only RMWs claim nothing;
a release RMW still cannot forward what it claims in the same instruction.

The ISA-neutral half (`EnvGTC` … `npSafeP_of_envGTRC`) is in
`EnvG/RmwGhostTakeCore.lean` (split; names unchanged);
this file keeps the AArch64 instance.
-/
import Kraken.Promising.SLR.EnvG.RmwGhostA64
import Kraken.Promising.SLR.EnvG.TakeRA64Link
import Kraken.Promising.SLR.EnvG.RmwGhostTakeCore

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-- `EnvGTC` for AArch64. -/
abbrev EnvGTCA (A : Arch) (tid : Nat) (pl : Plan) : SharedEnv := Kraken.Promising.SLR.EnvGTC isa A tid pl

/-- **The thread-local invariant of `EnvGTC`**: `QA64` with the `Safely`
judgment of `EnvGTC`. -/
def QA64TC (A : Arch) (tid : Nat) (pl : Plan) (e : Kraken.Executable Directive) (endPc : Int64)
    (post : MachineState × EStateA → Prop) (st : State) (σ : EStateA) : Prop :=
  st.exe = e ∧ st.decls = {} ∧ st.endPc = endPc ∧ Safely (e.instrStepEnv (EnvGTCA A tid pl)) post (st.st, σ)

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
  {endPc : Int64} {post : MachineState × EStateA → Prop}

/-- **The link hypotheses of `EnvGTC` at `QA64TC`**. -/
theorem linkHypsTRC_QA64TC (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e)
    (hpost : ∀ y, post y → y.1.2 = endPc) : LinkHypsTRC (I := isa) A tid pl (QA64TC A tid pl e endPc post) where
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
/-- **`done` at `QA64TC`**. -/
theorem post_of_halted_QA64TC (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTCA A tid pl) x R)
    {t : Thread isa} {σ : EStateA} (hQ : QA64TC A tid pl e endPc post t.st σ) (hh : t.halted = true) :
    post (t.st.st, σ) := by
  obtain ⟨he, -, hend, hsafe⟩ := hQ
  exact post_of_halted_env hstuck he hend hsafe hh

/-- **`ThreadRuleRXGS.ofSafelyEnvGTRC`**: the AArch64 rule link with taking
loads and claim-conditional RMWs (`ofSafelyEnvGTR` without the give-away side
condition, hence without fixing the release predicates). -/
def _root_.Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTRC
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTCA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGS G₀ A B tid :=
  ThreadRuleRXGS.ofEnvGTRC (linkHypsTRC_QA64TC (tid := tid) hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64TC hstuck hQ hh) hp hrel hcl

/-- **`NPSafeP` (frame `K2Scope AllocIds`) from a `Safely` judgment of
`EnvGTC`**. -/
theorem npSafeP_of_safelyEnvGTRC {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTCA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvGR (I := isa) tid pl (QA64TC A tid pl e endPc post) cl c r g) :
    NPSafeP (model isa) A B tid G₀ (K2Scope (model isa) AllocIds) n m cl c r g :=
  NPSafeP.of_ruleRXGS (ThreadRuleRXGS.ofSafelyEnvGTRC hpl hlive hshape hpost hstuck hB) n m cl c r g h

/-- **The AArch64 no-fault rule of `EnvGTC`**, unconditional in the thread's
promises, for fault-free code (`DirsNoFault e`). -/
theorem noFaultRule_ofSafelyEnvGTRC_struct {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTCA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRuleS (ThreadRuleRXGS.ofSafelyEnvGTRC hpl hlive hshape hpost hstuck hB) :=
  NoFaultRuleS.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp => by
    obtain ⟨σ, ⟨he', hds, hend, hsafe⟩⟩ := InvGR.q_at rF t h he hg ht E hnp
    rcases hsafe.unfold with hp | ⟨R, hR, -⟩
    · have := exec_eq_none_of_end (st := t.st) (by rw [hend]; exact hpost _ hp)
      rw [this] at hex; cases hex
    · obtain ⟨d, z, rest, hcode, -⟩ := id hR
      exact noFault_of_codeAt he' hds hcode (hnf d z (mem_of_codeAt hcode)) tree hex

end Link

/-- **The rule's invariant of `EnvGTC` at the initial configuration**, from
`QA64TC` at `σInit`. -/
theorem invGTRC_init {A : Arch} {tid : Nat} {pl : Plan} {ss : List isa.State} {m : List (Loc × Val)}
    {s : isa.State} (hs : ss[tid]? = some s) {r : Res} {g : Ghost} (hpend : g.pend = [])
    {e : Kraken.Executable Directive} {endPc : Int64} {post : MachineState × EStateA → Prop}
    (hQ : QA64TC A tid pl e endPc post s (σInit (Config.init ss m) r g)) :
    InvGR (I := isa) tid pl (QA64TC A tid pl e endPc post) True (Config.init ss m) r g :=
  ⟨σInit (Config.init ss m) r g, Thread.init s, coreAtR_init hs hpend, hQ⟩

end Kraken.Promising.AArch64.EnvG
