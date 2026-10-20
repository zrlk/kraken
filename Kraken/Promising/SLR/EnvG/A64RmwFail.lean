/-
The failing-RMW route, part 4: **the AArch64 link with failing
in-flight release RMWs** `ThreadRuleRXF.ofSafelyEnvGF`, beside
`ThreadRuleRX.ofSafelyEnvGR` (`EnvG/A64LinkR.lean`). Copies of
`A64LinkR`'s shape check, link and initial state with `Phase1ShapeF` (no
totality) and the `F` rule link (`EnvG/RmwFailRuleLink.lean`); `QA64R` is
reused.

The rule gives `NPSafeF`, which is Theorem 1′'s per-thread hypothesis only
once the open `Theorem1FChain` (`EnvG/RmwFailRule.lean`) is proved. No-fault:
`noFaultRuleF_ofSafelyEnvGF_struct` (`NoFaultRuleF`, the same structural
argument as `noFaultRule_ofSafelyEnvGR_struct`).

`dirs_phase1F p` decides `DirsPhase1F (layout p)`; it accepts `casal`
(`RmwFailSmoke.lean`).
-/
import Kraken.Promising.SLR.EnvG.A64LinkR
import Kraken.Promising.SLR.EnvG.RmwFailRuleLink

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-- **The phase-1 shape of the code with failing release RMWs** (stated
hypothesis, or `phase1TreeF_of_dirs`): every tree of a thread state running
`e` with no declarations is a deterministic single access (RMWs of any kind
and operation). -/
def Phase1TreeF (e : Kraken.Executable Directive) : Prop :=
  ∀ st : State, st.exe = e → st.decls = {} → ∀ tree, isa.exec st = some tree → Phase1ShapeF tree

/-- `R` phase-1 code is phase-1 code with failing release RMWs. -/
theorem Phase1TreeR.toF {A : Arch} {e : Kraken.Executable Directive} (h : Phase1TreeR A e) : Phase1TreeF e :=
  fun st he hds tree hex => (h st he hds tree hex).toF

/-- The adapter's tree of the directive `d` of size `z` is phase-1 with
failing release RMWs, from every machine state and pc (`DirPhase1`). -/
def DirPhase1F (e : _root_.Executable) (d : Directive) (z : Nat) : Prop :=
  ∀ (s : MachineData) (pc : Int64),
    Phase1ShapeF (toEv {} (@Directive.interp (_root_.Executable.labels e) d s (.mk pc (pc + .ofNat z))
      (fun s' => .done (s', pc + .ofNat z)) (fun pc' s' => .done (s', pc'))))

/-- Every directive of the text has a phase-1 tree with failing release RMWs. -/
def DirsPhase1F (e : _root_.Executable) : Prop :=
  ∀ d z, (d, z) ∈ e.2 → DirPhase1F e d z

/-- **`Phase1TreeR` from the per-directive check.** -/
theorem phase1TreeF_of_dirs {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
    (h : DirsPhase1F e) : Phase1TreeF e :=
  fun _ he hds _ htree => tree_of_codeAt (Φ := Phase1ShapeF) (fun f _ ht => phase1ShapeF_map f ht)
    (fun d z hm => h d z hm) he hds htree

/-- `R` per-directive phase-1 code is `F` per-directive phase-1 code. -/
theorem DirsPhase1R.toF {A : Arch} {e : _root_.Executable} (h : DirsPhase1R A e) : DirsPhase1F e :=
  fun d z hm s pc => (h d z hm s pc).toF

/-- The directives of a laid-out program are the program's
(`dirsPhase1_layout`). -/
theorem dirsPhase1F_layout [layout : _root_.Layout] {p : Program}
    (h : ∀ d ∈ p, ∀ (e : _root_.Executable) z, DirPhase1F e d z) : DirsPhase1F (layout p) := by
  intro d z hm
  obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact h _ (List.getElem_mem hi) _ _

set_option hygiene false in
/-- `dirs_phase1F p` proves `DirsPhase1F (layout p)` for a program `p` (a
definition) whose instructions make at most one access, deterministically
(RMWs of any kind and operation, `casal` included): one `simp` per
directive, as `dirs_phase1R`. -/
macro "dirs_phase1F " p:ident : tactic => `(tactic| (
  refine Kraken.Promising.AArch64.EnvG.dirsPhase1F_layout (p := $p) ?_
  intro d hd e z s pc
  simp only [$p:ident, List.mem_cons, List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals simp [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    Kraken.Promising.AArch64.toEv, Kraken.Promising.SLR.EnvG.Phase1ShapeF, Kraken.Promising.SLR.EnvG.DetAccess,
    Kraken.Promising.SLR.EnvG.SingleAccessS2, Kraken.Promising.SLR.EnvG.AccessFree,
    _root_.MachineData.load, _root_.MachineData.store,
    _root_.MachineData.loadK, _root_.MachineData.storeK, _root_.MachineData.rmwK,
    _root_.MachineData.setRegOrZr, _root_.MachineData.setRegOrSp, _root_.RegOrSp.interpBase,
    _root_.AddrExpr.checkSPAlignment, _root_.AddrExpr.interpLoad, _root_.AddrExpr.interpStore,
    _root_.UnscaledAddrExpr.interpStore,
    _root_.UnscaledAddrExpr.checkSPAlignment, _root_.UnscaledAddrExpr.interpLoad,
    _root_.Literal.interpLoad, _root_.AddrOrLit.interpLoad,
    Kraken.Promising.EvTree.access_empty]
  all_goals (repeat' (first | split |
    simp [Kraken.Promising.AArch64.toEv, Kraken.Promising.SLR.EnvG.Phase1ShapeF,
      Kraken.Promising.SLR.EnvG.DetAccess, Kraken.Promising.SLR.EnvG.SingleAccessS2,
      Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty]))))

/-! ## The link -/

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
  {endPc : Int64} {post : MachineState × EStateA → Prop} {rel₀ : Loc → Pred}

/-- **The link hypotheses with failing release RMWs at `QA64R`** (as
`linkHyps_QA64`, through `link_relFix`). -/
theorem linkHypsF_QA64 (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeF e)
    (hG : RelRmwGiveOk isa pl rel₀) (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsF (I := isa) A tid pl (QA64R A tid pl e endPc post rel₀) where
  valid := hpl
  shape st _ h tree hex := hshape st h.1.1 h.1.2.1 tree hex
  giveOk _ _ h := h.2 ▸ hG
  link := link_relFix rel₀ fun J st σ tree h hex hJ => by
    obtain ⟨he, hds, hend, hsafe⟩ := h
    rcases hsafe.unfold with hp | ⟨R, hR, hk⟩
    · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
      rw [this] at hex; cases hex
    · exact exec_treeJLive_of_instrStepEnv' J he hds hR (fun m g' hz => hJ _ _ ⟨he, hds, hend, hk _ hz⟩) hlive
        tree hex

/-- **`ThreadRuleRXF.ofSafelyEnvGF`**: the AArch64 rule link with
failing release RMWs (`ofSafelyEnvGR` with `Phase1TreeF`, the give-away side
condition at the release predicates `rel₀`, and the invariant `QA64R`). -/
def _root_.Kraken.Promising.SLR.EnvG.ThreadRuleRXF.ofSafelyEnvGF
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeF e) (hG : RelRmwGiveOk isa pl rel₀)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXF A B tid :=
  ThreadRuleRXF.ofEnvGF (linkHypsF_QA64 (tid := tid) hpl hlive hshape hG hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64 hstuck hQ.1 hh) hp hrel hcl

/-- **`NPSafeF` from a `Safely` judgment of `EnvG` with failing release RMWs**
(`NPSafeF.of_ruleRXF` at `ofSafelyEnvGF`). -/
theorem npSafeF_of_safelyEnvGF {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeF e) (hG : RelRmwGiveOk isa pl rel₀)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvGF (I := isa) tid pl (QA64R A tid pl e endPc post rel₀) cl c r g) :
    NPSafeF (model isa) A B tid n m cl c r g :=
  NPSafeF.of_ruleRXF (ThreadRuleRXF.ofSafelyEnvGF hpl hlive hshape hG hpost hstuck hB) n m cl c r g h

/-- **The AArch64 no-fault rule for the `F` link** from fault-free code
(`DirsNoFault e`), as `noFaultRule_ofSafelyEnvGR_struct`. -/
theorem noFaultRuleF_ofSafelyEnvGF_struct {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeF e) (hG : RelRmwGiveOk isa pl rel₀)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRuleF (ThreadRuleRXF.ofSafelyEnvGF hpl hlive hshape hG hpost hstuck hB) :=
  noFaultRuleF_ofEnvGF_struct _ _ fun st σ tree hQ hex => noFault_QA64 hnf hpost st σ tree hQ.1 hex

end Link


/-! ## The initial state -/

section Init

variable {A : Arch} {tid : Nat} {pl : Plan}

/-- **The invariant core with failing release RMWs at the initial
configuration** (the proof of `coreAt_init`). -/
theorem coreAtF_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = []) :
    CoreAtF tid pl True (Config.init ss m) r g (σInit (Config.init ss m) r g) (Thread.init s) := by
  have ht : (Config.init ss m : Config isa).threads[tid]? = some (Thread.init s) := by simp [Config.init, hs]
  refine ⟨⟨ht, SnapLe.refl _ _, Ghost.Le.refl g, ?_, Config.init_bnd ss m tid _ ht,
    .inl ⟨rfl, fun _ h => (by cases h)⟩, fun _ => trivial, ⟨fun h => (by cases h), fun h => (by cases h)⟩⟩,
    fun ts h => (by rw [hpend] at h; cases h), fun ts _ _ h => (by cases h)⟩
  refine ⟨fun l => by simp [σInit, Thread.init, Views.getCoh], Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
    Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, fun l => ?_, ?_⟩ <;>
    simp [σInit, Thread.init, Views.getFwd, Sim.FwdLe, Sim.XclLe]

/-- **The rule's invariant with failing release RMWs at the initial
configuration** from `QA64` at `σInit` (the release predicates are the
ghost's). -/
theorem invGF_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = []) {e : Kraken.Executable Directive} {endPc : Int64}
    {post : MachineState × EStateA → Prop} (hQ : QA64 A tid pl e endPc post s (σInit (Config.init ss m) r g)) :
    InvGF (I := isa) tid pl (QA64R A tid pl e endPc post g.rel) True (Config.init ss m) r g :=
  ⟨σInit (Config.init ss m) r g, Thread.init s, coreAtF_init hs hpend, hQ, rfl⟩

end Init

end Kraken.Promising.AArch64.EnvG
