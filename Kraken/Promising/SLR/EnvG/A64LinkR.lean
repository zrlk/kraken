/-
Whole-thread environment (`EnvG`): **the AArch64 link with
release-kind RMWs** `ThreadRuleRX.ofSafelyEnvGR`, additively beside
`ThreadRuleRX.ofSafelyEnvG` (`EnvG/A64Link.lean`), lifting the phase-1
limit "releases are stores".

It is the rule link with release-kind RMWs (`ThreadRuleRX.ofEnvGR`,
`EnvG/RuleLink.lean`) at

  `QA64R … rel₀ st σ := QA64 … st σ ∧ σ.g.rel = rel₀`

(`QA64` with the env's release predicates fixed: every `EnvG` step keeps
them, `link_relFix`), with `LinkHypsR` from `exec_treeJLive_of_instrStepEnv'`
as for `QA64`, the static check `e.rmwLive`, the shape `Phase1TreeR` and the
give-away side condition `RelRmwGiveOk isa pl rel₀`.

## Phase-1 limits (`KNOWN_GAPS.md`)

1. **An in-flight release RMW never fails** (`Phase1ShapeR`: a release-kind
   RMW's operation is total, `∀ x, op x ≠ none`). A failing RMW (a `casal`
   whose comparison fails, x64 `cmpxchg`) would leave its prepaid promise
   outstanding after the instruction, which the rule's `wp` forbids
   (`EnvG/LinkR.lean`). `swpal`, `ldaddl` and the other `ld<op>l` are total;
   `casal` releases are excluded.
2. **Planned-release RMWs claim nothing given away** (`RelRmwGiveOk I pl
   rel₀`): the update slots an RMW claims carry nothing at the locations a
   planned release of its written value gives away. The RMW's write is
   prepaid like a store (no claim at promise time), and at fulfilment the
   claimed slots join the thread's resource, which must still be the
   frozen `Inflight`'s `pl.after l v ts σ.r` (`Plan.after_op_claim`).
   Trivial for plans whose releases give nothing away
   (`RelRmwGiveOk.of_gives_nil`); in general a program obligation.

## Contents

- `Phase1TreeR`, `Phase1Tree.toR`; the per-directive check `DirsPhase1R`
  (`phase1TreeR_of_dirs`, tactic `dirs_phase1R p`, as for `dirs_phase1`).
- `QA64R`, `linkHypsR_QA64`, `ThreadRuleRX.ofSafelyEnvGR`,
  `npSafe_of_safelyEnvGR`.
- No-fault: `noFaultRule_ofEnvGR_struct` (ISA-neutral, as
  `noFaultRule_ofEnvG_struct`), `noFaultRule_ofSafelyEnvGR_struct` from
  fault-free code (`DirsNoFault e`).
- The initial invariant `invGR_init`.
-/
import Kraken.Promising.SLR.EnvG.SafelyBridge
import Kraken.Promising.SLR.EnvG.A64Answers
import Kraken.Promising.SLR.EnvG.TreeMap
import Kraken.Promising.SLR.EnvG.LinkRNoFault

/-! ## The no-fault rule with release-kind RMWs (ISA-neutral): `InvGR.q_at`,
`noFaultRule_ofEnvGR_struct` are in `EnvG/LinkRNoFault.lean` (moved there) -/

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## The phase-1 shape with release-kind RMWs -/

/-- **The phase-1 shape of the code with release-kind RMWs** (stated
hypothesis, or `phase1TreeR_of_dirs`): every tree of a thread state running
`e` with no declarations is a deterministic single access whose release-kind
RMW, if any, never fails. -/
def Phase1TreeR (A : Arch) (e : Kraken.Executable Directive) : Prop :=
  ∀ st : State, st.exe = e → st.decls = {} → ∀ tree, isa.exec st = some tree → Phase1ShapeR A tree

/-- Plain phase-1 code is phase-1 code with release-kind RMWs. -/
theorem Phase1Tree.toR {A : Arch} {e : Kraken.Executable Directive} (h : Phase1Tree A e) : Phase1TreeR A e :=
  fun st he hds tree hex => (h st he hds tree hex).toR

-- `singleAccessS2_map`, `phase1ShapeR_map`: `EnvG/TreeMap.lean` (moved there).

/-- The adapter's tree of the directive `d` of size `z` is phase-1 with
release-kind RMWs, from every machine state and pc (`DirPhase1`). -/
def DirPhase1R (A : Arch) (e : _root_.Executable) (d : Directive) (z : Nat) : Prop :=
  ∀ (s : MachineData) (pc : Int64),
    Phase1ShapeR A (toEv {} (@Directive.interp (_root_.Executable.labels e) d s (.mk pc (pc + .ofNat z))
      (fun s' => .done (s', pc + .ofNat z)) (fun pc' s' => .done (s', pc'))))

/-- Every directive of the text has a phase-1 tree with release-kind RMWs. -/
def DirsPhase1R (A : Arch) (e : _root_.Executable) : Prop :=
  ∀ d z, (d, z) ∈ e.2 → DirPhase1R A e d z

/-- **`Phase1TreeR` from the per-directive check.** -/
theorem phase1TreeR_of_dirs {A : Arch} {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
    (h : DirsPhase1R A e) : Phase1TreeR A e :=
  fun _ he hds _ htree => tree_of_codeAt (Φ := Phase1ShapeR A) (fun f _ ht => phase1ShapeR_map f ht)
    (fun d z hm => h d z hm) he hds htree

/-- Plain per-directive phase-1 code is phase-1 code with release-kind RMWs. -/
theorem DirsPhase1.toR {A : Arch} {e : _root_.Executable} (h : DirsPhase1 A e) : DirsPhase1R A e :=
  fun d z hm s pc => (h d z hm s pc).toR

/-- The directives of a laid-out program are the program's
(`dirsPhase1_layout`). -/
theorem dirsPhase1R_layout [layout : _root_.Layout] {A : Arch} {p : Program}
    (h : ∀ d ∈ p, ∀ (e : _root_.Executable) z, DirPhase1R A e d z) : DirsPhase1R A (layout p) := by
  intro d z hm
  obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact h _ (List.getElem_mem hi) _ _

set_option hygiene false in
/-- `dirs_phase1R p` proves `DirsPhase1R A (layout p)` for a program `p` (a
definition) whose instructions make at most one access, deterministically,
and whose release-kind RMWs never fail: one `simp` per directive, as
`dirs_phase1`. -/
macro "dirs_phase1R " p:ident : tactic => `(tactic| (
  refine Kraken.Promising.AArch64.EnvG.dirsPhase1R_layout (p := $p) ?_
  intro d hd e z s pc
  simp only [$p:ident, List.mem_cons, List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals simp [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    Kraken.Promising.AArch64.toEv, Kraken.Promising.SLR.EnvG.Phase1ShapeR, Kraken.Promising.SLR.EnvG.DetAccess,
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
    simp [Kraken.Promising.AArch64.toEv, Kraken.Promising.SLR.EnvG.Phase1ShapeR,
      Kraken.Promising.SLR.EnvG.DetAccess, Kraken.Promising.SLR.EnvG.SingleAccessS2,
      Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty]))))

/-! ## The link -/

/-- **The thread-local invariant with fixed release predicates**: `QA64`
and `σ.g.rel = rel₀`. -/
def QA64R (A : Arch) (tid : Nat) (pl : Plan) (e : Kraken.Executable Directive) (endPc : Int64)
    (post : MachineState × EStateA → Prop) (rel₀ : Loc → Pred) (st : State) (σ : EStateA) : Prop :=
  QA64 A tid pl e endPc post st σ ∧ σ.g.rel = rel₀

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
  {endPc : Int64} {post : MachineState × EStateA → Prop} {rel₀ : Loc → Pred}

/-- **The link hypotheses with release-kind RMWs at `QA64R`** (as
`linkHyps_QA64`, through `link_relFix`). -/
theorem linkHypsR_QA64 (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e)
    (hG : RelRmwGiveOk isa pl rel₀) (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsR (I := isa) A tid pl (QA64R A tid pl e endPc post rel₀) where
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

/-- **`ThreadRuleRX.ofSafelyEnvGR`**: the AArch64 rule link with
release-kind RMWs (`ofSafelyEnvG` with `Phase1TreeR`, the give-away side
condition at the release predicates `rel₀`, and the invariant `QA64R`). -/
def _root_.Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvGR
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e) (hG : RelRmwGiveOk isa pl rel₀)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRX A B tid :=
  ThreadRuleRX.ofEnvGR (linkHypsR_QA64 (tid := tid) hpl hlive hshape hG hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64 hstuck hQ.1 hh) hp hrel hcl

/-- **`NPSafe` from a `Safely` judgment of `EnvG` with release-kind RMWs**
(`NPSafe.of_ruleRX` at `ofSafelyEnvGR`). -/
theorem npSafe_of_safelyEnvGR {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e) (hG : RelRmwGiveOk isa pl rel₀)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvGR (I := isa) tid pl (QA64R A tid pl e endPc post rel₀) cl c r g) :
    NPSafe (model isa) A B tid n m cl c r g :=
  NPSafe.of_ruleRX (ThreadRuleRX.ofSafelyEnvGR hpl hlive hshape hG hpost hstuck hB) n m cl c r g h

/-- **The AArch64 no-fault rule with release-kind RMWs**, unconditional in
the thread's promises: `NoFaultRule (ofSafelyEnvGR …)` for fault-free code
(`DirsNoFault e`), as `noFaultRule_ofSafelyEnvG_struct`. -/
theorem noFaultRule_ofSafelyEnvGR_struct {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e) (hG : RelRmwGiveOk isa pl rel₀)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRule (ThreadRuleRX.ofSafelyEnvGR hpl hlive hshape hG hpost hstuck hB) :=
  noFaultRule_ofEnvGR_struct _ _ fun st σ tree hQ hex => noFault_QA64 hnf hpost st σ tree hQ.1 hex

end Link

/-! ## The initial state -/

section Init

variable {A : Arch} {tid : Nat} {pl : Plan}

/-- **The invariant core with release-kind RMWs at the initial
configuration** (the proof of `coreAt_init`). -/
theorem coreAtR_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = []) :
    CoreAtR tid pl True (Config.init ss m) r g (σInit (Config.init ss m) r g) (Thread.init s) := by
  have ht : (Config.init ss m : Config isa).threads[tid]? = some (Thread.init s) := by simp [Config.init, hs]
  refine ⟨⟨ht, SnapLe.refl _ _, Ghost.Le.refl g, ?_, Config.init_bnd ss m tid _ ht,
    .inl ⟨rfl, fun _ h => (by cases h)⟩, fun _ => trivial, ⟨fun h => (by cases h), fun h => (by cases h)⟩⟩,
    fun ts h => (by rw [hpend] at h; cases h), fun ts _ _ h => (by cases h)⟩
  refine ⟨fun l => by simp [σInit, Thread.init, Views.getCoh], Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
    Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, fun l => ?_, ?_⟩ <;>
    simp [σInit, Thread.init, Views.getFwd, Sim.FwdLe, Sim.XclLe]

/-- **The rule's invariant with release-kind RMWs at the initial
configuration** from `QA64` at `σInit` (the release predicates are the
ghost's). -/
theorem invGR_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = []) {e : Kraken.Executable Directive} {endPc : Int64}
    {post : MachineState × EStateA → Prop} (hQ : QA64 A tid pl e endPc post s (σInit (Config.init ss m) r g)) :
    InvGR (I := isa) tid pl (QA64R A tid pl e endPc post g.rel) True (Config.init ss m) r g :=
  ⟨σInit (Config.init ss m) r g, Thread.init s, coreAtR_init hs hpend, hQ, rfl⟩

end Init

end Kraken.Promising.AArch64.EnvG
