/-
Whole-thread environment (`EnvG`), phase 2: **the AArch64 link for
code with load-prefix trees** (`LDP`, `LDPSW`, `LDXP`/`LDAXP` of two
locations).

- `Phase2Tree A e`: every tree of a thread running `e` with no declarations
  is phase-1 (`Phase1Shape`) or phase-2 (`Phase2Shape`: a prefix of loads,
  then at most one access, no release-kind write). Discharged per directive
  (`phase2Tree_of_dirs`, through `tree_of_codeAt`) by the `dirs_phase2 p`
  tactic, which tries the phase-1 check of `dirs_phase1` first.
- `linkHyps2_QA64`: the hypotheses of the phase-2 rule link at `QA64` (the
  link proof of `linkHyps_QA64`, unchanged).
- `ThreadRuleRX.ofSafelyEnvG2`, `npSafe_of_safelyEnvG2`: `ofSafelyEnvG` and
  `npSafe_of_safelyEnvG` with `Phase2Tree` for `Phase1Tree`, the invariant
  the existing `InvG` at `QA64`.

Smoke test (`MultiA64Smoke.lean`): a one-instruction `ldp` program passes
`dirs_phase2` and fails `dirs_phase1`.
-/
import Kraken.Promising.SLR.EnvG.MultiRule
import Kraken.Promising.SLR.EnvG.SafelyBridge
import Kraken.Promising.SLR.EnvG.MultiCommon

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## Tree shapes along `EvTree.map`: `EnvG/MultiCommon.lean` (moved there) -/

/-! ## The phase-2 shape of the code -/

/-- **The phase-2 shape of the code** (stated hypothesis, or
`phase2Tree_of_dirs`): every tree of a thread state running `e` with no
declarations is phase-1 or phase-2. -/
def Phase2Tree (A : Arch) (e : Kraken.Executable Directive) : Prop :=
  ∀ st : State, st.exe = e → st.decls = {} → ∀ tree, isa.exec st = some tree →
    Phase1Shape A tree ∨ Phase2Shape A tree

/-- Phase-1 code is phase-2 code. -/
theorem Phase1Tree.to2 {A : Arch} {e : Kraken.Executable Directive} (h : Phase1Tree A e) : Phase2Tree A e :=
  fun st he hds tree hex => .inl (h st he hds tree hex)

/-- The adapter's tree of the directive `d` of size `z` is phase-1 or
phase-2, from every machine state and pc (as `DirPhase1`). -/
def DirPhase2 (A : Arch) (e : _root_.Executable) (d : Directive) (z : Nat) : Prop :=
  ∀ (s : MachineData) (pc : Int64),
    Phase1Shape A (toEv {} (@Directive.interp (_root_.Executable.labels e) d s (.mk pc (pc + .ofNat z))
      (fun s' => .done (s', pc + .ofNat z)) (fun pc' s' => .done (s', pc')))) ∨
    Phase2Shape A (toEv {} (@Directive.interp (_root_.Executable.labels e) d s (.mk pc (pc + .ofNat z))
      (fun s' => .done (s', pc + .ofNat z)) (fun pc' s' => .done (s', pc'))))

/-- Every directive of the text has a phase-1 or phase-2 tree. -/
def DirsPhase2 (A : Arch) (e : _root_.Executable) : Prop :=
  ∀ d z, (d, z) ∈ e.2 → DirPhase2 A e d z

/-- **`Phase2Tree` from the per-directive check.** -/
theorem phase2Tree_of_dirs {A : Arch} {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
    (h : DirsPhase2 A e) : Phase2Tree A e :=
  fun _ he hds _ htree => tree_of_codeAt (Φ := fun t => Phase1Shape A t ∨ Phase2Shape A t)
    (fun f _ ht => ht.imp (phase1Shape_map f) (phase2Shape_map f)) (fun d z hm => h d z hm) he hds htree

/-- The directives of a laid-out program are the program's (as
`dirsPhase1_layout`). -/
theorem dirsPhase2_layout [layout : _root_.Layout] {A : Arch} {p : Program}
    (h : ∀ d ∈ p, ∀ (e : _root_.Executable) z, DirPhase2 A e d z) : DirsPhase2 A (layout p) := by
  intro d z hm
  obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact h _ (List.getElem_mem hi) _ _

set_option hygiene false in
/-- `dirs_phase2 p` proves `DirsPhase2 A (layout p)` for a program `p` (a
definition): per directive, the phase-1 `simp` of `dirs_phase1`, else the
phase-2 one (a load prefix, at most one access, no release-kind write). -/
macro "dirs_phase2 " p:ident : tactic => `(tactic| (
  refine Kraken.Promising.AArch64.EnvG.dirsPhase2_layout (p := $p) ?_
  intro d hd e z s pc
  simp only [$p:ident, List.mem_cons, List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals simp only [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    _root_.MachineData.load, _root_.MachineData.store,
    _root_.MachineData.loadK, _root_.MachineData.storeK, _root_.MachineData.rmwK,
    _root_.MachineData.setRegOrZr, _root_.MachineData.setRegOrSp, _root_.RegOrSp.interpBase,
    _root_.AddrExpr.checkSPAlignment, _root_.AddrExpr.interpLoad, _root_.AddrExpr.interpStore,
    _root_.UnscaledAddrExpr.interpStore,
    _root_.UnscaledAddrExpr.checkSPAlignment, _root_.UnscaledAddrExpr.interpLoad,
    _root_.Literal.interpLoad, _root_.AddrOrLit.interpLoad]
  all_goals first
    | (refine Or.inl ?_
       simp [Kraken.Promising.AArch64.toEv, Kraken.Promising.SLR.EnvG.Phase1Shape,
         Kraken.Promising.SLR.EnvG.DetAccess, Kraken.Promising.SLR.EnvG.SingleAccessS,
         Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty]
       repeat' (first | split |
         simp [Kraken.Promising.AArch64.toEv, Kraken.Promising.SLR.EnvG.Phase1Shape,
           Kraken.Promising.SLR.EnvG.DetAccess, Kraken.Promising.SLR.EnvG.SingleAccessS,
           Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty])
       done)
    | (refine Or.inr ?_
       simp [Kraken.Promising.AArch64.toEv, Kraken.Promising.SLR.EnvG.Phase2Shape,
         Kraken.Promising.SLR.EnvG.MultiAccessS, Kraken.Promising.SLR.EnvG.NoRelWrite,
         Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty]
       repeat' (first | split |
         simp [Kraken.Promising.AArch64.toEv, Kraken.Promising.SLR.EnvG.Phase2Shape,
           Kraken.Promising.SLR.EnvG.MultiAccessS, Kraken.Promising.SLR.EnvG.NoRelWrite,
           Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty])
       done)))

/-! ## The link -/

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
  {endPc : Int64} {post : MachineState × EStateA → Prop}

/-- **The phase-2 link hypotheses at `QA64`** (the link proof of
`linkHyps_QA64`). -/
theorem linkHyps2_QA64 (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase2Tree A e)
    (hpost : ∀ y, post y → y.1.2 = endPc) : LinkHyps2 (I := isa) A tid pl (QA64 A tid pl e endPc post) where
  valid := hpl
  shape st _ h tree hex := hshape st h.1 h.2.1 tree hex
  link J st σ tree h hex hJ := by
    obtain ⟨he, hds, hend, hsafe⟩ := h
    rcases hsafe.unfold with hp | ⟨R, hR, hk⟩
    · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
      rw [this] at hex; cases hex
    · exact exec_treeJLive_of_instrStepEnv' J he hds hR (fun m g' hz => hJ _ _ ⟨he, hds, hend, hk _ hz⟩) hlive
        tree hex

/-- **`ThreadRuleRX.ofSafelyEnvG2`**: `ofSafelyEnvG` for code with phase-2
trees (`Phase2Tree`). -/
def _root_.Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvG2 {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase2Tree A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRX A B tid :=
  ThreadRuleRX.ofEnvG2 (linkHyps2_QA64 (tid := tid) hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64 hstuck hQ hh) hp hrel hcl

/-- **`NPSafe` from a `Safely` judgment of `EnvG`, phase-2 code**
(`NPSafe.of_ruleRX` at `ofSafelyEnvG2`). -/
theorem npSafe_of_safelyEnvG2 {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase2Tree A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvG (I := isa) A tid pl (QA64 A tid pl e endPc post) cl c r g) :
    NPSafe (model isa) A B tid n m cl c r g :=
  NPSafe.of_ruleRX (ThreadRuleRX.ofSafelyEnvG2 hpl hlive hshape hpost hstuck hB) n m cl c r g h

end Link

end Kraken.Promising.AArch64.EnvG
