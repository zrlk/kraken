/-
Whole-thread environment (`EnvG`), phase 3: **the AArch64 link for
code with multi-write trees** (`STP` of plain stores).

- `Phase3Tree A e`: every tree of a thread running `e` with no declarations
  is phase-1, phase-2 or phase-3 (`Phase3Shape`: a prefix of loads, then a
  sequence of stores, no release-kind write). Discharged per directive
  (`phase3Tree_of_dirs`) by the `dirs_phase3 p` tactic, which tries the
  phase-1 and phase-2 checks first.
- `linkHyps3_QA64`: the hypotheses of the phase-3 rule link at `QA64` (the
  link proof of `linkHyps_QA64`, unchanged).
- `ThreadRuleRX.ofSafelyEnvG3`, `npSafe_of_safelyEnvG3`,
  `noFaultRule_ofSafelyEnvG3_struct`: `ofSafelyEnvG2` and friends with
  `Phase3Tree` for `Phase2Tree`.

Smoke test (`MultiWriteA64Smoke.lean`): `stp x1, x2, [x0]` passes
`dirs_phase3` and fails `dirs_phase2`.
-/
import Kraken.Promising.SLR.EnvG.MultiWriteRule
import Kraken.Promising.SLR.EnvG.MultiA64
import Kraken.Promising.SLR.EnvG.A64Answers

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## Tree shapes along `EvTree.map` -/

theorem writesOnly_map {Sok : Loc → Val → Prop} {σ τ : Type} (f : σ → τ) (t : EvTree σ) (h : WritesOnly Sok t) :
    WritesOnly Sok (t.map f) := by
  induction t with
  | done _ => trivial
  | fault _ => trivial
  | choose _ _ ih => exact fun i => ih i (h i)
  | fence _ _ ih => exact ih () h
  | load _ _ _ _ _ => exact h.elim
  | store _ _ _ _ _ ih => exact ⟨h.1, fun b => ih b (h.2 b)⟩
  | rmw _ _ _ _ _ _ => exact h.elim

theorem multiWriteS_map {Lok : Prop} {Sok : Loc → Val → Prop} {Rok : RmwKind → Prop} {D : Prop} {σ τ : Type}
    (f : σ → τ) (t : EvTree σ) (h : MultiWriteS Lok Sok Rok D t) : MultiWriteS Lok Sok Rok D (t.map f) := by
  induction t with
  | done _ => exact h
  | fault _ => trivial
  | choose _ _ ih => exact fun i => ih i (h i)
  | fence _ _ ih => exact ih () h
  | load _ _ _ _ ih => exact ⟨h.1, fun v => ih v (h.2 v)⟩
  | store _ _ _ _ _ _ => exact ⟨h.1, fun b => writesOnly_map f _ (h.2 b)⟩
  | rmw _ _ _ _ _ _ => exact ⟨h.1, fun v => (accessFree_map f _).mpr (h.2 v)⟩

theorem phase3Shape_map {A : Arch} {σ τ : Type} (f : σ → τ) {t : EvTree σ} (h : Phase3Shape A t) :
    Phase3Shape A (t.map f) :=
  ⟨multiWriteS_map f t h.1, noRelWrite_map f t h.2⟩

/-! ## The phase-3 shape of the code -/

/-- **The phase-3 shape of the code** (stated hypothesis, or
`phase3Tree_of_dirs`): every tree of a thread state running `e` with no
declarations is phase-1, phase-2 or phase-3. -/
def Phase3Tree (A : Arch) (e : Kraken.Executable Directive) : Prop :=
  ∀ st : State, st.exe = e → st.decls = {} → ∀ tree, isa.exec st = some tree →
    Phase1Shape A tree ∨ Phase2Shape A tree ∨ Phase3Shape A tree

/-- Phase-2 code is phase-3 code. -/
theorem Phase2Tree.to3 {A : Arch} {e : Kraken.Executable Directive} (h : Phase2Tree A e) : Phase3Tree A e :=
  fun st he hds tree hex => (h st he hds tree hex).imp_right .inl

/-- The adapter's tree of the directive `d` of size `z` is phase-1, phase-2
or phase-3, from every machine state and pc (as `DirPhase2`). -/
def DirPhase3 (A : Arch) (e : _root_.Executable) (d : Directive) (z : Nat) : Prop :=
  ∀ (s : MachineData) (pc : Int64),
    Phase1Shape A (toEv {} (@Directive.interp (_root_.Executable.labels e) d s (.mk pc (pc + .ofNat z))
      (fun s' => .done (s', pc + .ofNat z)) (fun pc' s' => .done (s', pc')))) ∨
    Phase2Shape A (toEv {} (@Directive.interp (_root_.Executable.labels e) d s (.mk pc (pc + .ofNat z))
      (fun s' => .done (s', pc + .ofNat z)) (fun pc' s' => .done (s', pc')))) ∨
    Phase3Shape A (toEv {} (@Directive.interp (_root_.Executable.labels e) d s (.mk pc (pc + .ofNat z))
      (fun s' => .done (s', pc + .ofNat z)) (fun pc' s' => .done (s', pc'))))

/-- Every directive of the text has a phase-1, phase-2 or phase-3 tree. -/
def DirsPhase3 (A : Arch) (e : _root_.Executable) : Prop :=
  ∀ d z, (d, z) ∈ e.2 → DirPhase3 A e d z

/-- **`Phase3Tree` from the per-directive check.** -/
theorem phase3Tree_of_dirs {A : Arch} {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
    (h : DirsPhase3 A e) : Phase3Tree A e :=
  fun _ he hds _ htree => tree_of_codeAt
    (Φ := fun t => Phase1Shape A t ∨ Phase2Shape A t ∨ Phase3Shape A t)
    (fun f _ ht => ht.imp (phase1Shape_map f) (Or.imp (phase2Shape_map f) (phase3Shape_map f)))
    (fun d z hm => h d z hm) he hds htree

/-- The directives of a laid-out program are the program's (as
`dirsPhase2_layout`). -/
theorem dirsPhase3_layout [layout : _root_.Layout] {A : Arch} {p : Program}
    (h : ∀ d ∈ p, ∀ (e : _root_.Executable) z, DirPhase3 A e d z) : DirsPhase3 A (layout p) := by
  intro d z hm
  obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact h _ (List.getElem_mem hi) _ _

set_option hygiene false in
/-- `dirs_phase3 p` proves `DirsPhase3 A (layout p)` for a program `p` (a
definition): per directive, the phase-1 `simp` of `dirs_phase1`, else the
phase-2 one of `dirs_phase2`, else the phase-3 one (a load prefix, then
stores, no release-kind write). -/
macro "dirs_phase3 " p:ident : tactic => `(tactic| (
  refine Kraken.Promising.AArch64.EnvG.dirsPhase3_layout (p := $p) ?_
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
    | (refine Or.inr (Or.inl ?_)
       simp [Kraken.Promising.AArch64.toEv, Kraken.Promising.SLR.EnvG.Phase2Shape,
         Kraken.Promising.SLR.EnvG.MultiAccessS, Kraken.Promising.SLR.EnvG.NoRelWrite,
         Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty]
       repeat' (first | split |
         simp [Kraken.Promising.AArch64.toEv, Kraken.Promising.SLR.EnvG.Phase2Shape,
           Kraken.Promising.SLR.EnvG.MultiAccessS, Kraken.Promising.SLR.EnvG.NoRelWrite,
           Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty])
       done)
    | (refine Or.inr (Or.inr ?_)
       simp [Kraken.Promising.AArch64.toEv, Kraken.Promising.SLR.EnvG.Phase3Shape,
         Kraken.Promising.SLR.EnvG.MultiWriteS, Kraken.Promising.SLR.EnvG.WritesOnly,
         Kraken.Promising.SLR.EnvG.NoRelWrite, Kraken.Promising.Arch.storeKind, Kraken.Promising.Arch.armv8,
         Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty]
       repeat' (first | split |
         simp [Kraken.Promising.AArch64.toEv, Kraken.Promising.SLR.EnvG.Phase3Shape,
           Kraken.Promising.SLR.EnvG.MultiWriteS, Kraken.Promising.SLR.EnvG.WritesOnly,
           Kraken.Promising.SLR.EnvG.NoRelWrite, Kraken.Promising.Arch.storeKind, Kraken.Promising.Arch.armv8,
           Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty])
       done)))

/-! ## The link -/

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
  {endPc : Int64} {post : MachineState × EStateA → Prop}

/-- **The phase-3 link hypotheses at `QA64`** (the link proof of
`linkHyps_QA64`). -/
theorem linkHyps3_QA64 (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase3Tree A e)
    (hpost : ∀ y, post y → y.1.2 = endPc) : LinkHyps3 (I := isa) A tid pl (QA64 A tid pl e endPc post) where
  valid := hpl
  shape st _ h tree hex := hshape st h.1 h.2.1 tree hex
  link J st σ tree h hex hJ := by
    obtain ⟨he, hds, hend, hsafe⟩ := h
    rcases hsafe.unfold with hp | ⟨R, hR, hk⟩
    · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
      rw [this] at hex; cases hex
    · exact exec_treeJLive_of_instrStepEnv' J he hds hR (fun m g' hz => hJ _ _ ⟨he, hds, hend, hk _ hz⟩) hlive
        tree hex

/-- **`ThreadRuleRX.ofSafelyEnvG3`**: `ofSafelyEnvG` for code with phase-3
trees (`Phase3Tree`). -/
def _root_.Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvG3 {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase3Tree A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRX A B tid :=
  ThreadRuleRX.ofEnvG3 (linkHyps3_QA64 (tid := tid) hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64 hstuck hQ hh) hp hrel hcl

/-- **`NPSafe` from a `Safely` judgment of `EnvG`, phase-3 code**
(`NPSafe.of_ruleRX` at `ofSafelyEnvG3`). -/
theorem npSafe_of_safelyEnvG3 {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase3Tree A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvG (I := isa) A tid pl (QA64 A tid pl e endPc post) cl c r g) :
    NPSafe (model isa) A B tid n m cl c r g :=
  NPSafe.of_ruleRX (ThreadRuleRX.ofSafelyEnvG3 hpl hlive hshape hpost hstuck hB) n m cl c r g h

/-- **The AArch64 phase-3 no-fault rule**: `NoFaultRule (ofSafelyEnvG3 …)`
for fault-free code (`DirsNoFault e`), with or without promises. -/
theorem noFaultRule_ofSafelyEnvG3_struct {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase3Tree A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRule (ThreadRuleRX.ofSafelyEnvG3 hpl hlive hshape hpost hstuck hB) :=
  noFaultRule_ofEnvG3_struct _ _ (noFault_QA64 hnf hpost)

end Link

end Kraken.Promising.AArch64.EnvG
