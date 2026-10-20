/-
**Part 1: the x64 link of the adjacency
environment `EnvGCAdj`** (`EnvG/AdjCore.lean`: `EnvGC` whose release
obligation at an RMW may assume own-message adjacency `AdjAt`), with failing
in-flight release RMWs (F × C): `ThreadRuleRXF.ofSafelyEnvGFCAdjX`, the x64
counterpart of the adjacency link's `ThreadRuleRXF.ofSafelyEnvGFCAdj`
(`EnvG/AdjSpikeA64.lean`), built from the ISA-neutral rule link
`ThreadRuleRXF.ofEnvGFCAdj` (`EnvG/AdjSpikeRule.lean`) exactly as the x64 Treiber proof
built `ofSafelyEnvGFCX` (`EnvG/X64RmwFailGhost.lean`) from `ofEnvGFC`.

- **The environment** `EnvGCAdjX A tid pl S := (EnvGCAdj isa A tid pl).within S`
  and its invariant `QX64CAdj` (`QX64C` with `EnvGCAdjX`); the shape is
  the x64 `cmpxchg` lock proof's `Phase1TreeFX` (single-access trees, `lock cmpxchg` admitted).
- **x64 RMWs.** Every x64 RMW event is `.acqRel` and claims unconditionally
  (`claimSlotsC_acqRel`, `EnvG/X64RmwGhostLink.lean`). `RmwOkCAdj` and
  `AdjAt` are stated for any RMW kind and any profile, and the neutral link
  derives `AdjAt` from `readSuccs` at the RMW's read views (under `Arch.tso`
  `rmwReadViews` is the full fence first; `adj_of_readSuccs` takes any
  instruction views): so they apply on x64 unchanged, with no x64 lemma.
  `within S` changes only `ok`, and the x64 run lemma
  `exec_treeJLive_of_instrStepEnvW` is generic in the environment.

Contents: `EnvGCAdjX`, `QX64CAdj`, `linkHypsFCAdj_QX64CAdj`,
`post_of_halted_QX64CAdj`, **`ThreadRuleRXF.ofSafelyEnvGFCAdjX`**,
`npSafeF_of_safelyEnvGFCAdjX`, `noFault_QX64CAdj`,
`noFaultRuleF_ofSafelyEnvGFCAdjX_struct` (from `DirsNoFault`, unconditional in
the thread's promises), `qx64CAdj_of_partialTripleEnv`, `invGFCAdjX_init`.
Theorem 1′ for the rule is `theorem1FChain`; on x64 its assembly is
`CmpxPublic.final_of_relPureSafelyQX_tsoF'` (`EnvG/RelPureEnvX64F.lean`).

Phase-1 limits otherwise apply: single-access trees, read-side acquire only,
every access within the layout `S` (`Le16 S`); a release RMW cannot forward
what it claims.
-/
import Kraken.Promising.SLR.EnvG.AdjSpikeRule
import Kraken.Promising.SLR.EnvG.X64RmwFailGhost

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-- **`EnvGCAdj` for x64**, restricted to the shared layout `S`. -/
abbrev EnvGCAdjX (A : Arch) (tid : Nat) (pl : Plan) (S : SharedEnv.Layout) : SharedEnv :=
  (Kraken.Promising.SLR.EnvGCAdj isa A tid pl).within S

/-- **The thread-local invariant of `EnvGCAdjX`** (`QX64C` for `EnvGCAdjX`). -/
def QX64CAdj (A : Arch) (tid : Nat) (pl : Plan) (S : SharedEnv.Layout) (e : Kraken.Executable Directive)
    (endPc : Int64) (post : MachineState × EStateX → Prop) (st : State) (σ : EStateX) : Prop :=
  st.exe = e ∧ st.decls = {} ∧ st.endPc = endPc ∧ Split S st.st.1.dmem ∧
    Safely (e.instrStepEnv (EnvGCAdjX A tid pl S)) post (st.st, σ)

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout} {e : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateX → Prop}

/-- **The link hypotheses of `EnvGCAdj` at `QX64CAdj`** (`linkHypsFC_QX64C`
with `EnvGCAdjX`; `linkHypsFCAdj_QA64CAdj`, x64). -/
theorem linkHypsFCAdj_QX64CAdj (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeFX e)
    (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsFCAdj (I := isa) A tid pl (QX64CAdj A tid pl S e endPc post) where
  valid := hpl
  shape st _ h tree hex := hshape st h.1 h.2.1 tree hex
  link J st σ tree h hex hJ := by
    obtain ⟨he, hds, hend, hs, hsafe⟩ := h
    rcases hsafe.unfold with hp | ⟨R, hR, hk⟩
    · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
      rw [this] at hex; cases hex
    · exact exec_treeJLive_of_instrStepEnvW J hS he hds hs hR
        (fun m g' hz hs' => hJ _ _ ⟨he, hds, hend, hs', hk _ hz⟩) tree hex

omit [Kraken.Executable.ValidLayout e] in
/-- **`done` at `QX64CAdj`** (`post_of_halted_QX64C`). -/
theorem post_of_halted_QX64CAdj (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGCAdjX A tid pl S) x R)
    {t : Thread isa} {σ : EStateX} (hQ : QX64CAdj A tid pl S e endPc post t.st σ) (hh : t.halted = true) :
    post (t.st.st, σ) := by
  obtain ⟨he, -, hend, -, hsafe⟩ := hQ
  refine hsafe.post_of_stuck fun R hR => ?_
  have hdir := directive_isSome_of_instrStepEnv he hR
  have hh' : (exec t.st).isNone = true := hh
  unfold exec at hh'
  split at hh'
  · next hc =>
    simp only [Bool.or_eq_true, beq_iff_eq] at hc
    rcases hc with hc | hc
    · exact hstuck _ R (by rw [← hend]; exact hc) hR
    · rw [Option.isNone_iff_eq_none] at hc
      rw [hc] at hdir; cases hdir
  · cases hh'

/-- **`ThreadRuleRXF.ofSafelyEnvGFCAdjX`**: the x64 rule link of `EnvGCAdj`
(`ofSafelyEnvGFCX` with adjacency in the release obligation;
`ofSafelyEnvGFCAdj`, x64). Gives `ThreadRuleRXF`, hence `NPSafeF`. -/
def _root_.Kraken.Promising.SLR.EnvG.ThreadRuleRXF.ofSafelyEnvGFCAdjX
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeFX e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGCAdjX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXF A B tid :=
  ThreadRuleRXF.ofEnvGFCAdj (linkHypsFCAdj_QX64CAdj (tid := tid) hpl hS hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QX64CAdj hstuck hQ hh) hp hrel hcl

/-- **`NPSafeF` from a `Safely` judgment of `EnvGCAdjX`**
(`NPSafeF.of_ruleRXF` at `ofSafelyEnvGFCAdjX`). -/
theorem npSafeF_of_safelyEnvGFCAdjX {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeFX e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGCAdjX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvGF (I := isa) tid pl (QX64CAdj A tid pl S e endPc post) cl c r g) :
    NPSafeF (model isa) A B tid n m cl c r g :=
  NPSafeF.of_ruleRXF (ThreadRuleRXF.ofSafelyEnvGFCAdjX hpl hS hshape hpost hstuck hB) n m cl c r g h

/-- **Every tree from a `QX64CAdj`-state is fault-free**, for fault-free code
(`noFault_QX64C`). -/
theorem noFault_QX64CAdj (hnf : DirsNoFault e) (hpost : ∀ y, post y → y.1.2 = endPc) :
    ∀ st σ tree, QX64CAdj A tid pl S e endPc post st σ → isa.exec st = some tree → tree.NoFault := by
  intro st σ tree h hex
  obtain ⟨he, hds, hend, -, hsafe⟩ := h
  rcases hsafe.unfold with hp | -
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · exact noFault_of_exec he hds hnf tree hex

/-- **The x64 no-fault rule of the `EnvGCAdj` link**, unconditional in the
thread's promises, for fault-free code (`DirsNoFault e`;
`noFaultRuleF_ofSafelyEnvGFCAdj_struct`, x64). -/
theorem noFaultRuleF_ofSafelyEnvGFCAdjX_struct {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeFX e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGCAdjX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRuleF (ThreadRuleRXF.ofSafelyEnvGFCAdjX hpl hS hshape hpost hstuck hB) :=
  noFaultRuleF_ofEnvGFCAdj_struct _ _ (noFault_QX64CAdj hnf hpost)

end Link

/-! ## The start -/

section Start

variable {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout}

/-- **`QX64CAdj` from a partial triple** in `EnvGCAdjX`
(`qx64C_of_partialTripleEnv` for `EnvGCAdjX`). -/
theorem qx64CAdj_of_partialTripleEnv [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Kraken.Executable.ValidLayout (layout p)] {P Q : MachineData → EStateX → Prop}
    {E : Int64 → MachineData → EStateX → Prop} (ht : MachineWP.PartialTripleEnv (EnvGCAdjX A tid pl S) P p Q E)
    (henv : cenv = layout p) {st : State} (he : st.exe = layout p) (hds : st.decls = {})
    (hend : st.endPc = (layout p).addrOf p.length) (hpc : st.st.2 = (layout p).addrOf 0)
    (hs : Split S st.st.1.dmem) {σ : EStateX}
    (hP : P st.st.1 σ) (hE : ∀ a s g, ¬ E a s g := by simp) :
    QX64CAdj A tid pl S (layout p) ((layout p).addrOf p.length) (postOfX p Q) st σ := by
  refine ⟨he, hds, hend, hs, ?_⟩
  have hst : st.st = (st.st.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hpc, Executable.addrOf_zero, Layout.apply_fst]
  rw [hst]
  exact (Program.instrStepEnv_of_partialTripleEnv ht hP henv).mono fun _ h => h.imp id (hE _ _ _)

/-- **The rule's invariant of the x64 `EnvGCAdj` link at the initial
configuration**, from `QX64CAdj` at `σInitX` (`invGFCX_init`,
`invGFCAdj_init`, x64). -/
theorem invGFCAdjX_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = []) {e : Kraken.Executable Directive} {endPc : Int64}
    {post : MachineState × EStateX → Prop}
    (hQ : QX64CAdj A tid pl S e endPc post s (σInitX (Config.init ss m) r g)) :
    InvGF (I := isa) tid pl (QX64CAdj A tid pl S e endPc post) True (Config.init ss m) r g :=
  ⟨σInitX (Config.init ss m) r g, Thread.init s, coreAtFX_init hs hpend, hQ⟩

end Start

end Kraken.Promising.X64.EnvG

#print axioms Kraken.Promising.SLR.EnvG.ThreadRuleRXF.ofSafelyEnvGFCAdjX
#print axioms Kraken.Promising.X64.EnvG.npSafeF_of_safelyEnvGFCAdjX
#print axioms Kraken.Promising.X64.EnvG.noFaultRuleF_ofSafelyEnvGFCAdjX_struct
#print axioms Kraken.Promising.X64.EnvG.qx64CAdj_of_partialTripleEnv
#print axioms Kraken.Promising.X64.EnvG.invGFCAdjX_init
