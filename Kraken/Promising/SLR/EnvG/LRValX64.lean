/-
Whole-thread environment: **the x64
link of `EnvGLRV`** (`LRX64.lean` with `EnvGLRV` in place of `EnvGLR`; the
shapes `LRTreeX`/`dirs_lrX`, the run lemma and `CoreAtLR`'s start are
reused unchanged).

- `EnvGLRVX A tid pl S := (EnvGLRV isa A tid pl).within S`, `QX64LRV`;
- `link_QX64LRV`, `linkHypsLRV_QX64`, `post_of_halted_QX64LRV`;
- `ThreadRuleRX.ofSafelyEnvGLRVX`, `npSafe_of_safelyEnvGLRVX`,
  `noFaultRule_ofSafelyEnvGLRVX_struct`;
- `qx64LRV_of_partialTripleEnv`, `invGLRVX_init`.

Limits: `EnvGLR`'s (`LRX64.lean`), plus whole plan entries (`hwhole`).
-/
import Kraken.Promising.SLR.EnvG.LRValRule
import Kraken.Promising.SLR.EnvG.LRX64

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-- **`EnvGLRV` for x64**, restricted to the shared layout `S`. -/
abbrev EnvGLRVX (A : Arch) (tid : Nat) (pl : Plan) (S : SharedEnv.Layout) : SharedEnv :=
  (Kraken.Promising.SLR.EnvGLRV isa A tid pl).within S

/-- **The thread-local invariant of `EnvGLRV`, x64** (`QX64LR` with
`EnvGLRVX`). -/
def QX64LRV (A : Arch) (tid : Nat) (pl : Plan) (S : SharedEnv.Layout) (e : Kraken.Executable Directive)
    (endPc : Int64) (post : MachineState × EStateX → Prop) (st : State) (σ : EStateX) : Prop :=
  st.exe = e ∧ st.decls = {} ∧ st.endPc = endPc ∧ Split S st.st.1.dmem ∧
    Safely (e.instrStepEnv (EnvGLRVX A tid pl S)) post (st.st, σ)

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout} {e : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateX → Prop}

/-- The link step at `QX64LRV` (`link_QX64LR`'s proof). -/
theorem link_QX64LRV (hS : Le16 S) (hpost : ∀ y, post y → y.1.2 = endPc) :
    ∀ (J : TreeJLive (Kraken.Promising.SLR.EnvGLRV isa A tid pl) isa.State) st σ tree,
      QX64LRV A tid pl S e endPc post st σ → isa.exec st = some tree →
      (∀ st' σ', QX64LRV A tid pl S e endPc post st' σ' → J.Post st' σ') → J.W tree σ := by
  intro J st σ tree h hex hJ
  obtain ⟨he, hds, hend, hs, hsafe⟩ := h
  rcases hsafe.unfold with hp | ⟨R, hR, hk⟩
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · exact exec_treeJLive_of_instrStepEnvW J hS he hds hs hR
      (fun m g' hz hs' => hJ _ _ ⟨he, hds, hend, hs', hk _ hz⟩) tree hex

/-- **The `EnvGLRV` link hypotheses at `QX64LRV`.** -/
theorem linkHypsLRV_QX64 (hpl : pl.Valid) (hwhole : ∀ e ∈ pl.entries, e.split = none) (hS : Le16 S)
    (hshape : LRTreeX A e) (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsLRV (I := isa) A tid pl (QX64LRV A tid pl S e endPc post) where
  valid := hpl
  whole := hwhole
  shape st _ h tree hex := hshape st h.1 h.2.1 tree hex
  link := link_QX64LRV hS hpost

omit [Kraken.Executable.ValidLayout e] in
/-- **`done` at `QX64LRV`.** -/
theorem post_of_halted_QX64LRV (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGLRVX A tid pl S) x R)
    {t : Thread isa} {σ : EStateX} (hQ : QX64LRV A tid pl S e endPc post t.st σ) (hh : t.halted = true) :
    post (t.st.st, σ) := by
  obtain ⟨he, -, hend, -, hsafe⟩ := hQ
  exact post_of_halted_env hstuck he hend hsafe hh

/-- **`ThreadRuleRX.ofSafelyEnvGLRVX`**: the x64 rule link of `EnvGLRV`. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvGLRVX
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hwhole : ∀ e ∈ pl.entries, e.split = none) (hS : Le16 S) (hshape : LRTreeX A e)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGLRVX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRX A B tid :=
  ThreadRuleRX.ofEnvGLRV (linkHypsLRV_QX64 (tid := tid) hpl hwhole hS hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QX64LRV hstuck hQ hh) hp hrel hcl

/-- **`NPSafe` from a `Safely` judgment of `EnvGLRVX`**. -/
theorem npSafe_of_safelyEnvGLRVX {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hwhole : ∀ e ∈ pl.entries, e.split = none) (hS : Le16 S) (hshape : LRTreeX A e)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGLRVX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvGLR (I := isa) A tid pl (QX64LRV A tid pl S e endPc post) cl c r g) :
    NPSafe (model isa) A B tid n m cl c r g :=
  NPSafe.of_ruleRX (ThreadRuleRX.ofSafelyEnvGLRVX hpl hwhole hS hshape hpost hstuck hB) n m cl c r g h

/-- **The x64 `EnvGLRV` no-fault rule** for fault-free code. -/
theorem noFaultRule_ofSafelyEnvGLRVX_struct {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hwhole : ∀ e ∈ pl.entries, e.split = none) (hS : Le16 S) (hshape : LRTreeX A e)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGLRVX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRule (ThreadRuleRX.ofSafelyEnvGLRVX hpl hwhole hS hshape hpost hstuck hB) :=
  noFaultRule_ofEnvGLRV_struct _ _ fun st σ tree h hex => by
    obtain ⟨he, hds, hend, -, hsafe⟩ := h
    rcases hsafe.unfold with hp | -
    · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
      rw [this] at hex; cases hex
    · exact noFault_of_exec he hds hnf tree hex

end Link

section Triple

variable {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout}

/-- **`QX64LRV` from a partial triple** in `EnvGLRVX`. -/
theorem qx64LRV_of_partialTripleEnv [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Kraken.Executable.ValidLayout (layout p)] {P Q : MachineData → EStateX → Prop}
    {E : Int64 → MachineData → EStateX → Prop} (ht : MachineWP.PartialTripleEnv (EnvGLRVX A tid pl S) P p Q E)
    (henv : cenv = layout p) {st : State} (he : st.exe = layout p) (hds : st.decls = {})
    (hend : st.endPc = (layout p).addrOf p.length) (hpc : st.st.2 = (layout p).addrOf 0)
    (hs : Split S st.st.1.dmem) {σ : EStateX}
    (hP : P st.st.1 σ) (hE : ∀ a s g, ¬ E a s g := by simp) :
    QX64LRV A tid pl S (layout p) ((layout p).addrOf p.length) (postOfX p Q) st σ := by
  refine ⟨he, hds, hend, hs, ?_⟩
  have hst : st.st = (st.st.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hpc, Executable.addrOf_zero, Layout.apply_fst]
  rw [hst]
  exact (Program.instrStepEnv_of_partialTripleEnv ht hP henv).mono fun _ h => h.imp id (hE _ _ _)

/-- **The `EnvGLRV` rule's invariant at the initial configuration**
(`invGLRX_init`; the core is `coreAtLRX_init`). -/
theorem invGLRVX_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = []) {e : Kraken.Executable Directive} {endPc : Int64}
    {post : MachineState × EStateX → Prop}
    (hQ : QX64LRV A tid pl S e endPc post s (σInitX (Config.init ss m) r g)) :
    InvGLR (I := isa) A tid pl (QX64LRV A tid pl S e endPc post) True (Config.init ss m) r g :=
  ⟨_, _, coreAtLRX_init hs hpend, hQ⟩

end Triple

end Kraken.Promising.X64.EnvG
