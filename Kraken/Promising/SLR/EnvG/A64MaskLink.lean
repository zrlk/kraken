/-
**The AArch64 rule links over a masked image**. The AArch64 analogue of `EnvG/X64MaskLink.lean` and
`EnvG/X64MaskLinkTake.lean`. The device is
`EnvG/A64MaskCore.lean`'s: the thread's `Safely` judgment is over a mask
`e'` of its executable `e` (`MaskOf e e'`: the other roles' code and the
cell at the exit label replaced by data cells), and the thread runs the
whole image `e`.

- **`QA64M E e e' endPc post`**: the AArch64 invariant (`QA64`, `QA64T`,
  `QA64TU`, `QA64C`) with the `Safely` judgment over the mask. It is
  generic in the environment `E`, so one invariant serves every link
  family; at `e' = e` (`MaskOf.refl`) it is the family's own invariant.
- The generic link facts, from which each family's `LinkHyps…` is a few
  lines:
  - `QA64M.link`: one instruction of the image under a live tree judgment
    (`exec_treeJLive_of_instrStepEnv'` at the image's step that the mask's
    step is; the static check `e.rmwLive` is the image's);
  - `QA64M.shape`: a per-cell tree shape closed under `EvTree.map` needs to
    hold only of the **mask** (`Phase1Tree A e'`, `Phase1TreeF e'`: the
    thread's own cells; the pc-restricted phase-1 shape);
  - `post_of_halted_QA64M`: `done`, with the halt read off the mask
    (`hstuck` over `e'`, which holds at a masked exit cell even when the
    image has code there: the **guarded exit**);
  - `noFault_QA64M`: the trees are fault-free for a fault-free image
    (`DirsNoFault e`).
- `Safely.uncountA`: a counted `Safely` judgment forgets its counter (the
  runs of `vcgen` are counted for the spin loops' back edges).
- Families:
  - **cumulative take** (`EnvGTU`): `linkHypsTU_QA64M`,
    `ThreadRuleRXGS.ofSafelyEnvGTUM`, `npSafeP_of_safelyEnvGTUM`,
    `noFaultRule_ofSafelyEnvGTUM`, `invGTUM_init`;
  - **take** (`EnvGT`): `linkHypsT_QA64M`, `ThreadRuleRXGS.ofSafelyEnvGTM`,
    `noFaultRule_ofSafelyEnvGTM`, `invGTM_init`;
  - **plain** (`EnvG`): `linkHyps_QA64M`, `ThreadRuleRX.ofSafelyEnvGM`,
    `noFaultRule_ofSafelyEnvGM`, `invGM_init`;
  - **`FC`** (`EnvGC` with failing release RMWs): `linkHypsFC_QA64M`,
    `ThreadRuleRXF.ofSafelyEnvGFCM`, `noFaultRuleF_ofSafelyEnvGFCM`,
    `invGFCM_init`.

Phase-1 limits otherwise apply (single-access trees, read-side acquire
only, releases are stores), as in the families' existing links.
-/
import Kraken.Promising.SLR.EnvG.A64MaskCore
import Kraken.Promising.SLR.EnvG.TakeUA64
import Kraken.Promising.SLR.EnvG.A64Answers
import Kraken.Promising.SLR.EnvG.A64RmwFailGhost

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## The invariant and the generic link facts -/

/-- **The thread-local invariant over a mask**: the image `e`, no
declarations, the end `endPc`, and a `Safely` judgment of `E` over the mask
`e'`. -/
def QA64M (E : SharedEnv) (e e' : Kraken.Executable Directive) (endPc : Int64)
    (post : MachineState × E.State → Prop) (st : State) (σ : E.State) : Prop :=
  st.exe = e ∧ st.decls = {} ∧ st.endPc = endPc ∧ Safely (e'.instrStepEnv E) post (st.st, σ)

/-- A `Safely` judgment in `SharedEnv.counted env` is one in `env` (the
AArch64 copy of `MpInclAbs.Safely.uncountM`). -/
theorem Safely.uncountA {e : Kraken.Executable Directive} {env : SharedEnv}
    {post : MachineState × (SharedEnv.counted env).State → Prop} {x : MachineState}
    {g : (SharedEnv.counted env).State} (h : Safely (e.instrStepEnv (SharedEnv.counted env)) post (x, g)) :
    Safely (e.instrStepEnv env) (fun y => ∃ n : Nat, post (y.1, (y.2, n))) (x, g.1) := by
  have hs := h.sim
    (fun (x : MachineState × (SharedEnv.counted env).State) (y : MachineState × env.State) =>
      y = (x.1, x.2.1))
    (fun x y R hxy hT => hxy ▸ Executable.instrStepEnv_uncount hT) rfl
  refine hs.mono ?_
  rintro y ⟨x', rfl, hx⟩
  exact ⟨x'.2.2, hx⟩

section Generic

variable {E : SharedEnv} {e e' : Kraken.Executable Directive} {endPc : Int64}
  {post : MachineState × E.State → Prop}

/-- **One instruction of the image, under a live tree judgment**, from
`QA64M`: the mask's step is the image's, and the successors are again in
`QA64M`. -/
theorem QA64M.link [Kraken.Executable.ValidLayout e] (hm : MaskOf e e') (hlive : e.rmwLive = true)
    (hpost : ∀ y, post y → y.1.2 = endPc) (J : SLR.EnvG.TreeJLive E State) {st : State} {σ : E.State}
    {tree : EvTree State} (h : QA64M E e e' endPc post st σ) (hex : isa.exec st = some tree)
    (hJ : ∀ st' σ', QA64M E e e' endPc post st' σ' → J.Post st' σ') : J.W tree σ := by
  obtain ⟨he, hds, hend, hsafe⟩ := h
  rcases hsafe.unfold with hp | ⟨R, hR, hk⟩
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · exact exec_treeJLive_of_instrStepEnv' J he hds (instrStepEnv_of_mask hm hR).1
      (fun m g' hz => hJ _ _ ⟨he, hds, hend, hk _ hz⟩) hlive tree hex

/-- **The thread's tree is the masked thread's**, up to the executable in
its states: a thread in `QA64M` with a tree is at a cell the mask shares. -/
theorem QA64M.tree [Kraken.Executable.ValidLayout e] (hm : MaskOf e e') (hpost : ∀ y, post y → y.1.2 = endPc)
    {st : State} {σ : E.State} {tree : EvTree State} (h : QA64M E e e' endPc post st σ)
    (hex : isa.exec st = some tree) :
    ∃ tree', isa.exec { st with exe := e' } = some tree' ∧ tree = tree'.map fun s => { s with exe := e } := by
  obtain ⟨he, -, hend, hsafe⟩ := h
  rcases hsafe.unfold with hp | ⟨R, hR, -⟩
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · obtain ⟨-, d, z, r, r', hc, hc'⟩ := instrStepEnv_of_mask hm hR
    exact exec_of_mask hm he hc hc' hex

/-- **A per-cell tree shape of the mask holds of the thread's trees**: for
a shape `Φ` closed under `EvTree.map` that every masked thread state's tree
has (`Phase1Tree A e'` and the like). -/
theorem QA64M.shape [Kraken.Executable.ValidLayout e] (hm : MaskOf e e') (hpost : ∀ y, post y → y.1.2 = endPc)
    {Φ : ∀ {σ : Type}, EvTree σ → Prop} (hmap : ∀ {σ τ : Type} (f : σ → τ) (t : EvTree σ), Φ t → Φ (t.map f))
    (hΦ : ∀ st : State, st.exe = e' → st.decls = {} → ∀ tree, isa.exec st = some tree → Φ tree)
    {st : State} {σ : E.State} {tree : EvTree State} (h : QA64M E e e' endPc post st σ)
    (hex : isa.exec st = some tree) : Φ tree := by
  obtain ⟨tree', hex', rfl⟩ := QA64M.tree hm hpost h hex
  exact hmap _ _ (hΦ { st with exe := e' } rfl h.2.1 tree' hex')

/-- **`done` at `QA64M`**: a halted thread is at its postcondition, with the
halt read off the mask. -/
theorem post_of_halted_QA64M (hm : MaskOf e e')
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv E x R)
    {t : Thread isa} {σ : E.State} (hQ : QA64M E e e' endPc post t.st σ) (hh : t.halted = true) :
    post (t.st.st, σ) := by
  obtain ⟨he, -, hend, hsafe⟩ := hQ
  refine hsafe.post_of_stuck fun R hR => ?_
  have hdir := directive_isSome_of_instrStepEnv he (instrStepEnv_of_mask hm hR).1
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

/-- **Every tree from a `QA64M`-state is fault-free**, for a fault-free
image. -/
theorem noFault_QA64M [Kraken.Executable.ValidLayout e] (hm : MaskOf e e') (hnf : DirsNoFault e)
    (hpost : ∀ y, post y → y.1.2 = endPc) :
    ∀ st σ tree, QA64M E e e' endPc post st σ → isa.exec st = some tree → tree.NoFault := by
  intro st σ tree h hex
  obtain ⟨he, hds, hend, hsafe⟩ := h
  rcases hsafe.unfold with hp | ⟨R, hR, -⟩
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · obtain ⟨d, z, rest, hcode, -⟩ := (instrStepEnv_of_mask hm hR).1
    exact noFault_of_codeAt he hds hcode (hnf d z (mem_of_codeAt hcode)) tree hex

end Generic

/-! ## The cumulative take family: `EnvGTU` -/

section LinkTU

variable {A : Arch} {tid : Nat} {pl : Plan} {e e' : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateA → Prop}

/-- **The link hypotheses of `EnvGTU` at `QA64M`** (`linkHypsTU_QA64TU`
over a mask: the shape of the mask's cells only). -/
theorem linkHypsTU_QA64M (hm : MaskOf e e') (hpl : pl.Valid) (hlive : e.rmwLive = true)
    (hshape : Phase1Tree A e') (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsTU (I := isa) A tid pl (QA64M (EnvGTUA A tid pl) e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex :=
    QA64M.shape (Φ := fun t => Phase1Shape A t) hm hpost (fun f _ ht => phase1Shape_map f ht) hshape h hex
  link J _ _ _ h hex hJ := QA64M.link hm hlive hpost J h hex hJ

/-- **`ThreadRuleRXGS.ofSafelyEnvGTUM`**: `ofSafelyEnvGTU` over a mask `e'`
of the image `e`: the shape `Phase1Tree A e'` and the halt `hstuck` of the
mask; the static check `e.rmwLive` of the image. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTUM
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hm : MaskOf e e') (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e')
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTUA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGS G₀ A B tid :=
  ThreadRuleRXGS.ofEnvGTU (linkHypsTU_QA64M (tid := tid) hm hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64M hm hstuck hQ hh) hp hrel hcl

/-- **`NPSafeP` (frame `K2Scope AllocIds`) from a `Safely` judgment of
`EnvGTU` over a mask.** -/
theorem npSafeP_of_safelyEnvGTUM {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hm : MaskOf e e') (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e')
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTUA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvG (I := isa) A tid pl (QA64M (EnvGTUA A tid pl) e e' endPc post) cl c r g) :
    NPSafeP (model isa) A B tid G₀ (K2Scope (model isa) AllocIds) n m cl c r g :=
  NPSafeP.of_ruleRXGS (ThreadRuleRXGS.ofSafelyEnvGTUM hm hpl hlive hshape hpost hstuck hB) n m cl c r g h

/-- **The no-fault rule of `ofSafelyEnvGTUM`**, unconditional in the
thread's promises, for a fault-free image. -/
theorem noFaultRule_ofSafelyEnvGTUM {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hm : MaskOf e e') (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e')
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTUA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRuleS (ThreadRuleRXGS.ofSafelyEnvGTUM hm hpl hlive hshape hpost hstuck hB) :=
  NoFaultRuleS.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp => by
    obtain ⟨σ, hQ⟩ := InvG.q_at rF t h he hg ht E hnp
    exact noFault_QA64M (E := EnvGTUA A tid pl) hm hnf hpost t.st σ tree hQ hex

end LinkTU

/-- **The rule's invariant of `ofSafelyEnvGTUM` at the initial
configuration**, from `QA64M` at `σInit` (`invGTU_init` over a mask). -/
theorem invGTUM_init {A : Arch} {tid : Nat} {pl : Plan} {ss : List isa.State} {m : List (Loc × Val)}
    {s : isa.State} (hs : ss[tid]? = some s) {r : Res} {g : Ghost} (hpend : g.pend = [])
    {e e' : Kraken.Executable Directive} {endPc : Int64} {post : MachineState × EStateA → Prop}
    (hQ : QA64M (EnvGTUA A tid pl) e e' endPc post s (σInit (Config.init ss m) r g)) :
    InvG (I := isa) A tid pl (QA64M (EnvGTUA A tid pl) e e' endPc post) True (Config.init ss m) r g :=
  ⟨_, _, coreAt_init hs hpend, hQ⟩

/-! ## The take family: `EnvGT` -/

section LinkT

variable {A : Arch} {tid : Nat} {pl : Plan} {e e' : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateA → Prop}

/-- **The link hypotheses of `EnvGT` at `QA64M`.** -/
theorem linkHypsT_QA64M (hm : MaskOf e e') (hpl : pl.Valid) (hlive : e.rmwLive = true)
    (hshape : Phase1Tree A e') (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsT (I := isa) A tid pl (QA64M (EnvGTA A tid pl) e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex :=
    QA64M.shape (Φ := fun t => Phase1Shape A t) hm hpost (fun f _ ht => phase1Shape_map f ht) hshape h hex
  link J _ _ _ h hex hJ := QA64M.link hm hlive hpost J h hex hJ

/-- **`ThreadRuleRXGS.ofSafelyEnvGTM`**: `ofSafelyEnvGT` over a mask. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTM
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hm : MaskOf e e') (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e')
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGS G₀ A B tid :=
  ThreadRuleRXGS.ofEnvGT (linkHypsT_QA64M (tid := tid) hm hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64M hm hstuck hQ hh) hp hrel hcl

/-- **The no-fault rule of `ofSafelyEnvGTM`**, for a fault-free image. -/
theorem noFaultRule_ofSafelyEnvGTM {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hm : MaskOf e e') (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e')
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRuleS (ThreadRuleRXGS.ofSafelyEnvGTM hm hpl hlive hshape hpost hstuck hB) :=
  NoFaultRuleS.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp => by
    obtain ⟨σ, hQ⟩ := InvG.q_at rF t h he hg ht E hnp
    exact noFault_QA64M (E := EnvGTA A tid pl) hm hnf hpost t.st σ tree hQ hex

end LinkT

/-- **The rule's invariant of `ofSafelyEnvGTM` at the initial
configuration.** -/
theorem invGTM_init {A : Arch} {tid : Nat} {pl : Plan} {ss : List isa.State} {m : List (Loc × Val)}
    {s : isa.State} (hs : ss[tid]? = some s) {r : Res} {g : Ghost} (hpend : g.pend = [])
    {e e' : Kraken.Executable Directive} {endPc : Int64} {post : MachineState × EStateA → Prop}
    (hQ : QA64M (EnvGTA A tid pl) e e' endPc post s (σInit (Config.init ss m) r g)) :
    InvG (I := isa) A tid pl (QA64M (EnvGTA A tid pl) e e' endPc post) True (Config.init ss m) r g :=
  ⟨_, _, coreAt_init hs hpend, hQ⟩

/-! ## The plain family: `EnvG` -/

section LinkPlain

variable {A : Arch} {tid : Nat} {pl : Plan} {e e' : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateA → Prop}

/-- **The link hypotheses of `EnvG` at `QA64M`.** -/
theorem linkHyps_QA64M (hm : MaskOf e e') (hpl : pl.Valid) (hlive : e.rmwLive = true)
    (hshape : Phase1Tree A e') (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHyps (I := isa) A tid pl (QA64M (EnvGA A tid pl) e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex :=
    QA64M.shape (Φ := fun t => Phase1Shape A t) hm hpost (fun f _ ht => phase1Shape_map f ht) hshape h hex
  link J _ _ _ h hex hJ := QA64M.link hm hlive hpost J h hex hJ

/-- **`ThreadRuleRX.ofSafelyEnvGM`**: `ofSafelyEnvG` over a mask. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvGM
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hm : MaskOf e e') (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e')
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRX A B tid :=
  ThreadRuleRX.ofEnvG (linkHyps_QA64M (tid := tid) hm hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64M hm hstuck hQ hh) hp hrel hcl

/-- **The no-fault rule of `ofSafelyEnvGM`**, unconditional in the
thread's promises, for a fault-free image. -/
theorem noFaultRule_ofSafelyEnvGM {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hm : MaskOf e e') (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e')
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRule (ThreadRuleRX.ofSafelyEnvGM hm hpl hlive hshape hpost hstuck hB) :=
  noFaultRule_ofEnvG_struct _ _ (noFault_QA64M (E := EnvGA A tid pl) hm hnf hpost)

end LinkPlain

/-- **The rule's invariant of `ofSafelyEnvGM` at the initial
configuration.** -/
theorem invGM_init {A : Arch} {tid : Nat} {pl : Plan} {ss : List isa.State} {m : List (Loc × Val)}
    {s : isa.State} (hs : ss[tid]? = some s) {r : Res} {g : Ghost} (hpend : g.pend = [])
    {e e' : Kraken.Executable Directive} {endPc : Int64} {post : MachineState × EStateA → Prop}
    (hQ : QA64M (EnvGA A tid pl) e e' endPc post s (σInit (Config.init ss m) r g)) :
    InvG (I := isa) A tid pl (QA64M (EnvGA A tid pl) e e' endPc post) True (Config.init ss m) r g :=
  ⟨_, _, coreAt_init hs hpend, hQ⟩

/-! ## The `FC` family: `EnvGC` with failing release RMWs -/

section LinkFC

variable {A : Arch} {tid : Nat} {pl : Plan} {e e' : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateA → Prop}

/-- **The link hypotheses of `EnvGC` with failing release RMWs at
`QA64M`** (`linkHypsFC_QA64C` over a mask). -/
theorem linkHypsFC_QA64M (hm : MaskOf e e') (hpl : pl.Valid) (hlive : e.rmwLive = true)
    (hshape : Phase1TreeF e') (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsFC (I := isa) A tid pl (QA64M (EnvGCA A tid pl) e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex := QA64M.shape (Φ := Phase1ShapeF) hm hpost (fun f _ ht => phase1ShapeF_map f ht) hshape h hex
  link J _ _ _ h hex hJ := QA64M.link hm hlive hpost J h hex hJ

/-- **`ThreadRuleRXF.ofSafelyEnvGFCM`**: `ofSafelyEnvGFC` over a mask. -/
def _root_.Kraken.Promising.SLR.EnvG.ThreadRuleRXF.ofSafelyEnvGFCM
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hm : MaskOf e e') (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeF e')
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGCA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXF A B tid :=
  ThreadRuleRXF.ofEnvGFC (linkHypsFC_QA64M (tid := tid) hm hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64M hm hstuck hQ hh) hp hrel hcl

/-- **The no-fault rule of `ofSafelyEnvGFCM`**, for a fault-free image. -/
theorem noFaultRuleF_ofSafelyEnvGFCM {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hm : MaskOf e e') (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeF e')
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGCA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRuleF (ThreadRuleRXF.ofSafelyEnvGFCM hm hpl hlive hshape hpost hstuck hB) :=
  noFaultRuleF_ofEnvGFC_struct _ _ (noFault_QA64M (E := EnvGCA A tid pl) hm hnf hpost)

end LinkFC

/-- **The rule's invariant of `ofSafelyEnvGFCM` at the initial
configuration.** -/
theorem invGFCM_init {A : Arch} {tid : Nat} {pl : Plan} {ss : List isa.State} {m : List (Loc × Val)}
    {s : isa.State} (hs : ss[tid]? = some s) {r : Res} {g : Ghost} (hpend : g.pend = [])
    {e e' : Kraken.Executable Directive} {endPc : Int64} {post : MachineState × EStateA → Prop}
    (hQ : QA64M (EnvGCA A tid pl) e e' endPc post s (σInit (Config.init ss m) r g)) :
    InvGF (I := isa) tid pl (QA64M (EnvGCA A tid pl) e e' endPc post) True (Config.init ss m) r g :=
  ⟨σInit (Config.init ss m) r g, Thread.init s, coreAtF_init hs hpend, hQ⟩

end Kraken.Promising.AArch64.EnvG

#print axioms Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTUM
#print axioms Kraken.Promising.AArch64.EnvG.noFaultRule_ofSafelyEnvGTUM
#print axioms Kraken.Promising.AArch64.EnvG.invGTUM_init
#print axioms Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTM
#print axioms Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvGM
#print axioms Kraken.Promising.SLR.EnvG.ThreadRuleRXF.ofSafelyEnvGFCM
