/-
**The AArch64 rule links for threads with strict sized declarations**
. The AArch64 copy of the declarations proofs'
`EnvG/X64DeclsLink.lean`: one invariant, `QA64MD`, serves every AArch64 link
family the whole-image theorems use, masked or not.

## Why

Every AArch64 rule link (`QA64`, `QA64M`, `QA64CAdj`, …) asks
`st.decls = {}` of the thread, and the whole-image theorems inherit it
(`StartPushW.decls` and the like): they cover the `.kl` program as written,
but not the `.kl` runner's thread states, which carry the declarations of
the `.kl` header (`MemLayout.decls`, `Kraken/Litmus/Layout.lean`).

For **strict sized** declarations (`Decls.StrictSized`: a typed header)
`EnvG/A64DeclsBridge.lean` reads the thread's
tree as the `decls = {}` tree re-resolved against `ds` (`exec_reresolve`,
for code without `LDXP`/`STXP`: `Executable.noPairs`): an access at a
declared footprint, or at an undeclared address, is unchanged; a mixed-size
access becomes a fault. A fault satisfies every tree judgment and every
phase-1 shape, so the `decls = {}` link facts transfer to `decls = ds`.

## Contents

- **`QA64MD ds E e e' endPc post`**: `QA64M` with `st.decls = ds` in place
  of `st.decls = {}`; `QA64MD.of_QA64M`, `QA64MD.noDecls`, `QA64MD.link`,
  `QA64MD.tree`, `QA64MD.shape`, `post_of_halted_QA64MD`. Unmasked uses take
  `MaskOf.refl`. Every D link takes `(hsz : ds.StrictSized)` and
  `(hnp : e.noPairs = true)` before the `…M` arguments.
- The D forms of the families (`…MD` beside `…M`): cumulative take
  (`ThreadRuleRXGS.ofSafelyEnvGTUMD`), take (`…GTMD`), plain
  (`ThreadRuleRX.ofSafelyEnvGMD`), `FC` (`ThreadRuleRXF.ofSafelyEnvGFCMD`),
  the adjacency ghost (`…GFCAdjMD`), the take route with a claim-conditional
  RMW (`ThreadRuleRXGS.ofSafelyEnvGTRCMD`); the matching `invG…MD_init`.
- Purity with declarations: `RelPureSpec.HoldsD`, `relPureSpec_stepD`, and
  the chain entries `final_of_relPureSafelyD` / `_FD` / `_SD` (copies of
  `final_of_relPureSafely` / `F` / `S` at `HoldsD`, with
  `(ds : Nat → Decls)`, `hsz`, `hnp` per thread).

Not covered: the no-fault side (`reresolve` turns a mixed-size access into
a fault; the `_noFault` rules stay at `decls = {}`, see
`EnvG/A64DeclsBridge.lean`'s header).
-/
import Kraken.Promising.SLR.EnvG.A64DeclsBridge
import Kraken.Promising.SLR.EnvG.A64MaskLink
import Kraken.Promising.SLR.EnvG.A64MaskAdj
import Kraken.Promising.SLR.EnvG.A64MaskTC
import Kraken.Promising.SLR.EnvG.A64RmwFailFinal
import Kraken.Promising.SLR.EnvG.TakeFinal

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## The invariant with declarations and the generic link facts -/

/-- **The thread-local invariant over a mask, with declarations `ds`**:
`QA64M` with `st.decls = ds`. -/
def QA64MD (ds : Decls) (E : SharedEnv) (e e' : Kraken.Executable Directive) (endPc : Int64)
    (post : MachineState × E.State → Prop) (st : State) (σ : E.State) : Prop :=
  st.exe = e ∧ st.decls = ds ∧ st.endPc = endPc ∧ Safely (e'.instrStepEnv E) post (st.st, σ)

section Generic

variable {ds : Decls} {E : SharedEnv} {e e' : Kraken.Executable Directive} {endPc : Int64}
  {post : MachineState × E.State → Prop}

/-- `QA64M` is `QA64MD {}`. -/
theorem QA64MD.of_QA64M {st : State} {σ : E.State} (h : QA64M E e e' endPc post st σ) :
    QA64MD {} E e e' endPc post st σ := h

/-- `QA64MD` at the thread with its declarations dropped is `QA64M`. -/
theorem QA64MD.noDecls {st : State} {σ : E.State} (h : QA64MD ds E e e' endPc post st σ) :
    QA64M E e e' endPc post st.noDecls σ :=
  ⟨h.1, rfl, h.2.2.1, h.2.2.2⟩

/-- **One instruction of the image, under a live tree judgment**, from
`QA64MD` (`QA64M.link` through `exec_treeJLive_of_reresolve`). -/
theorem QA64MD.link [Kraken.Executable.ValidLayout e] (hsz : ds.StrictSized)
    (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e') (hlive : e.rmwLive = true)
    (hpost : ∀ y, post y → y.1.2 = endPc) (J : SLR.EnvG.TreeJLive E State) {st : State} {σ : E.State}
    {tree : EvTree State} (h : QA64MD ds E e e' endPc post st σ) (hex : isa.exec st = some tree)
    (hJ : ∀ st' σ', QA64MD ds E e e' endPc post st' σ' → J.Post st' σ') : J.W tree σ := by
  obtain ⟨he, hds, hend, hsafe⟩ := h
  rcases hsafe.unfold with hp | ⟨R, hR, hk⟩
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · subst hds he
    refine exec_treeJLive_of_reresolve J hnp hsz (fun tree₀ h₀ => ?_) tree hex
    exact exec_treeJLive_of_instrStepEnv' ((J.comap (State.withDecls st.decls)).reresolve st.decls hsz)
      (st := st.noDecls) rfl rfl (instrStepEnv_of_mask hm hR).1
      (fun m g' hz => by
        show J.Post (State.withDecls st.decls { st.noDecls with st := m }) g'
        rw [State.withDecls_noDecls_st]
        exact hJ _ _ ⟨rfl, rfl, hend, hk _ hz⟩) hlive tree₀ h₀

/-- **The thread's tree is the masked `decls = {}` thread's**, re-resolved
against `ds`, up to the executable and declarations in its states. -/
theorem QA64MD.tree [Kraken.Executable.ValidLayout e] (hnp : Kraken.Executable.noPairs e = true)
    (hm : MaskOf e e') (hpost : ∀ y, post y → y.1.2 = endPc)
    {st : State} {σ : E.State} {tree : EvTree State} (h : QA64MD ds E e e' endPc post st σ)
    (hex : isa.exec st = some tree) :
    ∃ tree', isa.exec { st with exe := e', decls := {} } = some tree' ∧
      tree = (tree'.reresolve ds).map fun s => { s with exe := e, decls := ds } := by
  have hds := h.2.1
  have he := h.1
  subst hds he
  rw [exec_reresolve st hnp] at hex
  obtain ⟨tree₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp hex
  obtain ⟨tree', hex', rfl⟩ := QA64M.tree hm hpost h.noDecls h₀
  refine ⟨tree', hex', ?_⟩
  erw [← EvTree.map_reresolve, evTree_map_map]
  rfl

/-- **A per-cell tree shape of the mask holds of the thread's trees**, for
a shape closed under `EvTree.map` and `EvTree.reresolve`. -/
theorem QA64MD.shape [Kraken.Executable.ValidLayout e] (hnp : Kraken.Executable.noPairs e = true)
    (hm : MaskOf e e') (hpost : ∀ y, post y → y.1.2 = endPc)
    {Φ : ∀ {σ : Type}, EvTree σ → Prop} (hmap : ∀ {σ τ : Type} (f : σ → τ) (t : EvTree σ), Φ t → Φ (t.map f))
    (hre : ∀ {σ : Type} (t : EvTree σ), Φ t → Φ (t.reresolve ds))
    (hΦ : ∀ st : State, st.exe = e' → st.decls = {} → ∀ tree, isa.exec st = some tree → Φ tree)
    {st : State} {σ : E.State} {tree : EvTree State} (h : QA64MD ds E e e' endPc post st σ)
    (hex : isa.exec st = some tree) : Φ tree := by
  obtain ⟨tree', hex', rfl⟩ := QA64MD.tree hnp hm hpost h hex
  exact hmap _ _ (hre _ (hΦ { st with exe := e', decls := {} } rfl rfl tree' hex'))

/-- **`done` at `QA64MD`**: a halted thread is at its postcondition, with
the halt read off the mask (`post_of_halted_QA64M`; the declarations play no
part). -/
theorem post_of_halted_QA64MD (hm : MaskOf e e')
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv E x R)
    {t : Thread isa} {σ : E.State} (hQ : QA64MD ds E e e' endPc post t.st σ) (hh : t.halted = true) :
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

end Generic

/-! ## The link families -/

section Families

variable {ds : Decls} {A : Arch} {tid : Nat} {pl : Plan} {e e' : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateA → Prop}

/-! ### Cumulative take (`EnvGTU`) -/

theorem linkHypsTU_QA64MD (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e')
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e') (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsTU (I := isa) A tid pl (QA64MD ds (EnvGTUA A tid pl) e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex := QA64MD.shape (Φ := fun t => Phase1Shape A t) hnp hm hpost
    (fun f _ ht => phase1Shape_map f ht) (fun _ ht => phase1Shape_reresolve hsz ht) hshape h hex
  link J _ _ _ h hex hJ := QA64MD.link hsz hnp hm hlive hpost J h hex hJ

/-- **`ThreadRuleRXGS.ofSafelyEnvGTUMD`**: `ofSafelyEnvGTUM` for a thread
with strict sized declarations `ds`. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTUMD
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e') (hpl : pl.Valid)
    (hlive : e.rmwLive = true) (hshape : Phase1Tree A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTUA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGS G₀ A B tid :=
  ThreadRuleRXGS.ofEnvGTU (linkHypsTU_QA64MD (tid := tid) hsz hnp hm hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64MD hm hstuck hQ hh) hp hrel hcl

omit [Kraken.Executable.ValidLayout e] in
theorem invGTUMD_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = [])
    (hQ : QA64MD ds (EnvGTUA A tid pl) e e' endPc post s (σInit (Config.init ss m) r g)) :
    InvG (I := isa) A tid pl (QA64MD ds (EnvGTUA A tid pl) e e' endPc post) True (Config.init ss m) r g :=
  ⟨_, _, coreAt_init hs hpend, hQ⟩

/-! ### Take (`EnvGT`) -/

theorem linkHypsT_QA64MD (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e')
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e') (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsT (I := isa) A tid pl (QA64MD ds (EnvGTA A tid pl) e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex := QA64MD.shape (Φ := fun t => Phase1Shape A t) hnp hm hpost
    (fun f _ ht => phase1Shape_map f ht) (fun _ ht => phase1Shape_reresolve hsz ht) hshape h hex
  link J _ _ _ h hex hJ := QA64MD.link hsz hnp hm hlive hpost J h hex hJ

/-- **`ThreadRuleRXGS.ofSafelyEnvGTMD`**: `ofSafelyEnvGTM` for a thread with
strict sized declarations `ds`. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTMD
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e') (hpl : pl.Valid)
    (hlive : e.rmwLive = true) (hshape : Phase1Tree A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGS G₀ A B tid :=
  ThreadRuleRXGS.ofEnvGT (linkHypsT_QA64MD (tid := tid) hsz hnp hm hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64MD hm hstuck hQ hh) hp hrel hcl

omit [Kraken.Executable.ValidLayout e] in
theorem invGTMD_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = [])
    (hQ : QA64MD ds (EnvGTA A tid pl) e e' endPc post s (σInit (Config.init ss m) r g)) :
    InvG (I := isa) A tid pl (QA64MD ds (EnvGTA A tid pl) e e' endPc post) True (Config.init ss m) r g :=
  ⟨_, _, coreAt_init hs hpend, hQ⟩

/-! ### Plain (`EnvG`) -/

theorem linkHyps_QA64MD (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e')
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e') (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHyps (I := isa) A tid pl (QA64MD ds (EnvGA A tid pl) e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex := QA64MD.shape (Φ := fun t => Phase1Shape A t) hnp hm hpost
    (fun f _ ht => phase1Shape_map f ht) (fun _ ht => phase1Shape_reresolve hsz ht) hshape h hex
  link J _ _ _ h hex hJ := QA64MD.link hsz hnp hm hlive hpost J h hex hJ

/-- **`ThreadRuleRX.ofSafelyEnvGMD`**: `ofSafelyEnvGM` for a thread with
strict sized declarations `ds`. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvGMD
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e') (hpl : pl.Valid)
    (hlive : e.rmwLive = true) (hshape : Phase1Tree A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRX A B tid :=
  ThreadRuleRX.ofEnvG (linkHyps_QA64MD (tid := tid) hsz hnp hm hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64MD hm hstuck hQ hh) hp hrel hcl

omit [Kraken.Executable.ValidLayout e] in
theorem invGMD_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = [])
    (hQ : QA64MD ds (EnvGA A tid pl) e e' endPc post s (σInit (Config.init ss m) r g)) :
    InvG (I := isa) A tid pl (QA64MD ds (EnvGA A tid pl) e e' endPc post) True (Config.init ss m) r g :=
  ⟨_, _, coreAt_init hs hpend, hQ⟩

/-! ### `FC`: `EnvGC` with failing release RMWs -/

theorem linkHypsFC_QA64MD (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e')
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeF e') (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsFC (I := isa) A tid pl (QA64MD ds (EnvGCA A tid pl) e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex := QA64MD.shape (Φ := Phase1ShapeF) hnp hm hpost (fun f _ ht => phase1ShapeF_map f ht)
    (fun _ ht => phase1ShapeF_reresolve ds _ ht) hshape h hex
  link J _ _ _ h hex hJ := QA64MD.link hsz hnp hm hlive hpost J h hex hJ

/-- **`ThreadRuleRXF.ofSafelyEnvGFCMD`**: `ofSafelyEnvGFCM` for a thread
with strict sized declarations `ds`. -/
def _root_.Kraken.Promising.SLR.EnvG.ThreadRuleRXF.ofSafelyEnvGFCMD
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e') (hpl : pl.Valid)
    (hlive : e.rmwLive = true) (hshape : Phase1TreeF e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGCA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXF A B tid :=
  ThreadRuleRXF.ofEnvGFC (linkHypsFC_QA64MD (tid := tid) hsz hnp hm hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64MD hm hstuck hQ hh) hp hrel hcl

omit [Kraken.Executable.ValidLayout e] in
theorem invGFCMD_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = [])
    (hQ : QA64MD ds (EnvGCA A tid pl) e e' endPc post s (σInit (Config.init ss m) r g)) :
    InvGF (I := isa) tid pl (QA64MD ds (EnvGCA A tid pl) e e' endPc post) True (Config.init ss m) r g :=
  ⟨σInit (Config.init ss m) r g, Thread.init s, coreAtF_init hs hpend, hQ⟩

/-! ### The adjacency ghost (`EnvGCAdj`) -/

theorem linkHypsFCAdj_QA64MD (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e')
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeF e') (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsFCAdj (I := isa) A tid pl (QA64MD ds (EnvGCAdjA A tid pl) e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex := QA64MD.shape (Φ := Phase1ShapeF) hnp hm hpost (fun f _ ht => phase1ShapeF_map f ht)
    (fun _ ht => phase1ShapeF_reresolve ds _ ht) hshape h hex
  link J _ _ _ h hex hJ := QA64MD.link hsz hnp hm hlive hpost J h hex hJ

/-- **`ThreadRuleRXF.ofSafelyEnvGFCAdjMD`**: `ofSafelyEnvGFCAdjM` for a
thread with strict sized declarations `ds`. -/
def _root_.Kraken.Promising.SLR.EnvG.ThreadRuleRXF.ofSafelyEnvGFCAdjMD
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e') (hpl : pl.Valid)
    (hlive : e.rmwLive = true) (hshape : Phase1TreeF e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGCAdjA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXF A B tid :=
  ThreadRuleRXF.ofEnvGFCAdj (linkHypsFCAdj_QA64MD (tid := tid) hsz hnp hm hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64MD hm hstuck hQ hh) hp hrel hcl

omit [Kraken.Executable.ValidLayout e] in
theorem invGFCAdjMD_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = [])
    (hQ : QA64MD ds (EnvGCAdjA A tid pl) e e' endPc post s (σInit (Config.init ss m) r g)) :
    InvGF (I := isa) tid pl (QA64MD ds (EnvGCAdjA A tid pl) e e' endPc post) True (Config.init ss m) r g :=
  ⟨σInit (Config.init ss m) r g, Thread.init s, coreAtF_init hs hpend, hQ⟩

/-! ### The take route with a claim-conditional RMW (`EnvGTC`) -/

theorem linkHypsTRC_QA64MD (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e')
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e') (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsTRC (I := isa) A tid pl (QA64MD ds (EnvGTCA A tid pl) e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex := QA64MD.shape (Φ := fun t => Phase1ShapeR A t) hnp hm hpost
    (fun f _ ht => phase1ShapeR_map f ht) (fun _ ht => phase1ShapeR_reresolve hsz ht) hshape h hex
  link J _ _ _ h hex hJ := QA64MD.link hsz hnp hm hlive hpost J h hex hJ

/-- **`ThreadRuleRXGS.ofSafelyEnvGTRCMD`**: `ofSafelyEnvGTRCM` for a thread
with strict sized declarations `ds`. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTRCMD
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e') (hpl : pl.Valid)
    (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTCA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGS G₀ A B tid :=
  ThreadRuleRXGS.ofEnvGTRC (linkHypsTRC_QA64MD (tid := tid) hsz hnp hm hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64MD hm hstuck hQ hh) hp hrel hcl

omit [Kraken.Executable.ValidLayout e] in
theorem invGTRCMD_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = [])
    (hQ : QA64MD ds (EnvGTCA A tid pl) e e' endPc post s (σInit (Config.init ss m) r g)) :
    InvGR (I := isa) tid pl (QA64MD ds (EnvGTCA A tid pl) e e' endPc post) True (Config.init ss m) r g :=
  ⟨σInit (Config.init ss m) r g, Thread.init s, coreAtR_init hs hpend, hQ⟩

end Families

/-! ## Purity with declarations -/

section Purity

open Kraken.Promising.SLR.EnvSpike

variable {A : Arch} {rel : Loc → Pred}

/-- **The purity specification holds at a thread state with strict sized
declarations `ds`** (`RelPureSpec.Holds` with `decls = ds`). -/
def _root_.Kraken.Promising.AArch64.EnvG.RelPureSpec.HoldsD (sp : RelPureSpec A rel) (ds : Decls)
    (st : State) : Prop :=
  st.exe = sp.e ∧ st.endPc = sp.endPc ∧ st.decls = ds ∧
    Safely (sp.e.instrStepEnv (SharedEnv.relPure A rel)) sp.post (st.st, ())

/-- `Holds` is `HoldsD {}`. -/
theorem RelPureSpec.holdsD_of_holds {sp : RelPureSpec A rel} {st : State} (h : sp.Holds st) :
    sp.HoldsD {} st := h

/-- **One instruction** (`relPureSpec_step` with declarations). -/
theorem relPureSpec_stepD (sp : RelPureSpec A rel) {ds : Decls} (hsz : ds.StrictSized)
    (hnp : Kraken.Executable.noPairs sp.e = true) {st : State} (h : sp.HoldsD ds st) (tree : EvTree State)
    (hex : isa.exec st = some tree) :
    tree.RelWrites A (fun l v => Pred.Pure (rel l) v) ∧ tree.All (sp.HoldsD ds) :=
  exec_treeJ_of_safelyD (TreeJ.relWrites A (fun l v => Pred.Pure (rel l) v) (sp.HoldsD ds)) hsz (hv := sp.valid) hnp
    sp.post_end (fun _ _ a b c d => ⟨a, b, c, d⟩) h.1 h.2.1 h.2.2.1 h.2.2.2 tree hex

/-- **`final_of_relPureSafely` with declarations**: the threads' purity
specifications hold with strict sized declarations `ds tid`, and their code
has no `LDXP`/`STXP`. -/
theorem final_of_relPureSafelyD (A : Arch) (fuel : Nat) {states : List isa.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop}
    {Φ : Config isa → Prop}
    (hH : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (sp : Nat → RelPureSpec A g₀.rel) (ds : Nat → Decls) (hsz : ∀ tid, (ds tid).StrictSized)
    (hnp : ∀ tid, Kraken.Executable.noPairs (sp tid).e = true)
    (h0 : ∀ tid s, states[tid]? = some s → (sp tid).HoldsD (ds tid) s)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafe (model isa) A B tid n m True (Config.init states initMem) (rF tid) g₀)
    {c : Config isa} (hc : Reachable A fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c :=
  final_of_relWritesJ A fuel hH hE hpend (fun tid st => (sp tid).HoldsD (ds tid) st)
    (fun tid _ tree h hex => relPureSpec_stepD (sp tid) (hsz tid) (hnp tid) h tree hex) h0 hsafe hc hf hfin

/-- **`final_of_relPureSafelyF` with declarations.** -/
theorem final_of_relPureSafelyFD (A : Arch) (fuel : Nat) {states : List isa.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop}
    {Φ : Config isa → Prop}
    (hH : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (sp : Nat → RelPureSpec A g₀.rel) (ds : Nat → Decls) (hsz : ∀ tid, (ds tid).StrictSized)
    (hnp : ∀ tid, Kraken.Executable.noPairs (sp tid).e = true)
    (h0 : ∀ tid s, states[tid]? = some s → (sp tid).HoldsD (ds tid) s)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafeF (model isa) A B tid n m True (Config.init states initMem) (rF tid) g₀)
    {c : Config isa} (hc : Reachable A fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c := by
  have hstep : ∀ tid st tree, (sp tid).HoldsD (ds tid) st → isa.exec st = some tree →
      tree.RelWrites A (fun l v => Pred.Pure (g₀.rel l) v) ∧ tree.All ((sp tid).HoldsD (ds tid)) :=
    fun tid _ tree h hex => relPureSpec_stepD (sp tid) (hsz tid) (hnp tid) h tree hex
  have hpure : PromisePure A fuel states initMem g₀.rel :=
    promisePure_of_relWrites (fun st => ∃ tid, (sp tid).HoldsD (ds tid) st)
      (fun _ hc' tid t ht => ⟨tid, relWrites_reach (fun tid st => (sp tid).HoldsD (ds tid) st) hstep h0 hc' tid t ht⟩)
      (fun st tree ⟨tid, hJ⟩ hex => (hstep tid st tree hJ hex).1)
  exact final_of_virtual hc hf
    (theorem1FChain A fuel B states initMem rF g₀ hH hE hpend hpure hsafe c hc ⟨c, .refl c, hf⟩) hfin

/-- **`final_of_relPureSafelyS` with declarations.** -/
theorem final_of_relPureSafelySD (A : Arch) (fuel : Nat) {states : List isa.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop}
    {Φ : Config isa → Prop}
    (hH : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (sp : Nat → RelPureSpec A g₀.rel) (ds : Nat → Decls) (hsz : ∀ tid, (ds tid).StrictSized)
    (hnp : ∀ tid, Kraken.Executable.noPairs (sp tid).e = true)
    (h0 : ∀ tid s, states[tid]? = some s → (sp tid).HoldsD (ds tid) s)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafeP (model isa) A B tid G₀ (K2Scope (model isa) AllocIds) n m True (Config.init states initMem)
        (rF tid) g₀)
    {c : Config isa} (hc : Reachable A fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c :=
  final_of_relWritesJS A fuel hH hE hpend (fun tid st => (sp tid).HoldsD (ds tid) st)
    (fun tid _ tree h hex => relPureSpec_stepD (sp tid) (hsz tid) (hnp tid) h tree hex) h0 hsafe hc hf hfin

end Purity

end Kraken.Promising.AArch64.EnvG

#print axioms Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTUMD
#print axioms Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTMD
#print axioms Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvGMD
#print axioms Kraken.Promising.SLR.EnvG.ThreadRuleRXF.ofSafelyEnvGFCMD
#print axioms Kraken.Promising.SLR.EnvG.ThreadRuleRXF.ofSafelyEnvGFCAdjMD
#print axioms Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTRCMD
#print axioms Kraken.Promising.AArch64.EnvG.final_of_relPureSafelyD
#print axioms Kraken.Promising.AArch64.EnvG.final_of_relPureSafelyFD
#print axioms Kraken.Promising.AArch64.EnvG.final_of_relPureSafelySD
