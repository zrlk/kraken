/-
**No fault at the runner's declarations (`decls = ds`), AArch64**. Additive: the
existing `…MD` rules
(`EnvG/A64DeclsLink.lean`, `EnvG/A64DeclsLinkMore.lean`) are unchanged.

## Why new rules

`EnvG/A64DeclsBridge.lean` reads a thread with strict sized declarations `ds`
as its `decls = {}` thread re-resolved against `ds` (`exec_reresolve`): a
mixed-size access becomes a fault. The no-fault-at-declarations proofs excluded those faults on x64
from the invariant: x64's `QX64M` is a `Safely` judgment over `E.within S`,
so every root access is an `S`-location (`rootInJ`). **AArch64's
`QA64M`/`QA64MD` carry no layout**: their `Safely` is over an `EnvG`
variant, whose `ok` holds of every load (`Env.lean`), so nothing in
`QA64MD` bounds a load address and the existing `…MD` rules' no-fault at
`decls = ds` does not follow from their invariant.

## The address run

An address depends on the machine state only (for the fixed-layout programs:
the address registers), not on the values read. So it is proved by a second
`Safely` run, in the trivial invariant environment `SharedEnv.invTop S`
(`inv S ⊤`: any value read, every access exactly an `S`-location):

- **`AddrSafeA S e endPc m`**: `Safely (e.instrStepEnv (invTop S)) (pc = endPc) (m, ())`.
  A per-thread predicate of the machine state alone (no SLR state), reusable
  by a program-level fault-freedom argument through `InvLinkAArch64`.
- **`QA64MAD ds S E e e' endPc post st σ`**: `QA64MD … st σ ∧ AddrSafeA S e' endPc st.st`.
- `QA64MAD.link`: one instruction under a live judgment `J` of `E`: the
  address run puts every leaf in `AddrSafeA` (`allLeavesJA`, run by
  `QA64MD.link` in `invTop S`), and `QA64MD.link` runs `J.guardA`. Side
  condition: `E`'s non-exclusive stores succeed (`StoreSuccA`, every `EnvG`
  variant).
- **`noFault_QA64MAD_rootD`**: from `AddrSafeA` the root accesses of the
  thread's `decls = {}` tree are `S`-locations (`rootInJA`); with
  `Decls.AgreesOnA ds S`, a fault-free image (`DirsNoFault e`) and the
  phase-1 single-access shape, the tree at `decls = ds` is fault-free
  (`noFault_reresolve_rootD`).
- The families the fixed-layout AArch64 programs use, each as its `…MD`
  form with `QA64MAD` for `QA64MD` (same `B`, so the rule can stand for the
  existing one in a runner proof): rule `…MAD`, `noFaultRule…MAD_rootD`,
  `invG…MAD_init`: plain (`EnvG`), take (`EnvGT`), cumulative take
  (`EnvGTU`), take with a claim-conditional RMW (`EnvGTC`), the
  claim-conditional RMW (`EnvGC`, `RC`), the ticket environments (`EnvGTD`,
  `EnvGTDR`).

Phase-1 limit: single-access trees (`RootOnlyDA`), as the no-fault-at-declarations proofs.
-/
import Kraken.Promising.SLR.EnvG.A64NoFaultDCommon
import Kraken.Promising.SLR.EnvG.A64DeclsLinkMore

open Kraken

namespace Kraken.Promising.AArch64

/-- **Address safety of a thread's machine state**: every run of `e` from
`m` in the trivial invariant environment on `S` (any value read) accesses
only `S`-locations, exactly, until it stops at `endPc`. A predicate of the
machine state alone. -/
def AddrSafeA (S : SharedEnv.Layout) (e : Kraken.Executable Directive) (endPc : Int64) (m : MachineState) : Prop :=
  Safely (e.instrStepEnv (SharedEnv.invTop S)) (fun y => y.1.2 = endPc) (m, ())

/-- **`AddrSafeA` from a partial triple** in `invTop S`, at the start of a
laid-out program, with no exceptional exit. -/
theorem addrSafeA_of_partialTripleEnv [CodeEnv] [layout : _root_.Layout] {S : SharedEnv.Layout} {p : Program}
    [Kraken.Executable.ValidLayout (layout p)] {P Q : MachineData → Unit → Prop}
    {E : Int64 → MachineData → Unit → Prop} (ht : MachineWP.PartialTripleEnv (SharedEnv.invTop S) P p Q E)
    (henv : cenv = layout p) {m : MachineState} (hpc : m.2 = (layout p).addrOf 0) (hP : P m.1 ())
    (hE : ∀ a s g, ¬ E a s g := by simp) :
    AddrSafeA S (layout p) ((layout p).addrOf p.length) m := by
  have hm : m = (m.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hpc, Executable.addrOf_zero, Layout.apply_fst]
  unfold AddrSafeA
  rw [hm]
  exact (Program.instrStepEnv_of_partialTripleEnv ht hP henv).mono fun _ h => h.elim And.left (hE _ _ _ ·|>.elim)

end Kraken.Promising.AArch64

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## The invariant and the generic facts -/

/-- **`QA64MD` with the address run on `S`.** -/
def QA64MAD (ds : Decls) (S : SharedEnv.Layout) (E : SharedEnv) (e e' : Kraken.Executable Directive)
    (endPc : Int64) (post : MachineState × E.State → Prop) (st : State) (σ : E.State) : Prop :=
  QA64MD ds E e e' endPc post st σ ∧ AddrSafeA S e' endPc st.st

section Generic

variable {ds : Decls} {S : SharedEnv.Layout} {E : SharedEnv} {e e' : Kraken.Executable Directive} {endPc : Int64}
  {post : MachineState × E.State → Prop}

/-- The address run is a `QA64MD` judgment of `invTop S`. -/
theorem QA64MAD.addr {st : State} {σ : E.State} (h : QA64MAD ds S E e e' endPc post st σ) :
    QA64MD ds (SharedEnv.invTop S) e e' endPc (fun y => y.1.2 = endPc) st () :=
  ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.2⟩

/-- **One instruction of the image, under a live tree judgment**, from
`QA64MAD`. -/
theorem QA64MAD.link [Kraken.Executable.ValidLayout e] (hss : E.StoreSuccA) (hsz : ds.StrictSized)
    (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e') (hlive : e.rmwLive = true)
    (hpost : ∀ y, post y → y.1.2 = endPc) (J : SLR.EnvG.TreeJLive E State) {st : State} {σ : E.State}
    {tree : EvTree State} (h : QA64MAD ds S E e e' endPc post st σ) (hex : isa.exec st = some tree)
    (hJ : ∀ st' σ', QA64MAD ds S E e e' endPc post st' σ' → J.Post st' σ') : J.W tree σ := by
  have hA : tree.AllLeavesA fun st' => AddrSafeA S e' endPc st'.st :=
    QA64MD.link hsz hnp hm hlive (fun _ h => h) (allLeavesJA S fun st' : State => AddrSafeA S e' endPc st'.st)
      h.addr hex fun _ _ h' => h'.2.2.2
  exact QA64MD.link hsz hnp hm hlive hpost (J.guardA hss _) h.1 hex (fun st' σ' h' ha => hJ st' σ' ⟨h', ha⟩) hA

/-- **Every tree from a `QA64MAD`-state is fault-free**, for declarations
that agree on the layout, a fault-free image and a single-access mask. -/
theorem noFault_QA64MAD_rootD [Kraken.Executable.ValidLayout e] (hag : ds.AgreesOnA S)
    (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e') (hlive : e.rmwLive = true) (hnf : DirsNoFault e)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hro : ∀ st : State, st.exe = e' → st.decls = {} → ∀ tree, isa.exec st = some tree → tree.RootOnlyDA) :
    ∀ st σ tree, QA64MAD ds S E e e' endPc post st σ → isa.exec st = some tree → tree.NoFault := by
  intro st σ tree h hex
  have hQ := h.1.noDecls
  obtain ⟨⟨he, hds, hend, -⟩, ha⟩ := h
  subst hds he
  rw [exec_reresolve st hnp] at hex
  obtain ⟨t₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp hex
  refine (EvTree.noFault_map _ _).mpr ?_
  have hnf₀ : t₀.NoFault := noFault_QA64M hm hnf hpost st.noDecls σ t₀ hQ h₀
  have hin : t₀.RootInSA S := by
    rcases ha.unfold with hp | ⟨R, hR, -⟩
    · rw [exec_eq_none_of_end (st := st.noDecls) (hp.trans hend.symm)] at h₀; cases h₀
    · exact exec_treeJLive_of_instrStepEnv' (rootInJA S) (st := st.noDecls) rfl rfl (instrStepEnv_of_mask hm hR).1
        (fun _ _ _ => trivial) hlive t₀ h₀
  obtain ⟨tree', hex', rfl⟩ := QA64M.tree hm hpost hQ h₀
  exact noFault_reresolve_rootD hag _ hin (rootOnlyDA_map _ _ (hro _ rfl rfl _ hex')) hnf₀

end Generic

/-! ## The families -/

section Families

variable {ds : Decls} {S : SharedEnv.Layout} {A : Arch} {tid : Nat} {pl : Plan} {e e' : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateA → Prop}

theorem rootOnlyDA_of_phase1Tree (hshape : Phase1Tree A e') :
    ∀ st : State, st.exe = e' → st.decls = {} → ∀ tree, isa.exec st = some tree → tree.RootOnlyDA :=
  fun st he hd tree hex => rootOnlyDA_of_phase1Shape (hshape st he hd tree hex)

theorem rootOnlyDA_of_phase1TreeR (hshape : Phase1TreeR A e') :
    ∀ st : State, st.exe = e' → st.decls = {} → ∀ tree, isa.exec st = some tree → tree.RootOnlyDA :=
  fun st he hd tree hex => rootOnlyDA_of_phase1ShapeR (hshape st he hd tree hex)

/-! ### Plain (`EnvG`) -/

theorem linkHyps_QA64MAD (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e')
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e') (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHyps (I := isa) A tid pl (QA64MAD ds S (EnvGA A tid pl) e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex := QA64MD.shape (Φ := fun t => Phase1Shape A t) hnp hm hpost
    (fun f _ ht => phase1Shape_map f ht) (fun _ ht => phase1Shape_reresolve hsz ht) hshape h.1 hex
  link J _ _ _ h hex hJ := QA64MAD.link (by exact fun h => .inl h.2.1) hsz hnp hm hlive hpost J h hex hJ

/-- **`ThreadRuleRX.ofSafelyEnvGMAD`**: `ofSafelyEnvGMD` with the address
run on `S`. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvGMAD
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop} (S : SharedEnv.Layout)
    (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e') (hpl : pl.Valid)
    (hlive : e.rmwLive = true) (hshape : Phase1Tree A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRX A B tid :=
  ThreadRuleRX.ofEnvG (linkHyps_QA64MAD (S := S) (tid := tid) hsz hnp hm hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64MD hm hstuck hQ.1 hh) hp hrel hcl

/-- **No fault for `ofSafelyEnvGMAD`** at declarations agreeing on `S`. -/
theorem noFaultRule_ofSafelyEnvGMAD_rootD {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e') (hpl : pl.Valid)
    (hlive : e.rmwLive = true) (hshape : Phase1Tree A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) (hag : ds.AgreesOnA S) :
    NoFaultRule (ThreadRuleRX.ofSafelyEnvGMAD S hsz hnp hm hpl hlive hshape hpost hstuck hB) :=
  noFaultRule_ofEnvG_struct _ _ (noFault_QA64MAD_rootD (E := EnvGA A tid pl) hag hnp hm hlive hnf hpost
    (rootOnlyDA_of_phase1Tree hshape))

omit [Kraken.Executable.ValidLayout e] in
theorem invGMAD_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = [])
    (hQ : QA64MAD ds S (EnvGA A tid pl) e e' endPc post s (σInit (Config.init ss m) r g)) :
    InvG (I := isa) A tid pl (QA64MAD ds S (EnvGA A tid pl) e e' endPc post) True (Config.init ss m) r g :=
  ⟨_, _, coreAt_init hs hpend, hQ⟩

/-! ### Take (`EnvGT`) -/

theorem linkHypsT_QA64MAD (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e')
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e') (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsT (I := isa) A tid pl (QA64MAD ds S (EnvGTA A tid pl) e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex := QA64MD.shape (Φ := fun t => Phase1Shape A t) hnp hm hpost
    (fun f _ ht => phase1Shape_map f ht) (fun _ ht => phase1Shape_reresolve hsz ht) hshape h.1 hex
  link J _ _ _ h hex hJ := QA64MAD.link (by exact fun h => .inl h.2.1) hsz hnp hm hlive hpost J h hex hJ

/-- **`ThreadRuleRXGS.ofSafelyEnvGTMAD`**: `ofSafelyEnvGTMD` with the address
run on `S`. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTMAD
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop} (S : SharedEnv.Layout)
    (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e') (hpl : pl.Valid)
    (hlive : e.rmwLive = true) (hshape : Phase1Tree A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGS G₀ A B tid :=
  ThreadRuleRXGS.ofEnvGT (linkHypsT_QA64MAD (S := S) (tid := tid) hsz hnp hm hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64MD hm hstuck hQ.1 hh) hp hrel hcl

/-- **No fault for `ofSafelyEnvGTMAD`** at declarations agreeing on `S`. -/
theorem noFaultRule_ofSafelyEnvGTMAD_rootD {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e') (hpl : pl.Valid)
    (hlive : e.rmwLive = true) (hshape : Phase1Tree A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) (hag : ds.AgreesOnA S) :
    NoFaultRuleS (ThreadRuleRXGS.ofSafelyEnvGTMAD S hsz hnp hm hpl hlive hshape hpost hstuck hB) :=
  NoFaultRuleS.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp' => by
    obtain ⟨σ, hQ⟩ := InvG.q_at rF t h he hg ht E hnp'
    exact noFault_QA64MAD_rootD (E := EnvGTA A tid pl) hag hnp hm hlive hnf hpost
      (rootOnlyDA_of_phase1Tree hshape) t.st σ tree hQ hex

omit [Kraken.Executable.ValidLayout e] in
theorem invGTMAD_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = [])
    (hQ : QA64MAD ds S (EnvGTA A tid pl) e e' endPc post s (σInit (Config.init ss m) r g)) :
    InvG (I := isa) A tid pl (QA64MAD ds S (EnvGTA A tid pl) e e' endPc post) True (Config.init ss m) r g :=
  ⟨_, _, coreAt_init hs hpend, hQ⟩

/-! ### Cumulative take (`EnvGTU`) -/

theorem linkHypsTU_QA64MAD (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e')
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e') (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsTU (I := isa) A tid pl (QA64MAD ds S (EnvGTUA A tid pl) e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex := QA64MD.shape (Φ := fun t => Phase1Shape A t) hnp hm hpost
    (fun f _ ht => phase1Shape_map f ht) (fun _ ht => phase1Shape_reresolve hsz ht) hshape h.1 hex
  link J _ _ _ h hex hJ := QA64MAD.link (by exact fun h => .inl h.2.1) hsz hnp hm hlive hpost J h hex hJ

/-- **`ThreadRuleRXGS.ofSafelyEnvGTUMAD`**: `ofSafelyEnvGTUMD` with the
address run on `S`. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTUMAD
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop} (S : SharedEnv.Layout)
    (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e') (hpl : pl.Valid)
    (hlive : e.rmwLive = true) (hshape : Phase1Tree A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTUA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGS G₀ A B tid :=
  ThreadRuleRXGS.ofEnvGTU (linkHypsTU_QA64MAD (S := S) (tid := tid) hsz hnp hm hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64MD hm hstuck hQ.1 hh) hp hrel hcl

/-- **No fault for `ofSafelyEnvGTUMAD`** at declarations agreeing on `S`. -/
theorem noFaultRule_ofSafelyEnvGTUMAD_rootD {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e') (hpl : pl.Valid)
    (hlive : e.rmwLive = true) (hshape : Phase1Tree A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTUA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) (hag : ds.AgreesOnA S) :
    NoFaultRuleS (ThreadRuleRXGS.ofSafelyEnvGTUMAD S hsz hnp hm hpl hlive hshape hpost hstuck hB) :=
  NoFaultRuleS.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp' => by
    obtain ⟨σ, hQ⟩ := InvG.q_at rF t h he hg ht E hnp'
    exact noFault_QA64MAD_rootD (E := EnvGTUA A tid pl) hag hnp hm hlive hnf hpost
      (rootOnlyDA_of_phase1Tree hshape) t.st σ tree hQ hex

omit [Kraken.Executable.ValidLayout e] in
theorem invGTUMAD_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = [])
    (hQ : QA64MAD ds S (EnvGTUA A tid pl) e e' endPc post s (σInit (Config.init ss m) r g)) :
    InvG (I := isa) A tid pl (QA64MAD ds S (EnvGTUA A tid pl) e e' endPc post) True (Config.init ss m) r g :=
  ⟨_, _, coreAt_init hs hpend, hQ⟩

/-! ### Take with a claim-conditional RMW (`EnvGTC`) -/

theorem linkHypsTRC_QA64MAD (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e')
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e') (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsTRC (I := isa) A tid pl (QA64MAD ds S (EnvGTCA A tid pl) e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex := QA64MD.shape (Φ := fun t => Phase1ShapeR A t) hnp hm hpost
    (fun f _ ht => phase1ShapeR_map f ht) (fun _ ht => phase1ShapeR_reresolve hsz ht) hshape h.1 hex
  link J _ _ _ h hex hJ := QA64MAD.link (by exact fun h => .inl h.2.1) hsz hnp hm hlive hpost J h hex hJ

/-- **`ThreadRuleRXGS.ofSafelyEnvGTRCMAD`**: `ofSafelyEnvGTRCMD` with the
address run on `S`. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTRCMAD
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop} (S : SharedEnv.Layout)
    (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e') (hpl : pl.Valid)
    (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTCA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGS G₀ A B tid :=
  ThreadRuleRXGS.ofEnvGTRC (linkHypsTRC_QA64MAD (S := S) (tid := tid) hsz hnp hm hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64MD hm hstuck hQ.1 hh) hp hrel hcl

/-- **No fault for `ofSafelyEnvGTRCMAD`** at declarations agreeing on `S`. -/
theorem noFaultRule_ofSafelyEnvGTRCMAD_rootD {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e') (hpl : pl.Valid)
    (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTCA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) (hag : ds.AgreesOnA S) :
    NoFaultRuleS (ThreadRuleRXGS.ofSafelyEnvGTRCMAD S hsz hnp hm hpl hlive hshape hpost hstuck hB) :=
  NoFaultRuleS.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp' => by
    obtain ⟨σ, hQ⟩ := InvGR.q_at rF t h he hg ht E hnp'
    exact noFault_QA64MAD_rootD (E := EnvGTCA A tid pl) hag hnp hm hlive hnf hpost
      (rootOnlyDA_of_phase1TreeR hshape) t.st σ tree hQ hex

omit [Kraken.Executable.ValidLayout e] in
theorem invGTRCMAD_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = [])
    (hQ : QA64MAD ds S (EnvGTCA A tid pl) e e' endPc post s (σInit (Config.init ss m) r g)) :
    InvGR (I := isa) tid pl (QA64MAD ds S (EnvGTCA A tid pl) e e' endPc post) True (Config.init ss m) r g :=
  ⟨σInit (Config.init ss m) r g, Thread.init s, coreAtR_init hs hpend, hQ⟩

/-! ### The claim-conditional RMW (`EnvGC`, `RC`) -/

theorem linkHypsRC_QA64MAD (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e')
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e') (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsRC (I := isa) A tid pl (QA64MAD ds S (EnvGCA A tid pl) e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex := QA64MD.shape (Φ := fun t => Phase1ShapeR A t) hnp hm hpost
    (fun f _ ht => phase1ShapeR_map f ht) (fun _ ht => phase1ShapeR_reresolve hsz ht) hshape h.1 hex
  link J _ _ _ h hex hJ := QA64MAD.link (by exact fun h => .inl h.2.1) hsz hnp hm hlive hpost J h hex hJ

/-- **`ThreadRuleRX.ofSafelyEnvGRCMAD`**: `ofSafelyEnvGRCMD` with the
address run on `S`. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvGRCMAD
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop} (S : SharedEnv.Layout)
    (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e') (hpl : pl.Valid)
    (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGCA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRX A B tid :=
  ThreadRuleRX.ofEnvGRC (linkHypsRC_QA64MAD (S := S) (tid := tid) hsz hnp hm hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64MD hm hstuck hQ.1 hh) hp hrel hcl

/-- **No fault for `ofSafelyEnvGRCMAD`** at declarations agreeing on `S`. -/
theorem noFaultRule_ofSafelyEnvGRCMAD_rootD {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e') (hpl : pl.Valid)
    (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGCA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) (hag : ds.AgreesOnA S) :
    NoFaultRule (ThreadRuleRX.ofSafelyEnvGRCMAD S hsz hnp hm hpl hlive hshape hpost hstuck hB) :=
  noFaultRule_ofEnvGRC_struct _ _ (noFault_QA64MAD_rootD (E := EnvGCA A tid pl) hag hnp hm hlive hnf hpost
    (rootOnlyDA_of_phase1TreeR hshape))

omit [Kraken.Executable.ValidLayout e] in
theorem invGRCMAD_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = [])
    (hQ : QA64MAD ds S (EnvGCA A tid pl) e e' endPc post s (σInit (Config.init ss m) r g)) :
    InvGR (I := isa) tid pl (QA64MAD ds S (EnvGCA A tid pl) e e' endPc post) True (Config.init ss m) r g :=
  ⟨σInit (Config.init ss m) r g, Thread.init s, coreAtR_init hs hpend, hQ⟩

/-! ### The ticket environments (`EnvGTD`, `EnvGTDR`) -/

section TD

variable {D : Dispenser}

theorem linkHypsTD_QA64MAD (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e')
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e') (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsTD (I := isa) A tid pl D (QA64MAD ds S (EnvGTDA A tid pl D) e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex := QA64MD.shape (Φ := fun t => Phase1Shape A t) hnp hm hpost
    (fun f _ ht => phase1Shape_map f ht) (fun _ ht => phase1Shape_reresolve hsz ht) hshape h.1 hex
  link J _ _ _ h hex hJ := QA64MAD.link (by exact fun h => .inl h.2.1) hsz hnp hm hlive hpost J h hex hJ

/-- **`ThreadRuleRXGSXE.ofSafelyEnvGTDMAD`**: `ofSafelyEnvGTDMD` with the
address run on `S`. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRXGSXE.ofSafelyEnvGTDMAD
    {B : Config isa → (modelX isa D.TX).R → (modelX isa D.TX).Ghost → Prop} (S : SharedEnv.Layout)
    (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e') (hpl : pl.Valid)
    (hlive : e.rmwLive = true) (hshape : Phase1Tree A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTDA A tid pl D) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGSXE G₀ D.TX A B tid :=
  ThreadRuleRXGSXE.ofEnvGTD (linkHypsTD_QA64MAD (S := S) (tid := tid) hsz hnp hm hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64MD hm hstuck hQ.1 hh) hp hrel hcl

/-- **No fault for `ofSafelyEnvGTDMAD`** at declarations agreeing on `S`. -/
theorem noFaultRule_ofSafelyEnvGTDMAD_rootD {B : Config isa → (modelX isa D.TX).R → (modelX isa D.TX).Ghost → Prop}
    (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e') (hpl : pl.Valid)
    (hlive : e.rmwLive = true) (hshape : Phase1Tree A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTDA A tid pl D) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) (hag : ds.AgreesOnA S) :
    NoFaultRuleSXE (ThreadRuleRXGSXE.ofSafelyEnvGTDMAD S hsz hnp hm hpl hlive hshape hpost hstuck hB) :=
  NoFaultRuleSXE.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp' => by
    obtain ⟨σ, hQ⟩ := InvGTD.q_at rF t h he hg ht E hnp'
    exact noFault_QA64MAD_rootD (E := EnvGTDA A tid pl D) hag hnp hm hlive hnf hpost
      (rootOnlyDA_of_phase1Tree hshape) t.st σ tree hQ hex

omit [Kraken.Executable.ValidLayout e] in
theorem invGTDMAD_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = [])
    (hQ : QA64MAD ds S (EnvGTDA A tid pl D) e e' endPc post s (σInit (Config.init ss m) r g)) :
    InvGTD (I := isa) A tid pl D (QA64MAD ds S (EnvGTDA A tid pl D) e e' endPc post) True (Config.init ss m) r g :=
  ⟨_, _, coreAt_init hs hpend, hQ, fun _ => by simp [Thread.init, Views.getCoh]⟩

theorem linkHypsTDR_QA64MAD (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e')
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e') (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsTDR (I := isa) A tid pl D (QA64MAD ds S (EnvGTDRA A tid pl D) e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex := QA64MD.shape (Φ := fun t => Phase1ShapeR A t) hnp hm hpost
    (fun f _ ht => phase1ShapeR_map f ht) (fun _ ht => phase1ShapeR_reresolve hsz ht) hshape h.1 hex
  link J _ _ _ h hex hJ := QA64MAD.link (by exact fun h => .inl h.2.1) hsz hnp hm hlive hpost J h hex hJ

/-- **`ThreadRuleRXGSXE.ofSafelyEnvGTDRMAD`**: `ofSafelyEnvGTDRMD` with the
address run on `S`. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRXGSXE.ofSafelyEnvGTDRMAD
    {B : Config isa → (modelX isa D.TX).R → (modelX isa D.TX).Ghost → Prop} (S : SharedEnv.Layout)
    (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e') (hpl : pl.Valid)
    (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTDRA A tid pl D) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGSXE G₀ D.TX A B tid :=
  ThreadRuleRXGSXE.ofEnvGTDR (linkHypsTDR_QA64MAD (S := S) (tid := tid) hsz hnp hm hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64MD hm hstuck hQ.1 hh) hp hrel hcl

/-- **No fault for `ofSafelyEnvGTDRMAD`** at declarations agreeing on `S`. -/
theorem noFaultRule_ofSafelyEnvGTDRMAD_rootD
    {B : Config isa → (modelX isa D.TX).R → (modelX isa D.TX).Ghost → Prop}
    (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e') (hpl : pl.Valid)
    (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTDRA A tid pl D) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) (hag : ds.AgreesOnA S) :
    NoFaultRuleSXE (ThreadRuleRXGSXE.ofSafelyEnvGTDRMAD S hsz hnp hm hpl hlive hshape hpost hstuck hB) :=
  NoFaultRuleSXE.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp' => by
    obtain ⟨σ, hQ⟩ := InvGTDR.q_at rF t h he hg ht E hnp'
    exact noFault_QA64MAD_rootD (E := EnvGTDRA A tid pl D) hag hnp hm hlive hnf hpost
      (rootOnlyDA_of_phase1TreeR hshape) t.st σ tree hQ hex

omit [Kraken.Executable.ValidLayout e] in
theorem invGTDRMAD_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = [])
    (hQ : QA64MAD ds S (EnvGTDRA A tid pl D) e e' endPc post s (σInit (Config.init ss m) r g)) :
    InvGTDR (I := isa) tid pl D (QA64MAD ds S (EnvGTDRA A tid pl D) e e' endPc post) True (Config.init ss m) r g :=
  ⟨_, _, coreAtR_init hs hpend, hQ, fun _ => by simp [Thread.init, Views.getCoh]⟩

end TD

end Families

end Kraken.Promising.AArch64.EnvG

#print axioms Kraken.Promising.AArch64.EnvG.noFault_QA64MAD_rootD
#print axioms Kraken.Promising.AArch64.EnvG.noFaultRule_ofSafelyEnvGMAD_rootD
#print axioms Kraken.Promising.AArch64.EnvG.noFaultRule_ofSafelyEnvGTMAD_rootD
#print axioms Kraken.Promising.AArch64.EnvG.noFaultRule_ofSafelyEnvGTUMAD_rootD
#print axioms Kraken.Promising.AArch64.EnvG.noFaultRule_ofSafelyEnvGTRCMAD_rootD
#print axioms Kraken.Promising.AArch64.EnvG.noFaultRule_ofSafelyEnvGRCMAD_rootD
#print axioms Kraken.Promising.AArch64.EnvG.noFaultRule_ofSafelyEnvGTDMAD_rootD
#print axioms Kraken.Promising.AArch64.EnvG.noFaultRule_ofSafelyEnvGTDRMAD_rootD
