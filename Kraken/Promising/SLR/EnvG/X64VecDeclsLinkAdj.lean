/-
**The x64 `EnvGCAdj` rule link and purity assembly for piece-free code with
strict sized declarations, without a layout**. Generic,
x64. D-forms of `X64AdjLink` and `RelPureEnvX64(F)`.

`X64AdjLink`'s `QX64CAdj` and `RelPureEnvX64`'s `RelPureSpecQX.Holds` ask
for `decls = {}`, a shared layout `S` (`Le16 S`), every access within it
(`E.within S`) and `Split S dmem`. For code that loads through registers an
EnvG proof cannot pin down (unclean-path values are arbitrary) and that has
a private stack, no such layout exists. With piece-free code
(`CodeNoPieces`, `X64VecRunNP`) and strict sized declarations
(`Decls.Sized`, `X64VecDeclsFault`) none of that is needed:

- `QX64VecDAdj A tid pl ds e endPc post`: `QX64CAdj` with `decls = ds` and
  no layout, in `EnvGCAdj` itself;
- `linkHypsFCAdj_QX64VecDAdj` (through `exec_treeJLive_of_instrStepEnvNPD`;
  the shape from `Phase1TreeFX e` at `decls = {}`, `EvTree.underDecls`
  keeping `Phase1ShapeF`), `post_of_halted_QX64VecDAdj`,
  **`ThreadRuleRXF.ofSafelyEnvGFCAdjVecD`**, `invGFCAdjVecD_init`,
  `qx64VecDAdj_of_partialTripleEnv`;
- the purity side: `RelPureSpecVecD` (code, end, post, `ds`),
  `RelPureSpecVecD.Holds`, `relPureSpecVecD_step`, `noNTInv_of_specVecD`,
  **`final_of_relPureSafelyVecD_tsoF`** (`CmpxPublic.
  final_of_relPureSafelyQX_tsoF'` for these specs: Theorem 1′ for `NPSafeF`
  by `theorem1FChain`).

No-fault is not covered: the declarations' mixed-size faults are a `W` law
of the restricted judgment, not excluded.
-/
import Kraken.Promising.SLR.EnvG.X64VecRunNP
import Kraken.Promising.SLR.EnvG.X64AdjLink
import Kraken.Promising.SLR.EnvG.RelPureEnvX64F

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

/-- `underDecls` keeps an access-free tree access-free. -/
theorem accessFree_underDecls {σ : Type} (ds : Decls) :
    ∀ t : EvTree σ, AccessFree t → AccessFree (t.underDecls ds) :=
  accessFree_reresolve ds

/-- `underDecls` keeps deterministic access. -/
theorem detAccess_underDecls {σ : Type} (ds : Decls) :
    ∀ t : EvTree σ, DetAccess t → DetAccess (t.underDecls ds) :=
  detAccess_reresolve ds

/-- `underDecls` keeps the unconstrained single-access shape. -/
theorem singleAccessS2_underDecls {σ : Type} (ds : Decls) :
    ∀ t : EvTree σ, SingleAccessS2 True (fun _ _ => True) (fun _ _ _ => True) True t →
      SingleAccessS2 True (fun _ _ => True) (fun _ _ _ => True) True (t.underDecls ds) :=
  singleAccessS2_reresolve ds

/-- `underDecls` keeps the `F` phase-1 shape (every access becomes either a
fault or the same access at the resolved location). -/
theorem phase1ShapeF_underDecls {σ : Type} (ds : Decls) (t : EvTree σ) (h : Phase1ShapeF t) :
    Phase1ShapeF (t.underDecls ds) :=
  phase1ShapeF_reresolve ds t h

end Kraken.Promising.SLR.EnvG

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-- **Phase-1 code at strict sized declarations**: `Phase1TreeFX` (stated at
`decls = {}`) gives the shape at any declarations. -/
theorem phase1ShapeF_of_treeFX_decls {e : Kraken.Executable Directive} (h : Phase1TreeFX e) {st : State}
    (he : st.exe = e) : ∀ tree, isa.exec st = some tree → Phase1ShapeF tree := by
  intro tree hex
  rw [exec_underDecls] at hex
  obtain ⟨tree₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp hex
  exact phase1ShapeF_map _ (phase1ShapeF_underDecls _ _ (h st.noDecls he rfl tree₀ h₀))

/-- **The thread-local invariant of the `EnvGCAdj` link for piece-free code
with declarations `ds`**: `QX64CAdj` with `decls = ds`, no layout, in
`EnvGCAdj` itself. -/
def QX64VecDAdj (A : Arch) (tid : Nat) (pl : Plan) (ds : Decls) (e : Kraken.Executable Directive)
    (endPc : Int64) (post : MachineState × EStateX → Prop) (st : State) (σ : EStateX) : Prop :=
  st.exe = e ∧ st.decls = ds ∧ st.endPc = endPc ∧
    Safely (e.instrStepEnv (Kraken.Promising.SLR.EnvGCAdj isa A tid pl)) post (st.st, σ)

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {ds : Decls} {e : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateX → Prop}

/-- **The link hypotheses of `EnvGCAdj` at `QX64VecDAdj`**
(`linkHypsFCAdj_QX64CAdj` with declarations, no layout). -/
theorem linkHypsFCAdj_QX64VecDAdj (hpl : pl.Valid) (hsz : ds.Sized) (hnp : CodeNoPieces e)
    (hshape : Phase1TreeFX e) (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsFCAdj (I := isa) A tid pl (QX64VecDAdj A tid pl ds e endPc post) where
  valid := hpl
  shape st _ h tree hex := phase1ShapeF_of_treeFX_decls hshape h.1 tree hex
  link J st σ tree h hex hJ := by
    obtain ⟨he, hds, hend, hsafe⟩ := h
    rcases hsafe.unfold with hp | ⟨R, hR, hk⟩
    · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
      rw [this] at hex; cases hex
    · exact exec_treeJLive_of_instrStepEnvNPD J he (hds ▸ hsz) hnp hR
        (fun m g' hz => hJ _ _ ⟨he, hds, hend, hk _ hz⟩) tree hex

omit [Kraken.Executable.ValidLayout e] in
/-- **`done` at `QX64VecDAdj`** (`post_of_halted_QX64CAdj`). -/
theorem post_of_halted_QX64VecDAdj
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (Kraken.Promising.SLR.EnvGCAdj isa A tid pl) x R)
    {t : Thread isa} {σ : EStateX} (hQ : QX64VecDAdj A tid pl ds e endPc post t.st σ) (hh : t.halted = true) :
    post (t.st.st, σ) := by
  obtain ⟨he, -, hend, hsafe⟩ := hQ
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

/-- **`ThreadRuleRXF.ofSafelyEnvGFCAdjVecD`**: the x64 rule link of
`EnvGCAdj` for piece-free code with strict sized declarations
(`ofSafelyEnvGFCAdjX` without a layout). -/
def _root_.Kraken.Promising.SLR.EnvG.ThreadRuleRXF.ofSafelyEnvGFCAdjVecD
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hsz : ds.Sized) (hnp : CodeNoPieces e) (hshape : Phase1TreeFX e)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (Kraken.Promising.SLR.EnvGCAdj isa A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXF A B tid :=
  ThreadRuleRXF.ofEnvGFCAdj (linkHypsFCAdj_QX64VecDAdj (tid := tid) hpl hsz hnp hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QX64VecDAdj hstuck hQ hh) hp hrel hcl

end Link

/-! ## The start -/

section Start

variable {A : Arch} {tid : Nat} {pl : Plan} {ds : Decls}

/-- **`QX64VecDAdj` from a partial triple** in `EnvGCAdj`
(`qx64CAdj_of_partialTripleEnv`). -/
theorem qx64VecDAdj_of_partialTripleEnv [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Kraken.Executable.ValidLayout (layout p)] {P Q : MachineData → EStateX → Prop}
    {E : Int64 → MachineData → EStateX → Prop}
    (ht : MachineWP.PartialTripleEnv (Kraken.Promising.SLR.EnvGCAdj isa A tid pl) P p Q E)
    (henv : cenv = layout p) {st : State} (he : st.exe = layout p) (hds : st.decls = ds)
    (hend : st.endPc = (layout p).addrOf p.length) (hpc : st.st.2 = (layout p).addrOf 0) {σ : EStateX}
    (hP : P st.st.1 σ) (hE : ∀ a s g, ¬ E a s g := by simp) :
    QX64VecDAdj A tid pl ds (layout p) ((layout p).addrOf p.length) (postOfX p Q) st σ := by
  refine ⟨he, hds, hend, ?_⟩
  have hst : st.st = (st.st.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hpc, Executable.addrOf_zero, Layout.apply_fst]
  rw [hst]
  exact (Program.instrStepEnv_of_partialTripleEnv ht hP henv).mono fun _ h => h.imp id (hE _ _ _)

/-- **The rule's invariant at the initial configuration**, from
`QX64VecDAdj` at `σInitX` (`invGFCAdjX_init`). -/
theorem invGFCAdjVecD_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = []) {e : Kraken.Executable Directive} {endPc : Int64}
    {post : MachineState × EStateX → Prop}
    (hQ : QX64VecDAdj A tid pl ds e endPc post s (σInitX (Config.init ss m) r g)) :
    InvGF (I := isa) tid pl (QX64VecDAdj A tid pl ds e endPc post) True (Config.init ss m) r g :=
  ⟨σInitX (Config.init ss m) r g, Thread.init s, coreAtFX_init hs hpend, hQ⟩

end Start

/-! ## Purity, with declarations, no layout -/

open Kraken.Promising.SLR.EnvSpike

/-- **A thread's purity specification for piece-free code with strict sized
declarations** (`RelPureSpecQX` without the layout): code, end address,
postcondition, declarations. -/
structure RelPureSpecVecD where
  e : Kraken.Executable Directive
  valid : Kraken.Executable.ValidLayout e
  endPc : Int64
  post : MachineState × Unit → Prop
  post_end : ∀ y, post y → y.1.2 = endPc
  ds : Decls
  sized : ds.Sized
  noPieces : CodeNoPieces e

/-- The specification holds at a thread state: its code, end address,
declarations, and `Safely` in `relPureQ A Q` at its machine state. -/
def RelPureSpecVecD.Holds (A : Arch) (Q : Loc → Val → Prop) (sp : RelPureSpecVecD) (st : State) : Prop :=
  st.exe = sp.e ∧ st.endPc = sp.endPc ∧ st.decls = sp.ds ∧
    Safely (sp.e.instrStepEnv (SharedEnv.relPureQ A Q)) sp.post (st.st, ())

/-- **One instruction** (`relPureSpecQX_step`, no layout, declarations). -/
theorem relPureSpecVecD_step {A : Arch} {Q : Loc → Val → Prop} (sp : RelPureSpecVecD) {st : State}
    (h : sp.Holds A Q st) (tree : EvTree State) (hex : isa.exec st = some tree) :
    tree.RelWrites A Q ∧ tree.All (sp.Holds A Q) := by
  obtain ⟨he, hend, hds, hsafe⟩ := h
  have hv := sp.valid
  rcases hsafe.unfold with hP | ⟨R, hT, hR⟩
  · have hpc : st.st.2 = sp.endPc := sp.post_end _ hP
    have hnone : isa.exec st = none := by
      show exec st = none
      simp [exec, hpc, hend]
    rw [hnone] at hex
    cases hex
  · exact exec_treeJ_of_instrStepEnvNPD (TreeJ.relWrites A Q (sp.Holds A Q)) he (hds ▸ sp.sized) sp.noPieces hT
      (fun m g' hm => by cases g'; exact ⟨he, hend, hds, hR _ hm⟩) tree hex

private theorem allMono_vecD {σ : Type} {P P' : σ → Prop} (hP : ∀ s, P s → P' s) :
    ∀ {t : EvTree σ}, t.All P → t.All P'
  | .done s, h => hP s h
  | .fault _, _ => trivial
  | .choose _ _, h => fun i => allMono_vecD hP (h i)
  | .load _ _ _ _, h => fun v => allMono_vecD hP (h v)
  | .store _ _ _ _ _, h => fun b => allMono_vecD hP (h b)
  | .rmw _ _ _ _ _, h => fun v => allMono_vecD hP (h v)
  | .fence _ _, h => fun u => allMono_vecD hP (h u)

/-- **The no-NT invariant, `Arch.tso`** (`noNTInv_of_specQX`). -/
theorem noNTInv_of_specVecD (sp : Nat → RelPureSpecVecD) :
    isa.NoNTInv Arch.tso (fun st => ∃ tid, (sp tid).Holds Arch.tso (fun _ _ => False) st) where
  noNT st h tree hex := by
    obtain ⟨tid, h⟩ := h
    exact EvTree.noNT_tso_of_relWrites_false (relPureSpecVecD_step (sp tid) h tree hex).1
  step st h tree hex := by
    obtain ⟨tid, h⟩ := h
    exact allMono_vecD (fun _ h' => ⟨tid, h'⟩) (relPureSpecVecD_step (sp tid) h tree hex).2

/-- **The x64 purity/adequacy link for `NPSafeF` rules, piece-free code with
strict sized declarations** (`CmpxPublic.final_of_relPureSafelyQX_tsoF'` for
`RelPureSpecVecD`). -/
theorem final_of_relPureSafelyVecD_tsoF {fuel : Nat}
    {states : List isa.State} {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost}
    {B : Config isa → Res → Ghost → Prop} {Φ : Config isa → Prop}
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (sp : Nat → RelPureSpecVecD)
    (h0 : ∀ tid s, states[tid]? = some s → (sp tid).Holds Arch.tso (fun _ _ => False) s)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafeF (model isa) Arch.tso B tid n m True (Config.init states initMem) (rF tid) g₀)
    {c : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c := by
  have hs : ∀ s ∈ states, ∃ tid, (sp tid).Holds Arch.tso (fun _ _ => False) s := fun s hs => by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
    exact ⟨i, h0 i _ (List.getElem?_eq_getElem hi)⟩
  have hstep : ∀ tid st tree, (sp tid).Holds Arch.tso (fun _ _ => False) st → isa.exec st = some tree →
      tree.RelWrites Arch.tso (fun l v => Pred.Pure (g₀.rel l) v) ∧
        tree.All ((sp tid).Holds Arch.tso (fun _ _ => False)) :=
    fun tid _ tree h hex => ⟨EvTree.NoNT.relWrites tso_storeKind_rel
      (EvTree.noNT_tso_of_relWrites_false (relPureSpecVecD_step (sp tid) h tree hex).1),
      (relPureSpecVecD_step (sp tid) h tree hex).2⟩
  have hpure : PromisePure Arch.tso fuel states initMem g₀.rel :=
    promisePure_of_relWrites (fun st => ∃ tid, (sp tid).Holds Arch.tso (fun _ _ => False) st)
      (fun _ hc' tid t ht => ⟨tid, relWrites_reach (fun tid st => (sp tid).Holds Arch.tso (fun _ _ => False) st)
        hstep h0 hc' tid t ht⟩)
      (fun st tree ⟨tid, hJ⟩ hex => (hstep tid st tree hJ hex).1)
  exact final_of_virtual hc hf
    (theorem1FChain Arch.tso fuel B states initMem rF g₀
      (fun _ hc' => Config.ntFree_of_noNTInv (noNTInv_of_specVecD sp) hs hc') hE hpend
      hpure hsafe c hc ⟨c, .refl c, hf⟩) hfin

/-- **The spec from a partial triple** in `relPureQ A Q`, at a thread state
at the start of `p` (`RelPureSpecX.holds_of_partialTripleEnv`, no layout). -/
def RelPureSpecVecD.ofProgram [layout : _root_.Layout] (p : Program)
    [hv : Kraken.Executable.ValidLayout (layout p)] (Q' : MachineData → Unit → Prop) (ds : Decls)
    (hsz : ds.Sized) (hnp : CodeNoPieces (layout p)) : RelPureSpecVecD where
  e := layout p
  valid := hv
  endPc := (layout p).addrOf p.length
  post x := (x.1.2 = (layout p).addrOf p.length ∧ Q' x.1.1 x.2) ∨ False
  post_end _ h := h.elim And.left False.elim
  ds := ds
  sized := hsz
  noPieces := hnp

theorem RelPureSpecVecD.holds_of_partialTripleEnv [CodeEnv] [layout : _root_.Layout] {A : Arch}
    {Q : Loc → Val → Prop} {p : Program} [Kraken.Executable.ValidLayout (layout p)] {P Q' : MachineData → Unit → Prop}
    {E : Int64 → MachineData → Unit → Prop} {ds : Decls} {hsz : ds.Sized} {hnp : CodeNoPieces (layout p)}
    (ht : MachineWP.PartialTripleEnv (SharedEnv.relPureQ A Q) P p Q' E)
    (henv : cenv = layout p) {st : State} (he : st.exe = layout p) (hds : st.decls = ds)
    (hend : st.endPc = (layout p).addrOf p.length) (hpc : st.st.2 = (layout p).addrOf 0)
    (hP : P st.st.1 ()) (hE : ∀ a s g, ¬ E a s g := by simp) :
    (RelPureSpecVecD.ofProgram p Q' ds hsz hnp).Holds A Q st := by
  refine ⟨he, hend, hds, ?_⟩
  have hst : st.st = (st.st.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hpc, Executable.addrOf_zero, Layout.apply_fst]
  rw [hst]
  exact (Program.instrStepEnv_of_partialTripleEnv ht hP henv).mono fun _ h => h.imp id (hE _ _ _)

end Kraken.Promising.X64.EnvG

#print axioms Kraken.Promising.SLR.EnvG.ThreadRuleRXF.ofSafelyEnvGFCAdjVecD
#print axioms Kraken.Promising.X64.EnvG.final_of_relPureSafelyVecD_tsoF
