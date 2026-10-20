/-
**The x64 rule links for threads with strict sized declarations**
. Generic in the environment: one
invariant, `QX64MD`, serves every x64 link family, masked or not.

## Why

Every x64 rule link (`QX64`, `QX64R`, `QX64CAdj`, `QX64M`, …) asks
`st.decls = {}` of the thread, and the verbatim theorems inherit it: they
cover the `.kl` program as written, but not the `.kl` runner's thread
states, which carry the declarations of the `.kl` header (`MemLayout.decls`,
`Kraken/Litmus/Layout.lean`). Declarations are semantic (`exec` resolves
every access through `Decls.resolve`), so the runner's configuration is not
an instance of the theorems.

For **strict sized** declarations (`Decls.Sized`: a typed header) the x64 vector
proofs' `X64VecDeclsFault` reads the thread's tree as
the `decls = {}` tree re-resolved against `ds` (`exec_underDecls`): an
access at a declared footprint, or at an undeclared address, is unchanged; a
mixed-size access becomes a fault. A fault satisfies every tree judgment
(`TreeJ.fault`) and every phase-1 shape, so the `decls = {}` link facts
transfer to `decls = ds` with **no condition on the code** — register-valued
addresses included, which `X64VecDecls.CellsDeclsAgree` could not cover.

## Contents

- Shapes under `EvTree.underDecls` (`Decls.Sized`): `accessFree_underDecls`,
  `detAccess_underDecls`, `singleAccessS(2)_underDecls`,
  `multiAccessS_underDeclsD`, `noRelWrite_underDeclsD`, and so
  `phase1Shape(F/R)_underDecls`, `lrShape_underDeclsD`.
  (`underDecls_access_cases`, `singleAccessS(2)_underDeclsD`,
  `phase1Shape(R)_underDeclsD` are the instances of `A64DeclsCommon`'s
  neutral `…_reresolve(S)`.)
- **`QX64MD ds E S e e' endPc post`**: `QX64M` with `st.decls = ds` in place
  of `st.decls = {}`; `QX64MD.of_QX64M`, `QX64MD.link`, `QX64MD.tree`,
  `QX64MD.shape`, `post_of_halted_QX64MD`. Unmasked uses take `MaskOf.refl`.
- The D forms of the link families the x64 verbatim theorems use, each a
  few lines on the generic facts (`…XMD` beside `…X`/`…XM`): plain
  (`ThreadRuleRX.ofSafelyEnvGXMD`), release-kind RMWs (`…GRXMD`, `QX64RMD`),
  failing release RMWs (`ThreadRuleRXF.ofSafelyEnvGFXMD`), the claim-conditional extension
  (`…GFCXMD`), the adjacency ghost (`…GFCAdjXMD`), `EnvGLRV`
  (`ThreadRuleRX.ofSafelyEnvGLRVXMD`), the take route
  (`ThreadRuleRXGS.ofSafelyEnvGTXMD`) and the take route with a
  claim-conditional RMW (`…GTRCXMD`); the matching `invG…XMD_init`; the
  ticket rule with a release-kind RMW (`linkHypsTDR_QX64MD`).
- Purity with declarations: `RelPureSpecQX.HoldsD`, `relPureSpecQX_stepD`,
  `noNTInv_of_specQXD`, and the chain entries
  `final_of_relPureSafelyQX_tsoD` / `_tsoFD` / `_tsoSD` (copies of the existing
  `_tso` / `_tsoF` / `_tsoS` at `HoldsD`).

Not covered: the no-fault side. `underDecls` turns a mixed-size access into
a fault, so a `NoFaultRule` at `decls = ds` needs the dynamic fact that the
thread's accesses are at declared footprints, which the static
`DirsNoFaultCode` does not give (see `X64VecDeclsFault`'s header).
-/
import Kraken.Promising.SLR.EnvG.X64VecDeclsLinkAdj
import Kraken.Promising.SLR.EnvG.X64MaskLink
import Kraken.Promising.SLR.EnvG.X64MaskLinkMore
import Kraken.Promising.SLR.EnvG.X64MaskLinkTake
import Kraken.Promising.SLR.EnvG.X64MaskLinkRmw
import Kraken.Promising.SLR.EnvG.X64MsQueueMaskAdj
import Kraken.Promising.SLR.EnvG.X64RmwFail
import Kraken.Promising.SLR.EnvG.RelPureEnvX64F
import Kraken.Promising.SLR.EnvG.TakeX64Final
import Kraken.Promising.SLR.EnvG.TicketRRuleLink

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

/-! ## Tree shapes under `underDecls` -/

section Shapes

variable {σ : Type} {ds : Decls}

/-- Under strict sized declarations, re-resolving an event keeps it or makes
it a fault. -/
theorem underDecls_access_cases (hs : ds.Sized) (l : Loc) (k : Loc → EvTree σ) :
    EvTree.access ds l.addr l.bytes k = k l ∨ ∃ m, EvTree.access ds l.addr l.bytes k = .fault m :=
  reresolve_access_cases hs l k

theorem singleAccessS_underDeclsD (hs : ds.Sized) {Lok : Prop} {Sok : Loc → Val → Prop} {Rok : RmwKind → Prop}
    {D : Prop} : ∀ {t : EvTree σ}, SingleAccessS Lok Sok Rok D t → SingleAccessS Lok Sok Rok D (t.underDecls ds) :=
  singleAccessS_reresolveS hs

theorem singleAccessS2_underDeclsD (hs : ds.Sized) {Lok : Prop} {Sok : Loc → Val → Prop}
    {Rok : RmwKind → Loc → (Val → Option Val) → Prop} {D : Prop} :
    ∀ {t : EvTree σ}, SingleAccessS2 Lok Sok Rok D t → SingleAccessS2 Lok Sok Rok D (t.underDecls ds) :=
  singleAccessS2_reresolveS hs

theorem multiAccessS_underDeclsD (hs : ds.Sized) {Lok : Prop} {Sok : Loc → Val → Prop} {Rok : RmwKind → Prop}
    {D : Prop} : ∀ {t : EvTree σ}, MultiAccessS Lok Sok Rok D t → MultiAccessS Lok Sok Rok D (t.underDecls ds)
  | .done _, h => h
  | .fault _, _ => trivial
  | .choose _ k, h => fun i => multiAccessS_underDeclsD hs (t := k i) (h i)
  | .fence _ ret, h => multiAccessS_underDeclsD hs (t := ret ()) h
  | .load k x l ret, h => by
    show MultiAccessS Lok Sok Rok D (EvTree.access ds l.addr l.bytes _)
    rcases underDecls_access_cases hs l (fun l' => .load k x l' fun v => (ret v).reresolve ds) with h' | ⟨m, h'⟩ <;>
      rw [h']
    · exact ⟨h.1, fun v => multiAccessS_underDeclsD hs (t := ret v) (h.2 v)⟩
    · trivial
  | .store k x l v ret, h => by
    show MultiAccessS Lok Sok Rok D (EvTree.access ds l.addr l.bytes _)
    rcases underDecls_access_cases hs l (fun l' => .store k x l' v fun b => (ret b).reresolve ds) with h' | ⟨m, h'⟩ <;>
      rw [h']
    · exact ⟨h.1, fun b => accessFree_underDecls ds _ (h.2 b)⟩
    · trivial
  | .rmw k nr l op ret, h => by
    show MultiAccessS Lok Sok Rok D (EvTree.access ds l.addr l.bytes _)
    rcases underDecls_access_cases hs l (fun l' => .rmw k nr l' op fun v => (ret v).reresolve ds) with h' | ⟨m, h'⟩ <;>
      rw [h']
    · exact ⟨h.1, fun v => accessFree_underDecls ds _ (h.2 v)⟩
    · trivial

theorem noRelWrite_underDeclsD (hs : ds.Sized) {A : Arch} :
    ∀ {t : EvTree σ}, NoRelWrite A t → NoRelWrite A (t.underDecls ds)
  | .done _, _ => trivial
  | .fault _, _ => trivial
  | .choose _ k, h => fun i => noRelWrite_underDeclsD hs (t := k i) (h i)
  | .fence _ ret, h => noRelWrite_underDeclsD hs (t := ret ()) h
  | .load k x l ret, h => by
    show NoRelWrite A (EvTree.access ds l.addr l.bytes _)
    rcases underDecls_access_cases hs l (fun l' => .load k x l' fun v => (ret v).reresolve ds) with h' | ⟨m, h'⟩ <;>
      rw [h']
    · exact fun v => noRelWrite_underDeclsD hs (t := ret v) (h v)
    · trivial
  | .store k x l v ret, h => by
    show NoRelWrite A (EvTree.access ds l.addr l.bytes _)
    rcases underDecls_access_cases hs l (fun l' => .store k x l' v fun b => (ret b).reresolve ds) with h' | ⟨m, h'⟩ <;>
      rw [h']
    · exact ⟨h.1, fun b => noRelWrite_underDeclsD hs (t := ret b) (h.2 b)⟩
    · trivial
  | .rmw k nr l op ret, h => by
    show NoRelWrite A (EvTree.access ds l.addr l.bytes _)
    rcases underDecls_access_cases hs l (fun l' => .rmw k nr l' op fun v => (ret v).reresolve ds) with h' | ⟨m, h'⟩ <;>
      rw [h']
    · exact ⟨h.1, fun v => noRelWrite_underDeclsD hs (t := ret v) (h.2 v)⟩
    · trivial

theorem phase1Shape_underDeclsD (hs : ds.Sized) {A : Arch} {t : EvTree σ} (h : Phase1Shape A t) :
    Phase1Shape A (t.underDecls ds) :=
  phase1Shape_reresolve hs h

theorem phase1ShapeR_underDeclsD (hs : ds.Sized) {A : Arch} {t : EvTree σ} (h : Phase1ShapeR A t) :
    Phase1ShapeR A (t.underDecls ds) :=
  phase1ShapeR_reresolve hs h

theorem phase2Shape_underDeclsD (hs : ds.Sized) {A : Arch} {t : EvTree σ} (h : Phase2Shape A t) :
    Phase2Shape A (t.underDecls ds) :=
  ⟨multiAccessS_underDeclsD hs h.1, noRelWrite_underDeclsD hs h.2⟩

theorem lrStoreShape_underDeclsD (hs : ds.Sized) {t : EvTree σ} (h : LRStoreShape t) :
    LRStoreShape (t.underDecls ds) :=
  let ⟨l, h⟩ := h; ⟨l, multiAccessS_underDeclsD hs h⟩

theorem lrShape_underDeclsD (hs : ds.Sized) {A : Arch} {t : EvTree σ} (h : LRShape A t) :
    LRShape A (t.underDecls ds) := by
  rcases h with h | h | h
  · exact .inl (phase1Shape_underDeclsD hs h)
  · exact .inr (.inl (phase2Shape_underDeclsD hs h))
  · exact .inr (.inr (lrStoreShape_underDeclsD hs h))

end Shapes

end Kraken.Promising.SLR.EnvG

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## The invariant with declarations and the generic link facts -/

/-- **The thread-local invariant over a mask, with declarations `ds`**: `QX64M`
with `st.decls = ds`. -/
def QX64MD (ds : Decls) (E : SharedEnv) (S : SharedEnv.Layout) (e e' : Kraken.Executable Directive) (endPc : Int64)
    (post : MachineState × E.State → Prop) (st : State) (σ : E.State) : Prop :=
  st.exe = e ∧ st.decls = ds ∧ st.endPc = endPc ∧ Split S st.st.1.dmem ∧
    Safely (e'.instrStepEnv (E.within S)) post (st.st, σ)

section Generic

variable {ds : Decls} {E : SharedEnv} {S : SharedEnv.Layout} {e e' : Kraken.Executable Directive} {endPc : Int64}
  {post : MachineState × E.State → Prop}

/-- `QX64M` is `QX64MD {}`. -/
theorem QX64MD.of_QX64M {st : State} {σ : E.State} (h : QX64M E S e e' endPc post st σ) :
    QX64MD {} E S e e' endPc post st σ := h

/-- `QX64MD` at the thread with its declarations dropped is `QX64M`. -/
theorem QX64MD.noDecls {st : State} {σ : E.State} (h : QX64MD ds E S e e' endPc post st σ) :
    QX64M E S e e' endPc post st.noDecls σ :=
  ⟨h.1, rfl, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- **One instruction of the image, under a live tree judgment**, from
`QX64MD` (`QX64M.link` through `exec_treeJLive_of_underDecls`). -/
theorem QX64MD.link [Kraken.Executable.ValidLayout e] (hsz : ds.Sized) (hm : MaskOf e e') (hS : Le16 S)
    (hpost : ∀ y, post y → y.1.2 = endPc) (J : SLR.EnvG.TreeJLive E State) {st : State} {σ : E.State}
    {tree : EvTree State} (h : QX64MD ds E S e e' endPc post st σ) (hex : isa.exec st = some tree)
    (hJ : ∀ st' σ', QX64MD ds E S e e' endPc post st' σ' → J.Post st' σ') : J.W tree σ := by
  obtain ⟨he, hds, hend, hs, hsafe⟩ := h
  rcases hsafe.unfold with hp | ⟨R, hR, hk⟩
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · subst hds
    refine exec_treeJLive_of_underDecls J hsz (fun tree₀ h₀ => ?_) tree hex
    exact exec_treeJLive_of_instrStepEnvW ((J.comap (State.withDecls st.decls)).underDecls st.decls hsz) hS
      (st := st.noDecls) he rfl hs (instrStepEnv_of_mask hm hR).1
      (fun m g' hz hs' => by
        show J.Post (State.withDecls st.decls { st.noDecls with st := m }) g'
        rw [State.withDecls_noDecls_st]
        exact hJ _ _ ⟨he, rfl, hend, hs', hk _ hz⟩) tree₀ h₀

/-- **The thread's tree is the masked `decls = {}` thread's**, re-resolved
against `ds`, up to the executable and declarations in its states. -/
theorem QX64MD.tree [Kraken.Executable.ValidLayout e] (hm : MaskOf e e') (hpost : ∀ y, post y → y.1.2 = endPc)
    {st : State} {σ : E.State} {tree : EvTree State} (h : QX64MD ds E S e e' endPc post st σ)
    (hex : isa.exec st = some tree) :
    ∃ tree', isa.exec { st with exe := e', decls := {} } = some tree' ∧
      tree = (tree'.underDecls ds).map fun s => { s with exe := e, decls := ds } := by
  have hds := h.2.1
  subst hds
  rw [exec_underDecls] at hex
  obtain ⟨tree₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp hex
  obtain ⟨tree', hex', rfl⟩ := QX64M.tree hm hpost h.noDecls h₀
  refine ⟨tree', hex', ?_⟩
  erw [← EvTree.map_underDecls, evTree_map_map_vec]
  rfl

/-- **A per-cell tree shape of the mask holds of the thread's trees**, for
a shape closed under `EvTree.map` and `EvTree.underDecls`. -/
theorem QX64MD.shape [Kraken.Executable.ValidLayout e] (hm : MaskOf e e')
    (hpost : ∀ y, post y → y.1.2 = endPc)
    {Φ : ∀ {σ : Type}, EvTree σ → Prop} (hmap : ∀ {σ τ : Type} (f : σ → τ) (t : EvTree σ), Φ t → Φ (t.map f))
    (hund : ∀ {σ : Type} (t : EvTree σ), Φ t → Φ (t.underDecls ds))
    (hΦ : ∀ st : State, st.exe = e' → st.decls = {} → ∀ tree, isa.exec st = some tree → Φ tree)
    {st : State} {σ : E.State} {tree : EvTree State} (h : QX64MD ds E S e e' endPc post st σ)
    (hex : isa.exec st = some tree) : Φ tree := by
  obtain ⟨tree', hex', rfl⟩ := QX64MD.tree hm hpost h hex
  exact hmap _ _ (hund _ (hΦ { st with exe := e', decls := {} } rfl rfl tree' hex'))

/-- **`done` at `QX64MD`**: a halted thread is at its postcondition, with
the halt read off the mask (`post_of_halted_QX64M`; the declarations play no
part). -/
theorem post_of_halted_QX64MD (hm : MaskOf e e')
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (E.within S) x R)
    {t : Thread isa} {σ : E.State} (hQ : QX64MD ds E S e e' endPc post t.st σ) (hh : t.halted = true) :
    post (t.st.st, σ) := by
  obtain ⟨he, -, hend, -, hsafe⟩ := hQ
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

/-- **One instruction from `QX64MD`, any tree judgment**: every tree of a
thread at `QX64MD ds E S e e endPc post` (declarations strict sized or none)
satisfies a tree judgment `J` of `E` whose leaf condition holds at `QX64MD`
(`TicketX.dispSpecX_stepD` for any `J`).

Moved here from `EnvG/X64Ticket2Public.lean` (same name), so that
the x64 one-instruction lemmas of the specifications shaped like `QX64MD`
(`relPureSpecQX_stepD`, `valSpecX_stepD`, `TicketX.dispSpecX_stepD`) are its
instances. -/
theorem _root_.Kraken.Promising.X64.EnvG.TicketX2.treeJ_of_QX64MD {E : SharedEnv} (J : EnvSpike.TreeJ E State)
    {ds : Decls} (hsz : ds.Sized ∨ ds = {})
    {S : SharedEnv.Layout} (hS : Le16 S) {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
    {endPc : Int64} {post : MachineState × E.State → Prop}
    (hJ : ∀ s g', QX64MD ds E S e e endPc post s g' → J.Post s g')
    (hpost : ∀ y, post y → y.1.2 = endPc) {st : State} {g : E.State} (h : QX64MD ds E S e e endPc post st g)
    (tree : EvTree State) (hex : isa.exec st = some tree) : J.W tree g := by
  obtain ⟨he, hds, hend, hs, hsafe⟩ := h
  rcases hsafe.unfold with hP | ⟨R, hT, hR'⟩
  · rw [exec_eq_none_of_end (by rw [hend]; exact hpost _ hP)] at hex
    cases hex
  rcases hsz with hsz | rfl
  · subst hds
    refine exec_treeJ_of_underDecls (J.toWithin S) hsz (fun tree₀ h₀ => ?_) tree hex
    exact exec_treeJ_of_instrStepEnv (((J.toWithin S).comap (State.withDecls st.decls)).underDecls st.decls hsz)
      (within_fit _ _) hS (st := st.noDecls) he rfl hs hT
      (fun m g' hm hs' => by
        show J.Post (State.withDecls st.decls { st.noDecls with st := m }) g'
        rw [State.withDecls_noDecls_st]
        exact hJ _ _ ⟨he, rfl, hend, hs', hR' _ hm⟩) tree₀ h₀
  · exact exec_treeJ_of_instrStepEnv (J.toWithin S) (within_fit _ _) hS he hds hs hT
      (fun m g' hm hs' => hJ _ _ ⟨he, hds, hend, hs', hR' _ hm⟩) tree hex

/-! ## The link families -/

section Families

variable {ds : Decls} {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout} {e e' : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateX → Prop}

/-! ### Plain `EnvG` -/

theorem linkHyps_QX64MD (hsz : ds.Sized) (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S)
    (hshape : Phase1TreeX A e') (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHyps (I := isa) A tid pl (QX64MD ds (Kraken.Promising.SLR.EnvG isa A tid pl) S e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex := QX64MD.shape (Φ := fun t => Phase1Shape A t) hm hpost
    (fun f _ ht => Kraken.Promising.AArch64.EnvG.phase1Shape_map f ht) (fun _ ht => phase1Shape_underDeclsD hsz ht)
    hshape h hex
  link J _ _ _ h hex hJ := QX64MD.link hsz hm hS hpost J h hex hJ

/-- **`ThreadRuleRX.ofSafelyEnvGXMD`**: `ofSafelyEnvGXM` for a thread with
strict sized declarations `ds`. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvGXMD
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hsz : ds.Sized) (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeX A e')
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRX A B tid :=
  ThreadRuleRX.ofEnvG (linkHyps_QX64MD (tid := tid) hsz hm hpl hS hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QX64MD hm hstuck hQ hh) hp hrel hcl

omit [Kraken.Executable.ValidLayout e] in
theorem invGXMD_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = [])
    (hQ : QX64MD ds (Kraken.Promising.SLR.EnvG isa A tid pl) S e e' endPc post s (σInitX (Config.init ss m) r g)) :
    InvG (I := isa) A tid pl (QX64MD ds (Kraken.Promising.SLR.EnvG isa A tid pl) S e e' endPc post) True
      (Config.init ss m) r g :=
  ⟨_, _, coreAtX_init hs hpend, hQ⟩

/-! ### Release-kind RMWs (`QX64R`) -/

/-- `QX64MD` with the env's release predicates fixed (`QX64R`). -/
def QX64RMD (ds : Decls) (A : Arch) (tid : Nat) (pl : Plan) (S : SharedEnv.Layout)
    (e e' : Kraken.Executable Directive) (endPc : Int64) (post : MachineState × EStateX → Prop)
    (rel₀ : Loc → Pred) (st : State) (σ : EStateX) : Prop :=
  QX64MD ds (Kraken.Promising.SLR.EnvG isa A tid pl) S e e' endPc post st σ ∧ σ.g.rel = rel₀

variable {rel₀ : Loc → Pred}

theorem linkHypsR_QX64MD (hsz : ds.Sized) (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S)
    (hshape : Phase1TreeRX A e') (hG : RelRmwGiveOk isa pl rel₀) (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsR (I := isa) A tid pl (QX64RMD ds A tid pl S e e' endPc post rel₀) where
  valid := hpl
  shape _ _ h _ hex := QX64MD.shape (Φ := fun t => Phase1ShapeR A t) hm hpost
    (fun f _ ht => Kraken.Promising.AArch64.EnvG.phase1ShapeR_map f ht) (fun _ ht => phase1ShapeR_underDeclsD hsz ht)
    hshape h.1 hex
  giveOk _ _ h := h.2 ▸ hG
  link := link_relFix rel₀ fun J _ _ _ h hex hJ => QX64MD.link hsz hm hS hpost J h hex hJ

/-- **`ThreadRuleRX.ofSafelyEnvGRXMD`**: `ofSafelyEnvGRX` over a mask, for a
thread with strict sized declarations `ds`. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvGRXMD
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hsz : ds.Sized) (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeRX A e')
    (hG : RelRmwGiveOk isa pl rel₀) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRX A B tid :=
  ThreadRuleRX.ofEnvGR (linkHypsR_QX64MD (tid := tid) hsz hm hpl hS hshape hG hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QX64MD hm hstuck hQ.1 hh) hp hrel hcl

omit [Kraken.Executable.ValidLayout e] in
theorem invGRXMD_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = [])
    (hQ : QX64MD ds (Kraken.Promising.SLR.EnvG isa A tid pl) S e e' endPc post s (σInitX (Config.init ss m) r g)) :
    InvGR (I := isa) tid pl (QX64RMD ds A tid pl S e e' endPc post g.rel) True (Config.init ss m) r g :=
  ⟨σInitX (Config.init ss m) r g, Thread.init s, coreAtRX_init hs hpend, hQ, rfl⟩

/-! ### Failing release RMWs (`EnvG`, `QX64R`) -/

theorem linkHypsF_QX64MD (hsz : ds.Sized) (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S)
    (hshape : Phase1TreeFX e') (hG : RelRmwGiveOk isa pl rel₀) (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsF (I := isa) A tid pl (QX64RMD ds A tid pl S e e' endPc post rel₀) where
  valid := hpl
  shape _ _ h _ hex := QX64MD.shape (Φ := Phase1ShapeF) hm hpost (fun f _ ht => phase1ShapeF_map f ht)
    (fun _ ht => phase1ShapeF_underDecls ds _ ht) hshape h.1 hex
  giveOk _ _ h := h.2 ▸ hG
  link := link_relFix rel₀ fun J _ _ _ h hex hJ => QX64MD.link hsz hm hS hpost J h hex hJ

/-- **`ThreadRuleRXF.ofSafelyEnvGFXMD`**: `ofSafelyEnvGFX` over a mask, for a
thread with strict sized declarations `ds`. -/
def _root_.Kraken.Promising.SLR.EnvG.ThreadRuleRXF.ofSafelyEnvGFXMD
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hsz : ds.Sized) (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeFX e')
    (hG : RelRmwGiveOk isa pl rel₀) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXF A B tid :=
  ThreadRuleRXF.ofEnvGF (linkHypsF_QX64MD (tid := tid) hsz hm hpl hS hshape hG hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QX64MD hm hstuck hQ.1 hh) hp hrel hcl

omit [Kraken.Executable.ValidLayout e] in
theorem invGFXMD_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = [])
    (hQ : QX64MD ds (Kraken.Promising.SLR.EnvG isa A tid pl) S e e' endPc post s (σInitX (Config.init ss m) r g)) :
    InvGF (I := isa) tid pl (QX64RMD ds A tid pl S e e' endPc post g.rel) True (Config.init ss m) r g :=
  ⟨σInitX (Config.init ss m) r g, Thread.init s, coreAtFX_init hs hpend, hQ, rfl⟩

/-! ### Claim-conditional RMWs with failing release RMWs (`EnvGC`) -/

theorem linkHypsFC_QX64MD (hsz : ds.Sized) (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S)
    (hshape : Phase1TreeFX e') (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsFC (I := isa) A tid pl (QX64MD ds (Kraken.Promising.SLR.EnvGC isa A tid pl) S e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex := QX64MD.shape (Φ := Phase1ShapeF) hm hpost (fun f _ ht => phase1ShapeF_map f ht)
    (fun _ ht => phase1ShapeF_underDecls ds _ ht) hshape h hex
  link J _ _ _ h hex hJ := QX64MD.link hsz hm hS hpost J h hex hJ

/-- **`ThreadRuleRXF.ofSafelyEnvGFCXMD`**: `ofSafelyEnvGFCXM` for a thread
with strict sized declarations `ds`. -/
def _root_.Kraken.Promising.SLR.EnvG.ThreadRuleRXF.ofSafelyEnvGFCXMD
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hsz : ds.Sized) (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeFX e')
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGCX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXF A B tid :=
  ThreadRuleRXF.ofEnvGFC (linkHypsFC_QX64MD (tid := tid) hsz hm hpl hS hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QX64MD hm hstuck hQ hh) hp hrel hcl

omit [Kraken.Executable.ValidLayout e] in
theorem invGFCXMD_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = [])
    (hQ : QX64MD ds (Kraken.Promising.SLR.EnvGC isa A tid pl) S e e' endPc post s (σInitX (Config.init ss m) r g)) :
    InvGF (I := isa) tid pl (QX64MD ds (Kraken.Promising.SLR.EnvGC isa A tid pl) S e e' endPc post) True
      (Config.init ss m) r g :=
  ⟨σInitX (Config.init ss m) r g, Thread.init s, coreAtFX_init hs hpend, hQ⟩

/-! ### The adjacency ghost (`EnvGCAdj`) -/

theorem linkHypsFCAdj_QX64MD (hsz : ds.Sized) (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S)
    (hshape : Phase1TreeFX e') (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsFCAdj (I := isa) A tid pl
      (QX64MD ds (Kraken.Promising.SLR.EnvGCAdj isa A tid pl) S e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex := QX64MD.shape (Φ := Phase1ShapeF) hm hpost (fun f _ ht => phase1ShapeF_map f ht)
    (fun _ ht => phase1ShapeF_underDecls ds _ ht) hshape h hex
  link J _ _ _ h hex hJ := QX64MD.link hsz hm hS hpost J h hex hJ

/-- **`ThreadRuleRXF.ofSafelyEnvGFCAdjXMD`**: `ofSafelyEnvGFCAdjXM` for a
thread with strict sized declarations `ds`. -/
def _root_.Kraken.Promising.SLR.EnvG.ThreadRuleRXF.ofSafelyEnvGFCAdjXMD
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hsz : ds.Sized) (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeFX e')
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGCAdjX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXF A B tid :=
  ThreadRuleRXF.ofEnvGFCAdj (linkHypsFCAdj_QX64MD (tid := tid) hsz hm hpl hS hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QX64MD hm hstuck hQ hh) hp hrel hcl

omit [Kraken.Executable.ValidLayout e] in
theorem invGFCAdjXMD_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = [])
    (hQ : QX64MD ds (Kraken.Promising.SLR.EnvGCAdj isa A tid pl) S e e' endPc post s
      (σInitX (Config.init ss m) r g)) :
    InvGF (I := isa) tid pl (QX64MD ds (Kraken.Promising.SLR.EnvGCAdj isa A tid pl) S e e' endPc post) True
      (Config.init ss m) r g :=
  ⟨σInitX (Config.init ss m) r g, Thread.init s, coreAtFX_init hs hpend, hQ⟩

/-! ### `EnvGLRV` -/

theorem linkHypsLRV_QX64MD (hsz : ds.Sized) (hm : MaskOf e e') (hpl : pl.Valid)
    (hwhole : ∀ e ∈ pl.entries, e.split = none) (hS : Le16 S) (hshape : LRTreeX A e')
    (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsLRV (I := isa) A tid pl (QX64MD ds (Kraken.Promising.SLR.EnvGLRV isa A tid pl) S e e' endPc post) where
  valid := hpl
  whole := hwhole
  shape _ _ h _ hex := QX64MD.shape (Φ := fun t => LRShape A t) hm hpost (fun f _ ht => lrShape_map f ht)
    (fun _ ht => lrShape_underDeclsD hsz ht) hshape h hex
  link J _ _ _ h hex hJ := QX64MD.link hsz hm hS hpost J h hex hJ

/-- **`ThreadRuleRX.ofSafelyEnvGLRVXMD`**: `ofSafelyEnvGLRVXM` for a thread
with strict sized declarations `ds`. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvGLRVXMD
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hsz : ds.Sized) (hm : MaskOf e e') (hpl : pl.Valid) (hwhole : ∀ e ∈ pl.entries, e.split = none) (hS : Le16 S)
    (hshape : LRTreeX A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGLRVX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRX A B tid :=
  ThreadRuleRX.ofEnvGLRV (linkHypsLRV_QX64MD (tid := tid) hsz hm hpl hwhole hS hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QX64MD hm hstuck hQ hh) hp hrel hcl

omit [Kraken.Executable.ValidLayout e] in
theorem invGLRVXMD_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = [])
    (hQ : QX64MD ds (Kraken.Promising.SLR.EnvGLRV isa A tid pl) S e e' endPc post s
      (σInitX (Config.init ss m) r g)) :
    InvGLR (I := isa) A tid pl (QX64MD ds (Kraken.Promising.SLR.EnvGLRV isa A tid pl) S e e' endPc post) True
      (Config.init ss m) r g :=
  ⟨_, _, coreAtLRX_init hs hpend, hQ⟩

/-! ### The take route (`EnvGT`) -/

theorem linkHypsT_QX64MD (hsz : ds.Sized) (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S)
    (hshape : Phase1TreeX A e') (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsT (I := isa) A tid pl (QX64MD ds (Kraken.Promising.SLR.EnvGT isa A tid pl) S e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex := QX64MD.shape (Φ := fun t => Phase1Shape A t) hm hpost
    (fun f _ ht => Kraken.Promising.AArch64.EnvG.phase1Shape_map f ht) (fun _ ht => phase1Shape_underDeclsD hsz ht)
    hshape h hex
  link J _ _ _ h hex hJ := QX64MD.link hsz hm hS hpost J h hex hJ

/-- **`ThreadRuleRXGS.ofSafelyEnvGTXMD`**: `ofSafelyEnvGTXM` for a thread
with strict sized declarations `ds`. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTXMD
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hsz : ds.Sized) (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeX A e')
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGS G₀ A B tid :=
  ThreadRuleRXGS.ofEnvGT (linkHypsT_QX64MD (tid := tid) hsz hm hpl hS hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QX64MD hm hstuck hQ hh) hp hrel hcl

omit [Kraken.Executable.ValidLayout e] in
theorem invGTXMD_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = [])
    (hQ : QX64MD ds (Kraken.Promising.SLR.EnvGT isa A tid pl) S e e' endPc post s (σInitX (Config.init ss m) r g)) :
    InvG (I := isa) A tid pl (QX64MD ds (Kraken.Promising.SLR.EnvGT isa A tid pl) S e e' endPc post) True
      (Config.init ss m) r g :=
  ⟨_, _, coreAtX_init hs hpend, hQ⟩

/-! ### The take route with a claim-conditional RMW (`EnvGTCI`) -/

theorem linkHypsTRC_QX64MD (hsz : ds.Sized) (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S)
    (hshape : Phase1TreeRX A e') (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsTRCI (I := isa) A tid pl (QX64MD ds (EnvGTCI isa A tid pl) S e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex := QX64MD.shape (Φ := fun t => Phase1ShapeR A t) hm hpost
    (fun f _ ht => Kraken.Promising.AArch64.EnvG.phase1ShapeR_map f ht) (fun _ ht => phase1ShapeR_underDeclsD hsz ht)
    hshape h hex
  link J _ _ _ h hex hJ := QX64MD.link hsz hm hS hpost J h hex hJ

/-- **`ThreadRuleRXGS.ofSafelyEnvGTRCXMD`**: `ofSafelyEnvGTRCXM` for a thread
with strict sized declarations `ds`. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTRCXMD
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hsz : ds.Sized) (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeRX A e')
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTCX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGS G₀ A B tid :=
  ThreadRuleRXGS.ofEnvGTRC (linkHypsTRC_QX64MD (tid := tid) hsz hm hpl hS hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QX64MD hm hstuck hQ hh) hp hrel hcl

omit [Kraken.Executable.ValidLayout e] in
theorem invGTRCXMD_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = [])
    (hQ : QX64MD ds (EnvGTCI isa A tid pl) S e e' endPc post s (σInitX (Config.init ss m) r g)) :
    InvGR (I := isa) tid pl (QX64MD ds (EnvGTCI isa A tid pl) S e e' endPc post) True (Config.init ss m) r g :=
  ⟨σInitX (Config.init ss m) r g, Thread.init s, coreAtRX_init hs hpend, hQ⟩

/-! ### The ticket rule with a release-kind ticket RMW (`EnvGTDR`) -/

/-- **The link hypotheses of the ticket rule with a release-kind ticket RMW
at `QX64MD`** (from the x64 ticket lock proof's `TicketX.linkHypsTDR_QX64MDX`, which
is now this at `MaskOf.refl` or `linkHypsTDR_QX64TDR` at `ds = {}`). -/
theorem linkHypsTDR_QX64MD {D : Dispenser} (hsz : ds.Sized) (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S)
    (hshape : Phase1TreeRX A e') (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsTDR (I := isa) A tid pl D (QX64MD ds (Kraken.Promising.SLR.EnvGTDR isa A tid pl D) S e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex := QX64MD.shape (Φ := fun t => Phase1ShapeR A t) hm hpost
    (fun f _ ht => Kraken.Promising.AArch64.EnvG.phase1ShapeR_map f ht) (fun _ ht => phase1ShapeR_underDeclsD hsz ht)
    hshape h hex
  link J _ _ _ h hex hJ := QX64MD.link hsz hm hS hpost J h hex hJ

end Families

/-! ## Purity with declarations -/

section Purity

variable {Q : Loc → Val → Prop}

/-- `EvTree.All` is monotone (a copy of `RelPureEnvX64`'s private `all_mono`). -/
private theorem all_monoD {σ : Type} {P P' : σ → Prop} (hP : ∀ s, P s → P' s) :
    ∀ {t : EvTree σ}, t.All P → t.All P'
  | .done s, h => hP s h
  | .fault _, _ => trivial
  | .choose _ _, h => fun i => all_monoD hP (h i)
  | .load _ _ _ _, h => fun v => all_monoD hP (h v)
  | .store _ _ _ _ _, h => fun b => all_monoD hP (h b)
  | .rmw _ _ _ _ _, h => fun v => all_monoD hP (h v)
  | .fence _ _, h => fun u => all_monoD hP (h u)

/-- **The all-release specification holds at a thread state with strict
sized declarations `ds`** (`RelPureSpecQX.Holds` with `decls = ds`). -/
def _root_.Kraken.Promising.X64.EnvG.RelPureSpecQX.HoldsD {A : Arch} (sp : RelPureSpecQX A Q) (ds : Decls)
    (st : State) : Prop :=
  st.exe = sp.e ∧ st.endPc = sp.endPc ∧ st.decls = ds ∧ Split sp.S st.st.1.dmem ∧
    Safely (sp.e.instrStepEnv ((SharedEnv.relPureQ A Q).within sp.S)) sp.post (st.st, ())

/-- `Holds` is `HoldsD {}`. -/
theorem RelPureSpecQX.holdsD_of_holds {A : Arch} {sp : RelPureSpecQX A Q} {st : State} (h : sp.Holds st) :
    sp.HoldsD {} st := h

/-- **One instruction** (`relPureSpecQX_step` with declarations). -/
theorem relPureSpecQX_stepD {A : Arch} (sp : RelPureSpecQX A Q) {ds : Decls} (hsz : ds.Sized) {st : State}
    (h : sp.HoldsD ds st) (tree : EvTree State) (hex : isa.exec st = some tree) :
    tree.RelWrites A Q ∧ tree.All (sp.HoldsD ds) :=
  haveI := sp.valid
  TicketX2.treeJ_of_QX64MD (EnvSpike.TreeJ.relWrites A Q (sp.HoldsD ds)) (Or.inl hsz) sp.le16
    (fun _ _ h => ⟨h.1, h.2.2.1, h.2.1, h.2.2.2⟩) sp.post_end ⟨h.1, h.2.2.1, h.2.1, h.2.2.2⟩ tree hex

/-- **The no-NT invariant of a program with declarations** (`noNTInv_of_specQX`). -/
theorem noNTInv_of_specQXD (sp : Nat → RelPureSpecQX Arch.tso fun _ _ => False) (ds : Nat → Decls)
    (hsz : ∀ tid, (ds tid).Sized) :
    isa.NoNTInv Arch.tso (fun st => ∃ tid, (sp tid).HoldsD (ds tid) st) where
  noNT st h tree hex := by
    obtain ⟨tid, h⟩ := h
    exact EvTree.noNT_tso_of_relWrites_false (relPureSpecQX_stepD (sp tid) (hsz tid) h tree hex).1
  step st h tree hex := by
    obtain ⟨tid, h⟩ := h
    exact all_monoD (fun _ h' => ⟨tid, h'⟩) (relPureSpecQX_stepD (sp tid) (hsz tid) h tree hex).2

/-- **`final_of_relPureSafelyQX_tso` with declarations**: the threads'
all-release specifications hold with strict sized declarations `ds tid`. -/
theorem final_of_relPureSafelyQX_tsoD (fuel : Nat) {states : List isa.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop}
    {Φ : Config isa → Prop}
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (sp : Nat → RelPureSpecQX Arch.tso fun _ _ => False) (ds : Nat → Decls) (hsz : ∀ tid, (ds tid).Sized)
    (h0 : ∀ tid s, states[tid]? = some s → (sp tid).HoldsD (ds tid) s)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafe (model isa) Arch.tso B tid n m True (Config.init states initMem) (rF tid) g₀)
    {c : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c := by
  have hs : ∀ s ∈ states, ∃ tid, (sp tid).HoldsD (ds tid) s := fun s hs => by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
    exact ⟨i, h0 i _ (List.getElem?_eq_getElem hi)⟩
  exact final_of_relWritesJ Arch.tso fuel (fun _ hc' => Config.ntFree_of_noNTInv (noNTInv_of_specQXD sp ds hsz) hs hc')
    hE hpend (fun tid st => (sp tid).HoldsD (ds tid) st)
    (fun tid _ tree h hex => ⟨EvTree.NoNT.relWrites tso_storeKind_rel
      (EvTree.noNT_tso_of_relWrites_false (relPureSpecQX_stepD (sp tid) (hsz tid) h tree hex).1),
      (relPureSpecQX_stepD (sp tid) (hsz tid) h tree hex).2⟩) h0 hsafe hc hf hfin

/-- **`final_of_relPureSafelyQX_tsoF` with declarations.** -/
theorem final_of_relPureSafelyQX_tsoFD {fuel : Nat} (hchain : Theorem1FChain (I := isa) Arch.tso fuel)
    {states : List isa.State} {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost}
    {B : Config isa → Res → Ghost → Prop} {Φ : Config isa → Prop}
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (sp : Nat → RelPureSpecQX Arch.tso fun _ _ => False) (ds : Nat → Decls) (hsz : ∀ tid, (ds tid).Sized)
    (h0 : ∀ tid s, states[tid]? = some s → (sp tid).HoldsD (ds tid) s)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafeF (model isa) Arch.tso B tid n m True (Config.init states initMem) (rF tid) g₀)
    {c : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c := by
  have hs : ∀ s ∈ states, ∃ tid, (sp tid).HoldsD (ds tid) s := fun s hs => by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
    exact ⟨i, h0 i _ (List.getElem?_eq_getElem hi)⟩
  have hstep : ∀ tid st tree, (sp tid).HoldsD (ds tid) st → isa.exec st = some tree →
      tree.RelWrites Arch.tso (fun l v => Pred.Pure (g₀.rel l) v) ∧ tree.All ((sp tid).HoldsD (ds tid)) :=
    fun tid _ tree h hex => ⟨EvTree.NoNT.relWrites tso_storeKind_rel
      (EvTree.noNT_tso_of_relWrites_false (relPureSpecQX_stepD (sp tid) (hsz tid) h tree hex).1),
      (relPureSpecQX_stepD (sp tid) (hsz tid) h tree hex).2⟩
  have hpure : PromisePure Arch.tso fuel states initMem g₀.rel :=
    promisePure_of_relWrites (fun st => ∃ tid, (sp tid).HoldsD (ds tid) st)
      (fun _ hc' tid t ht => ⟨tid, relWrites_reach (fun tid st => (sp tid).HoldsD (ds tid) st) hstep h0 hc' tid t ht⟩)
      (fun st tree ⟨tid, hJ⟩ hex => (hstep tid st tree hJ hex).1)
  exact final_of_virtual hc hf
    (hchain B states initMem rF g₀ (fun _ hc' => Config.ntFree_of_noNTInv (noNTInv_of_specQXD sp ds hsz) hs hc')
      hE hpend hpure hsafe c hc ⟨c, .refl c, hf⟩) hfin

/-- **`final_of_relPureSafelyQX_tsoS` with declarations.** -/
theorem final_of_relPureSafelyQX_tsoSD (fuel : Nat) {states : List isa.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop}
    {Φ : Config isa → Prop}
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (sp : Nat → RelPureSpecQX Arch.tso fun _ _ => False) (ds : Nat → Decls) (hsz : ∀ tid, (ds tid).Sized)
    (h0 : ∀ tid s, states[tid]? = some s → (sp tid).HoldsD (ds tid) s)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafeP (model isa) Arch.tso B tid G₀ (K2Scope (model isa) AllocIds) n m True (Config.init states initMem)
        (rF tid) g₀)
    {c : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c := by
  have hs : ∀ s ∈ states, ∃ tid, (sp tid).HoldsD (ds tid) s := fun s hs => by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
    exact ⟨i, h0 i _ (List.getElem?_eq_getElem hi)⟩
  exact final_of_relWritesJSX Arch.tso fuel
    (fun _ hc' => Config.ntFree_of_noNTInv (noNTInv_of_specQXD sp ds hsz) hs hc')
    hE hpend (fun tid st => (sp tid).HoldsD (ds tid) st)
    (fun tid _ tree h hex => ⟨EvTree.NoNT.relWrites tso_storeKind_rel
      (EvTree.noNT_tso_of_relWrites_false (relPureSpecQX_stepD (sp tid) (hsz tid) h tree hex).1),
      (relPureSpecQX_stepD (sp tid) (hsz tid) h tree hex).2⟩) h0 hsafe hc hf hfin

end Purity

end Kraken.Promising.X64.EnvG

#print axioms Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvGXMD
#print axioms Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvGRXMD
#print axioms Kraken.Promising.SLR.EnvG.ThreadRuleRXF.ofSafelyEnvGFXMD
#print axioms Kraken.Promising.SLR.EnvG.ThreadRuleRXF.ofSafelyEnvGFCXMD
#print axioms Kraken.Promising.SLR.EnvG.ThreadRuleRXF.ofSafelyEnvGFCAdjXMD
#print axioms Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvGLRVXMD
#print axioms Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTXMD
#print axioms Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTRCXMD
#print axioms Kraken.Promising.X64.EnvG.final_of_relPureSafelyQX_tsoD
#print axioms Kraken.Promising.X64.EnvG.final_of_relPureSafelyQX_tsoFD
#print axioms Kraken.Promising.X64.EnvG.final_of_relPureSafelyQX_tsoSD
