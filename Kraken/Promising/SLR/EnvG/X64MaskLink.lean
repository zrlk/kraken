/-
**The x64 rule links over a masked image**. The device is
`EnvG/X64MaskCore.lean`'s: the thread's `Safely`
judgment is over a mask `e'` of its executable `e` (`MaskOf e e'`: the
other roles' code and the cell at the exit label replaced by data cells).

- **`QX64M E S e e' endPc post`**: `QX64`'s invariant with the `Safely`
  judgment over the mask, in `E.within S`. It is generic in the environment
  `E`, so one invariant serves every x64 link family.
- The generic link facts, from which each family's `LinkHyps…` is a few
  lines:
  - `QX64M.link`: one instruction of the image under a live tree judgment
    (`exec_treeJLive_of_instrStepEnvW` at the image's step that the mask's
    step is);
  - `QX64M.tree`: the thread's tree is the masked thread's tree, up to the
    executable in its states, so a per-cell tree shape closed under
    `EvTree.map` needs to hold only of the **mask** (`Phase1TreeFX e'`,
    `Phase1TreeRX A e'`, …: the thread's own cells, the other roles' code
    excluded). This is the pc-restricted phase-1 shape;
  - `post_of_halted_QX64M`: `done`, with the halt from the mask
    (`hstuck` over `e'`, which holds at a masked exit cell even when the
    image has code there);
  - `noFault_QX64M`: the trees are fault-free for fault-free non-data cells
    (`DirsNoFaultCode e`).
- **The `FC` family** (claim-conditional environment with failing release
  RMWs, `EnvGCX`): `linkHypsFC_QX64M`, `ThreadRuleRXF.ofSafelyEnvGFCXM`,
  `noFaultRuleF_ofSafelyEnvGFCXM`, `invGFCXM_init`.

Phase-1 limits otherwise apply: single-access trees, read-side acquire
only, every access within the layout `S` (`Le16 S`).
-/
import Kraken.Promising.SLR.EnvG.X64MaskCore
import Kraken.Promising.SLR.EnvG.X64RmwFailGhost
import Kraken.Promising.SLR.EnvG.X64ImageNoFault

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## The invariant and the generic link facts -/

/-- **The thread-local invariant over a mask**: the image `e`, no
declarations, the end `endPc`, the private memory split by `S`, and a
`Safely` judgment over the mask `e'` in `E.within S`. -/
def QX64M (E : SharedEnv) (S : SharedEnv.Layout) (e e' : Kraken.Executable Directive) (endPc : Int64)
    (post : MachineState × E.State → Prop) (st : State) (σ : E.State) : Prop :=
  st.exe = e ∧ st.decls = {} ∧ st.endPc = endPc ∧ Split S st.st.1.dmem ∧
    Safely (e'.instrStepEnv (E.within S)) post (st.st, σ)

section Generic

variable {E : SharedEnv} {S : SharedEnv.Layout} {e e' : Kraken.Executable Directive} {endPc : Int64}
  {post : MachineState × E.State → Prop}

/-- **One instruction of the image, under a live tree judgment**, from
`QX64M`: the mask's step is the image's, and the successors are again in
`QX64M`. -/
theorem QX64M.link [Kraken.Executable.ValidLayout e] (hm : MaskOf e e') (hS : Le16 S)
    (hpost : ∀ y, post y → y.1.2 = endPc) (J : SLR.EnvG.TreeJLive E State) {st : State} {σ : E.State}
    {tree : EvTree State} (h : QX64M E S e e' endPc post st σ) (hex : isa.exec st = some tree)
    (hJ : ∀ st' σ', QX64M E S e e' endPc post st' σ' → J.Post st' σ') : J.W tree σ := by
  obtain ⟨he, hds, hend, hs, hsafe⟩ := h
  rcases hsafe.unfold with hp | ⟨R, hR, hk⟩
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · exact exec_treeJLive_of_instrStepEnvW J hS he hds hs (instrStepEnv_of_mask hm hR).1
      (fun m g' hz hs' => hJ _ _ ⟨he, hds, hend, hs', hk _ hz⟩) tree hex

/-- **The thread's tree is the masked thread's**, up to the executable in
its states: a thread in `QX64M` with a tree is at a cell the mask shares. -/
theorem QX64M.tree [Kraken.Executable.ValidLayout e] (hm : MaskOf e e') (hpost : ∀ y, post y → y.1.2 = endPc)
    {st : State} {σ : E.State} {tree : EvTree State} (h : QX64M E S e e' endPc post st σ)
    (hex : isa.exec st = some tree) :
    ∃ tree', isa.exec { st with exe := e' } = some tree' ∧ tree = tree'.map fun s => { s with exe := e } := by
  obtain ⟨he, -, hend, -, hsafe⟩ := h
  rcases hsafe.unfold with hp | ⟨R, hR, -⟩
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · obtain ⟨-, d, z, r, r', hc, hc'⟩ := instrStepEnv_of_mask hm hR
    exact exec_of_mask hm he hc hc' hex

/-- **A per-cell tree shape of the mask holds of the thread's trees**: for
a shape `Φ` closed under `EvTree.map` that every masked thread state's tree
has (`Phase1TreeFX e'` and the like). -/
theorem QX64M.shape [Kraken.Executable.ValidLayout e] (hm : MaskOf e e') (hpost : ∀ y, post y → y.1.2 = endPc)
    {Φ : ∀ {σ : Type}, EvTree σ → Prop} (hmap : ∀ {σ τ : Type} (f : σ → τ) (t : EvTree σ), Φ t → Φ (t.map f))
    (hΦ : ∀ st : State, st.exe = e' → st.decls = {} → ∀ tree, isa.exec st = some tree → Φ tree)
    {st : State} {σ : E.State} {tree : EvTree State} (h : QX64M E S e e' endPc post st σ)
    (hex : isa.exec st = some tree) : Φ tree := by
  obtain ⟨tree', hex', rfl⟩ := QX64M.tree hm hpost h hex
  exact hmap _ _ (hΦ { st with exe := e' } rfl h.2.1 tree' hex')

/-- **`done` at `QX64M`**: a halted thread is at its postcondition, with the
halt read off the mask. -/
theorem post_of_halted_QX64M (hm : MaskOf e e')
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (E.within S) x R)
    {t : Thread isa} {σ : E.State} (hQ : QX64M E S e e' endPc post t.st σ) (hh : t.halted = true) :
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

/-- **Every tree from a `QX64M`-state is fault-free**, for an image whose
non-data cells are fault-free. -/
theorem noFault_QX64M [Kraken.Executable.ValidLayout e] (hm : MaskOf e e') (hnf : DirsNoFaultCode e)
    (hpost : ∀ y, post y → y.1.2 = endPc) :
    ∀ st σ tree, QX64M E S e e' endPc post st σ → isa.exec st = some tree → tree.NoFault := by
  intro st σ tree h hex
  obtain ⟨he, hds, hend, -, hsafe⟩ := h
  rcases hsafe.unfold with hp | ⟨R, hR, -⟩
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · exact noFault_of_exec_step he hds hnf (instrStepEnv_of_mask hm hR).1 tree hex

end Generic

/-! ## The `FC` family: `EnvGCX` with failing release RMWs -/

section LinkFC

variable {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout} {e e' : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateX → Prop}

/-- **The link hypotheses of `EnvGC` with failing release RMWs at `QX64M`**
(`linkHypsFC_QX64C` over a mask: the shape of the mask's cells only). -/
theorem linkHypsFC_QX64M (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeFX e')
    (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsFC (I := isa) A tid pl (QX64M (Kraken.Promising.SLR.EnvGC isa A tid pl) S e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex := QX64M.shape (Φ := Phase1ShapeF) hm hpost (fun f _ ht => phase1ShapeF_map f ht) hshape h hex
  link J _ _ _ h hex hJ := QX64M.link hm hS hpost J h hex hJ

/-- **`ThreadRuleRXF.ofSafelyEnvGFCXM`**: `ofSafelyEnvGFCX` over a mask `e'`
of the image `e`: the shape `Phase1TreeFX e'` of the mask (the thread's own
cells), the halt `hstuck` of the mask (a masked exit cell). -/
def _root_.Kraken.Promising.SLR.EnvG.ThreadRuleRXF.ofSafelyEnvGFCXM
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeFX e')
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGCX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXF A B tid :=
  ThreadRuleRXF.ofEnvGFC (linkHypsFC_QX64M (tid := tid) hm hpl hS hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QX64M hm hstuck hQ hh) hp hrel hcl

/-- **The no-fault rule of `ofSafelyEnvGFCXM`**, unconditional in the
thread's promises, for an image whose non-data cells are fault-free. -/
theorem noFaultRuleF_ofSafelyEnvGFCXM {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeFX e')
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGCX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFaultCode e) :
    NoFaultRuleF (ThreadRuleRXF.ofSafelyEnvGFCXM hm hpl hS hshape hpost hstuck hB) :=
  noFaultRuleF_ofEnvGFC_struct _ _ (noFault_QX64M (E := Kraken.Promising.SLR.EnvGC isa A tid pl) hm hnf hpost)

end LinkFC

/-- **The rule's invariant of `ofSafelyEnvGFCXM` at the initial
configuration**, from `QX64M` at `σInitX` (`invGFCX_init` over a mask). -/
theorem invGFCXM_init {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout} {ss : List isa.State}
    {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s) {r : Res} {g : Ghost} (hpend : g.pend = [])
    {e e' : Kraken.Executable Directive} {endPc : Int64} {post : MachineState × EStateX → Prop}
    (hQ : QX64M (Kraken.Promising.SLR.EnvGC isa A tid pl) S e e' endPc post s (σInitX (Config.init ss m) r g)) :
    InvGF (I := isa) tid pl (QX64M (Kraken.Promising.SLR.EnvGC isa A tid pl) S e e' endPc post) True
      (Config.init ss m) r g :=
  ⟨σInitX (Config.init ss m) r g, Thread.init s, coreAtFX_init hs hpend, hQ⟩

/-! ## Range masks of phase-1 images (`A64MaskHelpers`' lemmas, x64) -/

/-- A label cell is phase-1 with failing release RMWs. -/
theorem label_dirPhase1FX_any (l : Label) (e : _root_.Executable) (z : Nat) : DirPhase1FX e (.label l) z := by
  intro s pc
  simp [_root_.Directive.interp, Kraken.Promising.X64.toEv, Phase1ShapeF, DetAccess, SingleAccessS2, AccessFree]

/-- A data cell is phase-1 with failing release RMWs (its tree is a
fault). -/
theorem byteArray_dirPhase1FX_any (b : ByteArray) (e : _root_.Executable) (z : Nat) :
    DirPhase1FX e (.byteArray b) z := by
  intro s pc
  simp [_root_.Directive.interp, Kraken.Promising.X64.toEv, Phase1ShapeF, DetAccess, SingleAccessS2, AccessFree]

/-- **A range mask of an image whose kept slice is phase-1 is phase-1**
(failing release RMWs): only the kept cells, labels and empty data cells
remain. -/
theorem phase1TreeFX_maskKeep_range [layout : _root_.Layout] {p : Program} [Executable.ValidLayout (layout p)]
    {lo hi : Nat} (h : ∀ d ∈ (p.drop lo).take (hi - lo), ∀ (e : _root_.Executable) z, DirPhase1FX e d z) :
    Phase1TreeFX (layout (p.maskKeep (keepRange lo hi))) :=
  haveI := ValidLayout.of_mask (maskOf_layout (layout := layout) (keepRange lo hi) p)
  phase1TreeFX_of_dirs (dirsPhase1FX_layout (mem_maskKeep_range (Φd := fun d => ∀ e z, DirPhase1FX e d z)
    h (fun l => label_dirPhase1FX_any l) (byteArray_dirPhase1FX_any _)))

end Kraken.Promising.X64.EnvG

#print axioms Kraken.Promising.SLR.EnvG.ThreadRuleRXF.ofSafelyEnvGFCXM
#print axioms Kraken.Promising.X64.EnvG.noFaultRuleF_ofSafelyEnvGFCXM
#print axioms Kraken.Promising.X64.EnvG.invGFCXM_init
