/-
**More x64 rule links over a masked image**. `EnvG/X64MaskLink.lean`'s `QX64M`
and its generic link facts
(`QX64M.link`, `QX64M.shape`, `post_of_halted_QX64M`, `noFault_QX64M`),
instantiated at two more x64 families:

- **plain `EnvG`** (`ofSafelyEnvGX` over a mask): `linkHyps_QX64M`,
  `ThreadRuleRX.ofSafelyEnvGXM`, `noFaultRule_ofSafelyEnvGXM`, `invGXM_init`;
- **`EnvGLRV`** (`ofSafelyEnvGLRVX` over a mask): `linkHypsLRV_QX64M`,
  `ThreadRuleRX.ofSafelyEnvGLRVXM`, `noFaultRule_ofSafelyEnvGLRVXM`,
  `invGLRVXM_init`.

In each, the shape (`Phase1TreeX A e'`, `LRTreeX A e'`) and the halt
(`hstuck`) are the mask's, the fault-freedom (`DirsNoFaultCode e`) the
image's.
-/
import Kraken.Promising.SLR.EnvG.X64MaskLink
import Kraken.Promising.SLR.EnvG.LRValX64

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## Plain `EnvG` -/

section LinkG

variable {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout} {e e' : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateX → Prop}

/-- **The link hypotheses of `EnvG` at `QX64M`** (`linkHyps_QX64` over a
mask: the shape of the mask's cells only). -/
theorem linkHyps_QX64M (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeX A e')
    (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHyps (I := isa) A tid pl (QX64M (Kraken.Promising.SLR.EnvG isa A tid pl) S e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex :=
    QX64M.shape (Φ := fun t => Phase1Shape A t) hm hpost (fun f _ ht => phase1Shape_map f ht) hshape h hex
  link J _ _ _ h hex hJ := QX64M.link hm hS hpost J h hex hJ

/-- **`ThreadRuleRX.ofSafelyEnvGXM`**: `ofSafelyEnvGX` over a mask `e'` of
the image `e`: the shape `Phase1TreeX A e'` and the halt `hstuck` of the
mask. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvGXM
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeX A e')
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRX A B tid :=
  ThreadRuleRX.ofEnvG (linkHyps_QX64M (tid := tid) hm hpl hS hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QX64M hm hstuck hQ hh) hp hrel hcl

/-- **The no-fault rule of `ofSafelyEnvGXM`**, for an image whose non-data
cells are fault-free. -/
theorem noFaultRule_ofSafelyEnvGXM {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeX A e')
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFaultCode e) :
    NoFaultRule (ThreadRuleRX.ofSafelyEnvGXM hm hpl hS hshape hpost hstuck hB) :=
  noFaultRule_ofEnvG_struct _ _ (noFault_QX64M (E := Kraken.Promising.SLR.EnvG isa A tid pl) hm hnf hpost)

end LinkG

/-- **The rule's invariant of `ofSafelyEnvGXM` at the initial
configuration**, from `QX64M` at `σInitX` (`invGX_init` over a mask). -/
theorem invGXM_init {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout} {ss : List isa.State}
    {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s) {r : Res} {g : Ghost} (hpend : g.pend = [])
    {e e' : Kraken.Executable Directive} {endPc : Int64} {post : MachineState × EStateX → Prop}
    (hQ : QX64M (Kraken.Promising.SLR.EnvG isa A tid pl) S e e' endPc post s (σInitX (Config.init ss m) r g)) :
    InvG (I := isa) A tid pl (QX64M (Kraken.Promising.SLR.EnvG isa A tid pl) S e e' endPc post) True
      (Config.init ss m) r g :=
  ⟨_, _, coreAtX_init hs hpend, hQ⟩

/-! ## `EnvGLRV` -/

section LinkLRV

variable {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout} {e e' : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateX → Prop}

/-- **The link hypotheses of `EnvGLRV` at `QX64M`** (`linkHypsLRV_QX64` over
a mask). -/
theorem linkHypsLRV_QX64M (hm : MaskOf e e') (hpl : pl.Valid) (hwhole : ∀ e ∈ pl.entries, e.split = none)
    (hS : Le16 S) (hshape : LRTreeX A e') (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsLRV (I := isa) A tid pl (QX64M (Kraken.Promising.SLR.EnvGLRV isa A tid pl) S e e' endPc post) where
  valid := hpl
  whole := hwhole
  shape _ _ h _ hex :=
    QX64M.shape (Φ := fun t => LRShape A t) hm hpost (fun f _ ht => lrShape_map f ht) hshape h hex
  link J _ _ _ h hex hJ := QX64M.link hm hS hpost J h hex hJ

/-- **`ThreadRuleRX.ofSafelyEnvGLRVXM`**: `ofSafelyEnvGLRVX` over a mask `e'`
of the image `e`: the shape `LRTreeX A e'` and the halt `hstuck` of the
mask. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvGLRVXM
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hm : MaskOf e e') (hpl : pl.Valid) (hwhole : ∀ e ∈ pl.entries, e.split = none) (hS : Le16 S)
    (hshape : LRTreeX A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGLRVX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRX A B tid :=
  ThreadRuleRX.ofEnvGLRV (linkHypsLRV_QX64M (tid := tid) hm hpl hwhole hS hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QX64M hm hstuck hQ hh) hp hrel hcl

/-- **The no-fault rule of `ofSafelyEnvGLRVXM`**, for an image whose
non-data cells are fault-free. -/
theorem noFaultRule_ofSafelyEnvGLRVXM {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hm : MaskOf e e') (hpl : pl.Valid) (hwhole : ∀ e ∈ pl.entries, e.split = none) (hS : Le16 S)
    (hshape : LRTreeX A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGLRVX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFaultCode e) :
    NoFaultRule (ThreadRuleRX.ofSafelyEnvGLRVXM hm hpl hwhole hS hshape hpost hstuck hB) :=
  noFaultRule_ofEnvGLRV_struct _ _ (noFault_QX64M (E := Kraken.Promising.SLR.EnvGLRV isa A tid pl) hm hnf hpost)

end LinkLRV

/-- **The rule's invariant of `ofSafelyEnvGLRVXM` at the initial
configuration**, from `QX64M` at `σInitX` (`invGLRVX_init` over a mask). -/
theorem invGLRVXM_init {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout} {ss : List isa.State}
    {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s) {r : Res} {g : Ghost} (hpend : g.pend = [])
    {e e' : Kraken.Executable Directive} {endPc : Int64} {post : MachineState × EStateX → Prop}
    (hQ : QX64M (Kraken.Promising.SLR.EnvGLRV isa A tid pl) S e e' endPc post s (σInitX (Config.init ss m) r g)) :
    InvGLR (I := isa) A tid pl (QX64M (Kraken.Promising.SLR.EnvGLRV isa A tid pl) S e e' endPc post) True
      (Config.init ss m) r g :=
  ⟨_, _, coreAtLRX_init hs hpend, hQ⟩

end Kraken.Promising.X64.EnvG

#print axioms Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvGXM
#print axioms Kraken.Promising.X64.EnvG.noFaultRule_ofSafelyEnvGXM
#print axioms Kraken.Promising.X64.EnvG.invGXM_init
#print axioms Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvGLRVXM
#print axioms Kraken.Promising.X64.EnvG.noFaultRule_ofSafelyEnvGLRVXM
#print axioms Kraken.Promising.X64.EnvG.invGLRVXM_init
