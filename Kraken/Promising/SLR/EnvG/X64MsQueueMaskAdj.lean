/-
**The x64 `EnvGCAdj` rule link over a masked image**.
`EnvG/X64MaskLink.lean`'s `QX64M` and its generic link
facts (`QX64M.link`, `QX64M.shape`, `post_of_halted_QX64M`,
`noFault_QX64M`), instantiated at the adjacency environment
`EnvGCAdj` with failing release RMWs (`EnvG/X64AdjLink.lean`'s family):

- `linkHypsFCAdj_QX64M`, `ThreadRuleRXF.ofSafelyEnvGFCAdjXM`,
  `noFaultRuleF_ofSafelyEnvGFCAdjXM`, `invGFCAdjXM_init`.

The shape (`Phase1TreeFX e'`) and the halt (`hstuck`) are the mask's, the
fault-freedom (`DirsNoFaultCode e`) the image's. Used by the x64 msqueue
enqueuers, whose exit label is followed by the dequeuer's code.
-/
import Kraken.Promising.SLR.EnvG.X64MaskLink
import Kraken.Promising.SLR.EnvG.X64AdjLink

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

section LinkFCAdj

variable {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout} {e e' : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateX → Prop}

/-- **The link hypotheses of `EnvGCAdj` at `QX64M`** (`linkHypsFCAdj_QX64CAdj`
over a mask: the shape of the mask's cells only). -/
theorem linkHypsFCAdj_QX64M (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeFX e')
    (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsFCAdj (I := isa) A tid pl
      (QX64M (Kraken.Promising.SLR.EnvGCAdj isa A tid pl) S e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex := QX64M.shape (Φ := Phase1ShapeF) hm hpost (fun f _ ht => phase1ShapeF_map f ht) hshape h hex
  link J _ _ _ h hex hJ := QX64M.link hm hS hpost J h hex hJ

/-- **`ThreadRuleRXF.ofSafelyEnvGFCAdjXM`**: `ofSafelyEnvGFCAdjX` over a mask
`e'` of the image `e`: the shape `Phase1TreeFX e'` and the halt `hstuck` of
the mask. -/
def _root_.Kraken.Promising.SLR.EnvG.ThreadRuleRXF.ofSafelyEnvGFCAdjXM
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeFX e')
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGCAdjX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXF A B tid :=
  ThreadRuleRXF.ofEnvGFCAdj (linkHypsFCAdj_QX64M (tid := tid) hm hpl hS hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QX64M hm hstuck hQ hh) hp hrel hcl

/-- **The no-fault rule of `ofSafelyEnvGFCAdjXM`**, unconditional in the
thread's promises, for an image whose non-data cells are fault-free. -/
theorem noFaultRuleF_ofSafelyEnvGFCAdjXM {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeFX e')
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGCAdjX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFaultCode e) :
    NoFaultRuleF (ThreadRuleRXF.ofSafelyEnvGFCAdjXM hm hpl hS hshape hpost hstuck hB) :=
  noFaultRuleF_ofEnvGFCAdj_struct _ _
    (noFault_QX64M (E := Kraken.Promising.SLR.EnvGCAdj isa A tid pl) hm hnf hpost)

end LinkFCAdj

/-- **The rule's invariant of `ofSafelyEnvGFCAdjXM` at the initial
configuration**, from `QX64M` at `σInitX` (`invGFCAdjX_init` over a mask). -/
theorem invGFCAdjXM_init {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout} {ss : List isa.State}
    {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s) {r : Res} {g : Ghost} (hpend : g.pend = [])
    {e e' : Kraken.Executable Directive} {endPc : Int64} {post : MachineState × EStateX → Prop}
    (hQ : QX64M (Kraken.Promising.SLR.EnvGCAdj isa A tid pl) S e e' endPc post s (σInitX (Config.init ss m) r g)) :
    InvGF (I := isa) tid pl (QX64M (Kraken.Promising.SLR.EnvGCAdj isa A tid pl) S e e' endPc post) True
      (Config.init ss m) r g :=
  ⟨σInitX (Config.init ss m) r g, Thread.init s, coreAtFX_init hs hpend, hQ⟩

end Kraken.Promising.X64.EnvG

#print axioms Kraken.Promising.SLR.EnvG.ThreadRuleRXF.ofSafelyEnvGFCAdjXM
#print axioms Kraken.Promising.X64.EnvG.noFaultRuleF_ofSafelyEnvGFCAdjXM
#print axioms Kraken.Promising.X64.EnvG.invGFCAdjXM_init
