/-
**The AArch64 adjacency link over a masked image.**
`EnvG/AdjSpikeA64.lean`'s `EnvGCAdj` link
(`ThreadRuleRXF.ofSafelyEnvGFCAdj`) with the `Safely` judgment over a mask
`e'` of the thread's executable `e` (`QA64M (EnvGCAdjA A tid pl) e e'`,
`EnvG/A64MaskLink.lean`): the shape `Phase1TreeF e'` and the halt of the
mask, the static check `e.rmwLive` and fault-freedom of the image. The
`FC` family of `EnvG/A64MaskLink.lean` with `EnvGCAdj` for `EnvGC`.

- `linkHypsFCAdj_QA64M`, `ThreadRuleRXF.ofSafelyEnvGFCAdjM`,
  `noFaultRuleF_ofSafelyEnvGFCAdjM`, `invGFCAdjM_init`.

Phase-1 limits apply as in `ofSafelyEnvGFCAdj` (single-access trees,
read-side acquire only, releases are stores or failing release RMWs).
-/
import Kraken.Promising.SLR.EnvG.A64MaskLink
import Kraken.Promising.SLR.EnvG.AdjSpikeA64

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

section LinkFCAdj

variable {A : Arch} {tid : Nat} {pl : Plan} {e e' : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateA → Prop}

/-- **The link hypotheses of `EnvGCAdj` at `QA64M`** (`linkHypsFCAdj_QA64CAdj`
over a mask). -/
theorem linkHypsFCAdj_QA64M (hm : MaskOf e e') (hpl : pl.Valid) (hlive : e.rmwLive = true)
    (hshape : Phase1TreeF e') (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsFCAdj (I := isa) A tid pl (QA64M (EnvGCAdjA A tid pl) e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex := QA64M.shape (Φ := Phase1ShapeF) hm hpost (fun f _ ht => phase1ShapeF_map f ht) hshape h hex
  link J _ _ _ h hex hJ := QA64M.link hm hlive hpost J h hex hJ

/-- **`ThreadRuleRXF.ofSafelyEnvGFCAdjM`**: `ofSafelyEnvGFCAdj` over a mask
`e'` of the image `e`. -/
def _root_.Kraken.Promising.SLR.EnvG.ThreadRuleRXF.ofSafelyEnvGFCAdjM
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hm : MaskOf e e') (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeF e')
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGCAdjA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXF A B tid :=
  ThreadRuleRXF.ofEnvGFCAdj (linkHypsFCAdj_QA64M (tid := tid) hm hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64M hm hstuck hQ hh) hp hrel hcl

/-- **The no-fault rule of `ofSafelyEnvGFCAdjM`**, unconditional in the
thread's promises, for a fault-free image. -/
theorem noFaultRuleF_ofSafelyEnvGFCAdjM {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hm : MaskOf e e') (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeF e')
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGCAdjA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRuleF (ThreadRuleRXF.ofSafelyEnvGFCAdjM hm hpl hlive hshape hpost hstuck hB) :=
  noFaultRuleF_ofEnvGFCAdj_struct _ _ (noFault_QA64M (E := EnvGCAdjA A tid pl) hm hnf hpost)

end LinkFCAdj

/-- **The rule's invariant of `ofSafelyEnvGFCAdjM` at the initial
configuration**, from `QA64M` at `σInit`. -/
theorem invGFCAdjM_init {A : Arch} {tid : Nat} {pl : Plan} {ss : List isa.State} {m : List (Loc × Val)}
    {s : isa.State} (hs : ss[tid]? = some s) {r : Res} {g : Ghost} (hpend : g.pend = [])
    {e e' : Kraken.Executable Directive} {endPc : Int64} {post : MachineState × EStateA → Prop}
    (hQ : QA64M (EnvGCAdjA A tid pl) e e' endPc post s (σInit (Config.init ss m) r g)) :
    InvGF (I := isa) tid pl (QA64M (EnvGCAdjA A tid pl) e e' endPc post) True (Config.init ss m) r g :=
  ⟨σInit (Config.init ss m) r g, Thread.init s, coreAtF_init hs hpend, hQ⟩

end Kraken.Promising.AArch64.EnvG

#print axioms Kraken.Promising.SLR.EnvG.ThreadRuleRXF.ofSafelyEnvGFCAdjM
#print axioms Kraken.Promising.AArch64.EnvG.noFaultRuleF_ofSafelyEnvGFCAdjM
#print axioms Kraken.Promising.AArch64.EnvG.invGFCAdjM_init
