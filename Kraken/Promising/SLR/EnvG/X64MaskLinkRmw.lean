/-
**The x64 link with taking loads and claim-conditional RMWs over a masked
image**.
`EnvG/X64MaskLink.lean`'s `QX64M` and its generic link facts at `EnvGTC`
(`ofSafelyEnvGTRCX`, `EnvG/X64RmwGhostLink.lean`, over a mask):
`linkHypsTRC_QX64M`, `ThreadRuleRXGS.ofSafelyEnvGTRCXM`,
`noFaultRule_ofSafelyEnvGTRCXM`, `invGTRCXM_init`. The shape
(`Phase1TreeRX A e'`) and the halt (`hstuck`) are the mask's, the
fault-freedom (`DirsNoFaultCode e`) the image's.
-/
import Kraken.Promising.SLR.EnvG.X64MaskLink
import Kraken.Promising.SLR.EnvG.X64RmwGhostLink

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

section LinkTRC

variable {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout} {e e' : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateX → Prop}

/-- **The link hypotheses of `EnvGTC` at `QX64M`** (`linkHypsTRC_QX64TC`
over a mask: the shape of the mask's cells only). -/
theorem linkHypsTRC_QX64M (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeRX A e')
    (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsTRCI (I := isa) A tid pl (QX64M (EnvGTCI isa A tid pl) S e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex :=
    QX64M.shape (Φ := fun t => Phase1ShapeR A t) hm hpost
      (fun f _ ht => Kraken.Promising.AArch64.EnvG.phase1ShapeR_map f ht) hshape h hex
  link J _ _ _ h hex hJ := QX64M.link hm hS hpost J h hex hJ

/-- **`ThreadRuleRXGS.ofSafelyEnvGTRCXM`**: `ofSafelyEnvGTRCX` over a mask
`e'` of the image `e`: the shape `Phase1TreeRX A e'` and the halt `hstuck` of
the mask. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTRCXM
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeRX A e')
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTCX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGS G₀ A B tid :=
  ThreadRuleRXGS.ofEnvGTRC (linkHypsTRC_QX64M (tid := tid) hm hpl hS hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QX64M hm hstuck hQ hh) hp hrel hcl

/-- **The no-fault rule of `ofSafelyEnvGTRCXM`**, unconditional in the
thread's promises, for an image whose non-data cells are fault-free. -/
theorem noFaultRule_ofSafelyEnvGTRCXM {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeRX A e')
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTCX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFaultCode e) :
    NoFaultRuleSX (ThreadRuleRXGS.ofSafelyEnvGTRCXM hm hpl hS hshape hpost hstuck hB) :=
  NoFaultRuleSX.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp => by
    obtain ⟨σ, hQ⟩ := InvGR.q_atX rF t h he hg ht E hnp
    exact noFault_QX64M (E := EnvGTCI isa A tid pl) hm hnf hpost t.st σ tree hQ hex

end LinkTRC

/-- **The rule's invariant of `ofSafelyEnvGTRCXM` at the initial
configuration**, from `QX64M` at `σInitX` (`invGTRCX_init` over a mask). -/
theorem invGTRCXM_init {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout} {ss : List isa.State}
    {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s) {r : Res} {g : Ghost} (hpend : g.pend = [])
    {e e' : Kraken.Executable Directive} {endPc : Int64} {post : MachineState × EStateX → Prop}
    (hQ : QX64M (EnvGTCI isa A tid pl) S e e' endPc post s (σInitX (Config.init ss m) r g)) :
    InvGR (I := isa) tid pl (QX64M (EnvGTCI isa A tid pl) S e e' endPc post) True (Config.init ss m) r g :=
  ⟨σInitX (Config.init ss m) r g, Thread.init s, coreAtRX_init hs hpend, hQ⟩

end Kraken.Promising.X64.EnvG

#print axioms Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTRCXM
#print axioms Kraken.Promising.X64.EnvG.noFaultRule_ofSafelyEnvGTRCXM
#print axioms Kraken.Promising.X64.EnvG.invGTRCXM_init
