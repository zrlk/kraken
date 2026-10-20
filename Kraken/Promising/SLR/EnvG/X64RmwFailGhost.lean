/-
**Part 1: the x64 link of the
claim-conditional environment with failing in-flight release RMWs** (F × C):
`ThreadRuleRXF.ofSafelyEnvGFCX`, the x64 counterpart of the Treiber proof's
`ThreadRuleRXF.ofSafelyEnvGFC` (`EnvG/A64RmwFailGhost.lean`), built from the
ISA-neutral `F × C` rule link `ThreadRuleRXF.ofEnvGFC`
(`EnvG/RmwFailGhostRule.lean`) as the x64 claim-conditional RMW proof built `ofSafelyEnvGRCX`
(`EnvG/X64RmwGhostLink.lean`) from `ofEnvGRC`.

- The environment is the x64 claim-conditional RMW proof's
  `EnvGCX A tid pl S = (EnvGC isa A tid pl).within S`
  and the invariant its `QX64C`; the shape is the x64 `cmpxchg` lock proof's `Phase1TreeFX`
  (`EnvG/X64RmwFail.lean`: single-access trees, `lock cmpxchg` admitted, no
  totality of an in-flight release RMW).
- On x64 every RMW event is `.acqRel` and claims unconditionally
  (`claimSlotsC_acqRel`), so of the claim-conditional extension's change only the give-from-own half
  matters: a `lock cmpxchg` release (a Treiber push publishing a node, a
  Treiber pop writing a loaded value) gives from the thread's own resource,
  with no `RelRmwGiveOk` and no `Plan.Whole`, and it may fail (a failed
  `lock cmpxchg` writes nothing; the outstanding promise of a prepaid branch
  whose comparison fails ends in `PostSF`'s `Alive` escape, excluded by
  `NPSafeF`'s step guard).
- The rule gives `NPSafeF`; Theorem 1′ for it is `theorem1FChain`
  (`EnvG/RmwFailChain.lean`). `final_of_relPureSafelyQX_tsoF'` is the x64 `cmpxchg` lock proof's
  `final_of_relPureSafelyQX_tsoF` (`EnvG/RelPureEnvX64F.lean`) with the chain
  hypothesis discharged by `theorem1FChain` (the x64 counterpart of
  `final_of_relPureSafelyF`, `EnvG/A64RmwFailFinal.lean`); it moved
  (name and statement unchanged) to `EnvG/RelPureEnvX64F.lean`, the x64
  default for `NPSafeF` rules, and this file re-exports it by import.

Contents: `linkHypsFC_QX64C`, **`ThreadRuleRXF.ofSafelyEnvGFCX`**,
`npSafeF_of_safelyEnvGFCX`, `noFaultRuleF_ofSafelyEnvGFCX_struct` (from
`DirsNoFault`, unconditional in the thread's promises), `invGFCX_init`
(`final_of_relPureSafelyQX_tsoF'`: see `EnvG/RelPureEnvX64F.lean`).

Phase-1 limits otherwise apply: single-access trees, read-side acquire only,
every access within the layout `S` (`Le16 S`); a release RMW cannot forward
what it claims.
-/
import Kraken.Promising.SLR.EnvG.RmwFailGhostRule
import Kraken.Promising.SLR.EnvG.X64RmwGhostLink
import Kraken.Promising.SLR.EnvG.X64RmwFail
import Kraken.Promising.SLR.EnvG.RelPureEnvX64F

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout} {e : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateX → Prop}

/-- **The link hypotheses of `EnvGC` with failing release RMWs at `QX64C`**
(`linkHypsFC_QA64C`, x64; `linkHypsRC_QX64C` with `Phase1TreeFX`). -/
theorem linkHypsFC_QX64C (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeFX e)
    (hpost : ∀ y, post y → y.1.2 = endPc) : LinkHypsFC (I := isa) A tid pl (QX64C A tid pl S e endPc post) where
  valid := hpl
  shape st _ h tree hex := hshape st h.1 h.2.1 tree hex
  link J st σ tree h hex hJ := by
    obtain ⟨he, hds, hend, hs, hsafe⟩ := h
    rcases hsafe.unfold with hp | ⟨R, hR, hk⟩
    · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
      rw [this] at hex; cases hex
    · exact exec_treeJLive_of_instrStepEnvW J hS he hds hs hR
        (fun m g' hz hs' => hJ _ _ ⟨he, hds, hend, hs', hk _ hz⟩) tree hex

/-- **`ThreadRuleRXF.ofSafelyEnvGFCX`**: the x64 rule link of `EnvGC` with
failing release RMWs (`ofSafelyEnvGFC`, x64; `ofSafelyEnvGRCX` with
`Phase1TreeFX`: `lock cmpxchg` releases that give from the thread's own
resource are admitted). Gives `ThreadRuleRXF`, hence `NPSafeF`. -/
def _root_.Kraken.Promising.SLR.EnvG.ThreadRuleRXF.ofSafelyEnvGFCX
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeFX e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGCX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXF A B tid :=
  ThreadRuleRXF.ofEnvGFC (linkHypsFC_QX64C (tid := tid) hpl hS hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QX64C hstuck hQ hh) hp hrel hcl

/-- **`NPSafeF` from a `Safely` judgment of `EnvGCX` with failing release
RMWs** (`NPSafeF.of_ruleRXF` at `ofSafelyEnvGFCX`). -/
theorem npSafeF_of_safelyEnvGFCX {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeFX e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGCX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvGF (I := isa) tid pl (QX64C A tid pl S e endPc post) cl c r g) :
    NPSafeF (model isa) A B tid n m cl c r g :=
  NPSafeF.of_ruleRXF (ThreadRuleRXF.ofSafelyEnvGFCX hpl hS hshape hpost hstuck hB) n m cl c r g h

/-- **The x64 no-fault rule of the `FC` link**, unconditional in the thread's
promises, for fault-free code (`DirsNoFault e`;
`noFaultRuleF_ofSafelyEnvGFC_struct`, x64). -/
theorem noFaultRuleF_ofSafelyEnvGFCX_struct {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeFX e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGCX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRuleF (ThreadRuleRXF.ofSafelyEnvGFCX hpl hS hshape hpost hstuck hB) :=
  noFaultRuleF_ofEnvGFC_struct _ _ (noFault_QX64C hnf hpost)

end Link

/-- **The rule's invariant of the x64 `FC` link at the initial
configuration**, from `QX64C` at `σInitX` (`invGFC_init`, x64). -/
theorem invGFCX_init {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout} {ss : List isa.State}
    {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s) {r : Res} {g : Ghost} (hpend : g.pend = [])
    {e : Kraken.Executable Directive} {endPc : Int64} {post : MachineState × EStateX → Prop}
    (hQ : QX64C A tid pl S e endPc post s (σInitX (Config.init ss m) r g)) :
    InvGF (I := isa) tid pl (QX64C A tid pl S e endPc post) True (Config.init ss m) r g :=
  ⟨σInitX (Config.init ss m) r g, Thread.init s, coreAtFX_init hs hpend, hQ⟩

end Kraken.Promising.X64.EnvG

#print axioms Kraken.Promising.SLR.EnvG.ThreadRuleRXF.ofSafelyEnvGFCX
#print axioms Kraken.Promising.X64.EnvG.npSafeF_of_safelyEnvGFCX
#print axioms Kraken.Promising.X64.EnvG.noFaultRuleF_ofSafelyEnvGFCX_struct
#print axioms Kraken.Promising.X64.EnvG.invGFCX_init
#print axioms Kraken.Promising.X64.EnvG.CmpxPublic.final_of_relPureSafelyQX_tsoF'
