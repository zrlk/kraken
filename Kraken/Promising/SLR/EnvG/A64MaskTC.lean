/-
**The AArch64 `EnvGTC` link over a masked image.**
`EnvG/RmwGhostTake.lean`'s claim-conditional link with
taking loads (`ThreadRuleRXGS.ofSafelyEnvGTRC`) with the `Safely` judgment
over a mask `e'` of the thread's executable `e` (`QA64M (EnvGTCA A tid pl) e
e'`, `EnvG/A64MaskLink.lean`): the shape `Phase1TreeR A e'` and the halt of
the mask, the static check `e.rmwLive` and fault-freedom of the image. The
`EnvGT` family of `EnvG/A64MaskLink.lean` with `EnvGTC` for `EnvGT`.

- `linkHypsTRC_QA64M`, `ThreadRuleRXGS.ofSafelyEnvGTRCM`,
  `noFaultRule_ofSafelyEnvGTRCM`, `invGTRCM_init`.
- `dirs_phase1R_any p`, `label_dirPhase1R_any`, `byteArray_dirPhase1R_any`,
  `phase1TreeR_maskKeep_range`: the release-kind-RMW copies of
  `EnvG/A64MaskHelpers.lean`'s `F` pieces.

Phase-1 limits apply as in `ofSafelyEnvGTRC` (single-access trees,
release-kind RMWs never fail).
-/
import Kraken.Promising.SLR.EnvG.A64MaskLink
import Kraken.Promising.SLR.EnvG.RmwGhostTake

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

section LinkTRC

variable {A : Arch} {tid : Nat} {pl : Plan} {e e' : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateA → Prop}

/-- **The link hypotheses of `EnvGTC` at `QA64M`** (`linkHypsTRC_QA64TC`
over a mask). -/
theorem linkHypsTRC_QA64M (hm : MaskOf e e') (hpl : pl.Valid) (hlive : e.rmwLive = true)
    (hshape : Phase1TreeR A e') (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsTRC (I := isa) A tid pl (QA64M (EnvGTCA A tid pl) e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex :=
    QA64M.shape (Φ := fun t => Phase1ShapeR A t) hm hpost (fun f _ ht => phase1ShapeR_map f ht) hshape h hex
  link J _ _ _ h hex hJ := QA64M.link hm hlive hpost J h hex hJ

/-- **`ThreadRuleRXGS.ofSafelyEnvGTRCM`**: `ofSafelyEnvGTRC` over a mask
`e'` of the image `e`. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTRCM
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hm : MaskOf e e') (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e')
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTCA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGS G₀ A B tid :=
  ThreadRuleRXGS.ofEnvGTRC (linkHypsTRC_QA64M (tid := tid) hm hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64M hm hstuck hQ hh) hp hrel hcl

/-- **The no-fault rule of `ofSafelyEnvGTRCM`**, unconditional in the
thread's promises, for a fault-free image. -/
theorem noFaultRule_ofSafelyEnvGTRCM {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hm : MaskOf e e') (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e')
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTCA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRuleS (ThreadRuleRXGS.ofSafelyEnvGTRCM hm hpl hlive hshape hpost hstuck hB) :=
  NoFaultRuleS.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp => by
    obtain ⟨σ, hQ⟩ := InvGR.q_at rF t h he hg ht E hnp
    exact noFault_QA64M (E := EnvGTCA A tid pl) hm hnf hpost t.st σ tree hQ hex

end LinkTRC

/-- **The rule's invariant of `ofSafelyEnvGTRCM` at the initial
configuration**, from `QA64M` at `σInit`. -/
theorem invGTRCM_init {A : Arch} {tid : Nat} {pl : Plan} {ss : List isa.State} {m : List (Loc × Val)}
    {s : isa.State} (hs : ss[tid]? = some s) {r : Res} {g : Ghost} (hpend : g.pend = [])
    {e e' : Kraken.Executable Directive} {endPc : Int64} {post : MachineState × EStateA → Prop}
    (hQ : QA64M (EnvGTCA A tid pl) e e' endPc post s (σInit (Config.init ss m) r g)) :
    InvGR (I := isa) tid pl (QA64M (EnvGTCA A tid pl) e e' endPc post) True (Config.init ss m) r g :=
  ⟨σInit (Config.init ss m) r g, Thread.init s, coreAtR_init hs hpend, hQ⟩

/-! ## Phase-1 cells with release-kind RMWs, for every ambient executable -/

set_option hygiene false in
/-- `dirs_phase1R_any p` proves `∀ d ∈ p, ∀ e z, DirPhase1R A e d z` for a
program `p` (a definition) whose instructions make at most one access,
deterministically, and whose release-kind RMWs never fail (`dirs_phase1R`'s
script with an `∀ e` binder). -/
macro "dirs_phase1R_any " p:ident : tactic => `(tactic| (
  intro d hd e z s pc
  simp only [$p:ident, List.mem_cons, List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals simp [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    Kraken.Promising.AArch64.toEv, Kraken.Promising.SLR.EnvG.Phase1ShapeR, Kraken.Promising.SLR.EnvG.DetAccess,
    Kraken.Promising.SLR.EnvG.SingleAccessS2, Kraken.Promising.SLR.EnvG.AccessFree,
    _root_.MachineData.load, _root_.MachineData.store,
    _root_.MachineData.loadK, _root_.MachineData.storeK, _root_.MachineData.rmwK,
    _root_.MachineData.setRegOrZr, _root_.MachineData.setRegOrSp, _root_.RegOrSp.interpBase,
    _root_.AddrExpr.checkSPAlignment, _root_.AddrExpr.interpLoad, _root_.AddrExpr.interpStore,
    _root_.UnscaledAddrExpr.interpStore,
    _root_.UnscaledAddrExpr.checkSPAlignment, _root_.UnscaledAddrExpr.interpLoad,
    _root_.Literal.interpLoad, _root_.AddrOrLit.interpLoad,
    Kraken.Promising.EvTree.access_empty]
  all_goals (repeat' (first | split |
    simp [Kraken.Promising.AArch64.toEv, Kraken.Promising.SLR.EnvG.Phase1ShapeR,
      Kraken.Promising.SLR.EnvG.DetAccess, Kraken.Promising.SLR.EnvG.SingleAccessS2,
      Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty]))))

/-- A label cell is phase-1 with release-kind RMWs. -/
theorem label_dirPhase1R_any (A : Arch) (l : Label) (e : _root_.Executable) (z : Nat) :
    DirPhase1R A e (.label l) z := by
  intro s pc
  simp [_root_.Directive.interp, Kraken.Promising.AArch64.toEv, Phase1ShapeR, DetAccess, SingleAccessS2]

/-- A data cell is phase-1 with release-kind RMWs (its tree is a fault). -/
theorem byteArray_dirPhase1R_any (A : Arch) (b : ByteArray) (e : _root_.Executable) (z : Nat) :
    DirPhase1R A e (.byteArray b) z := by
  intro s pc
  simp [_root_.Directive.interp, Kraken.Promising.AArch64.toEv, Phase1ShapeR, DetAccess, SingleAccessS2]

/-- **A range mask of a phase-1 image is phase-1** (release-kind RMWs). -/
theorem phase1TreeR_maskKeep_range [layout : _root_.Layout] {A : Arch} {p : Program}
    [Executable.ValidLayout (layout p)] {lo hi : Nat} (h : ∀ d ∈ p, ∀ (e : _root_.Executable) z, DirPhase1R A e d z) :
    Phase1TreeR A (layout (p.maskKeep (keepRange lo hi))) :=
  haveI := ValidLayout.of_mask (maskOf_layout (layout := layout) (keepRange lo hi) p)
  phase1TreeR_of_dirs (dirsPhase1R_layout (mem_maskKeep_range (Φd := fun d => ∀ e z, DirPhase1R A e d z)
    (fun d hd => h d (List.mem_of_mem_drop (List.mem_of_mem_take hd)))
    (fun l => label_dirPhase1R_any A l) (byteArray_dirPhase1R_any A _)))

end Kraken.Promising.AArch64.EnvG

#print axioms Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTRCM
#print axioms Kraken.Promising.AArch64.EnvG.noFaultRule_ofSafelyEnvGTRCM
#print axioms Kraken.Promising.AArch64.EnvG.invGTRCM_init
#print axioms Kraken.Promising.AArch64.EnvG.phase1TreeR_maskKeep_range
