/-
Whole-thread environment (`EnvG`): **the AArch64 rule
link at the fence-aware guard** `ThreadRuleRXG.ofSafelyEnvGHyb`, additively
beside `ThreadRuleRX.ofSafelyEnvG` (`EnvG/A64Link.lean`), with the same
hypotheses.

It is `ThreadRuleRXG.ofEnvGHyb` (`EnvG/FenceEnv.lean`) at

  `QA64H rel st σ := QA64 A tid pl e endPc post st σ ∧ σ.g.rel = rel`,

whose `LinkHyps` come from `linkHyps_QA64` through `link_relFix`. The
invariant of `ofSafelyEnvG` gives the one of `ofSafelyEnvGHyb` at
`rel = g.rel` (`invG_QA64H`: the core's `EnvRel.ghost` fixes the env's
release predicates), so a thread proved for `ofSafelyEnvG` needs nothing new
for `npSafeP_hyb_of_safelyEnvG_S`, the per-thread hypothesis of
`theorem1IIPure_of_relWritesF`. A fence-released store (`dmb ish; str`) of
an impure value is a planned release in the thread's `Safely` proof
(`StoreOk`'s `effRel` via the fence bits); its prepayment is the generic one.
-/
import Kraken.Promising.SLR.EnvG.FenceEnv
import Kraken.Promising.SLR.EnvG.A64Link

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-- **The thread-local invariant with fixed release predicates**: `QA64`
and the env's release predicates are `rel`. -/
def QA64H (A : Arch) (tid : Nat) (pl : Plan) (e : Kraken.Executable Directive) (endPc : Int64)
    (post : MachineState × EStateA → Prop) (rel : Loc → Pred) (st : State) (σ : EStateA) : Prop :=
  QA64 A tid pl e endPc post st σ ∧ σ.g.rel = rel

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
  {endPc : Int64} {post : MachineState × EStateA → Prop}

/-- **The link hypotheses at `QA64H`** (`linkHyps_QA64`, `link_relFix`). -/
theorem linkHyps_QA64H (rel : Loc → Pred) (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e)
    (hpost : ∀ y, post y → y.1.2 = endPc) : LinkHyps (I := isa) A tid pl (QA64H A tid pl e endPc post rel) where
  valid := hpl
  shape st σ h := (linkHyps_QA64 (tid := tid) hpl hlive hshape hpost).shape st σ h.1
  link := link_relFix rel (linkHyps_QA64 (tid := tid) hpl hlive hshape hpost).link

/-- **`ThreadRuleRXG.ofSafelyEnvGHyb`**: the AArch64 rule link at the
fence-aware guard `GHyb rel`, with `ofSafelyEnvG`'s hypotheses. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRXG.ofSafelyEnvGHyb
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop} (rel : Loc → Pred)
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXG (GHyb rel) A B tid :=
  ThreadRuleRXG.ofEnvGHyb (linkHyps_QA64H (tid := tid) rel hpl hlive hshape hpost) (fun _ _ h => h.2)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64 hstuck hQ.1 hh) hp hrel hcl

omit [Kraken.Executable.ValidLayout e] in
/-- **`ofSafelyEnvG`'s invariant gives `ofSafelyEnvGHyb`'s** at the
release predicates of the ghost. -/
theorem invG_QA64H {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvG (I := isa) A tid pl (QA64 A tid pl e endPc post) cl c r g) :
    InvG (I := isa) A tid pl (QA64H A tid pl e endPc post g.rel) cl c r g := by
  obtain ⟨σ, t, hC, hQ⟩ := h
  exact ⟨σ, t, hC, hQ, hC.rel.ghost.rel.symm⟩

/-- **`NPSafeP (GHyb g.rel)` in option (S)'s frame from a `Safely` judgment
of `EnvG`**, from any configuration where `ofSafelyEnvG`'s invariant holds
(e.g. the initial one of an existing EnvG proof). -/
theorem npSafeP_hyb_of_safelyEnvG_S {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvG (I := isa) A tid pl (QA64 A tid pl e endPc post) cl c r g) :
    NPSafeP (model isa) A B tid (GHyb g.rel) (K2Scope (model isa) AllocIds) n m cl c r g :=
  (NPSafeP.of_ruleRXG (ThreadRuleRXG.ofSafelyEnvGHyb g.rel hpl hlive hshape hpost hstuck hB) n m cl c r g
    (invG_QA64H h)).toAllocIds

end Link

end Kraken.Promising.AArch64.EnvG

#print axioms Kraken.Promising.AArch64.EnvG.npSafeP_hyb_of_safelyEnvG_S
