/-
**Part 5: the AArch64 link, start and
no-fault with the cumulative take.** Adapted from
`EnvG/TakeA64Link.lean` and `EnvG/TakeA64Rule.lean` (unchanged) for
`EnvGTU` (`EnvG/TakeUEnv.lean`).

- `EnvGTUA`, `QA64TU`, `linkHypsTU_QA64TU`, `post_of_halted_QA64TU`.
- **`ThreadRuleRXGS.ofSafelyEnvGTU : ThreadRuleRXGS G₀`** and
  **`npSafeP_of_safelyEnvGTU`** (frame `K2Scope (model isa) AllocIds`); the
  hypotheses are `ofSafelyEnvGT`'s, for `EnvGTU`.
- Start: `qa64TU_of_partialTripleEnv`, `invGTU_init`.
- No fault: `noFault_QA64TU`, **`noFaultRule_ofSafelyEnvGTU_struct`** (for
  fault-free code, unconditional in the thread's promises; `NoFaultRuleS`,
  `EnvG/TakeNoFault.lean`, unchanged).
- `vcgen`: `EnvGTU` has the `SharedEnv.FenceMono` instance and the simp set
  of `EnvG/TakeUEnv.lean`, so `envMono_lift_spec` (`EnvG/A64VCGen.lean`)
  runs silent instructions as on `EnvGT`.

Phase-1 limits as `EnvG/TakeA64Link.lean`.
-/
import Kraken.Promising.SLR.EnvG.TakeURuleLink
import Kraken.Promising.SLR.EnvG.TakeA64Rule
import Kraken.Promising.SLR.EnvG.TakeVCGen

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-- `EnvGTU` for AArch64. -/
abbrev EnvGTUA (A : Arch) (tid : Nat) (pl : Plan) : SharedEnv := Kraken.Promising.SLR.EnvGTU isa A tid pl

/-- **The thread-local invariant with cumulatively taking loads** (`QA64T`
for `EnvGTU`). -/
def QA64TU (A : Arch) (tid : Nat) (pl : Plan) (e : Kraken.Executable Directive) (endPc : Int64)
    (post : MachineState × EStateA → Prop) (st : State) (σ : EStateA) : Prop :=
  st.exe = e ∧ st.decls = {} ∧ st.endPc = endPc ∧ Safely (e.instrStepEnv (EnvGTUA A tid pl)) post (st.st, σ)

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
  {endPc : Int64} {post : MachineState × EStateA → Prop}

/-- **The link hypotheses at `QA64TU`.** -/
theorem linkHypsTU_QA64TU (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e)
    (hpost : ∀ y, post y → y.1.2 = endPc) : LinkHypsTU (I := isa) A tid pl (QA64TU A tid pl e endPc post) where
  valid := hpl
  shape st _ h tree hex := hshape st h.1 h.2.1 tree hex
  link J st σ tree h hex hJ := by
    obtain ⟨he, hds, hend, hsafe⟩ := h
    rcases hsafe.unfold with hp | ⟨R, hR, hk⟩
    · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
      rw [this] at hex; cases hex
    · exact exec_treeJLive_of_instrStepEnv' J he hds hR (fun m g' hz => hJ _ _ ⟨he, hds, hend, hk _ hz⟩) hlive
        tree hex

omit [Kraken.Executable.ValidLayout e] in
/-- **`done` at `QA64TU`.** -/
theorem post_of_halted_QA64TU (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTUA A tid pl) x R)
    {t : Thread isa} {σ : EStateA} (hQ : QA64TU A tid pl e endPc post t.st σ) (hh : t.halted = true) :
    post (t.st.st, σ) := by
  obtain ⟨he, -, hend, hsafe⟩ := hQ
  exact post_of_halted_env hstuck he hend hsafe hh

/-- **`ThreadRuleRXGS.ofSafelyEnvGTU`**: the AArch64 rule link with
cumulatively taking loads (hypotheses as `ofSafelyEnvGT`, for `EnvGTU`). -/
def _root_.Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTU
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTUA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGS G₀ A B tid :=
  ThreadRuleRXGS.ofEnvGTU (linkHypsTU_QA64TU (tid := tid) hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64TU hstuck hQ hh) hp hrel hcl

/-- **`NPSafeP` (frame `K2Scope AllocIds`) from a `Safely` judgment of
`EnvGTU`.** -/
theorem npSafeP_of_safelyEnvGTU {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTUA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvG (I := isa) A tid pl (QA64TU A tid pl e endPc post) cl c r g) :
    NPSafeP (model isa) A B tid G₀ (K2Scope (model isa) AllocIds) n m cl c r g :=
  NPSafeP.of_ruleRXGS (ThreadRuleRXGS.ofSafelyEnvGTU hpl hlive hshape hpost hstuck hB) n m cl c r g h

/-- **Every tree from a `QA64TU`-state is fault-free**, for fault-free code. -/
theorem noFault_QA64TU (hnf : DirsNoFault e) (hpost : ∀ y, post y → y.1.2 = endPc) :
    ∀ st σ tree, QA64TU A tid pl e endPc post st σ → isa.exec st = some tree → tree.NoFault := by
  intro st σ tree h hex
  obtain ⟨he, hds, hend, hsafe⟩ := h
  rcases hsafe.unfold with hp | ⟨R, hR, -⟩
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · obtain ⟨d, z, rest, hcode, -⟩ := id hR
    exact noFault_of_codeAt he hds hcode (hnf d z (mem_of_codeAt hcode)) tree hex

/-- **The AArch64 no-fault rule with cumulatively taking loads**,
unconditional in the thread's promises. -/
theorem noFaultRule_ofSafelyEnvGTU_struct {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTUA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRuleS (ThreadRuleRXGS.ofSafelyEnvGTU hpl hlive hshape hpost hstuck hB) :=
  NoFaultRuleS.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp => by
    obtain ⟨σ, hQ⟩ := InvG.q_at rF t h he hg ht E hnp
    exact noFault_QA64TU hnf hpost t.st σ tree hQ hex

end Link

/-! ## Start -/

section Triple

variable {A : Arch} {tid : Nat} {pl : Plan}

/-- **`QA64TU` from a partial triple** in `EnvGTU` at a thread state at the
start of `p`, whose exceptional exit `E` never holds. -/
theorem qa64TU_of_partialTripleEnv [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Kraken.Executable.ValidLayout (layout p)] {P Q : MachineData → EStateA → Prop}
    {E : Int64 → MachineData → EStateA → Prop} (ht : MachineWP.PartialTripleEnv (EnvGTUA A tid pl) P p Q E)
    (henv : cenv = layout p) {st : State} (he : st.exe = layout p) (hds : st.decls = {})
    (hend : st.endPc = (layout p).addrOf p.length) (hpc : st.st.2 = (layout p).addrOf 0) {σ : EStateA}
    (hP : P st.st.1 σ) (hE : ∀ a s g, ¬ E a s g := by simp) :
    QA64TU A tid pl (layout p) ((layout p).addrOf p.length) (postOf p Q) st σ := by
  refine ⟨he, hds, hend, ?_⟩
  have hst : st.st = (st.st.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hpc, Executable.addrOf_zero, Layout.apply_fst]
  rw [hst]
  exact (Program.instrStepEnv_of_partialTripleEnv ht hP henv).mono fun _ h => h.imp id (hE _ _ _)

/-- **The rule's invariant at the initial configuration** from `QA64TU` at
`σInit`. -/
theorem invGTU_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = []) {e : Kraken.Executable Directive} {endPc : Int64}
    {post : MachineState × EStateA → Prop} (hQ : QA64TU A tid pl e endPc post s (σInit (Config.init ss m) r g)) :
    InvG (I := isa) A tid pl (QA64TU A tid pl e endPc post) True (Config.init ss m) r g :=
  ⟨_, _, coreAt_init hs hpend, hQ⟩

end Triple

end Kraken.Promising.AArch64.EnvG

#print axioms Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTU
#print axioms Kraken.Promising.AArch64.EnvG.npSafeP_of_safelyEnvGTU
#print axioms Kraken.Promising.AArch64.EnvG.noFaultRule_ofSafelyEnvGTU_struct
#print axioms Kraken.Promising.AArch64.EnvG.invGTU_init
