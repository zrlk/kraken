/-
**Part 6: the x64 link with the cumulative
take.** Adapted from `EnvG/TakeX64Link.lean` and
`EnvG/TakeX64VCGen.lean` (unchanged) for `EnvGTU`.

- `EnvGTUX A tid pl S := (EnvGTU isa A tid pl).within S`, `QX64TU`.
- `linkHypsTU_QX64TU`, `post_of_halted_QX64TU`,
  **`ThreadRuleRXGS.ofSafelyEnvGTUX : ThreadRuleRXGS G₀`**,
  **`npSafeP_of_safelyEnvGTUX`**, `noFault_QX64TU`,
  **`noFaultRule_ofSafelyEnvGTUX_struct`**, `qx64TU_of_partialTripleEnv`,
  `invGTUX_init`.
- `vcgen`: the `SharedEnv.FenceMonoX (EnvGTU I A tid pl)` instance
  (`fenceMonoX_le_envGTUX`); `takeEffU_wr_full` (a load by a thread that
  holds all of `x` leaves `x` as it was; every non-forwarded x64 load may
  take).

Phase-1 limits as `EnvG/TakeX64Link.lean`.
-/
import Kraken.Promising.SLR.EnvG.TakeURuleLink
import Kraken.Promising.SLR.EnvG.TakeX64Link
import Kraken.Promising.SLR.EnvG.TakeX64VCGen
import Kraken.Promising.SLR.EnvG.Alias

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-- **`EnvGTU` for x64**, restricted to the shared layout `S`. -/
abbrev EnvGTUX (A : Arch) (tid : Nat) (pl : Plan) (S : SharedEnv.Layout) : SharedEnv :=
  (Kraken.Promising.SLR.EnvGTU isa A tid pl).within S

/-- **The thread-local invariant with cumulatively taking loads, x64.** -/
def QX64TU (A : Arch) (tid : Nat) (pl : Plan) (S : SharedEnv.Layout) (e : Kraken.Executable Directive)
    (endPc : Int64) (post : MachineState × EStateX → Prop) (st : State) (σ : EStateX) : Prop :=
  st.exe = e ∧ st.decls = {} ∧ st.endPc = endPc ∧ Split S st.st.1.dmem ∧
    Safely (e.instrStepEnv (EnvGTUX A tid pl S)) post (st.st, σ)

/-! ## `vcgen` -/

instance instFenceMonoXEnvGTU {I : ISA} (A : Arch) (tid : Nat) (pl : Plan) : (EnvGTU I A tid pl).FenceMonoX :=
  ⟨FenceLe, FenceLe.refl, fenceInv_fenceLeTU A tid pl⟩

@[simp] theorem fenceMonoX_le_envGTUX {I : ISA} (A : Arch) (tid : Nat) (pl : Plan) :
    (SharedEnv.FenceMonoX.le (env := EnvGTU I A tid pl)) = FenceLe := rfl

-- **A load keeps a full write permission** (`takeEff_wr_full` for the
-- cumulative take): the ISA-neutral `takeEffU_keepsFull`, statement verbatim.
hoist_alias [Kraken.Promising.SLR.EnvG.takeEffU_keepsFull ↦ Kraken.Promising.X64.EnvG.takeEffU_wr_full]

/-! ## The link -/

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout} {e : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateX → Prop}

/-- **The link hypotheses at `QX64TU`** (the x64 run lemma at `E := EnvGTU`). -/
theorem linkHypsTU_QX64TU (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeX A e)
    (hpost : ∀ y, post y → y.1.2 = endPc) : LinkHypsTU (I := isa) A tid pl (QX64TU A tid pl S e endPc post) where
  valid := hpl
  shape st _ h tree hex := hshape st h.1 h.2.1 tree hex
  link J st σ tree h hex hJ := by
    obtain ⟨he, hds, hend, hs, hsafe⟩ := h
    rcases hsafe.unfold with hp | ⟨R, hR, hk⟩
    · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
      rw [this] at hex; cases hex
    · exact exec_treeJLive_of_instrStepEnvW J hS he hds hs hR
        (fun m g' hz hs' => hJ _ _ ⟨he, hds, hend, hs', hk _ hz⟩) tree hex

omit [Kraken.Executable.ValidLayout e] in
/-- **`done` at `QX64TU`.** -/
theorem post_of_halted_QX64TU (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTUX A tid pl S) x R)
    {t : Thread isa} {σ : EStateX} (hQ : QX64TU A tid pl S e endPc post t.st σ) (hh : t.halted = true) :
    post (t.st.st, σ) := by
  obtain ⟨he, -, hend, -, hsafe⟩ := hQ
  exact post_of_halted_env hstuck he hend hsafe hh

/-- **`ThreadRuleRXGS.ofSafelyEnvGTUX`**: the x64 rule link with
cumulatively taking loads (hypotheses as `ofSafelyEnvGTX`, for `EnvGTUX`). -/
def _root_.Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTUX
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeX A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTUX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGS G₀ A B tid :=
  ThreadRuleRXGS.ofEnvGTU (linkHypsTU_QX64TU (tid := tid) hpl hS hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QX64TU hstuck hQ hh) hp hrel hcl

/-- **`NPSafeP` (frame `K2Scope AllocIds`) from a `Safely` judgment of
`EnvGTUX`.** -/
theorem npSafeP_of_safelyEnvGTUX {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeX A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTUX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvG (I := isa) A tid pl (QX64TU A tid pl S e endPc post) cl c r g) :
    NPSafeP (model isa) A B tid G₀ (K2Scope (model isa) AllocIds) n m cl c r g :=
  NPSafeP.of_ruleRXGS (ThreadRuleRXGS.ofSafelyEnvGTUX hpl hS hshape hpost hstuck hB) n m cl c r g h

/-- **Every tree from a `QX64TU`-state is fault-free**, for fault-free code. -/
theorem noFault_QX64TU (hnf : DirsNoFault e) (hpost : ∀ y, post y → y.1.2 = endPc) :
    ∀ st σ tree, QX64TU A tid pl S e endPc post st σ → isa.exec st = some tree → tree.NoFault := by
  intro st σ tree h hex
  obtain ⟨he, hds, hend, -, hsafe⟩ := h
  rcases hsafe.unfold with hp | -
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · exact noFault_of_exec he hds hnf tree hex

/-- **The x64 no-fault rule with cumulatively taking loads**, unconditional
in the thread's promises. -/
theorem noFaultRule_ofSafelyEnvGTUX_struct {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeX A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTUX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRuleS (ThreadRuleRXGS.ofSafelyEnvGTUX hpl hS hshape hpost hstuck hB) :=
  NoFaultRuleS.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp => by
    obtain ⟨σ, hQ⟩ := InvG.q_at rF t h he hg ht E hnp
    exact noFault_QX64TU hnf hpost t.st σ tree hQ hex

end Link

/-! ## The start -/

section Start

variable {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout}

/-- **`QX64TU` from a partial triple** in `EnvGTUX`. -/
theorem qx64TU_of_partialTripleEnv [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Kraken.Executable.ValidLayout (layout p)] {P Q : MachineData → EStateX → Prop}
    {E : Int64 → MachineData → EStateX → Prop} (ht : MachineWP.PartialTripleEnv (EnvGTUX A tid pl S) P p Q E)
    (henv : cenv = layout p) {st : State} (he : st.exe = layout p) (hds : st.decls = {})
    (hend : st.endPc = (layout p).addrOf p.length) (hpc : st.st.2 = (layout p).addrOf 0)
    (hs : Split S st.st.1.dmem) {σ : EStateX}
    (hP : P st.st.1 σ) (hE : ∀ a s g, ¬ E a s g := by simp) :
    QX64TU A tid pl S (layout p) ((layout p).addrOf p.length) (postOfX p Q) st σ := by
  refine ⟨he, hds, hend, hs, ?_⟩
  have hst : st.st = (st.st.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hpc, Executable.addrOf_zero, Layout.apply_fst]
  rw [hst]
  exact (Program.instrStepEnv_of_partialTripleEnv ht hP henv).mono fun _ h => h.imp id (hE _ _ _)

/-- **The rule's invariant at the initial configuration** from `QX64TU`. -/
theorem invGTUX_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = []) {e : Kraken.Executable Directive} {endPc : Int64}
    {post : MachineState × EStateX → Prop}
    (hQ : QX64TU A tid pl S e endPc post s (σInitX (Config.init ss m) r g)) :
    InvG (I := isa) A tid pl (QX64TU A tid pl S e endPc post) True (Config.init ss m) r g :=
  ⟨_, _, coreAtX_init hs hpend, hQ⟩

end Start

end Kraken.Promising.X64.EnvG

#print axioms Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTUX
#print axioms Kraken.Promising.X64.EnvG.npSafeP_of_safelyEnvGTUX
#print axioms Kraken.Promising.X64.EnvG.noFaultRule_ofSafelyEnvGTUX_struct
#print axioms Kraken.Promising.X64.EnvG.takeEffU_wr_full
