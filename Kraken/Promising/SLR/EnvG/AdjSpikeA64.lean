/-
Part 4: **the AArch64 link of the
sibling environment `EnvGCAdj`** (F × C with own-message adjacency in the
release obligation, `ThreadRuleRXF.ofSafelyEnvGFCAdj`). A copy of
`EnvG/A64RmwFailGhost.lean` (and of `EnvG/RmwGhostA64.lean`'s `QA64C` and
`post_of_halted_QA64C`) with `EnvGCAdj` for `EnvGC`.

The judgment is `Safely (e.instrStepEnv (EnvGCAdjA A tid pl)) post`
(`QA64CAdj`). Programs proved on `EnvGC` prove `EnvGCAdj`'s permissions
(`envGC_ok_toCAdj`: the release obligation only gains a hypothesis) and see
the same outcomes (`envGCAdj_step_iff`).

Contents: `EnvGCAdjA`, `QA64CAdj`, `linkHypsFCAdj_QA64CAdj`,
`post_of_halted_QA64CAdj`, `ThreadRuleRXF.ofSafelyEnvGFCAdj`,
`npSafeF_of_safelyEnvGFCAdj`, `noFaultRuleF_ofSafelyEnvGFCAdj_struct`,
`invGFCAdj_init`.
-/
import Kraken.Promising.SLR.EnvG.AdjSpikeRule
import Kraken.Promising.SLR.EnvG.A64RmwFailGhost

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-- `EnvGCAdj` for AArch64. -/
abbrev EnvGCAdjA (A : Arch) (tid : Nat) (pl : Plan) : SharedEnv := Kraken.Promising.SLR.EnvGCAdj isa A tid pl

/-- **The thread-local invariant of `EnvGCAdj`**: `QA64` with the `Safely`
judgment of `EnvGCAdj`. -/
def QA64CAdj (A : Arch) (tid : Nat) (pl : Plan) (e : Kraken.Executable Directive) (endPc : Int64)
    (post : MachineState × EStateA → Prop) (st : State) (σ : EStateA) : Prop :=
  st.exe = e ∧ st.decls = {} ∧ st.endPc = endPc ∧ Safely (e.instrStepEnv (EnvGCAdjA A tid pl)) post (st.st, σ)

/-! ## Programs proved on `EnvGC` are programs on `EnvGCAdj` -/

/-- **`AllEnv` of `EnvGC` gives `AllEnv` of `EnvGCAdj`** (weaker RMW
permission, same outcomes). -/
theorem Effects.AllEnv.toCAdj {A : Arch} {tid : Nat} {pl : Plan}
    {post : MachineState → (EnvGCA A tid pl).State → Prop} (ef : Effects) :
    ∀ g, ef.AllEnv (EnvGCA A tid pl) g post → ef.AllEnv (EnvGCAdjA A tid pl) g post := by
  have hs : ∀ {a : SharedAccess} {g : Kraken.Promising.SLR.EnvG.State isa} {ret : a.Ret}
      {g' : Kraken.Promising.SLR.EnvG.State isa},
      (EnvGCAdjA A tid pl).step a g ret g' → (EnvGCA A tid pl).step a g ret g' :=
    fun h => envGCAdj_step_iff.mp h
  induction ef with
  | done a => exact fun g h => h
  | unimplemented => exact fun _ h => h
  | syscall => exact fun _ h => h
  | unaligned_sp => exact fun _ h => h
  | nonmem_load dmem addr w ret ih =>
    exact fun g h => ⟨envGC_ok_toCAdj h.1, fun v g' h' => ih _ _ g' (h.2 v g' (hs h'))⟩
  | nonmem_store dmem addr v ret ih =>
    exact fun g h => ⟨envGC_ok_toCAdj h.1, fun b g' h' => ih _ g' (h.2 b g' (hs h'))⟩
  | undefined ret ih => exact fun g h v => ih v g (h v)
  | require_read_access _ _ ok ih => exact fun g h => ih () g h
  | require_write_access _ _ ok ih => exact fun g h => ih () g h
  | require_exec_access _ ok ih => exact fun g h => ih () g h
  | sync_load k xcl dmem addr w ret ih =>
    exact fun g h => ⟨envGC_ok_toCAdj h.1, fun v g' h' => ih _ _ g' (h.2 v g' (hs h'))⟩
  | sync_store k xcl dmem addr v ret ih =>
    exact fun g h => ⟨envGC_ok_toCAdj h.1, fun b g' h' => ih _ _ g' (h.2 b g' (hs h'))⟩
  | rmw k nr dmem addr w op ret ih =>
    exact fun g h => ⟨envGC_ok_toCAdj h.1, fun v g' h' => ih _ _ g' (h.2 v g' (hs h'))⟩
  | fence k ok ih => exact fun g h => ⟨envGC_ok_toCAdj h.1, fun g' h' => ih () g' (h.2 g' (hs h'))⟩
  | rmw_pair k dmem addr cmp1 cmp2 new1 new2 ret ih =>
    intro g h succ rev
    have h' := h succ rev
    cases rev with
    | true =>
      exact ⟨envGC_ok_toCAdj h'.1, fun v₂ g₁ h₁ => ⟨envGC_ok_toCAdj (h'.2 v₂ g₁ (hs h₁)).1,
        fun v₁ g₂ h₂ he => ih _ _ _ g₂ ((h'.2 v₂ g₁ (hs h₁)).2 v₁ g₂ (hs h₂) he)⟩⟩
    | false =>
      exact ⟨envGC_ok_toCAdj h'.1, fun v₁ g₁ h₁ => ⟨envGC_ok_toCAdj (h'.2 v₁ g₁ (hs h₁)).1,
        fun v₂ g₂ h₂ he => ih _ _ _ g₂ ((h'.2 v₁ g₁ (hs h₁)).2 v₂ g₂ (hs h₂) he)⟩⟩
  | sync_load_pair => exact fun _ h => h
  | sync_store_pair => exact fun _ h => h

/-- **`QA64C` gives `QA64CAdj`**: a `Safely` judgment of `EnvGC` (e.g.
`treiber_pp`'s) is one of `EnvGCAdj`. -/
theorem qa64C_toCAdj {A : Arch} {tid : Nat} {pl : Plan} {e : Kraken.Executable Directive} {endPc : Int64}
    {post : MachineState × EStateA → Prop} {st : State} {σ : EStateA}
    (h : QA64C A tid pl e endPc post st σ) : QA64CAdj A tid pl e endPc post st σ := by
  obtain ⟨he, hds, hend, Inv, hx, hInv⟩ := h
  refine ⟨he, hds, hend, Inv, hx, fun y hy => (hInv y hy).imp id fun ⟨R, hT, hR⟩ => ⟨R, ?_, hR⟩⟩
  obtain ⟨d, z, rest, hcode, hstep⟩ := hT
  refine ⟨d, z, rest, hcode, ?_⟩
  rcases hstep with h' | h'
  · exact .inl (Effects.AllEnv.toCAdj _ _ h')
  · exact .inr (Effects.AllEnv.toCAdj _ _ h')

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
  {endPc : Int64} {post : MachineState × EStateA → Prop}

/-- **The link hypotheses of `EnvGCAdj` at `QA64CAdj`** (`linkHypsFC_QA64C`). -/
theorem linkHypsFCAdj_QA64CAdj (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeF e)
    (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsFCAdj (I := isa) A tid pl (QA64CAdj A tid pl e endPc post) where
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
/-- **`done` at `QA64CAdj`** (`post_of_halted_QA64C`). -/
theorem post_of_halted_QA64CAdj (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGCAdjA A tid pl) x R)
    {t : Thread isa} {σ : EStateA} (hQ : QA64CAdj A tid pl e endPc post t.st σ) (hh : t.halted = true) :
    post (t.st.st, σ) := by
  obtain ⟨he, -, hend, hsafe⟩ := hQ
  exact post_of_halted_env hstuck he hend hsafe hh

/-- **`ThreadRuleRXF.ofSafelyEnvGFCAdj`**: the AArch64 rule link of
`EnvGCAdj` (`ofSafelyEnvGFC` with adjacency in the release obligation). -/
def _root_.Kraken.Promising.SLR.EnvG.ThreadRuleRXF.ofSafelyEnvGFCAdj
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeF e)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGCAdjA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXF A B tid :=
  ThreadRuleRXF.ofEnvGFCAdj (linkHypsFCAdj_QA64CAdj (tid := tid) hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64CAdj hstuck hQ hh) hp hrel hcl

/-- **`NPSafeF` from a `Safely` judgment of `EnvGCAdj`**. -/
theorem npSafeF_of_safelyEnvGFCAdj {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeF e)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGCAdjA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvGF (I := isa) tid pl (QA64CAdj A tid pl e endPc post) cl c r g) :
    NPSafeF (model isa) A B tid n m cl c r g :=
  NPSafeF.of_ruleRXF (ThreadRuleRXF.ofSafelyEnvGFCAdj hpl hlive hshape hpost hstuck hB) n m cl c r g h

/-- **The AArch64 no-fault rule of the `EnvGCAdj` link**, unconditional in
the thread's promises, for fault-free code (`DirsNoFault e`). -/
theorem noFaultRuleF_ofSafelyEnvGFCAdj_struct {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeF e)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGCAdjA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRuleF (ThreadRuleRXF.ofSafelyEnvGFCAdj hpl hlive hshape hpost hstuck hB) :=
  noFaultRuleF_ofEnvGFCAdj_struct _ _ fun st σ tree hQ hex => by
    obtain ⟨he, hds, hend, hsafe⟩ := hQ
    rcases hsafe.unfold with hp | ⟨R, hR, -⟩
    · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
      rw [this] at hex; cases hex
    · obtain ⟨d, z, rest, hcode, -⟩ := id hR
      exact noFault_of_codeAt he hds hcode (hnf d z (mem_of_codeAt hcode)) tree hex

end Link

/-- **The rule's invariant of the `EnvGCAdj` link at the initial
configuration**, from `QA64CAdj` at `σInit`. -/
theorem invGFCAdj_init {A : Arch} {tid : Nat} {pl : Plan} {ss : List isa.State} {m : List (Loc × Val)}
    {s : isa.State} (hs : ss[tid]? = some s) {r : Res} {g : Ghost} (hpend : g.pend = [])
    {e : Kraken.Executable Directive} {endPc : Int64} {post : MachineState × EStateA → Prop}
    (hQ : QA64CAdj A tid pl e endPc post s (σInit (Config.init ss m) r g)) :
    InvGF (I := isa) tid pl (QA64CAdj A tid pl e endPc post) True (Config.init ss m) r g :=
  ⟨σInit (Config.init ss m) r g, Thread.init s, coreAtF_init hs hpend, hQ⟩

end Kraken.Promising.AArch64.EnvG
