/-
**The x64 layer of the EnvG value bridge** (route (c2)).

The ISA-neutral part applies unchanged: `(valsEnv E G).within S` is
`valsEnv (E.within S) G` by `rfl`, so `exec_treeJLive_of_instrStepEnvW` gives
`LinkHypsFCAdjV`'s `link` from a judgment in `EnvGCAdjXV` (the x64 pilot's, by
`rfl`). Contents: `QX64CAdjV` wrappers, `threadSpecX_allInv`,
**`final_of_relPureSafelyQX_tsoFV`**, **`envGValsBridgeX_ofSpecs`**.

**Scope.** The purity specifications are the existing, unrestricted ones
(`RelPureSpecQX.Holds`), which give `NTFree` and `PromisePure` as in
`final_of_relPureSafelyQX_tsoF'`. Value-restricted purity judgments
(the x64 pilot's `RelPureSpecQX.HoldsV`) are handled by `envGValsBridgeX_ofPure`
(`Lower/KitX64ValsPure.lean`).
-/
import Kraken.Promising.SLR.EnvG.ValsChain
import Kraken.Promising.SLR.EnvG.X64AdjLink
import Kraken.Promising.SLR.EnvG.RelPureEnvX64F
import Kraken.Promising.InvLinkX64

namespace Kraken.Promising.X64.EnvG.Vals

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.EnvSpike
open Kraken.Promising.SLR.EnvG.Vals Kraken.Promising.X64.EnvG

/-- Restricting the layout commutes with restricting the load answers. -/
theorem valsEnv_within (E : SharedEnv) (G : Loc → Val → Prop) (S : SharedEnv.Layout) :
    (valsEnv E G).within S = valsEnv (E.within S) G := rfl

/-- **`EnvGCAdjX` with value-restricted load answers.** -/
abbrev EnvGCAdjXV (A : Arch) (tid : Nat) (pl : SLR.EnvG.Plan) (S : SharedEnv.Layout) (G : Loc → Val → Prop) :
    SharedEnv :=
  valsEnv (EnvGCAdjX A tid pl S) G

/-- `QX64CAdj` with the `Safely` judgment of `EnvGCAdjXV`. -/
def QX64CAdjV (A : Arch) (tid : Nat) (pl : SLR.EnvG.Plan) (S : SharedEnv.Layout) (G : Loc → Val → Prop)
    (e : Kraken.Executable Directive) (endPc : Int64) (post : MachineState × EStateX → Prop) (st : State)
    (σ : EStateX) : Prop :=
  st.exe = e ∧ st.decls = {} ∧ st.endPc = endPc ∧ Split S st.st.1.dmem ∧
    Safely (e.instrStepEnv (EnvGCAdjXV A tid pl S G)) post (st.st, σ)

section Link

variable {A : Arch} {tid : Nat} {pl : SLR.EnvG.Plan} {S : SharedEnv.Layout} {G : Loc → Val → Prop}
  {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {endPc : Int64}
  {post : MachineState × EStateX → Prop}

/-- **The link hypotheses at `QX64CAdjV`** (`linkHypsFCAdj_QX64CAdj` over the
value-restricted env). -/
theorem linkHypsFCAdjV_QX64CAdjV (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeFX e)
    (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsFCAdjV (I := isa) A tid pl G (QX64CAdjV A tid pl S G e endPc post) where
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
/-- **`done` at `QX64CAdjV`** (`post_of_halted_QX64CAdj`). -/
theorem post_of_halted_QX64CAdjV
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGCAdjXV A tid pl S G) x R)
    {t : Thread isa} {σ : EStateX} (hQ : QX64CAdjV A tid pl S G e endPc post t.st σ) (hh : t.halted = true) :
    post (t.st.st, σ) := by
  obtain ⟨he, -, hend, -, hsafe⟩ := hQ
  refine hsafe.post_of_stuck fun R hR => ?_
  have hdir := directive_isSome_of_instrStepEnv he hR
  have hh' : (exec t.st).isNone = true := hh
  unfold exec at hh'
  split at hh'
  · next hc =>
    simp only [Bool.or_eq_true, beq_iff_eq] at hc
    rcases hc with hc | hc
    · exact hstuck _ R (by rw [← hend]; exact hc) hR
    · rw [Option.isNone_iff_eq_none] at hc
      rw [hc] at hdir; cases hdir
  · cases hh'

/-- **`NPSafeF` over `Erase ∧ MemInv G` from a `Safely` judgment of
`EnvGCAdjXV`** and the thread's value specification `J`
(`npSafeF_of_safelyEnvGFCAdjX` with value facts). -/
theorem npSafeFV_of_safelyEnvGFCAdjXV
    {B : Config isa → (modelX isa (MemInvX G)).R → (modelX isa (MemInvX G)).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeFX e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGCAdjXV A tid pl S G) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    {J : isa.State → Prop} (hJ : ∀ st tree, J st → isa.exec st = some tree → tree.AllInv G J)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvGF (I := isa) tid pl (QX64CAdjV A tid pl S G e endPc post) cl c r g) (hj : OwnJ tid J c) :
    NPSafeF (modelX isa (MemInvX G)) A B tid n m cl c r g :=
  NPSafeF.of_ruleRXFV (ThreadRuleRXFV.ofEnvGFCAdjV (linkHypsFCAdjV_QX64CAdjV (tid := tid) hpl hS hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QX64CAdjV hstuck hQ hh) hp hrel hcl)
    hJ n m cl c r g h hj

end Link

/-- **The rule's invariant at the initial configuration**, from `QX64CAdjV`
at `σInitX` (`invGFCAdjX_init`). -/
theorem invGFCAdjXV_init {A : Arch} {tid : Nat} {pl : SLR.EnvG.Plan} {S : SharedEnv.Layout} {G : Loc → Val → Prop}
    {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = []) {e : Kraken.Executable Directive} {endPc : Int64}
    {post : MachineState × EStateX → Prop}
    (hQ : QX64CAdjV A tid pl S G e endPc post s (σInitX (Config.init ss m) r g)) :
    InvGF (I := isa) tid pl (QX64CAdjV A tid pl S G e endPc post) True (Config.init ss m) r g :=
  ⟨σInitX (Config.init ss m) r g, Thread.init s, coreAtFX_init hs hpend, hQ⟩

/-- **The tree law of an x64 `inv S G` value specification** (the per-tree
form of `threadSpec_stepPreserves`). -/
theorem threadSpecX_allInv {S : SharedEnv.Layout} {G : Loc → Val → Prop} (hS : Le16 S) (sp : ThreadSpec S G) :
    ∀ st tree, sp.Holds st → isa.exec st = some tree → tree.AllInv G sp.Holds := by
  intro st tree ⟨he, hend, hds, hs, hinv⟩ hex
  have hv := sp.valid
  rcases sp.closed _ hinv with hP | ⟨R, hT, hR⟩
  · have hpc : st.st.2 = sp.endPc := sp.post_end _ hP
    have hnone : isa.exec st = none := by
      show exec st = none
      simp [exec, hpc, hend]
    rw [hnone] at hex; cases hex
  · exact (exec_allInv_of_instrStepEnv hS he hds hs hT tree hex).mono fun st' ⟨⟨hRo, hs'⟩, he', hend', hds'⟩ =>
      ⟨he'.trans he, hend'.trans hend, hds'.trans hds, hs', hR _ hRo⟩

/-- **`final_of_relPureSafelyQX_tsoF'` with value facts** (route (c2)):
tokens at `modelX isa (MemInvX G)`, the value side by per-thread
specifications `J`; `NTFree` and `PromisePure` from the existing (unrestricted)
x64 purity specifications. -/
theorem final_of_relPureSafelyQX_tsoFV {fuel : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
    {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop} {Φ : Config isa → Prop}
    (G : Loc → Val → Prop) (J : Nat → isa.State → Prop)
    (hJ : ∀ tid st tree, J tid st → isa.exec st = some tree → tree.AllInv G (J tid))
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (hm0 : MemInv G (Config.init states initMem).mem) (h0v : ∀ tid s, states[tid]? = some s → J tid s)
    (sp : Nat → RelPureSpecQX Arch.tso fun _ _ => False) (h0 : ∀ tid s, states[tid]? = some s → (sp tid).Holds s)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafeF (modelX isa (MemInvX G)) Arch.tso B tid n m True (Config.init states initMem) (rF tid) g₀)
    {c : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c := by
  have hs : ∀ s ∈ states, ∃ tid, (sp tid).Holds s := fun s hs => by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
    exact ⟨i, h0 i _ (List.getElem?_eq_getElem hi)⟩
  have hstep : ∀ tid st tree, (sp tid).Holds st → isa.exec st = some tree →
      tree.RelWrites Arch.tso (fun l v => Pred.Pure (g₀.rel l) v) ∧ tree.All (sp tid).Holds :=
    fun tid _ tree h hex => ⟨EvTree.NoNT.relWrites tso_storeKind_rel
      (EvTree.noNT_tso_of_relWrites_false (relPureSpecQX_step (sp tid) h tree hex).1),
      (relPureSpecQX_step (sp tid) h tree hex).2⟩
  have hpure : PromisePure Arch.tso fuel states initMem g₀.rel :=
    promisePure_of_relWrites (fun st => ∃ tid, (sp tid).Holds st)
      (fun _ hc' tid t ht => ⟨tid, relWrites_reach (fun tid st => (sp tid).Holds st) hstep h0 hc' tid t ht⟩)
      (fun st tree ⟨tid, hJ⟩ hex => (hstep tid st tree hJ hex).1)
  exact final_of_chainV G J hJ (fun _ hc' => Config.ntFree_of_noNTInv (noNTInv_of_specQX sp) hs hc') hE hpend
    hm0 h0v hpure hsafe hc hf hfin

/-- **The x64 bridge from `inv S G` specifications** (route (c2)): the x64 pilot's
`EnvGValsBridgeX` shape with `hvals` replaced by `inv_reachable`'s hypotheses
(`hm0`, `h0v`) and the purity specifications unrestricted (see the module
docstring). -/
theorem envGValsBridgeX_ofSpecs {S : SharedEnv.Layout} (hS : Le16 S) (G : Loc → Val → Prop)
    (vs : Nat → ThreadSpec S G) {fuel : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
    {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop} {Φ : Config isa → Prop}
    {pl : Nat → SLR.EnvG.Plan} {e : Nat → Kraken.Executable Directive} {endPc : Nat → Int64}
    {post : Nat → MachineState × EStateX → Prop}
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (sp : Nat → RelPureSpecQX Arch.tso fun _ _ => False) (h0 : ∀ tid s, states[tid]? = some s → (sp tid).Holds s)
    (hm0 : MemInv G (Config.init states initMem).mem)
    (h0v : ∀ tid t, (Config.init states initMem).threads[tid]? = some t → (vs tid).Holds t.st)
    (hthr : ∀ tid, tid < states.length →
      Kraken.Executable.ValidLayout (e tid) ∧ (pl tid).Valid ∧ Phase1TreeFX (e tid) ∧
      (∀ y, post tid y → y.1.2 = endPc tid) ∧
      (∀ x R, x.1.2 = endPc tid → ¬ (e tid).instrStepEnv (EnvGCAdjXV Arch.tso tid (pl tid) S G) x R) ∧
      (∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post tid (t.st.st, σ) → t.prom = [] →
        EnvRel tid (pl tid) σ c t r g cl → cl → B c r g) ∧
      ∃ s, states[tid]? = some s ∧
        QX64CAdjV Arch.tso tid (pl tid) S G (e tid) (endPc tid) (post tid) s
          (σInitX (Config.init states initMem) (rF tid) g₀))
    {c : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c := by
  have h0v' : ∀ tid s, states[tid]? = some s → (vs tid).Holds s :=
    fun tid s hs => h0v tid (Thread.init s) (by simp [Config.init]; exact ⟨s, hs, rfl⟩)
  refine final_of_relPureSafelyQX_tsoFV G (fun tid => (vs tid).Holds) (fun tid => threadSpecX_allInv hS (vs tid))
    hE hpend hm0 h0v' sp h0 ?_ hc hf hfin
  intro tid htid n m
  obtain ⟨hv, hpl, hshape, hpost, hstuck, hB, s, hs, hQ⟩ := hthr tid htid
  exact npSafeFV_of_safelyEnvGFCAdjXV (e := e tid) hpl hS hshape hpost hstuck hB
    (threadSpecX_allInv hS (vs tid)) n m (invGFCAdjXV_init hs (List.eq_nil_iff_forall_not_mem.mpr hpend) hQ)
    ⟨Thread.init s, by simp [Config.init, hs], h0v' tid s hs⟩

end Kraken.Promising.X64.EnvG.Vals

#print axioms Kraken.Promising.X64.EnvG.Vals.final_of_relPureSafelyQX_tsoFV
#print axioms Kraken.Promising.X64.EnvG.Vals.envGValsBridgeX_ofSpecs
