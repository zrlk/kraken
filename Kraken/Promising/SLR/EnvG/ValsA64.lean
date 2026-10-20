/-
**Part 4 of 4: the AArch64 layer and the bridge** (route (c2)).

`EnvGCAdjV`/`QA64CAdjV` (the stack-frame pilot's, definitionally) with the rule link
wrappers; **`final_of_relPureSafelyFV`**; **`EnvGValsBridgeJ`/`envGValsBridgeJ`**:
the stack-frame pilot's `EnvGValsBridge` with `hvals` (every reachable memory satisfies
`MemInv G`, which cannot feed the token: it must re-establish `MemInv G` at
arbitrary post-step configurations) replaced by the value specification
(`MemInv G` initially, a per-thread `J` with its tree law, `J` initially);
**`envGValsBridge_ofSpecs`** from `inv S G` `ThreadSpec`s
(`threadSpec_allInv`), whose value hypotheses are `inv_reachable`'s.
Phase-1 limits apply (`Phase1TreeF`).
-/
import Kraken.Promising.SLR.EnvG.ValsChain
import Kraken.Promising.SLR.EnvG.AdjSpikeA64
import Kraken.Promising.SLR.EnvG.A64RmwFailFinal
import Kraken.Promising.InvLinkAArch64

namespace Kraken.Promising.AArch64.EnvG.Vals

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.EnvSpike
open Kraken.Promising.SLR.EnvG.Vals Kraken.Promising.AArch64.EnvG

/-- **`EnvGCAdj` (AArch64) with value-restricted load answers.** -/
abbrev EnvGCAdjV (A : Arch) (tid : Nat) (pl : SLR.EnvG.Plan) (G : Loc → Val → Prop) : SharedEnv :=
  valsEnv (EnvGCAdjA A tid pl) G

/-- `QA64CAdj` with the `Safely` judgment of `EnvGCAdjV`. -/
def QA64CAdjV (A : Arch) (tid : Nat) (pl : SLR.EnvG.Plan) (G : Loc → Val → Prop) (e : Kraken.Executable Directive)
    (endPc : Int64) (post : MachineState × EStateA → Prop) (st : State) (σ : EStateA) : Prop :=
  st.exe = e ∧ st.decls = {} ∧ st.endPc = endPc ∧ Safely (e.instrStepEnv (EnvGCAdjV A tid pl G)) post (st.st, σ)

section Link

variable {A : Arch} {tid : Nat} {pl : SLR.EnvG.Plan} {G : Loc → Val → Prop} {e : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateA → Prop}

/-- **The link hypotheses at `QA64CAdjV`** (`linkHypsFCAdj_QA64CAdj` over the
value-restricted env; the run lemma is generic in the env). -/
theorem linkHypsFCAdjV_QA64CAdjV (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeF e)
    (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsFCAdjV (I := isa) A tid pl G (QA64CAdjV A tid pl G e endPc post) where
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
/-- **`done` at `QA64CAdjV`**: a halted thread satisfies the postcondition. -/
theorem post_of_halted_QA64CAdjV
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGCAdjV A tid pl G) x R)
    {t : Thread isa} {σ : EStateA} (hQ : QA64CAdjV A tid pl G e endPc post t.st σ) (hh : t.halted = true) :
    post (t.st.st, σ) := by
  obtain ⟨he, -, hend, hsafe⟩ := hQ
  exact post_of_halted_env hstuck he hend hsafe hh

/-- **`NPSafeF` over `Erase ∧ MemInv G` from a `Safely` judgment of
`EnvGCAdjV`** and the thread's value specification `J`
(`npSafeF_of_safelyEnvGFCAdj` with value facts). -/
theorem npSafeFV_of_safelyEnvGFCAdjV
    {B : Config isa → (modelX isa (MemInvX G)).R → (modelX isa (MemInvX G)).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeF e)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGCAdjV A tid pl G) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    {J : isa.State → Prop} (hJ : ∀ st tree, J st → isa.exec st = some tree → tree.AllInv G J)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvGF (I := isa) tid pl (QA64CAdjV A tid pl G e endPc post) cl c r g) (hj : OwnJ tid J c) :
    NPSafeF (modelX isa (MemInvX G)) A B tid n m cl c r g :=
  NPSafeF.of_ruleRXFV (ThreadRuleRXFV.ofEnvGFCAdjV (linkHypsFCAdjV_QA64CAdjV (tid := tid) hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64CAdjV hstuck hQ hh) hp hrel hcl)
    hJ n m cl c r g h hj

end Link

/-- **`final_of_relPureSafelyF` with value facts** (route (c2)): tokens at
`modelX isa (MemInvX G)`, the value side by per-thread specifications `J`
(tree law `hJ`, `MemInv G` initially, `J` at the initial states). -/
theorem final_of_relPureSafelyFV (A : Arch) (fuel : Nat) {states : List isa.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop}
    {Φ : Config isa → Prop} (G : Loc → Val → Prop) (J : Nat → isa.State → Prop)
    (hJ : ∀ tid st tree, J tid st → isa.exec st = some tree → tree.AllInv G (J tid))
    (hH : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (hm0 : MemInv G (Config.init states initMem).mem) (h0v : ∀ tid s, states[tid]? = some s → J tid s)
    (sp : Nat → RelPureSpec A g₀.rel) (h0 : ∀ tid s, states[tid]? = some s → (sp tid).Holds s)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafeF (modelX isa (MemInvX G)) A B tid n m True (Config.init states initMem) (rF tid) g₀)
    {c : Config isa} (hc : Reachable A fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c := by
  have hstep : ∀ tid st tree, (sp tid).Holds st → isa.exec st = some tree →
      tree.RelWrites A (fun l v => Pred.Pure (g₀.rel l) v) ∧ tree.All (sp tid).Holds :=
    fun tid _ tree h hex => relPureSpec_step (sp tid) h tree hex
  have hpure : PromisePure A fuel states initMem g₀.rel :=
    promisePure_of_relWrites (fun st => ∃ tid, (sp tid).Holds st)
      (fun _ hc' tid t ht => ⟨tid, relWrites_reach (fun tid st => (sp tid).Holds st) hstep h0 hc' tid t ht⟩)
      (fun st tree ⟨tid, hJ⟩ hex => (hstep tid st tree hJ hex).1)
  exact final_of_chainV G J hJ hH hE hpend hm0 h0v hpure hsafe hc hf hfin

/-- **The EnvG ↔ value-invariant bridge, route (c2)**: the stack-frame pilot's
`EnvGValsBridge` with `hvals` replaced by the value specification (initial
memory, per-thread `J` with its tree law, `J` at the initial states); every
per-thread premise is the stack-frame pilot's. Proved: `envGValsBridgeJ`. -/
def EnvGValsBridgeJ (G : Loc → Val → Prop) : Prop :=
  ∀ (A : Arch) (fuel : Nat) (states : List isa.State) (initMem : List (Loc × Val)) (rF : Nat → Res) (g₀ : Ghost)
    (B : Config isa → Res → Ghost → Prop) (Φ : Config isa → Prop) (pl : Nat → SLR.EnvG.Plan)
    (e : Nat → Kraken.Executable Directive) (endPc : Nat → Int64) (post : Nat → MachineState × EStateA → Prop)
    (J : Nat → isa.State → Prop),
    (∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A) →
    Erase rF g₀ (fun _ => False) (Config.init states initMem) → g₀.pend = [] →
    ∀ (sp : Nat → RelPureSpec A g₀.rel), (∀ tid s, states[tid]? = some s → (sp tid).Holds s) →
    -- the value side (replaces `hvals`)
    MemInv G (Config.init states initMem).mem →
    (∀ tid st tree, J tid st → isa.exec st = some tree → tree.AllInv G (J tid)) →
    (∀ tid s, states[tid]? = some s → J tid s) →
    -- per thread: unchanged from the stack-frame pilot
    (∀ tid, tid < states.length →
      Kraken.Executable.ValidLayout (e tid) ∧ (pl tid).Valid ∧ (e tid).rmwLive = true ∧ Phase1TreeF (e tid) ∧
      (∀ y, post tid y → y.1.2 = endPc tid) ∧
      (∀ x R, x.1.2 = endPc tid → ¬ (e tid).instrStepEnv (EnvGCAdjV A tid (pl tid) G) x R) ∧
      (∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post tid (t.st.st, σ) → t.prom = [] →
        EnvRel tid (pl tid) σ c t r g cl → cl → B c r g) ∧
      ∃ s, states[tid]? = some s ∧
        QA64CAdjV A tid (pl tid) G (e tid) (endPc tid) (post tid) s (σInit (Config.init states initMem) (rF tid) g₀)) →
    ∀ c, Reachable A fuel (Config.init states initMem) c → c.final = true →
    (∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) →
    Φ c

/-- **The bridge holds** for every `G`. -/
theorem envGValsBridgeJ (G : Loc → Val → Prop) : EnvGValsBridgeJ G := by
  intro A fuel states initMem rF g₀ B Φ pl e endPc post J hH hE hpend sp h0 hm0 hJ h0v hthr c hc hf hfin
  refine final_of_relPureSafelyFV A fuel G J hJ hH hE (by simp [hpend]) hm0 h0v sp h0 ?_ hc hf hfin
  intro tid htid n m
  obtain ⟨hv, hpl, hlive, hshape, hpost, hstuck, hB, s, hs, hQ⟩ := hthr tid htid
  exact npSafeFV_of_safelyEnvGFCAdjV (e := e tid) hpl hlive hshape hpost hstuck hB (hJ tid) n m
    ⟨σInit (Config.init states initMem) (rF tid) g₀, Thread.init s, coreAtF_init hs hpend, hQ⟩
    ⟨Thread.init s, by simp [Config.init, hs], h0v tid s hs⟩

/-- **The tree law of an `inv S G` value specification** (the per-tree form of
`threadSpec_stepPreserves`). -/
theorem threadSpec_allInv {S : SharedEnv.Layout} {G : Loc → Val → Prop} (sp : ThreadSpec S G) :
    ∀ st tree, sp.Holds st → isa.exec st = some tree → tree.AllInv G sp.Holds := by
  intro st tree ⟨he, hend, hds, hinv⟩ hex
  have hv := sp.valid
  rcases sp.closed _ hinv with hP | ⟨R, hT, hR⟩
  · have hpc : st.st.2 = sp.endPc := sp.post_end _ hP
    have hnone : isa.exec st = none := by
      show exec st = none
      simp [exec, hpc, hend]
    rw [hnone] at hex; cases hex
  · exact (exec_allInv_of_instrStepEnv he hds hT tree hex).mono fun st' ⟨hRo, he', hend', hds'⟩ =>
      ⟨he'.trans he, hend'.trans hend, hds'.trans hds, hR _ hRo⟩

/-- **The bridge from `inv S G` specifications**: `envGValsBridgeJ` at
`J tid := (vs tid).Holds`. The value hypotheses `hm0`, `h0v` are exactly
`inv_reachable`'s, so a caller that discharged `hvals` by
`(inv_reachable vs hm0 h0v hc).1` passes `hm0 h0v` instead. -/
theorem envGValsBridge_ofSpecs {S : SharedEnv.Layout} (G : Loc → Val → Prop) (vs : Nat → ThreadSpec S G)
    (A : Arch) (fuel : Nat) (states : List isa.State) (initMem : List (Loc × Val)) (rF : Nat → Res) (g₀ : Ghost)
    (B : Config isa → Res → Ghost → Prop) (Φ : Config isa → Prop) (pl : Nat → SLR.EnvG.Plan)
    (e : Nat → Kraken.Executable Directive) (endPc : Nat → Int64) (post : Nat → MachineState × EStateA → Prop)
    (hH : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : g₀.pend = [])
    (sp : Nat → RelPureSpec A g₀.rel) (h0 : ∀ tid s, states[tid]? = some s → (sp tid).Holds s)
    (hm0 : MemInv G (Config.init states initMem).mem)
    (h0v : ∀ tid t, (Config.init states initMem).threads[tid]? = some t → (vs tid).Holds t.st)
    (hthr : ∀ tid, tid < states.length →
      Kraken.Executable.ValidLayout (e tid) ∧ (pl tid).Valid ∧ (e tid).rmwLive = true ∧ Phase1TreeF (e tid) ∧
      (∀ y, post tid y → y.1.2 = endPc tid) ∧
      (∀ x R, x.1.2 = endPc tid → ¬ (e tid).instrStepEnv (EnvGCAdjV A tid (pl tid) G) x R) ∧
      (∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post tid (t.st.st, σ) → t.prom = [] →
        EnvRel tid (pl tid) σ c t r g cl → cl → B c r g) ∧
      ∃ s, states[tid]? = some s ∧
        QA64CAdjV A tid (pl tid) G (e tid) (endPc tid) (post tid) s (σInit (Config.init states initMem) (rF tid) g₀))
    (c : Config isa) (hc : Reachable A fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c :=
  envGValsBridgeJ G A fuel states initMem rF g₀ B Φ pl e endPc post (fun tid => (vs tid).Holds) hH hE hpend sp h0
    hm0 (fun tid => threadSpec_allInv (vs tid))
    (fun tid s hs => h0v tid (Thread.init s) (by simp [Config.init, hs])) hthr c hc hf hfin

end Kraken.Promising.AArch64.EnvG.Vals

#print axioms Kraken.Promising.AArch64.EnvG.Vals.envGValsBridgeJ
#print axioms Kraken.Promising.AArch64.EnvG.Vals.envGValsBridge_ofSpecs
