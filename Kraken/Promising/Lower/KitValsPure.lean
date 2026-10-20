/-
Purity under a global value invariant: `PromisePure` from purity judgments
in a value-restricted environment.

The purity step of the Theorem 1′ chain (`promisePure_of_relWrites`) asks
every non-release write of every reachable instruction to write a pure value,
on every branch of the instruction's event tree. A thread whose pointer
accesses only miss its private memory for the values a global invariant `G`
allows (a node address read from a shared cell) cannot prove that in
`relPure`: the vcgen proof needs the load answers to satisfy `G`. When every
thread keeps `MemInv G` (a value specification, `EvTree.AllInv G`), every
load of a reachable run does answer a `G`-value, so the branches with other
answers are never run, and purity in `valsEnv (relPure A rel) G` suffices.

ISA-neutral part (in `SLR/PromisePureVals.lean`, moved there unchanged so
that the x64 layer `Lower/KitX64ValsPure.lean` can use it; imported here):
- `EvTree.RelWritesV A Q G R`: `RelWrites A Q` on the branches whose load
  answers satisfy `G`, leaves in `R`; `EvTree.AllInv.and_relWritesV`.
- `runTree_relFulfilsLive_of_relWritesV`,
  `stepOne_relFulfilsLive_of_relWritesV`: the run lemmas of
  `PromisePureGeneral` from a memory satisfying `MemInv G` and a tree
  satisfying `AllInv G` (the memory stays in `MemInv G` along the run).
- **`promisePure_of_relWritesV`**: `PromisePure` from per-thread
  invariants `J` whose trees satisfy `AllInv G J` and `RelWritesV` (a value
  specification and a value-restricted purity judgment at once), `MemInv G`
  initially and `J` at the initial states.

AArch64 part:
- `TreeJ.relWritesV`: `RelWritesV` as a tree judgment of
  `valsEnv (relPureQ A Q) G`.
- `RelPureSpec.HoldsV G sp`: a purity specification whose `Safely` judgment
  is in `valsEnv (relPure A rel) G`; `relPureSpecV_step`,
  `RelPureSpec.holdsV_of_partialTripleEnv`.
- **`final_of_relPureSafelyFVP`**: `final_of_relPureSafelyFV` with the
  purity specifications in `valsEnv (relPure A rel) G`.

Machine: the executable Promising machine (`Reachable A`). Phase-1 limits
apply to the chain's `NPSafeF` premise only, as before.
-/
import Kraken.Promising.Lower.Kit
import Kraken.Promising.SLR.PromisePureVals

namespace Kraken.Promising.Lower.KitVals

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvSpike Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG.Vals (valsEnv MemInvX)
open Kraken.Promising.AArch64.EnvG.Vals (EnvGCAdjV QA64CAdjV npSafeFV_of_safelyEnvGFCAdjV threadSpec_allInv)

/-! ## The AArch64 link -/

/-- **`RelWritesV` as a tree judgment** of the value-restricted purity
environment `valsEnv (relPureQ A Q) G`. -/
def TreeJ.relWritesV (A : Arch) (Q G : Loc → Val → Prop) {σ : Type} (R : σ → Prop) :
    TreeJ (valsEnv (SharedEnv.relPureQ A Q) G) σ where
  W t _ := t.RelWritesV A Q G R
  Post s _ := R s
  done h := h
  fault := trivial
  choose h := h
  load _ h := fun v hv => h v () ⟨trivial, hv⟩
  store hok h := ⟨hok, fun b => h b () ⟨trivial, trivial⟩⟩
  rmw hok h := ⟨hok, fun v => h v () ⟨trivial, trivial⟩⟩
  fence _ h := fun _ => h () ⟨trivial, trivial⟩

variable {A : Arch} {rel : Loc → Pred}

/-- A purity specification holds at a thread state **in the value-restricted
purity environment**: its code, end address, no declarations, and the
`Safely` judgment in `valsEnv (relPure A rel) G`. -/
def _root_.Kraken.Promising.AArch64.EnvG.RelPureSpec.HoldsV (G : Loc → Val → Prop) (sp : RelPureSpec A rel) (st : isa.State) : Prop :=
  st.exe = sp.e ∧ st.endPc = sp.endPc ∧ st.decls = {} ∧
    Safely (sp.e.instrStepEnv (valsEnv (SharedEnv.relPure A rel) G)) sp.post (st.st, ())

/-- **One instruction** (`relPureSpec_step` on the `G`-branches). -/
theorem relPureSpecV_step {G : Loc → Val → Prop} (sp : RelPureSpec A rel) {st : isa.State}
    (h : sp.HoldsV G st) (tree : EvTree isa.State) (hex : isa.exec st = some tree) :
    tree.RelWritesV A (fun l v => Pred.Pure (rel l) v) G (sp.HoldsV G) := by
  obtain ⟨he, hend, hds, hs⟩ := h
  have hv := sp.valid
  rcases hs.unfold with hP | ⟨R, hT, hR⟩
  · have hpc : st.st.2 = sp.endPc := sp.post_end _ hP
    have hnone : isa.exec st = none := by
      show exec st = none
      simp [exec, hpc, hend]
    rw [hnone] at hex
    cases hex
  · exact Kraken.Promising.AArch64.EnvSpike.exec_treeJ_of_instrStepEnv (TreeJ.relWritesV A _ G (sp.HoldsV G))
      he hds hT (fun m g' hm => by cases g'; exact ⟨he, hend, hds, hR _ hm⟩) tree hex

/-- **The spec from a partial triple** in `valsEnv (relPure A rel) G`
(`RelPureSpec.holds_of_partialTripleEnv`). -/
theorem _root_.Kraken.Promising.AArch64.EnvG.RelPureSpec.holdsV_of_partialTripleEnv {G : Loc → Val → Prop} [CodeEnv] [layout : _root_.Layout]
    {p : Program} [Kraken.Executable.ValidLayout (layout p)] {P Q : MachineData → Unit → Prop}
    {E : Int64 → MachineData → Unit → Prop}
    (ht : MachineWP.PartialTripleEnv (valsEnv (SharedEnv.relPure A rel) G) P p Q E)
    (henv : cenv = layout p) {st : isa.State} (he : st.exe = layout p) (hds : st.decls = {})
    (hend : st.endPc = (layout p).addrOf p.length) (hpc : st.st.2 = (layout p).addrOf 0)
    (hP : P st.st.1 ()) (hE : ∀ a s g, ¬ E a s g := by simp) :
    (RelPureSpec.ofProgram (A := A) (rel := rel) p Q).HoldsV G st :=
  ⟨he, hend, hds, safely_start_of_partialTripleEnv ht henv hpc hP hE⟩

/-! ## The chain with value-restricted purity -/

/-- **`final_of_relPureSafelyFV` with the purity specifications in
`valsEnv (relPure A rel) G`** (`promisePure_of_relWritesV`, at the per-thread
invariant "value specification and purity specification"). -/
theorem final_of_relPureSafelyFVP (A : Arch) (fuel : Nat) {states : List isa.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop}
    {Φ : Config isa → Prop} (G : Loc → Val → Prop) (J : Nat → isa.State → Prop)
    (hJ : ∀ tid st tree, J tid st → isa.exec st = some tree → tree.AllInv G (J tid))
    (hH : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (hm0 : MemInv G (Config.init states initMem).mem) (h0v : ∀ tid s, states[tid]? = some s → J tid s)
    (sp : Nat → RelPureSpec A g₀.rel) (h0 : ∀ tid s, states[tid]? = some s → (sp tid).HoldsV G s)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafeF (modelX isa (MemInvX G)) A B tid n m True (Config.init states initMem) (rF tid) g₀)
    {c : Config isa} (hc : Reachable A fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c := by
  have hpure : PromisePure A fuel states initMem g₀.rel :=
    promisePure_of_relWritesV G (fun tid st => J tid st ∧ (sp tid).HoldsV G st)
      (fun tid st tree ⟨h1, h2⟩ hex =>
        ⟨(hJ tid st tree h1 hex).and_relWritesV (relPureSpecV_step (sp tid) h2 tree hex), _,
          relPureSpecV_step (sp tid) h2 tree hex⟩)
      hm0 (fun tid s hs => ⟨h0v tid s hs, h0 tid s hs⟩)
  exact Kraken.Promising.SLR.EnvG.Vals.final_of_chainV G J hJ hH hE hpend hm0 h0v hpure hsafe hc hf hfin

/-- **The value bridge from `inv S G` specifications, with value-restricted
purity** (`envGValsBridge_ofSpecs` with `sp`'s judgments in
`valsEnv (relPure A g₀.rel) G`). -/
theorem envGValsBridge_ofSpecsP {S : SharedEnv.Layout} (G : Loc → Val → Prop) (vs : Nat → ThreadSpec S G)
    (A : Arch) (fuel : Nat) (states : List isa.State) (initMem : List (Loc × Val)) (rF : Nat → Res) (g₀ : Ghost)
    (B : Config isa → Res → Ghost → Prop) (Φ : Config isa → Prop) (pl : Nat → SLR.EnvG.Plan)
    (e : Nat → Kraken.Executable Directive) (endPc : Nat → Int64) (post : Nat → MachineState × EStateA → Prop)
    (hH : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : g₀.pend = [])
    (sp : Nat → RelPureSpec A g₀.rel) (h0 : ∀ tid s, states[tid]? = some s → (sp tid).HoldsV G s)
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
    Φ c := by
  refine final_of_relPureSafelyFVP A fuel G (fun tid => (vs tid).Holds) (fun tid => threadSpec_allInv (vs tid))
    hH hE (by simp [hpend]) hm0 (fun tid s hs => h0v tid (Thread.init s) (by simp [Config.init, hs])) sp h0 ?_
    hc hf hfin
  intro tid htid n m
  obtain ⟨hv, hpl, hlive, hshape, hpost, hstuck, hB, s, hs, hQ⟩ := hthr tid htid
  exact npSafeFV_of_safelyEnvGFCAdjV (e := e tid) hpl hlive hshape hpost hstuck hB (threadSpec_allInv (vs tid)) n m
    ⟨σInit (Config.init states initMem) (rF tid) g₀, Thread.init s, coreAtF_init hs hpend, hQ⟩
    ⟨Thread.init s, by simp [Config.init, hs], h0v tid (Thread.init s) (by simp [Config.init, hs])⟩

end Kraken.Promising.Lower.KitVals
