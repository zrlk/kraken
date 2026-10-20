/-
**The fence-aware purity environment, AArch64 link**: from one `vcgen` judgment per thread in
`SharedEnv.relPureF A g₀.rel` to the purity hypotheses of
`final_of_relWritesF` (the `RelWritesF` analogue of
`EnvG/RelPureEnvA64.lean`).

- `relPureFQ` is a `SharedEnv.FenceMono` environment (`le b b' := b → b'`:
  fences only set the flag), so `envMono_lift_spec` runs silent
  instructions; `dmb_shared_spec` keeps the precise flag step.
- `RelPureFSpec A rel`, `RelPureFSpec.Holds sp st b`: the thread state runs
  `sp.e` with end address `sp.endPc`, no declarations, and
  `Safely (sp.e.instrStepEnv (relPureF A rel)) sp.post` at `(st.st, b)`.
- `relPureFSpec_step`: one instruction (`EnvSpike.exec_treeJ_of_instrStepEnv`
  at `TreeJ.relWritesF`).
- `final_of_relPureFSafely`: `final_of_relWritesF` with the purity
  hypotheses replaced by one spec per thread id, holding at its initial
  state with the flag clear (`final_of_relWritesFJ`).
- `RelPureFSpec.holds_of_partialTripleEnv`: the entry from a
  `PartialTripleEnv`, as `RelPureSpec.holds_of_partialTripleEnv`.
-/
import Kraken.Promising.SLR.EnvG.FenceEnvPure
import Kraken.Promising.SLR.EnvG.RelPureEnvA64
import Kraken.Promising.SLR.EnvG.A64VCGen

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvSpike

/-- **The flag only grows at fences**: `relPureFQ` is a `FenceMono`
environment. -/
instance (A : Arch) (Q : Loc → Val → Prop) : (SharedEnv.relPureFQ A Q).FenceMono where
  le b b' := b = true → b' = true
  refl _ := id
  fenceInv b k b₁ h₁ := ⟨trivial, fun b₂ (h₂ : b₂ = (b₁ || decide (k = .sy))) hb => by
    rw [h₂, h₁ hb]; rfl⟩

@[simp] theorem fenceMono_le_relPureFQ (A : Arch) (Q : Loc → Val → Prop) (b b' : Bool) :
    SharedEnv.FenceMono.le (env := SharedEnv.relPureFQ A Q) b b' ↔ (b = true → b' = true) := Iff.rfl

/-- **A thread's fence-aware purity specification**: code, end address and a
postcondition at the end address; the invariant is `Safely` in
`relPureF A rel`. -/
structure RelPureFSpec (A : Arch) (rel : Loc → Pred) where
  e : Kraken.Executable Directive
  valid : Kraken.Executable.ValidLayout e
  endPc : Int64
  post : MachineState × Bool → Prop
  post_end : ∀ y, post y → y.1.2 = endPc

variable {A : Arch} {rel : Loc → Pred}

/-- The specification holds at a thread state and flag. -/
def RelPureFSpec.Holds (sp : RelPureFSpec A rel) (st : State) (b : Bool) : Prop :=
  st.exe = sp.e ∧ st.endPc = sp.endPc ∧ st.decls = {} ∧
    Safely (sp.e.instrStepEnv (SharedEnv.relPureF A rel)) sp.post (st.st, b)

/-- **One instruction**: from a state where the spec holds at flag `b`,
every tree of the thread is `RelWritesF` at `b`, and every leaf satisfies
the spec at its flag. -/
theorem relPureFSpec_step (sp : RelPureFSpec A rel) {st : State} {b : Bool} (h : sp.Holds st b)
    (tree : EvTree State) (hex : isa.exec st = some tree) :
    tree.RelWritesF A (fun l v => Pred.Pure (rel l) v) (b = true) ∧ RunsF sp.Holds b tree := by
  obtain ⟨he, hend, hds, hs⟩ := h
  have hv := sp.valid
  rcases hs.unfold with hP | ⟨R, hT, hR⟩
  · have hpc : st.st.2 = sp.endPc := sp.post_end _ hP
    have hnone : isa.exec st = none := by
      show exec st = none
      simp [exec, hpc, hend]
    rw [hnone] at hex
    cases hex
  · exact EnvSpike.exec_treeJ_of_instrStepEnv (TreeJ.relWritesF A (fun l v => Pred.Pure (rel l) v) sp.Holds)
      he hds hT (fun m g' hm => ⟨he, hend, hds, hR _ hm⟩) tree hex

/-- **`final_of_relWritesF` from fence-aware purity specifications**: one
`RelPureFSpec A g₀.rel` per thread id, holding at the thread's initial state
with the flag clear, replaces `Jinv`, `hJ` and `hcell`. -/
theorem final_of_relPureFSafely (A : Arch) (fuel : Nat) {states : List isa.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop}
    {Φ : Config isa → Prop}
    (hH : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (sp : Nat → RelPureFSpec A g₀.rel) (h0 : ∀ tid s, states[tid]? = some s → (sp tid).Holds s false)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafeP (model isa) A B tid (GHyb g₀.rel) (K2Scope (model isa) AllocIds) n m True
        (Config.init states initMem) (rF tid) g₀)
    {c : Config isa} (hc : Reachable A fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c :=
  final_of_relWritesFJ A fuel hH hE hpend (fun tid st b => (sp tid).Holds st b)
    (fun tid _ _ tree h hex => relPureFSpec_step (sp tid) h tree hex) h0 hsafe hc hf hfin

/-! ## From `vcgen` triples -/

/-- The specification of a laid-out program `p`: the end of its text, and
`Q` there. -/
def RelPureFSpec.ofProgram [layout : _root_.Layout] (p : Program) [hv : Kraken.Executable.ValidLayout (layout p)]
    (Q : MachineData → Bool → Prop) : RelPureFSpec A rel where
  e := layout p
  valid := hv
  endPc := (layout p).addrOf p.length
  post x := (x.1.2 = (layout p).addrOf p.length ∧ Q x.1.1 x.2) ∨ False
  post_end _ h := h.elim And.left False.elim

/-- **The spec from a partial triple** in `relPureF A rel`, at a thread state
at the start of `p` with the flag clear, whose exceptional exit `E` never
holds. -/
theorem RelPureFSpec.holds_of_partialTripleEnv [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Kraken.Executable.ValidLayout (layout p)] {P Q : MachineData → Bool → Prop}
    {E : Int64 → MachineData → Bool → Prop}
    (ht : MachineWP.PartialTripleEnv (SharedEnv.relPureF A rel) P p Q E)
    (henv : cenv = layout p) {st : State} (he : st.exe = layout p) (hds : st.decls = {})
    (hend : st.endPc = (layout p).addrOf p.length) (hpc : st.st.2 = (layout p).addrOf 0)
    (hP : P st.st.1 false) (hE : ∀ a s g, ¬ E a s g := by simp) :
    (RelPureFSpec.ofProgram (A := A) (rel := rel) p Q).Holds st false := by
  refine ⟨he, hend, hds, ?_⟩
  have hst : st.st = (st.st.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hpc, Executable.addrOf_zero, Layout.apply_fst]
  rw [hst]
  exact (Program.instrStepEnv_of_partialTripleEnv ht hP henv).mono fun _ h => h.imp id (hE _ _ _)

end Kraken.Promising.AArch64.EnvG

#print axioms Kraken.Promising.AArch64.EnvG.final_of_relPureFSafely
