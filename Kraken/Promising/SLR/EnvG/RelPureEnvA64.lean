/-
**The purity environment, AArch64 link**: from one `vcgen` judgment per thread in
`SharedEnv.relPure A g₀.rel` to the purity hypotheses of
`final_of_relWrites`.

- `RelPureSpec A rel`: a thread's code (validly laid out), end address and
  postcondition (only at the end address). `RelPureSpec.Holds sp st`: the
  thread state runs `sp.e` with end address `sp.endPc`, no declarations, and
  `Safely (sp.e.instrStepEnv (relPure A rel)) sp.post` at its machine state
  (the pattern of `InvLinkAArch64.ThreadSpec`, with `Safely` as the
  invariant).
- `relPureSpec_step`: **one instruction**. From a state where the spec
  holds, every tree of the thread is `RelWrites A (Pure ∘ rel)` and all its
  leaves satisfy the spec again: at the end address there is no tree; away
  from it `Safely` unfolds to an environment step, which
  `EnvSpike.exec_treeJ_of_instrStepEnv` carries to the tree judgment
  `TreeJ.relWrites`.
- `final_of_relPureSafely`: **`final_of_relWrites` with the purity
  hypotheses (`Jinv`, `hJ`, `hcell`) replaced by one spec per thread id
  holding at its initial state** (`final_of_relWritesJ`).
- `RelPureSpec.ofProgram p Q`, `RelPureSpec.holds_of_partialTripleEnv`: the
  entry from a `PartialTripleEnv` (a `TripleEnv` through `.partial`; a
  counted one through `.uncount`) of a laid-out program at a thread state at
  the start of its text, as `qa64_of_partialTripleEnv`.

No phase-1 restriction applies here: the trees may have any number of
accesses, and releasing RMWs are simply release writes (unconstrained), as in
`EvTree.RelWrites`.
-/
import Kraken.Promising.SLR.EnvG.RelPureEnv
import Kraken.Promising.SLR.EnvSpikeA64
import Kraken.AArch64.EnvCfg

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvSpike

/-- **A thread's purity specification**: code, end address and a
postcondition at the end address; the invariant is `Safely` in
`relPure A rel`. -/
structure RelPureSpec (A : Arch) (rel : Loc → Pred) where
  e : Kraken.Executable Directive
  valid : Kraken.Executable.ValidLayout e
  endPc : Int64
  post : MachineState × Unit → Prop
  post_end : ∀ y, post y → y.1.2 = endPc

variable {A : Arch} {rel : Loc → Pred}

/-- The specification holds at a thread state: its code, end address, no
declarations, and the `Safely` judgment at its machine state. -/
def RelPureSpec.Holds (sp : RelPureSpec A rel) (st : State) : Prop :=
  st.exe = sp.e ∧ st.endPc = sp.endPc ∧ st.decls = {} ∧
    Safely (sp.e.instrStepEnv (SharedEnv.relPure A rel)) sp.post (st.st, ())

/-- **One instruction**: from a state where the spec holds, every tree of the
thread writes only pure values non-release, and every leaf satisfies the
spec. -/
theorem relPureSpec_step (sp : RelPureSpec A rel) {st : State} (h : sp.Holds st) (tree : EvTree State)
    (hex : isa.exec st = some tree) :
    tree.RelWrites A (fun l v => Pred.Pure (rel l) v) ∧ tree.All sp.Holds := by
  obtain ⟨he, hend, hds, hs⟩ := h
  have hv := sp.valid
  rcases hs.unfold with hP | ⟨R, hT, hR⟩
  · have hpc : st.st.2 = sp.endPc := sp.post_end _ hP
    have hnone : isa.exec st = none := by
      show exec st = none
      simp [exec, hpc, hend]
    rw [hnone] at hex
    cases hex
  · exact EnvSpike.exec_treeJ_of_instrStepEnv (TreeJ.relWrites A (fun l v => Pred.Pure (rel l) v) sp.Holds) he hds hT
      (fun m g' hm => by cases g'; exact ⟨he, hend, hds, hR _ hm⟩) tree hex

/-- **`final_of_relWrites` from purity specifications**: one
`RelPureSpec A g₀.rel` per thread id, holding at the thread's initial state,
replaces `Jinv`, `hJ` and `hcell`. -/
theorem final_of_relPureSafely (A : Arch) (fuel : Nat) {states : List isa.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop}
    {Φ : Config isa → Prop}
    (hH : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (sp : Nat → RelPureSpec A g₀.rel) (h0 : ∀ tid s, states[tid]? = some s → (sp tid).Holds s)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafe (model isa) A B tid n m True (Config.init states initMem) (rF tid) g₀)
    {c : Config isa} (hc : Reachable A fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c :=
  final_of_relWritesJ A fuel hH hE hpend (fun tid st => (sp tid).Holds st)
    (fun tid _ tree h hex => relPureSpec_step (sp tid) h tree hex) h0 hsafe hc hf hfin

/-! ## From `vcgen` triples -/

/-- The specification of a laid-out program `p`: the end of its text, and
`Q` there. -/
def RelPureSpec.ofProgram [layout : _root_.Layout] (p : Program) [hv : Kraken.Executable.ValidLayout (layout p)]
    (Q : MachineData → Unit → Prop) : RelPureSpec A rel where
  e := layout p
  valid := hv
  endPc := (layout p).addrOf p.length
  post x := (x.1.2 = (layout p).addrOf p.length ∧ Q x.1.1 x.2) ∨ False
  post_end _ h := h.elim And.left False.elim

/-- **The spec from a partial triple** in `relPure A rel`, at a thread state
at the start of `p`, whose exceptional exit `E` never holds. -/
theorem RelPureSpec.holds_of_partialTripleEnv [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Kraken.Executable.ValidLayout (layout p)] {P Q : MachineData → Unit → Prop}
    {E : Int64 → MachineData → Unit → Prop}
    (ht : MachineWP.PartialTripleEnv (SharedEnv.relPure A rel) P p Q E)
    (henv : cenv = layout p) {st : State} (he : st.exe = layout p) (hds : st.decls = {})
    (hend : st.endPc = (layout p).addrOf p.length) (hpc : st.st.2 = (layout p).addrOf 0)
    (hP : P st.st.1 ()) (hE : ∀ a s g, ¬ E a s g := by simp) :
    (RelPureSpec.ofProgram (A := A) (rel := rel) p Q).Holds st := by
  refine ⟨he, hend, hds, ?_⟩
  have hst : st.st = (st.st.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hpc, Executable.addrOf_zero, Layout.apply_fst]
  rw [hst]
  exact (Program.instrStepEnv_of_partialTripleEnv ht hP henv).mono fun _ h => h.imp id (hE _ _ _)

end Kraken.Promising.AArch64.EnvG
