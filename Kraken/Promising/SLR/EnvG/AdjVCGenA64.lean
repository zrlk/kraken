/-
**AArch64 start lemmas for the adjacency environment `EnvGCAdj`**.

- `safely_start_of_partialTripleEnv`: the `Safely` judgment of **any**
  environment `E` at a thread state at the start of `p`, from a partial
  triple whose exceptional exit never holds. It is the common core of the
  per-environment copies `qa64_of_partialTripleEnv` (`EnvG/SafelyBridge.lean`),
  `qa64C_of_partialTripleEnv`/`qa64TC_of_partialTripleEnv`
  (`EnvG/RmwGhostVCGen.lean`), `qa64T_of_partialTripleEnv`, … (left as they
  are; a later round can re-prove them from it).
- `qa64CAdj_of_partialTripleEnv`: moved here unchanged (same name and
  statement) from `EnvG/Treiber2Public.lean`, now
  `⟨he, hds, hend, safely_start_of_partialTripleEnv …⟩`.
-/
import Kraken.Promising.SLR.EnvG.AdjSpikeA64
import Kraken.Promising.SLR.EnvG.RmwGhostVCGen

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-- **The `Safely` judgment at a thread's start from a partial triple**, in
any environment `E`: at a thread state at the start of `p` (`hpc`), the
triple's postcondition is `postOf p Q` when its exceptional exit `Ex` never
holds. -/
theorem safely_start_of_partialTripleEnv {E : SharedEnv} [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Kraken.Executable.ValidLayout (layout p)] {P Q : MachineData → E.State → Prop}
    {Ex : Int64 → MachineData → E.State → Prop} (ht : MachineWP.PartialTripleEnv E P p Q Ex)
    (henv : cenv = layout p) {st : State} (hpc : st.st.2 = (layout p).addrOf 0) {σ : E.State}
    (hP : P st.st.1 σ) (hE : ∀ a s g, ¬ Ex a s g) :
    Safely ((layout p).instrStepEnv E) (fun x => (x.1.2 = (layout p).addrOf p.length ∧ Q x.1.1 x.2) ∨ False)
      (st.st, σ) := by
  have hst : st.st = (st.st.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hpc, Executable.addrOf_zero, Layout.apply_fst]
  rw [hst]
  exact (Program.instrStepEnv_of_partialTripleEnv ht hP henv).mono fun _ h => h.imp id (hE _ _ _)

/-- **`QA64CAdj` from a partial triple** in `EnvGCAdj` at a thread state at
the start of `p`, whose exceptional exit `E` never holds (moved here from
`EnvG/Treiber2Public.lean`; an instance of
`safely_start_of_partialTripleEnv`). -/
theorem qa64CAdj_of_partialTripleEnv {A : Arch} {tid : Nat} {pl : Plan} [CodeEnv] [layout : _root_.Layout]
    {p : Program} [Kraken.Executable.ValidLayout (layout p)] {P Q : MachineData → EStateA → Prop}
    {E : Int64 → MachineData → EStateA → Prop} (ht : MachineWP.PartialTripleEnv (EnvGCAdjA A tid pl) P p Q E)
    (henv : cenv = layout p) {st : State} (he : st.exe = layout p) (hds : st.decls = {})
    (hend : st.endPc = (layout p).addrOf p.length) (hpc : st.st.2 = (layout p).addrOf 0) {σ : EStateA}
    (hP : P st.st.1 σ) (hE : ∀ a s g, ¬ E a s g := by simp) :
    QA64CAdj A tid pl (layout p) ((layout p).addrOf p.length) (postOf p Q) st σ :=
  ⟨he, hds, hend, safely_start_of_partialTripleEnv ht henv hpc hP hE⟩

end Kraken.Promising.AArch64.EnvG
