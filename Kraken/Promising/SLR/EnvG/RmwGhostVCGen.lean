/-
**Part 1: `vcgen` over `EnvGC`/`EnvGTC`**
(the `EnvG/Simp.lean` + `EnvG/A64VCGen.lean` support, and its `EnvGT` copy
`EnvG/TakeVCGen.lean`, for the claim-conditional extension's claim-conditional environments
`EnvG/RmwGhost.lean`, `EnvG/RmwGhostTake.lean`). Additive; closes the claim-conditional extension's
open issue 1.

- **`@[simp]` `ok`/`step`** at states typed `(EnvGC I A tid pl).State` /
  `(EnvGTC I A tid pl).State` (as `vcgen` goals carry them): `ok` is
  `StoreOk`/`RmwOkC` (trivial for loads and fences); a load step is `LoadOut`
  (`EnvGC`) or `LoadOutT` (`EnvGTC`), a store `StoreOut`, an RMW `RmwOutC`,
  a fence `FenceOut`. So the `EnvG`/`EnvGT` load and store facts
  (`loadOutT_facts`, `storeOut_facts`, …) and `rmwOutC_facts` apply after
  `simp`; the step forms `step_loadFactsTC`, `step_storeFactsTC`,
  `step_rmwFactsTC` take the `EnvGTC` step directly.
- **`SharedEnv.FenceMono`** for both, with `le = FenceLe`: their fences are
  `EnvG`'s, so `fenceInv_fenceLe` is the proof. `envMono_lift_spec`
  (`@[spec 40]`) then runs silent instructions, also under
  `SharedEnv.counted` (the generic instance). `fenceMono_le_envGC`,
  `fenceMono_le_envGTC` (`@[simp]`).
- **Release-only RMWs**: `claimSlotsC_armv8_rel` (`@[simp]`): on armv8 a
  `.rel` RMW (`swpl`, `ldaddl`) claims nothing, so its outcome's resource is
  `pl.after … ⋅ prod []`. The `vcgen` rule for `SWP`/`LD<op>` is the generic
  `swp_shared_spec`/`ldop_shared_spec` (`AArch64/EnvVCGen.lean`), which is
  stated for any environment; no new spec is needed.
- AArch64 start: `qa64C_of_partialTripleEnv` (`QA64C`, the `EnvGC` invariant
  of `EnvG/RmwGhostA64.lean`) and `qa64TC_of_partialTripleEnv` (`QA64TC`), the
  copies of `qa64_of_partialTripleEnv`/`qa64T_of_partialTripleEnv`.

Everything above the AArch64 start is ISA-neutral and lives in
`EnvG/RmwGhostVCGenCommon.lean` (moved unchanged).

Phase-1 limits as `EnvG/RmwGhostTake.lean`.
-/
import Kraken.Promising.SLR.EnvG.RmwGhostTake
import Kraken.Promising.SLR.EnvG.RmwGhostVCGenCommon
import Kraken.Promising.SLR.EnvG.TakeVCGen
import Kraken.Promising.SLR.EnvG.TakeA64Rule
import Kraken.Promising.SLR.EnvG.TakeFacts

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## Start -/

section Triple

variable {A : Arch} {tid : Nat} {pl : Plan}

/-- **`QA64C` from a partial triple** in `EnvGC` at a thread state at the
start of `p`, whose exceptional exit `E` never holds. -/
theorem qa64C_of_partialTripleEnv [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Kraken.Executable.ValidLayout (layout p)] {P Q : MachineData → EStateA → Prop}
    {E : Int64 → MachineData → EStateA → Prop} (ht : MachineWP.PartialTripleEnv (EnvGCA A tid pl) P p Q E)
    (henv : cenv = layout p) {st : State} (he : st.exe = layout p) (hds : st.decls = {})
    (hend : st.endPc = (layout p).addrOf p.length) (hpc : st.st.2 = (layout p).addrOf 0) {σ : EStateA}
    (hP : P st.st.1 σ) (hE : ∀ a s g, ¬ E a s g := by simp) :
    QA64C A tid pl (layout p) ((layout p).addrOf p.length) (postOf p Q) st σ := by
  refine ⟨he, hds, hend, ?_⟩
  have hst : st.st = (st.st.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hpc, Executable.addrOf_zero, Layout.apply_fst]
  rw [hst]
  exact (Program.instrStepEnv_of_partialTripleEnv ht hP henv).mono fun _ h => h.imp id (hE _ _ _)

/-- **`QA64TC` from a partial triple** in `EnvGTC` at a thread state at the
start of `p`, whose exceptional exit `E` never holds. -/
theorem qa64TC_of_partialTripleEnv [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Kraken.Executable.ValidLayout (layout p)] {P Q : MachineData → EStateA → Prop}
    {E : Int64 → MachineData → EStateA → Prop} (ht : MachineWP.PartialTripleEnv (EnvGTCA A tid pl) P p Q E)
    (henv : cenv = layout p) {st : State} (he : st.exe = layout p) (hds : st.decls = {})
    (hend : st.endPc = (layout p).addrOf p.length) (hpc : st.st.2 = (layout p).addrOf 0) {σ : EStateA}
    (hP : P st.st.1 σ) (hE : ∀ a s g, ¬ E a s g := by simp) :
    QA64TC A tid pl (layout p) ((layout p).addrOf p.length) (postOf p Q) st σ := by
  refine ⟨he, hds, hend, ?_⟩
  have hst : st.st = (st.st.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hpc, Executable.addrOf_zero, Layout.apply_fst]
  rw [hst]
  exact (Program.instrStepEnv_of_partialTripleEnv ht hP henv).mono fun _ h => h.imp id (hE _ _ _)

end Triple

end Kraken.Promising.AArch64.EnvG
