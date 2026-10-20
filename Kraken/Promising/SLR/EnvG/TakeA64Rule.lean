/-
**Part 3: the AArch64 rule with taking
loads, start and no-fault.** Additive (`EnvG/TakeA64Link.lean` unchanged).

- `qa64T_of_partialTripleEnv`, `invGT_init`: `QA64T` from a `vcgen` partial
  triple in `EnvGT` at a thread's start, and the rule's invariant at the
  initial configuration (`qa64_of_partialTripleEnv`/`invG_init` for `EnvGT`;
  the invariant core `coreAt_init` is shared).
- `NoFaultRuleS R`: `NoFaultRule` (`SLR/Sim/NoFault.lean`, stated for
  `ThreadRuleRX`) for a rule whose loads may take (`ThreadRuleRXGS`), same
  field. `NoFaultRuleS.ofNoFault`: from fault-free trees. (ISA-neutral; in
  `EnvG/TakeNoFault.lean`, same names and statements.)
- `noFault_QA64T`, **`noFaultRule_ofSafelyEnvGT_struct`**: the no-fault rule
  of `ThreadRuleRXGS.ofSafelyEnvGT` for fault-free code (`DirsNoFault e`),
  unconditional in the thread's promises (the copy of
  `noFaultRule_ofSafelyEnvG_struct`).

Phase-1 limits as `EnvG/TakeA64Link.lean`.
-/
import Kraken.Promising.SLR.EnvG.TakeA64Link
import Kraken.Promising.SLR.EnvG.A64Answers
import Kraken.Promising.SLR.EnvG.SafelyBridge
import Kraken.Promising.SLR.EnvG.TakeNoFault

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## Start -/

section Triple

variable {A : Arch} {tid : Nat} {pl : Plan}

/-- **`QA64T` from a partial triple** in `EnvGT` at a thread state at the
start of `p`, whose exceptional exit `E` never holds. -/
theorem qa64T_of_partialTripleEnv [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Kraken.Executable.ValidLayout (layout p)] {P Q : MachineData → EStateA → Prop}
    {E : Int64 → MachineData → EStateA → Prop} (ht : MachineWP.PartialTripleEnv (EnvGTA A tid pl) P p Q E)
    (henv : cenv = layout p) {st : State} (he : st.exe = layout p) (hds : st.decls = {})
    (hend : st.endPc = (layout p).addrOf p.length) (hpc : st.st.2 = (layout p).addrOf 0) {σ : EStateA}
    (hP : P st.st.1 σ) (hE : ∀ a s g, ¬ E a s g := by simp) :
    QA64T A tid pl (layout p) ((layout p).addrOf p.length) (postOf p Q) st σ := by
  refine ⟨he, hds, hend, ?_⟩
  have hst : st.st = (st.st.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hpc, Executable.addrOf_zero, Layout.apply_fst]
  rw [hst]
  exact (Program.instrStepEnv_of_partialTripleEnv ht hP henv).mono fun _ h => h.imp id (hE _ _ _)

/-- **The rule's invariant at the initial configuration** from `QA64T` at
`σInit`. -/
theorem invGT_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = []) {e : Kraken.Executable Directive} {endPc : Int64}
    {post : MachineState × EStateA → Prop} (hQ : QA64T A tid pl e endPc post s (σInit (Config.init ss m) r g)) :
    InvG (I := isa) A tid pl (QA64T A tid pl e endPc post) True (Config.init ss m) r g :=
  ⟨_, _, coreAt_init hs hpend, hQ⟩

end Triple

end Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
  {endPc : Int64} {post : MachineState × EStateA → Prop}

/-- **Every tree from a `QA64T`-state is fault-free**, for fault-free code
(`noFault_QA64` for `EnvGT`). -/
theorem noFault_QA64T (hnf : DirsNoFault e) (hpost : ∀ y, post y → y.1.2 = endPc) :
    ∀ st σ tree, QA64T A tid pl e endPc post st σ → isa.exec st = some tree → tree.NoFault := by
  intro st σ tree h hex
  obtain ⟨he, hds, hend, hsafe⟩ := h
  rcases hsafe.unfold with hp | ⟨R, hR, -⟩
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · obtain ⟨d, z, rest, hcode, -⟩ := id hR
    exact noFault_of_codeAt he hds hcode (hnf d z (mem_of_codeAt hcode)) tree hex

/-- **The AArch64 no-fault rule with taking loads**, unconditional in the
thread's promises: `NoFaultRuleS (ofSafelyEnvGT …)` for fault-free code
(`noFaultRule_ofSafelyEnvG_struct` for `EnvGT`). -/
theorem noFaultRule_ofSafelyEnvGT_struct {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRuleS (ThreadRuleRXGS.ofSafelyEnvGT hpl hlive hshape hpost hstuck hB) :=
  NoFaultRuleS.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp => by
    obtain ⟨σ, hQ⟩ := InvG.q_at rF t h he hg ht E hnp
    exact noFault_QA64T hnf hpost t.st σ tree hQ hex

end Link

end Kraken.Promising.AArch64.EnvG

#print axioms Kraken.Promising.AArch64.EnvG.noFaultRule_ofSafelyEnvGT_struct
#print axioms Kraken.Promising.AArch64.EnvG.invGT_init
