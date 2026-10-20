/-
**Part 1: the x64 link with taking loads**,
`ThreadRuleRXGS.ofSafelyEnvGTX`: the x64 counterpart of
`ThreadRuleRXGS.ofSafelyEnvGT` (`EnvG/TakeA64Link.lean`), built as
`ThreadRuleRX.ofSafelyEnvGX` (`EnvG/X64Link.lean`) is built from
`ofSafelyEnvG`.

## The environment

A thread is proved in **`EnvGTX A tid pl S := (EnvGT isa A tid pl).within S`**:
`EnvGT` (non-forwarded acquire loads take their exposed slots,
`EnvG/TakeEnv.lean`) with every access restricted to a location of the shared
layout `S`, exactly as `EnvGX` restricts `EnvG`.

How `EnvGT` composes with `within`: `within` changes only `ok` (adds
`AccessIn S`); the state and the step relation are `EnvGT`'s, so every take
fact (`step_loadFactsT`, `LoadOutT`, `takeAll_wr_full`, `takeAll_held`)
applies verbatim to an `EnvGTX` step. The x64 run lemma
`exec_treeJLive_of_instrStepEnvW` (`EnvG/X64LiveRun.lean`) is generic in the
environment `E`, so at `E := EnvGT isa A tid pl` it turns a step of
`EnvGTX` into any live tree judgment of `EnvGT`: the `link` field of
`LinkHypsT` (`EnvG/TakeRuleLink.lean`). Nothing of the take route had to be
redone for x64.

Under `Arch.tso` every plain `mov` load is an acquire (`plainLoad := .acqPc`),
so **every non-forwarded x64 load may take**; every plain `mov` store is a
release *store* (`Phase1TreeX` admits it). x64 RMWs are release-kind and are
rejected by `Phase1TreeX` (there is no `EnvGT` link with release-kind RMWs on
x64 yet; `TakeRLink.lean`'s `ofEnvGTR` would be the base).

## Contents

- `EnvGTX`, `QX64T` (`QX64` for `EnvGTX`).
- `linkHypsT_QX64T`, `post_of_halted_QX64T`,
  **`ThreadRuleRXGS.ofSafelyEnvGTX : ThreadRuleRXGS G₀`**,
  **`npSafeP_of_safelyEnvGTX`** (frame `K2Scope (model isa) AllocIds`).
- No fault: `NoFaultRuleSX` (an alias of `NoFaultRuleS`,
  `EnvG/TakeNoFault.lean`,; formerly a local copy), `NoFaultRuleSX.ofNoFault`,
  `noFault_QX64T`, **`noFaultRule_ofSafelyEnvGTX_struct`** (unconditional in
  the thread's promises, from `DirsNoFault e`).
- Start: `qx64T_of_partialTripleEnv`, **`invGTX_init`**.

Phase-1 limits: as `ofSafelyEnvGX` (single-access trees, releases are stores,
`Phase1TreeX` a stated hypothesis, `Le16 S`), plus those of the take route:
only non-forwarded acquire loads take, no fence-node take, the take and the
use of what is taken are in different instructions.
-/
import Kraken.Promising.SLR.EnvG.TakeRuleLink
import Kraken.Promising.SLR.EnvG.X64Link
import Kraken.Promising.SLR.EnvG.TakeNoFault
import Kraken.Promising.SLR.EnvG.Alias

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## The environment and the invariant -/

/-- **`EnvGT` for x64**, restricted to the shared layout `S`. -/
abbrev EnvGTX (A : Arch) (tid : Nat) (pl : Plan) (S : SharedEnv.Layout) : SharedEnv :=
  (Kraken.Promising.SLR.EnvGT isa A tid pl).within S

/-- **The thread-local invariant with taking loads, x64** (`QX64` for
`EnvGTX`). -/
def QX64T (A : Arch) (tid : Nat) (pl : Plan) (S : SharedEnv.Layout) (e : Kraken.Executable Directive)
    (endPc : Int64) (post : MachineState × EStateX → Prop) (st : State) (σ : EStateX) : Prop :=
  st.exe = e ∧ st.decls = {} ∧ st.endPc = endPc ∧ Split S st.st.1.dmem ∧
    Safely (e.instrStepEnv (EnvGTX A tid pl S)) post (st.st, σ)

/-! ## No fault for rules whose loads may take

`NoFaultRuleSX` was a local copy of `NoFaultRuleS` (then in the AArch64 file
`EnvG/TakeA64Rule.lean`). `NoFaultRuleS` is now in the ISA-neutral
`EnvG/TakeNoFault.lean`, and `NoFaultRuleSX` with its constructor, field,
recursors and `ofNoFault` are aliases of it (`hoist_alias`, same statements;
the structure itself is now a reducible definition). -/

hoist_alias [
  Kraken.Promising.SLR.NoFaultRuleS ↦ Kraken.Promising.X64.EnvG.NoFaultRuleSX,
  Kraken.Promising.SLR.NoFaultRuleS.mk ↦ Kraken.Promising.X64.EnvG.NoFaultRuleSX.mk,
  Kraken.Promising.SLR.NoFaultRuleS.rec ↦ Kraken.Promising.X64.EnvG.NoFaultRuleSX.rec,
  Kraken.Promising.SLR.NoFaultRuleS.recOn ↦ Kraken.Promising.X64.EnvG.NoFaultRuleSX.recOn,
  Kraken.Promising.SLR.NoFaultRuleS.casesOn ↦ Kraken.Promising.X64.EnvG.NoFaultRuleSX.casesOn,
  Kraken.Promising.SLR.NoFaultRuleS.noFault ↦ Kraken.Promising.X64.EnvG.NoFaultRuleSX.noFault,
  Kraken.Promising.SLR.NoFaultRuleS.ofNoFault ↦ Kraken.Promising.X64.EnvG.NoFaultRuleSX.ofNoFault]

/-! ## The link -/

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout} {e : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateX → Prop}

/-- **The link hypotheses at `QX64T`** (`linkHypsT_QA64T`, x64): the x64 run
lemma at `E := EnvGT`. -/
theorem linkHypsT_QX64T (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeX A e)
    (hpost : ∀ y, post y → y.1.2 = endPc) : LinkHypsT (I := isa) A tid pl (QX64T A tid pl S e endPc post) where
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
/-- **`done` at `QX64T`** (`post_of_halted_QX64`, for `EnvGTX`). -/
theorem post_of_halted_QX64T (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTX A tid pl S) x R)
    {t : Thread isa} {σ : EStateX} (hQ : QX64T A tid pl S e endPc post t.st σ) (hh : t.halted = true) :
    post (t.st.st, σ) := by
  obtain ⟨he, -, hend, -, hsafe⟩ := hQ
  exact post_of_halted_env hstuck he hend hsafe hh

/-- **`ThreadRuleRXGS.ofSafelyEnvGTX`**: the x64 rule link with taking loads
(hypotheses as `ThreadRuleRX.ofSafelyEnvGX`, for `EnvGTX`). A thread whose
code has phase-1 trees, proved by a `Safely` judgment of `EnvGTX A tid pl S`
(`Le16 S`) with postcondition `post` only at `endPc` (and no step there),
satisfies `ThreadRuleRXGS G₀ A B tid` for every `B` that `post` gives at a
halted thread with no promise. No `rmwLive` check (every x64 tree is live). -/
def _root_.Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTX
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeX A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGS G₀ A B tid :=
  ThreadRuleRXGS.ofEnvGT (linkHypsT_QX64T (tid := tid) hpl hS hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QX64T hstuck hQ hh) hp hrel hcl

/-- **`NPSafeP` (frame `K2Scope AllocIds`) from a `Safely` judgment of
`EnvGTX`** (`NPSafeP.of_ruleRXGS` at `ofSafelyEnvGTX`). -/
theorem npSafeP_of_safelyEnvGTX {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeX A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvG (I := isa) A tid pl (QX64T A tid pl S e endPc post) cl c r g) :
    NPSafeP (model isa) A B tid G₀ (K2Scope (model isa) AllocIds) n m cl c r g :=
  NPSafeP.of_ruleRXGS (ThreadRuleRXGS.ofSafelyEnvGTX hpl hS hshape hpost hstuck hB) n m cl c r g h

/-- **Every tree from a `QX64T`-state is fault-free**, for fault-free code
(`noFault_QX64`, for `EnvGTX`). -/
theorem noFault_QX64T (hnf : DirsNoFault e) (hpost : ∀ y, post y → y.1.2 = endPc) :
    ∀ st σ tree, QX64T A tid pl S e endPc post st σ → isa.exec st = some tree → tree.NoFault := by
  intro st σ tree h hex
  obtain ⟨he, hds, hend, -, hsafe⟩ := h
  rcases hsafe.unfold with hp | -
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · exact noFault_of_exec he hds hnf tree hex

/-- **The x64 no-fault rule with taking loads**, unconditional in the
thread's promises: `NoFaultRuleSX (ofSafelyEnvGTX …)` for fault-free code
(`noFaultRule_ofSafelyEnvGT_struct`, x64). -/
theorem noFaultRule_ofSafelyEnvGTX_struct {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeX A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRuleSX (ThreadRuleRXGS.ofSafelyEnvGTX hpl hS hshape hpost hstuck hB) :=
  NoFaultRuleSX.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp => by
    obtain ⟨σ, hQ⟩ := InvG.q_at rF t h he hg ht E hnp
    exact noFault_QX64T hnf hpost t.st σ tree hQ hex

end Link

/-! ## The start -/

section Start

variable {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout}

/-- **`QX64T` from a partial triple** in `EnvGTX` at a thread state at the
start of `p` with a split private memory, whose exceptional exit `E` never
holds (`qx64_of_partialTripleEnv`, for `EnvGTX`). -/
theorem qx64T_of_partialTripleEnv [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Kraken.Executable.ValidLayout (layout p)] {P Q : MachineData → EStateX → Prop}
    {E : Int64 → MachineData → EStateX → Prop} (ht : MachineWP.PartialTripleEnv (EnvGTX A tid pl S) P p Q E)
    (henv : cenv = layout p) {st : State} (he : st.exe = layout p) (hds : st.decls = {})
    (hend : st.endPc = (layout p).addrOf p.length) (hpc : st.st.2 = (layout p).addrOf 0)
    (hs : Split S st.st.1.dmem) {σ : EStateX}
    (hP : P st.st.1 σ) (hE : ∀ a s g, ¬ E a s g := by simp) :
    QX64T A tid pl S (layout p) ((layout p).addrOf p.length) (postOfX p Q) st σ := by
  refine ⟨he, hds, hend, hs, ?_⟩
  have hst : st.st = (st.st.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hpc, Executable.addrOf_zero, Layout.apply_fst]
  rw [hst]
  exact (Program.instrStepEnv_of_partialTripleEnv ht hP henv).mono fun _ h => h.imp id (hE _ _ _)

/-- **The rule's invariant at the initial configuration** from `QX64T` at
`σInitX` (`invGX_init`, for `EnvGTX`; the core `coreAtX_init` is shared). -/
theorem invGTX_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = []) {e : Kraken.Executable Directive} {endPc : Int64}
    {post : MachineState × EStateX → Prop}
    (hQ : QX64T A tid pl S e endPc post s (σInitX (Config.init ss m) r g)) :
    InvG (I := isa) A tid pl (QX64T A tid pl S e endPc post) True (Config.init ss m) r g :=
  ⟨_, _, coreAtX_init hs hpend, hQ⟩

end Start

end Kraken.Promising.X64.EnvG

#print axioms Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTX
#print axioms Kraken.Promising.X64.EnvG.npSafeP_of_safelyEnvGTX
#print axioms Kraken.Promising.X64.EnvG.noFaultRule_ofSafelyEnvGTX_struct
#print axioms Kraken.Promising.X64.EnvG.invGTX_init
