/-
**Part 1: the x64 links of the
claim-conditional environments** `EnvGC` (`EnvG/RmwGhost.lean`) and
`EnvGTC` (`EnvG/RmwGhostTake.lean`): `ThreadRuleRX.ofSafelyEnvGRCX` and
`ThreadRuleRXGS.ofSafelyEnvGTRCX`, the x64 counterparts of the claim-conditional extension's
`ofSafelyEnvGRC` (`EnvG/RmwGhostA64.lean`) and `ofSafelyEnvGTRC`
(`EnvG/RmwGhostTake.lean`), built as `ofSafelyEnvGRX` (`EnvG/X64Link.lean`)
and `ofSafelyEnvGTX` (`EnvG/TakeX64Link.lean`) are built.

## The environments

- **`EnvGCX A tid pl S := (EnvGC isa A tid pl).within S`**, invariant
  `QX64C` (`QX64` with `EnvGCX`).
- **`EnvGTCX A tid pl S := (EnvGTCI isa A tid pl).within S`**, invariant
  `QX64TC`. `EnvGTCI` is the claim-conditional extension's `EnvGTC` (state, permissions and
  store/RMW/fence steps of `EnvGC`, the taking load step `LoadOutT`). It and
  `nodeSimT2_envGTCI`, `treeJ_envGTCI_eraseWPRDSR_start`,
  `TreeJLive.storeOkTCI`/`rmwOkTCI`, `LinkHypsTRCI`, `InvGR.wpTRCI`,
  `InvGR.prepayTRCI`, `ThreadRuleRXGS.ofEnvGTRCI` were verbatim copies of the
  ISA-neutral half of `EnvG/RmwGhostTake.lean`; that half is
  `EnvG/RmwGhostTakeCore.lean` and these names are statement-preserving
  aliases (`hoist_alias`) of its originals.

`within` changes only `ok`, so the RMW facts (`rmwOutC_facts`), the take facts
and the x64 run lemma `exec_treeJLive_of_instrStepEnvW` (generic in the
environment) apply unchanged, as in `TakeX64Link.lean`.

## x64 RMWs always claim

Every RMW event the x64 adapter emits has kind `.acqRel`: `RegOrMem.rmw`
(`xchg`, `lock xadd`, `lock cmpxchg`, `lock` arithmetic), the locked
`inc`/`dec`/`neg`/`not` forms and `lock cmpxchg16b` all call
`MachineData.rmwK .acqRel` / `rmw16K .acqRel` (`X64/Semantics.lean`); an
unlocked memory-destination RMW is a load and a store, not an RMW event. And
`Arch.tso` maps a `.plain` RMW to `.acqRel` too. `ClaimOk A k vs l tr` is
`A.rmwKind k = .acqRel ∨ (acquire ∧ not forwarded)`, so for these kinds it
holds **unconditionally** (`claimOk_acqRel`, `claimOk_tso_plain`): no view,
forwarding or ghost condition enters. Hence on x64 `claimSlotsC = claimedSlots`
(`claimSlotsC_acqRel`, `claimSlotsC_tso_plain`): `EnvGC` claims exactly what
`EnvG` claims, and on x64 the claim-conditional extension's change reduces to the give-from-own (GO)
half: a release RMW gives from `σ.r` and keeps the claimed slots, so there is
no `RelRmwGiveOk` and no `Plan.Whole` on RMW releases (as against
`ofSafelyEnvGRX`).

## Contents

- Claims: `claimOk_acqRel`, `claimOk_tso_plain`, `claimSlotsC_acqRel`,
  `claimSlotsC_tso_plain` (`@[simp]`).
- `EnvGC`: `noFaultRule_ofEnvGRC_structX` (alias of the claim-conditional extension's ISA-neutral
  `noFaultRule_ofEnvGRC_struct`, `EnvG/LinkRNoFault.lean`),
  `EnvGCX`, `QX64C`, `linkHypsRC_QX64C`, `post_of_halted_QX64C`,
  **`ThreadRuleRX.ofSafelyEnvGRCX`**, `npSafe_of_safelyEnvGRCX`,
  `noFaultRule_ofSafelyEnvGRCX_struct`, `qx64C_of_partialTripleEnv`,
  `invGRCX_init`.
- `EnvGTC`: the aliases above, `EnvGTCX`, `QX64TC`, `linkHypsTRC_QX64TC`,
  `post_of_halted_QX64TC`, **`ThreadRuleRXGS.ofSafelyEnvGTRCX`**,
  `npSafeP_of_safelyEnvGTRCX` (frame `K2Scope AllocIds`),
  `noFaultRule_ofSafelyEnvGTRCX_struct` (`NoFaultRuleSX`, unconditional in
  promises), `qx64TC_of_partialTripleEnv`, `invGTRCX_init`.

Phase-1 limits: as `ofSafelyEnvGRX` (single-access trees, `Phase1TreeRX`, an
in-flight release RMW never fails, so no `lock cmpxchg` release; `Le16 S`),
plus, for `EnvGTCX`, those of the take route (only non-forwarded acquire
loads take; no take at an RMW or fence node). A release RMW still cannot
forward what it claims in the same instruction.
-/
import Kraken.Promising.SLR.EnvG.RmwGhostRule
import Kraken.Promising.SLR.EnvG.TakeRLink
import Kraken.Promising.SLR.EnvG.TakeX64Link
import Kraken.Promising.SLR.EnvG.RmwGhostTakeCore
import Kraken.Promising.SLR.EnvG.LinkRNoFault
import Kraken.Promising.SLR.EnvG.Alias

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## x64 RMWs always claim -/

/-- An acquire-release RMW always meets the claim condition, under any
profile, at any views and read. -/
theorem claimOk_acqRel (A : Arch) (vs : Views) (l : Loc) (tr : Time) : ClaimOk A .acqRel vs l tr := .inl rfl

/-- Under `Arch.tso` a plain RMW is acquire-release, so it always meets the
claim condition. -/
theorem claimOk_tso_plain (vs : Views) (l : Loc) (tr : Time) : ClaimOk Arch.tso .plain vs l tr := .inl rfl

/-- **An acquire-release RMW claims all the update slots of its read**
(every x64 RMW event is one: `MachineData.rmwK .acqRel`). -/
@[simp] theorem claimSlotsC_acqRel (A : Arch) (vs : Views) (g : Ghost) (l : Loc) (tr : Time) :
    claimSlotsC A .acqRel vs g l tr = claimedSlots g l tr :=
  claimSlotsC_of_ok (claimOk_acqRel A vs l tr)

@[simp] theorem claimSlotsC_tso_plain (vs : Views) (g : Ghost) (l : Loc) (tr : Time) :
    claimSlotsC Arch.tso .plain vs g l tr = claimedSlots g l tr :=
  claimSlotsC_of_ok (claimOk_tso_plain vs l tr)

/-! ## The no-fault rule of `EnvGC` (statement-preserving alias of the
ISA-neutral `noFaultRule_ofEnvGRC_struct`, `EnvG/LinkRNoFault.lean`; formerly a
local copy) -/

hoist_alias [Kraken.Promising.SLR.EnvG.noFaultRule_ofEnvGRC_struct ↦ Kraken.Promising.X64.EnvG.noFaultRule_ofEnvGRC_structX]

/-! ## `EnvGTC`: statement-preserving aliases of the ISA-neutral originals in
`EnvG/RmwGhostTakeCore.lean` (formerly verbatim copies) -/

hoist_alias [Kraken.Promising.SLR.EnvGTC ↦ Kraken.Promising.X64.EnvG.EnvGTCI,
  Kraken.Promising.SLR.EnvG.nodeSimT2_envGTC ↦ Kraken.Promising.X64.EnvG.nodeSimT2_envGTCI,
  Kraken.Promising.SLR.EnvG.treeJ_envGTC_eraseWPRDSR_start ↦ Kraken.Promising.X64.EnvG.treeJ_envGTCI_eraseWPRDSR_start,
  Kraken.Promising.SLR.EnvG.TreeJLive.storeOkTC ↦ Kraken.Promising.X64.EnvG.TreeJLive.storeOkTCI,
  Kraken.Promising.SLR.EnvG.TreeJLive.rmwOkTC ↦ Kraken.Promising.X64.EnvG.TreeJLive.rmwOkTCI,
  Kraken.Promising.SLR.EnvG.LinkHypsTRC ↦ Kraken.Promising.X64.EnvG.LinkHypsTRCI,
  Kraken.Promising.SLR.EnvG.LinkHypsTRC.mk ↦ Kraken.Promising.X64.EnvG.LinkHypsTRCI.mk,
  Kraken.Promising.SLR.EnvG.LinkHypsTRC.valid ↦ Kraken.Promising.X64.EnvG.LinkHypsTRCI.valid,
  Kraken.Promising.SLR.EnvG.LinkHypsTRC.shape ↦ Kraken.Promising.X64.EnvG.LinkHypsTRCI.shape,
  Kraken.Promising.SLR.EnvG.LinkHypsTRC.link ↦ Kraken.Promising.X64.EnvG.LinkHypsTRCI.link,
  Kraken.Promising.SLR.EnvG.LinkHypsTRC.rec ↦ Kraken.Promising.X64.EnvG.LinkHypsTRCI.rec,
  Kraken.Promising.SLR.EnvG.LinkHypsTRC.recOn ↦ Kraken.Promising.X64.EnvG.LinkHypsTRCI.recOn,
  Kraken.Promising.SLR.EnvG.LinkHypsTRC.casesOn ↦ Kraken.Promising.X64.EnvG.LinkHypsTRCI.casesOn,
  Kraken.Promising.SLR.EnvG.InvGR.wpTRC ↦ Kraken.Promising.X64.EnvG.InvGR.wpTRCI,
  Kraken.Promising.SLR.EnvG.InvGR.prepayTRC ↦ Kraken.Promising.X64.EnvG.InvGR.prepayTRCI,
  Kraken.Promising.SLR.EnvG.ThreadRuleRXGS.ofEnvGTRC ↦ Kraken.Promising.X64.EnvG.ThreadRuleRXGS.ofEnvGTRCI]

/-! ## The x64 environments and invariants -/

/-- **`EnvGC` for x64**, restricted to the shared layout `S`. -/
abbrev EnvGCX (A : Arch) (tid : Nat) (pl : Plan) (S : SharedEnv.Layout) : SharedEnv :=
  (Kraken.Promising.SLR.EnvGC isa A tid pl).within S

/-- **`EnvGTC` for x64**, restricted to the shared layout `S`. -/
abbrev EnvGTCX (A : Arch) (tid : Nat) (pl : Plan) (S : SharedEnv.Layout) : SharedEnv :=
  (EnvGTCI isa A tid pl).within S

/-- **The thread-local invariant of `EnvGCX`** (`QX64` for `EnvGCX`). -/
def QX64C (A : Arch) (tid : Nat) (pl : Plan) (S : SharedEnv.Layout) (e : Kraken.Executable Directive)
    (endPc : Int64) (post : MachineState × EStateX → Prop) (st : State) (σ : EStateX) : Prop :=
  st.exe = e ∧ st.decls = {} ∧ st.endPc = endPc ∧ Split S st.st.1.dmem ∧
    Safely (e.instrStepEnv (EnvGCX A tid pl S)) post (st.st, σ)

/-- **The thread-local invariant of `EnvGTCX`** (`QX64` for `EnvGTCX`). -/
def QX64TC (A : Arch) (tid : Nat) (pl : Plan) (S : SharedEnv.Layout) (e : Kraken.Executable Directive)
    (endPc : Int64) (post : MachineState × EStateX → Prop) (st : State) (σ : EStateX) : Prop :=
  st.exe = e ∧ st.decls = {} ∧ st.endPc = endPc ∧ Split S st.st.1.dmem ∧
    Safely (e.instrStepEnv (EnvGTCX A tid pl S)) post (st.st, σ)

/-! ## The `EnvGC` link -/

section LinkC

variable {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout} {e : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateX → Prop}

/-- **The link hypotheses of `EnvGC` at `QX64C`** (`linkHypsRC_QA64C`, x64). -/
theorem linkHypsRC_QX64C (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeRX A e)
    (hpost : ∀ y, post y → y.1.2 = endPc) : LinkHypsRC (I := isa) A tid pl (QX64C A tid pl S e endPc post) where
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
/-- **`done` at `QX64C`**. -/
theorem post_of_halted_QX64C (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGCX A tid pl S) x R)
    {t : Thread isa} {σ : EStateX} (hQ : QX64C A tid pl S e endPc post t.st σ) (hh : t.halted = true) :
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

/-- **`ThreadRuleRX.ofSafelyEnvGRCX`**: the x64 rule link of `EnvGC`
(`ofSafelyEnvGRC`, x64; `ofSafelyEnvGRX` without `RelRmwGiveOk`, hence
without fixing the release predicates). On x64 every RMW claims
(`claimSlotsC_acqRel`); a release RMW gives from the thread's own resource. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvGRCX
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeRX A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGCX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRX A B tid :=
  ThreadRuleRX.ofEnvGRC (linkHypsRC_QX64C (tid := tid) hpl hS hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QX64C hstuck hQ hh) hp hrel hcl

/-- **`NPSafe` from a `Safely` judgment of `EnvGCX`**. -/
theorem npSafe_of_safelyEnvGRCX {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeRX A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGCX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvGR (I := isa) tid pl (QX64C A tid pl S e endPc post) cl c r g) :
    NPSafe (model isa) A B tid n m cl c r g :=
  NPSafe.of_ruleRX (ThreadRuleRX.ofSafelyEnvGRCX hpl hS hshape hpost hstuck hB) n m cl c r g h

/-- **Every tree from a `QX64C`-state is fault-free**, for fault-free code. -/
theorem noFault_QX64C (hnf : DirsNoFault e) (hpost : ∀ y, post y → y.1.2 = endPc) :
    ∀ st σ tree, QX64C A tid pl S e endPc post st σ → isa.exec st = some tree → tree.NoFault := by
  intro st σ tree h hex
  obtain ⟨he, hds, hend, -, hsafe⟩ := h
  rcases hsafe.unfold with hp | -
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · exact noFault_of_exec he hds hnf tree hex

/-- **The x64 no-fault rule of `EnvGC`**, unconditional in the thread's
promises, for fault-free code. -/
theorem noFaultRule_ofSafelyEnvGRCX_struct {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeRX A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGCX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRule (ThreadRuleRX.ofSafelyEnvGRCX hpl hS hshape hpost hstuck hB) :=
  noFaultRule_ofEnvGRC_structX _ _ (noFault_QX64C hnf hpost)

end LinkC

/-! ## The `EnvGTC` link -/

section LinkTC

variable {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout} {e : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateX → Prop}

/-- **The link hypotheses of `EnvGTC` at `QX64TC`** (`linkHypsTRC_QA64TC`,
x64). -/
theorem linkHypsTRC_QX64TC (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeRX A e)
    (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsTRCI (I := isa) A tid pl (QX64TC A tid pl S e endPc post) where
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
/-- **`done` at `QX64TC`**. -/
theorem post_of_halted_QX64TC (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTCX A tid pl S) x R)
    {t : Thread isa} {σ : EStateX} (hQ : QX64TC A tid pl S e endPc post t.st σ) (hh : t.halted = true) :
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

/-- **`ThreadRuleRXGS.ofSafelyEnvGTRCX`**: the x64 rule link with taking loads
and claim-conditional RMWs (`ofSafelyEnvGTRC`, x64). Every non-forwarded x64
load may take (it is an acquire under `Arch.tso`); every x64 RMW claims, and a
release RMW (`xchg`, `lock xadd`) gives from the thread's own resource: no
`RelRmwGiveOk`, no `Plan.Whole`. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTRCX
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeRX A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTCX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGS G₀ A B tid :=
  ThreadRuleRXGS.ofEnvGTRC (linkHypsTRC_QX64TC (tid := tid) hpl hS hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QX64TC hstuck hQ hh) hp hrel hcl

/-- **`NPSafeP` (frame `K2Scope AllocIds`) from a `Safely` judgment of
`EnvGTCX`**. -/
theorem npSafeP_of_safelyEnvGTRCX {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeRX A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTCX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvGR (I := isa) tid pl (QX64TC A tid pl S e endPc post) cl c r g) :
    NPSafeP (model isa) A B tid G₀ (K2Scope (model isa) AllocIds) n m cl c r g :=
  NPSafeP.of_ruleRXGS (ThreadRuleRXGS.ofSafelyEnvGTRCX hpl hS hshape hpost hstuck hB) n m cl c r g h

/-- **Every tree from a `QX64TC`-state is fault-free**, for fault-free code. -/
theorem noFault_QX64TC (hnf : DirsNoFault e) (hpost : ∀ y, post y → y.1.2 = endPc) :
    ∀ st σ tree, QX64TC A tid pl S e endPc post st σ → isa.exec st = some tree → tree.NoFault := by
  intro st σ tree h hex
  obtain ⟨he, hds, hend, -, hsafe⟩ := h
  rcases hsafe.unfold with hp | -
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · exact noFault_of_exec he hds hnf tree hex

/-- **The x64 no-fault rule of `EnvGTC`**, unconditional in the thread's
promises, for fault-free code (`noFaultRule_ofSafelyEnvGTRC_struct`, x64). -/
theorem noFaultRule_ofSafelyEnvGTRCX_struct {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeRX A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTCX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRuleSX (ThreadRuleRXGS.ofSafelyEnvGTRCX hpl hS hshape hpost hstuck hB) :=
  NoFaultRuleSX.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp => by
    obtain ⟨σ, hQ⟩ := InvGR.q_atX rF t h he hg ht E hnp
    exact noFault_QX64TC hnf hpost t.st σ tree hQ hex

end LinkTC

/-! ## The start -/

section Start

variable {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout}

/-- **`QX64C` from a partial triple** in `EnvGCX` (`qx64_of_partialTripleEnv`
for `EnvGCX`). -/
theorem qx64C_of_partialTripleEnv [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Kraken.Executable.ValidLayout (layout p)] {P Q : MachineData → EStateX → Prop}
    {E : Int64 → MachineData → EStateX → Prop} (ht : MachineWP.PartialTripleEnv (EnvGCX A tid pl S) P p Q E)
    (henv : cenv = layout p) {st : State} (he : st.exe = layout p) (hds : st.decls = {})
    (hend : st.endPc = (layout p).addrOf p.length) (hpc : st.st.2 = (layout p).addrOf 0)
    (hs : Split S st.st.1.dmem) {σ : EStateX}
    (hP : P st.st.1 σ) (hE : ∀ a s g, ¬ E a s g := by simp) :
    QX64C A tid pl S (layout p) ((layout p).addrOf p.length) (postOfX p Q) st σ := by
  refine ⟨he, hds, hend, hs, ?_⟩
  have hst : st.st = (st.st.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hpc, Executable.addrOf_zero, Layout.apply_fst]
  rw [hst]
  exact (Program.instrStepEnv_of_partialTripleEnv ht hP henv).mono fun _ h => h.imp id (hE _ _ _)

/-- **`QX64TC` from a partial triple** in `EnvGTCX`. -/
theorem qx64TC_of_partialTripleEnv [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Kraken.Executable.ValidLayout (layout p)] {P Q : MachineData → EStateX → Prop}
    {E : Int64 → MachineData → EStateX → Prop} (ht : MachineWP.PartialTripleEnv (EnvGTCX A tid pl S) P p Q E)
    (henv : cenv = layout p) {st : State} (he : st.exe = layout p) (hds : st.decls = {})
    (hend : st.endPc = (layout p).addrOf p.length) (hpc : st.st.2 = (layout p).addrOf 0)
    (hs : Split S st.st.1.dmem) {σ : EStateX}
    (hP : P st.st.1 σ) (hE : ∀ a s g, ¬ E a s g := by simp) :
    QX64TC A tid pl S (layout p) ((layout p).addrOf p.length) (postOfX p Q) st σ := by
  refine ⟨he, hds, hend, hs, ?_⟩
  have hst : st.st = (st.st.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hpc, Executable.addrOf_zero, Layout.apply_fst]
  rw [hst]
  exact (Program.instrStepEnv_of_partialTripleEnv ht hP henv).mono fun _ h => h.imp id (hE _ _ _)

/-- **The rule's invariant of `EnvGCX` at the initial configuration**, from
`QX64C` at `σInitX` (no release predicates to fix: `invGRC_init`, x64). -/
theorem invGRCX_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = []) {e : Kraken.Executable Directive} {endPc : Int64}
    {post : MachineState × EStateX → Prop} (hQ : QX64C A tid pl S e endPc post s (σInitX (Config.init ss m) r g)) :
    InvGR (I := isa) tid pl (QX64C A tid pl S e endPc post) True (Config.init ss m) r g :=
  ⟨σInitX (Config.init ss m) r g, Thread.init s, coreAtRX_init hs hpend, hQ⟩

/-- **The rule's invariant of `EnvGTCX` at the initial configuration**, from
`QX64TC` at `σInitX`. -/
theorem invGTRCX_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = []) {e : Kraken.Executable Directive} {endPc : Int64}
    {post : MachineState × EStateX → Prop}
    (hQ : QX64TC A tid pl S e endPc post s (σInitX (Config.init ss m) r g)) :
    InvGR (I := isa) tid pl (QX64TC A tid pl S e endPc post) True (Config.init ss m) r g :=
  ⟨σInitX (Config.init ss m) r g, Thread.init s, coreAtRX_init hs hpend, hQ⟩

end Start

end Kraken.Promising.X64.EnvG

#print axioms Kraken.Promising.X64.EnvG.claimSlotsC_acqRel
#print axioms Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvGRCX
#print axioms Kraken.Promising.X64.EnvG.npSafe_of_safelyEnvGRCX
#print axioms Kraken.Promising.X64.EnvG.noFaultRule_ofSafelyEnvGRCX_struct
#print axioms Kraken.Promising.X64.EnvG.invGRCX_init
#print axioms Kraken.Promising.SLR.ThreadRuleRXGS.ofSafelyEnvGTRCX
#print axioms Kraken.Promising.X64.EnvG.npSafeP_of_safelyEnvGTRCX
#print axioms Kraken.Promising.X64.EnvG.noFaultRule_ofSafelyEnvGTRCX_struct
#print axioms Kraken.Promising.X64.EnvG.invGTRCX_init
