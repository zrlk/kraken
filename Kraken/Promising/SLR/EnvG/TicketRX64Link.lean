/-
**Item 3 (b): the x64 ticket link with a
release-kind ticket RMW** (`lock xadd`), `ThreadRuleRXGSXE.ofSafelyEnvGTDRX`:
`EnvG/TicketRA64Link.lean` for x64, built as `EnvG/TakeX64Link.lean` builds
`ofSafelyEnvGTX` (all unchanged).

A thread is proved in **`EnvGTDRX A tid pl D S := (EnvGTDR isa A tid pl D).within S`**:
`EnvGTDR` (`EnvG/TicketREnv.lean`; every x64 `lock` RMW is release-kind, so
the x64 ticket RMW needs `EnvGTDR`, not `EnvGTD`) with every access
restricted to a location of the shared layout `S`. `within` changes only
`ok`, so the x64 run lemma `exec_treeJLive_of_instrStepEnvW` at
`E := EnvGTDR isa A tid pl D` gives the `link` field of `LinkHypsTDR`.

- `EnvGTDRX`, `QX64TDR`; `linkHypsTDR_QX64TDR` (`Phase1TreeRX`),
  `post_of_halted_QX64TDR`.
- **`ThreadRuleRXGSXE.ofSafelyEnvGTDRX : ThreadRuleRXGSXE G₀ D.TX`**,
  **`npSafeP_of_safelyEnvGTDRX`** (frame `K2Scope (model isa) AllocIds`, the
  per-thread input of `theorem1IIPureX_G₀_S`).
- No fault: `noFault_QX64TDR`, **`noFaultRule_ofSafelyEnvGTDRX_struct`**.
- Start: `qx64TDR_of_partialTripleEnv`, **`invGTDRX_init`** (`coreAtRX_init`).
- Smoke: `xaddTake`, the ticket take of `X64/ticketlock2.kl` (`movl $1`;
  `lock xaddl`), is `Phase1TreeRX` (`xaddTake_phase1R`, by `dirs_phase1RX`)
  and fault-free (`xaddTake_noFault`).

Phase-1 limits: as `ofSafelyEnvGTX` (single-access trees: an unlocked
`incl (owner)` release is a load+store tree and is *not* covered; `Le16 S`)
and `EnvGTDR`'s (the plan never releases at the ticket counter).
-/
import Kraken.Promising.SLR.EnvG.TicketRRuleLink
import Kraken.Promising.SLR.EnvG.TakeX64Link
import Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## The environment and the invariant -/

/-- **`EnvGTDR` for x64**, restricted to the shared layout `S`. -/
abbrev EnvGTDRX (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser) (S : SharedEnv.Layout) : SharedEnv :=
  (Kraken.Promising.SLR.EnvGTDR isa A tid pl D).within S

/-- **The thread-local invariant of the x64 ticket environment with a
release-kind ticket RMW** (`QX64T` for `EnvGTDRX`). -/
def QX64TDR (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser) (S : SharedEnv.Layout)
    (e : Kraken.Executable Directive) (endPc : Int64) (post : MachineState × EStateX → Prop) (st : State)
    (σ : EStateX) : Prop :=
  st.exe = e ∧ st.decls = {} ∧ st.endPc = endPc ∧ Split S st.st.1.dmem ∧
    Safely (e.instrStepEnv (EnvGTDRX A tid pl D S)) post (st.st, σ)

/-! ## The link -/

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {D : Dispenser} {S : SharedEnv.Layout}
  {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {endPc : Int64}
  {post : MachineState × EStateX → Prop}

/-- **The link hypotheses at `QX64TDR`** (`linkHypsT_QX64T` for `EnvGTDR`,
with `Phase1TreeRX`). -/
theorem linkHypsTDR_QX64TDR (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeRX A e)
    (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsTDR (I := isa) A tid pl D (QX64TDR A tid pl D S e endPc post) where
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
/-- **`done` at `QX64TDR`**. -/
theorem post_of_halted_QX64TDR (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTDRX A tid pl D S) x R)
    {t : Thread isa} {σ : EStateX} (hQ : QX64TDR A tid pl D S e endPc post t.st σ) (hh : t.halted = true) :
    post (t.st.st, σ) := by
  obtain ⟨he, -, hend, -, hsafe⟩ := hQ
  exact post_of_halted_env hstuck he hend hsafe hh

/-- **`ThreadRuleRXGSXE.ofSafelyEnvGTDRX`**: the x64 ticket rule link with a
release-kind ticket RMW (`lock xadd`). No `rmwLive` check (every x64 tree is
live). -/
def _root_.Kraken.Promising.SLR.ThreadRuleRXGSXE.ofSafelyEnvGTDRX
    {B : Config isa → (modelX isa D.TX).R → (modelX isa D.TX).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeRX A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTDRX A tid pl D S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGSXE G₀ D.TX A B tid :=
  ThreadRuleRXGSXE.ofEnvGTDR (linkHypsTDR_QX64TDR (tid := tid) hpl hS hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QX64TDR hstuck hQ hh) hp hrel hcl

/-- **`NPSafeP` over `Erase ∧ TX` (frame `K2Scope AllocIds`) from a `Safely`
judgment of `EnvGTDRX`** (`NPSafeP.of_ruleRXGSXE` at `ofSafelyEnvGTDRX`). -/
theorem npSafeP_of_safelyEnvGTDRX {B : Config isa → (modelX isa D.TX).R → (modelX isa D.TX).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeRX A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTDRX A tid pl D S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvGTDR (I := isa) tid pl D (QX64TDR A tid pl D S e endPc post) cl c r g) :
    NPSafeP (modelX isa D.TX) A B tid G₀ (K2Scope (model isa) AllocIds) n m cl c r g :=
  NPSafeP.of_ruleRXGSXE (ThreadRuleRXGSXE.ofSafelyEnvGTDRX hpl hS hshape hpost hstuck hB) n m cl c r g h

/-- **Every tree from a `QX64TDR`-state is fault-free**, for fault-free code. -/
theorem noFault_QX64TDR (hnf : DirsNoFault e) (hpost : ∀ y, post y → y.1.2 = endPc) :
    ∀ st σ tree, QX64TDR A tid pl D S e endPc post st σ → isa.exec st = some tree → tree.NoFault := by
  intro st σ tree h hex
  obtain ⟨he, hds, hend, -, hsafe⟩ := h
  rcases hsafe.unfold with hp | -
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · exact noFault_of_exec he hds hnf tree hex

/-- **The x64 ticket no-fault rule with a release-kind ticket RMW**,
unconditional in the thread's promises. -/
theorem noFaultRule_ofSafelyEnvGTDRX_struct
    {B : Config isa → (modelX isa D.TX).R → (modelX isa D.TX).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeRX A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGTDRX A tid pl D S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRuleSXE (ThreadRuleRXGSXE.ofSafelyEnvGTDRX hpl hS hshape hpost hstuck hB) :=
  NoFaultRuleSXE.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp => by
    obtain ⟨σ, hQ⟩ := InvGTDR.q_at rF t h he hg ht E hnp
    exact noFault_QX64TDR hnf hpost t.st σ tree hQ hex

end Link

/-! ## The start -/

section Start

variable {A : Arch} {tid : Nat} {pl : Plan} {D : Dispenser} {S : SharedEnv.Layout}

/-- **`QX64TDR` from a partial triple** in `EnvGTDRX` at a thread state at the
start of `p` with a split private memory, whose exceptional exit `E` never
holds. -/
theorem qx64TDR_of_partialTripleEnv [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Kraken.Executable.ValidLayout (layout p)] {P Q : MachineData → EStateX → Prop}
    {E : Int64 → MachineData → EStateX → Prop} (ht : MachineWP.PartialTripleEnv (EnvGTDRX A tid pl D S) P p Q E)
    (henv : cenv = layout p) {st : State} (he : st.exe = layout p) (hds : st.decls = {})
    (hend : st.endPc = (layout p).addrOf p.length) (hpc : st.st.2 = (layout p).addrOf 0)
    (hs : Split S st.st.1.dmem) {σ : EStateX}
    (hP : P st.st.1 σ) (hE : ∀ a s g, ¬ E a s g := by simp) :
    QX64TDR A tid pl D S (layout p) ((layout p).addrOf p.length) (postOfX p Q) st σ := by
  refine ⟨he, hds, hend, hs, ?_⟩
  have hst : st.st = (st.st.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hpc, Executable.addrOf_zero, Layout.apply_fst]
  rw [hst]
  exact (Program.instrStepEnv_of_partialTripleEnv ht hP henv).mono fun _ h => h.imp id (hE _ _ _)

/-- **The rule's invariant at the initial configuration** from `QX64TDR` at
`σInitX` (`coreAtRX_init`; the initial views are `0`). -/
theorem invGTDRX_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = []) {e : Kraken.Executable Directive} {endPc : Int64}
    {post : MachineState × EStateX → Prop}
    (hQ : QX64TDR A tid pl D S e endPc post s (σInitX (Config.init ss m) r g)) :
    InvGTDR (I := isa) tid pl D (QX64TDR A tid pl D S e endPc post) True (Config.init ss m) r g :=
  ⟨_, _, coreAtRX_init hs hpend, hQ, fun _ => by simp [Thread.init, Views.getCoh]⟩

end Start

/-! ## Smoke: the ticket take of `X64/ticketlock2.kl` -/

section Smoke

open Kraken.X64.Parser

/-- The ticket take of `X64/ticketlock2.kl`'s worker, with `(next)` as
`(%rdi)`. -/
def xaddTake : Program := parse("
worker:
  movl $1,%eax
  lock xaddl %eax,(%rdi)
  jmp done
done:
")

/-- info: 5 -/
#guard_msgs in
#eval xaddTake.length

variable [layout : _root_.Layout]

/-- The `lock xaddl` is a release-kind RMW that never fails: phase-1 with
release-kind RMWs (the shape `ofSafelyEnvGTDRX` needs). -/
theorem xaddTake_phase1R [Executable.ValidLayout (layout xaddTake)] : Phase1TreeRX Arch.tso (layout xaddTake) :=
  phase1TreeRX_of_dirs (by dirs_phase1RX xaddTake)

theorem xaddTake_noFault : DirsNoFault (layout xaddTake) := by
  dirs_no_fault xaddTake
  all_goals simp [_root_.RelRegOrMem.interp, Kraken.Promising.X64.toEv, EvTree.NoFault]

end Smoke

end Kraken.Promising.X64.EnvG

#print axioms Kraken.Promising.SLR.ThreadRuleRXGSXE.ofSafelyEnvGTDRX
#print axioms Kraken.Promising.X64.EnvG.npSafeP_of_safelyEnvGTDRX
#print axioms Kraken.Promising.X64.EnvG.noFaultRule_ofSafelyEnvGTDRX_struct
#print axioms Kraken.Promising.X64.EnvG.invGTDRX_init
#print axioms Kraken.Promising.X64.EnvG.xaddTake_phase1R
