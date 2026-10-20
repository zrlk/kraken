/-
The x64 `cmpxchg` lock proof, part 1: **the x64 link with failing in-flight release RMWs**
`ThreadRuleRXF.ofSafelyEnvGFX`, beside `ThreadRuleRX.ofSafelyEnvGRX`
(`EnvG/X64Link.lean`) and the AArch64 `ThreadRuleRXF.ofSafelyEnvGF`
(`EnvG/A64RmwFail.lean`). Copies of `A64RmwFail`'s shape check,
link and initial state at x64 types, under `EnvGX A tid pl S` (`Le16 S`) and
`QX64R`, through the ISA-neutral `F` rule link (`EnvG/RmwFailRuleLink.lean`).

Under `Arch.tso` every x64 RMW is release-kind; the `R` link
(`ofSafelyEnvGRX`) rejects `lock cmpxchg` because an in-flight release RMW
must never fail (`Phase1ShapeR`). Here the shape is `Phase1ShapeF` (no
totality), so `lock cmpxchg` is accepted (`dirs_phase1FX`).

The rule gives `NPSafeF`, which is Theorem 1′'s per-thread hypothesis only
once the open `Theorem1FChain` (`EnvG/RmwFailRule.lean`) is proved. No-fault:
`noFaultRuleF_ofSafelyEnvGFX_struct` (`NoFaultRuleF`, the structural argument
of `noFaultRule_ofSafelyEnvGRX_struct`).

`.toF` lemmas (`Phase1TreeRX.toF`, `DirsPhase1RX.toF`) let `R` shape proofs
feed the `F` link. Other phase-1 limits apply (single-access trees,
read-side acquire only, planned-release RMWs claim nothing given away).
-/
import Kraken.Promising.SLR.EnvG.X64Link
import Kraken.Promising.SLR.EnvG.RmwFailRuleLink
import Kraken.Promising.SLR.EnvG.Alias

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## The phase-1 shape with failing release RMWs, x64 -/

/-- **The phase-1 shape of x64 code with failing release RMWs**
(`A64RmwFail.Phase1TreeF`, x64). -/
def Phase1TreeFX (e : Kraken.Executable Directive) : Prop :=
  ∀ st : State, st.exe = e → st.decls = {} → ∀ tree, isa.exec st = some tree → Phase1ShapeF tree

/-- `R` phase-1 code is phase-1 code with failing release RMWs. -/
theorem Phase1TreeRX.toF {A : Arch} {e : Kraken.Executable Directive} (h : Phase1TreeRX A e) : Phase1TreeFX e :=
  fun st he hds tree hex => (h st he hds tree hex).toF

-- `phase1ShapeF_map`: the alias of the ISA-neutral original (`EnvG/RmwFailRuleLink.lean`)
hoist_alias [Kraken.Promising.AArch64.EnvG.phase1ShapeF_map ↦ Kraken.Promising.X64.EnvG.phase1ShapeF_map]

/-- The adapter's tree of the directive `d` of size `z` is phase-1 with
failing release RMWs, from every machine state and pc. -/
def DirPhase1FX (e : _root_.Executable) (d : Directive) (z : Nat) : Prop :=
  ∀ (s : MachineData) (pc : Int64),
    Phase1ShapeF (toEv {} (@Directive.interp (_root_.Executable.labels e) d s (.mk pc (pc + .ofNat z))
      (fun s' => .done (s', pc + .ofNat z)) (fun pc' s' => .done (s', pc'))))

/-- Every directive of the text has a phase-1 tree with failing release RMWs. -/
def DirsPhase1FX (e : _root_.Executable) : Prop := ∀ d z, (d, z) ∈ e.2 → DirPhase1FX e d z

/-- **`Phase1TreeFX` from the per-directive check.** -/
theorem phase1TreeFX_of_dirs {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
    (h : DirsPhase1FX e) : Phase1TreeFX e :=
  fun _ he hds _ htree => tree_of_codeAt (Φ := Phase1ShapeF) (fun f _ ht => phase1ShapeF_map f ht)
    (fun d z hm => h d z hm) he hds htree

/-- `R` per-directive phase-1 code is `F` per-directive phase-1 code. -/
theorem DirsPhase1RX.toF {A : Arch} {e : _root_.Executable} (h : DirsPhase1RX A e) : DirsPhase1FX e :=
  fun d z hm s pc => (h d z hm s pc).toF

theorem dirsPhase1FX_layout [layout : _root_.Layout] {p : Program}
    (h : ∀ d ∈ p, ∀ (e : _root_.Executable) z, DirPhase1FX e d z) : DirsPhase1FX (layout p) := by
  intro d z hm
  obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact h _ (List.getElem_mem hi) _ _

set_option hygiene false in
/-- `dirs_phase1FX p` proves `DirsPhase1FX (layout p)` for an x64 program
`p` (a definition) whose instructions make at most one access,
deterministically (RMWs of any kind and operation, `lock cmpxchg`
included): one `simp` per directive, as `dirs_phase1RX`. -/
macro "dirs_phase1FX " p:ident : tactic => `(tactic| (
  refine Kraken.Promising.X64.EnvG.dirsPhase1FX_layout (p := $p) ?_
  intro d hd e z s pc
  simp only [$p:ident, List.mem_cons, List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals simp [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    Kraken.Promising.X64.toEv, Kraken.Promising.SLR.EnvG.Phase1ShapeF, Kraken.Promising.SLR.EnvG.DetAccess,
    Kraken.Promising.SLR.EnvG.SingleAccessS2, Kraken.Promising.SLR.EnvG.AccessFree,
    _root_.MachineData.load, _root_.MachineData.store,
    _root_.MachineData.rmwK, _root_.RegOrMem.interp, _root_.Operand.interp, _root_.MachineData.set,
    _root_.RegOrMem.rmw, Kraken.Promising.EvTree.access_empty]
  all_goals (repeat' (first | split |
    simp [Kraken.Promising.X64.toEv, Kraken.Promising.SLR.EnvG.Phase1ShapeF,
      Kraken.Promising.SLR.EnvG.DetAccess, Kraken.Promising.SLR.EnvG.SingleAccessS2,
      Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty]))))

/-! ## The link -/

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout} {e : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateX → Prop} {rel₀ : Loc → Pred}

/-- **The link hypotheses with failing release RMWs at `QX64R`**
(`linkHypsF_QA64`, x64). -/
theorem linkHypsF_QX64 (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeFX e)
    (hG : RelRmwGiveOk isa pl rel₀) (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsF (I := isa) A tid pl (QX64R A tid pl S e endPc post rel₀) where
  valid := hpl
  shape st _ h tree hex := hshape st h.1.1 h.1.2.1 tree hex
  giveOk _ _ h := h.2 ▸ hG
  link := link_relFix rel₀ (link_QX64 hS hpost)

/-- **`ThreadRuleRXF.ofSafelyEnvGFX`**: the x64 rule link with failing
release RMWs (`ofSafelyEnvGRX` with `Phase1TreeFX`: `lock cmpxchg` admitted).
Gives `ThreadRuleRXF`, hence `NPSafeF`; Theorem 1′ for it is the open
`Theorem1FChain`. -/
def _root_.Kraken.Promising.SLR.EnvG.ThreadRuleRXF.ofSafelyEnvGFX
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeFX e) (hG : RelRmwGiveOk isa pl rel₀)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXF A B tid :=
  ThreadRuleRXF.ofEnvGF (linkHypsF_QX64 (tid := tid) hpl hS hshape hG hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QX64 hstuck hQ.1 hh) hp hrel hcl

/-- **`NPSafeF` from a `Safely` judgment of `EnvGX` with failing release
RMWs** (`NPSafeF.of_ruleRXF` at `ofSafelyEnvGFX`). -/
theorem npSafeF_of_safelyEnvGFX {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeFX e) (hG : RelRmwGiveOk isa pl rel₀)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvGF (I := isa) tid pl (QX64R A tid pl S e endPc post rel₀) cl c r g) :
    NPSafeF (model isa) A B tid n m cl c r g :=
  NPSafeF.of_ruleRXF (ThreadRuleRXF.ofSafelyEnvGFX hpl hS hshape hG hpost hstuck hB) n m cl c r g h

/-- **The x64 no-fault rule for the `F` link** from fault-free code
(`DirsNoFault e`), as `noFaultRule_ofSafelyEnvGRX_struct`. -/
theorem noFaultRuleF_ofSafelyEnvGFX_struct {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeFX e) (hG : RelRmwGiveOk isa pl rel₀)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRuleF (ThreadRuleRXF.ofSafelyEnvGFX hpl hS hshape hG hpost hstuck hB) :=
  noFaultRuleF_ofEnvGF_struct _ _ fun st σ tree hQ hex => noFault_QX64 hnf hpost st σ tree hQ.1 hex

end Link

/-! ## The initial state -/

section Init

variable {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout}

/-- **The invariant core with failing release RMWs at the initial
configuration** (`coreAtF_init`, x64). -/
theorem coreAtFX_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = []) :
    CoreAtF tid pl True (Config.init ss m) r g (σInitX (Config.init ss m) r g) (Thread.init s) := by
  have ht : (Config.init ss m : Config isa).threads[tid]? = some (Thread.init s) := by simp [Config.init, hs]
  refine ⟨⟨ht, SnapLe.refl _ _, Ghost.Le.refl g, ?_, Config.init_bnd ss m tid _ ht,
    .inl ⟨rfl, fun _ h => (by cases h)⟩, fun _ => trivial, ⟨fun h => (by cases h), fun h => (by cases h)⟩⟩,
    fun ts h => (by rw [hpend] at h; cases h), fun ts _ _ h => (by cases h)⟩
  refine ⟨fun l => by simp [σInitX, Thread.init, Views.getCoh], Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
    Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, fun l => ?_, ?_⟩ <;>
    simp [σInitX, Thread.init, Views.getFwd, Sim.FwdLe, Sim.XclLe]

/-- **The rule's invariant with failing release RMWs at the initial
configuration** from `QX64` at `σInitX` (`invGF_init`, x64; the release
predicates are the ghost's). -/
theorem invGFX_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = []) {e : Kraken.Executable Directive} {endPc : Int64}
    {post : MachineState × EStateX → Prop} (hQ : QX64 A tid pl S e endPc post s (σInitX (Config.init ss m) r g)) :
    InvGF (I := isa) tid pl (QX64R A tid pl S e endPc post g.rel) True (Config.init ss m) r g :=
  ⟨σInitX (Config.init ss m) r g, Thread.init s, coreAtFX_init hs hpend, hQ, rfl⟩

end Init

end Kraken.Promising.X64.EnvG
