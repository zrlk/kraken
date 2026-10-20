/-
Whole-thread environment (`EnvG`), phase 2: **the x64 link for code
with load-prefix trees** (`MultiA64.lean` at x64 types, `X64Link.lean`'s
`EnvGX`/`QX64`).

On x64 the phase-2 trees are the non-atomic vector loads read in pieces
(`movups`/`movdqu`/`vmovdqu` from memory: two or more 8-byte TSO loads).
Under `Arch.tso` every x64 store and RMW is release-kind, so `Phase2Shape`'s
`NoRelWrite` rejects every x64 write: a vector store (`movups` to memory) is
neither phase-2 nor phase-3 (`MultiWriteRule.lean`), and remains open (a
release-kind multi-write tree).

- `Phase2TreeX A e`, `DirPhase2X`, `DirsPhase2X`, `phase2TreeX_of_dirs`,
  `dirsPhase2X_layout`, tactic `dirs_phase2X p` (tries the phase-1 `simp`
  of `dirs_phase1X` first, then the phase-2 one).
- `linkHyps2_QX64` (the link proof `link_QX64`, unchanged),
  `ThreadRuleRX.ofSafelyEnvG2X`, `npSafe_of_safelyEnvG2X`.
- No fault: `noFaultRule_ofEnvG2_structX` (an alias of the ISA-neutral
  `noFaultRule_ofEnvG2_struct`, `MultiCommon.lean`),
  `noFaultRule_ofSafelyEnvG2X_struct`.

The ISA-neutral tree lemmas (`multiAccessS_map`, …) live in
`MultiCommon.lean` (namespace `Kraken.Promising.AArch64.EnvG`); the names in
`Kraken.Promising.X64.EnvG` are statement-preserving aliases (formerly
copies).

Smoke test: `MultiX64Smoke.lean`.
-/
import Kraken.Promising.SLR.EnvG.X64Link
import Kraken.Promising.SLR.EnvG.MultiRule
import Kraken.Promising.SLR.EnvG.MultiCommon

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## Tree shapes along `EvTree.map` (statement-preserving aliases of the
ISA-neutral originals in `EnvG/MultiCommon.lean`; formerly copies) -/

hoist_alias [Kraken.Promising.AArch64.EnvG.multiAccessS_map ↦ Kraken.Promising.X64.EnvG.multiAccessS_map,
  Kraken.Promising.AArch64.EnvG.noRelWrite_map ↦ Kraken.Promising.X64.EnvG.noRelWrite_map,
  Kraken.Promising.AArch64.EnvG.phase2Shape_map ↦ Kraken.Promising.X64.EnvG.phase2Shape_map]

/-! ## The phase-2 shape of the code -/

/-- **The phase-2 shape of the code, x64** (`MultiA64.Phase2Tree`): every tree
of a thread state running `e` with no declarations is phase-1 or phase-2. -/
def Phase2TreeX (A : Arch) (e : Kraken.Executable Directive) : Prop :=
  ∀ st : State, st.exe = e → st.decls = {} → ∀ tree, isa.exec st = some tree →
    Phase1Shape A tree ∨ Phase2Shape A tree

/-- Phase-1 code is phase-2 code. -/
theorem Phase1TreeX.to2 {A : Arch} {e : Kraken.Executable Directive} (h : Phase1TreeX A e) : Phase2TreeX A e :=
  fun st he hds tree hex => .inl (h st he hds tree hex)

/-- The adapter's tree of the directive `d` of size `z` is phase-1 or
phase-2, from every machine state and pc (as `DirPhase1X`). -/
def DirPhase2X (A : Arch) (e : _root_.Executable) (d : Directive) (z : Nat) : Prop :=
  ∀ (s : MachineData) (pc : Int64),
    Phase1Shape A (toEv {} (@Directive.interp (_root_.Executable.labels e) d s (.mk pc (pc + .ofNat z))
      (fun s' => .done (s', pc + .ofNat z)) (fun pc' s' => .done (s', pc')))) ∨
    Phase2Shape A (toEv {} (@Directive.interp (_root_.Executable.labels e) d s (.mk pc (pc + .ofNat z))
      (fun s' => .done (s', pc + .ofNat z)) (fun pc' s' => .done (s', pc'))))

/-- Every directive of the text has a phase-1 or phase-2 tree. -/
def DirsPhase2X (A : Arch) (e : _root_.Executable) : Prop := ∀ d z, (d, z) ∈ e.2 → DirPhase2X A e d z

/-- **`Phase2TreeX` from the per-directive check.** -/
theorem phase2TreeX_of_dirs {A : Arch} {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
    (h : DirsPhase2X A e) : Phase2TreeX A e :=
  fun _ he hds _ htree => tree_of_codeAt (Φ := fun t => Phase1Shape A t ∨ Phase2Shape A t)
    (fun f _ ht => ht.imp (phase1Shape_map f) (phase2Shape_map f)) (fun d z hm => h d z hm) he hds htree

/-- The directives of a laid-out program are the program's. -/
theorem dirsPhase2X_layout [layout : _root_.Layout] {A : Arch} {p : Program}
    (h : ∀ d ∈ p, ∀ (e : _root_.Executable) z, DirPhase2X A e d z) : DirsPhase2X A (layout p) := by
  intro d z hm
  obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact h _ (List.getElem_mem hi) _ _

set_option hygiene false in
/-- `dirs_phase2X p` proves `DirsPhase2X A (layout p)` for an x64 program `p`
(a definition): per directive, the phase-1 `simp` of `dirs_phase1X`, else the
phase-2 one (a load prefix, at most one access, no release-kind write; under
`Arch.tso` no write at all after the loads). -/
macro "dirs_phase2X " p:ident : tactic => `(tactic| (
  refine Kraken.Promising.X64.EnvG.dirsPhase2X_layout (p := $p) ?_
  intro d hd e z s pc
  simp only [$p:ident, List.mem_cons, List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals simp only [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    _root_.MachineData.load, _root_.MachineData.store,
    _root_.MachineData.rmwK, _root_.RegOrMem.interp, _root_.Operand.interp, _root_.MachineData.set,
    _root_.RegOrMem.rmw, _root_.AvxOperation.interp, _root_.AvxRegOrMem.interp, _root_.MachineData.loadAvx,
    _root_.MachineData.storeAvx, _root_.MachineData.setAvx, _root_.MachineData.setAvxLegacy]
  all_goals first
    | (refine Or.inl ?_
       simp [Kraken.Promising.X64.toEv, Kraken.Promising.SLR.EnvG.Phase1Shape,
         Kraken.Promising.SLR.EnvG.DetAccess, Kraken.Promising.SLR.EnvG.SingleAccessS,
         Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty,
         Kraken.Promising.X64.loadPieces, Kraken.Promising.X64.storePieces]
       repeat' (first | split |
         simp [Kraken.Promising.X64.toEv, Kraken.Promising.SLR.EnvG.Phase1Shape,
           Kraken.Promising.SLR.EnvG.DetAccess, Kraken.Promising.SLR.EnvG.SingleAccessS,
           Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty,
           Kraken.Promising.X64.loadPieces, Kraken.Promising.X64.storePieces])
       done)
    | (refine Or.inr ?_
       simp [Kraken.Promising.X64.toEv, Kraken.Promising.SLR.EnvG.Phase2Shape,
         Kraken.Promising.SLR.EnvG.MultiAccessS, Kraken.Promising.SLR.EnvG.NoRelWrite,
         Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty,
         Kraken.Promising.X64.loadPieces, Kraken.Promising.X64.storePieces]
       repeat' (first | split |
         simp [Kraken.Promising.X64.toEv, Kraken.Promising.SLR.EnvG.Phase2Shape,
           Kraken.Promising.SLR.EnvG.MultiAccessS, Kraken.Promising.SLR.EnvG.NoRelWrite,
           Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty,
           Kraken.Promising.X64.loadPieces, Kraken.Promising.X64.storePieces])
       done)))

/-! ## The no-fault rule (statement-preserving alias of the ISA-neutral
`noFaultRule_ofEnvG2_struct`, `EnvG/MultiCommon.lean`; formerly a copy) -/

hoist_alias [Kraken.Promising.SLR.EnvG.noFaultRule_ofEnvG2_struct ↦ Kraken.Promising.X64.EnvG.noFaultRule_ofEnvG2_structX]

/-! ## The link -/

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout} {e : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateX → Prop}

/-- **The phase-2 link hypotheses at `QX64`** (the link proof `link_QX64`). -/
theorem linkHyps2_QX64 (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase2TreeX A e)
    (hpost : ∀ y, post y → y.1.2 = endPc) : LinkHyps2 (I := isa) A tid pl (QX64 A tid pl S e endPc post) where
  valid := hpl
  shape st _ h tree hex := hshape st h.1 h.2.1 tree hex
  link := link_QX64 hS hpost

/-- **`ThreadRuleRX.ofSafelyEnvG2X`**: `ofSafelyEnvGX` for code with phase-2
trees (`Phase2TreeX`). -/
def _root_.Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvG2X
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase2TreeX A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRX A B tid :=
  ThreadRuleRX.ofEnvG2 (linkHyps2_QX64 (tid := tid) hpl hS hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QX64 hstuck hQ hh) hp hrel hcl

/-- **`NPSafe` from a `Safely` judgment of `EnvGX`, phase-2 code**
(`NPSafe.of_ruleRX` at `ofSafelyEnvG2X`). -/
theorem npSafe_of_safelyEnvG2X {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase2TreeX A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvG (I := isa) A tid pl (QX64 A tid pl S e endPc post) cl c r g) :
    NPSafe (model isa) A B tid n m cl c r g :=
  NPSafe.of_ruleRX (ThreadRuleRX.ofSafelyEnvG2X hpl hS hshape hpost hstuck hB) n m cl c r g h

/-- **The x64 phase-2 no-fault rule**, unconditional in the thread's promises. -/
theorem noFaultRule_ofSafelyEnvG2X_struct {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase2TreeX A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRule (ThreadRuleRX.ofSafelyEnvG2X hpl hS hshape hpost hstuck hB) :=
  noFaultRule_ofEnvG2_structX _ _ (noFault_QX64 hnf hpost)

end Link

end Kraken.Promising.X64.EnvG
