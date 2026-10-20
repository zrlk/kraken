/-
EnvG on x64: **the x64 rule links**
`ThreadRuleRX.ofSafelyEnvGX` and `ThreadRuleRX.ofSafelyEnvGRX`, the x64
counterparts of `ofSafelyEnvG` (`A64Link.lean`) and `ofSafelyEnvGR`
(`A64LinkR.lean`), with the same statement shapes at x64 types.

## The x64 environment

A thread is proved in **`EnvGX A tid pl S := (EnvG isa A tid pl).within S`**:
`EnvG` with every access restricted to a location of the shared layout `S`
(`X64LiveRun.lean`). The restriction is what the x64 run lemma needs to
agree with the adapter on non-atomic vector accesses (pieces) and on
`atomic` vector accesses (`Le16 S`); a thread proof in `EnvGX` is a proof in
`EnvG` that, in addition, touches only `S`. A judgment of `EnvG` is one of
`EnvGX` (`TreeJLive.toWithin`), so the rule link (`EnvG/RuleLink.lean`)
applies unchanged at the invariant

  `QX64 st σ := st.exe = e ∧ st.decls = {} ∧ st.endPc = endPc ∧
    Split S st.st.1.dmem ∧ Safely (e.instrStepEnv (EnvGX A tid pl S)) post (st.st, σ)`

(`Split`: no byte of a location of `S` is in the thread's private memory;
instructions keep it, `exec_treeJLive_of_instrStepEnvW`). There is no static
`rmwLive` check: every x64 tree is live (`X64Live.exec_rmwLive`).

## Release-kind RMWs

Under `Arch.tso` every x64 RMW (`xchg`, `lock xadd`, `lock cmpxchg`, …) is
`.acqRel`, hence release-kind, so `Phase1Tree` (no release-kind RMW)
rejects every x64 RMW; `ofSafelyEnvGRX` (`Phase1TreeR`, `QX64R`,
`RelRmwGiveOk`) is the form x64 locks need. The phase-1 limits for release-kind RMWs apply
(`A64LinkR.lean`, `KNOWN_GAPS.md`): an in-flight release RMW never fails
(`lock cmpxchg` releases are out: `Phase1ShapeR` rejects them), and
planned-release RMWs claim nothing given away (`RelRmwGiveOk`).

## Contents

- `EnvGX`, `EStateX`, `Phase1TreeX`, `Phase1TreeRX`, `QX64`, `QX64R`.
- `linkHyps_QX64`, `ThreadRuleRX.ofSafelyEnvGX`, `npSafe_of_safelyEnvGX`;
  `linkHypsR_QX64`, `ThreadRuleRX.ofSafelyEnvGRX`, `npSafe_of_safelyEnvGRX`.
- No fault from fault-free code (`DirsNoFault e`, `EnvLinkTermX64.lean`,
  tactic `dirs_no_fault`): `noFaultRule_ofSafelyEnvGX_struct`,
  `noFaultRule_ofSafelyEnvGRX_struct` (`noFaultRule_ofEnvGR_structX` and
  `InvGR.q_atX` are aliases of the ISA-neutral `noFaultRule_ofEnvGR_struct`
  and `InvGR.q_at`, `EnvG/LinkRNoFault.lean`).
- The per-directive phase-1 checks `DirsPhase1X`/`DirsPhase1RX`
  (`phase1TreeX_of_dirs`, `phase1TreeRX_of_dirs`, tactics `dirs_phase1X p`,
  `dirs_phase1RX p`).
- The start: `qx64_of_partialTripleEnv` (from a `vcgen` triple in `EnvGX`),
  `σInitX`, `invGX_init`, `invGRX_init`.

The ISA-neutral tree lemmas (`accessFree_map`, …, `phase1ShapeR_map`) live
in `EnvG/TreeMap.lean` (namespace `Kraken.Promising.AArch64.EnvG`); the
names in `Kraken.Promising.X64.EnvG` are statement-preserving aliases
(formerly copies).

Phase-1 limits apply (single-access trees, read-side acquire only).
-/
import Kraken.Promising.SLR.EnvG.X64LiveRun
import Kraken.Promising.SLR.EnvG.Answers
import Kraken.EnvCfg
import Kraken.Promising.SLR.EnvG.TreeMap
import Kraken.Promising.SLR.EnvG.LinkRNoFault
import Kraken.Promising.SLR.EnvG.Alias

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## Tree shapes along `EvTree.map` (statement-preserving aliases of the
ISA-neutral originals in `EnvG/TreeMap.lean`; formerly copies) -/

hoist_alias [Kraken.Promising.AArch64.EnvG.accessFree_map ↦ Kraken.Promising.X64.EnvG.accessFree_map,
  Kraken.Promising.AArch64.EnvG.detAccess_map ↦ Kraken.Promising.X64.EnvG.detAccess_map,
  Kraken.Promising.AArch64.EnvG.singleAccessS_map ↦ Kraken.Promising.X64.EnvG.singleAccessS_map,
  Kraken.Promising.AArch64.EnvG.phase1Shape_map ↦ Kraken.Promising.X64.EnvG.phase1Shape_map,
  Kraken.Promising.AArch64.EnvG.singleAccessS2_map ↦ Kraken.Promising.X64.EnvG.singleAccessS2_map,
  Kraken.Promising.AArch64.EnvG.phase1ShapeR_map ↦ Kraken.Promising.X64.EnvG.phase1ShapeR_map]

/-! ## The thread's tree is a code cell's tree (x64) -/

/-- The directive a thread state's pc finds, from `codeAt`. -/
theorem directive_of_codeAt {st : State} {d : Directive} {z : Nat} {rest : List (Directive × Nat)}
    (hcode : Kraken.Executable.codeAt st.exe st.st.2 = (d, z) :: rest) : st.directive = some d := by
  obtain ⟨exe, endPc, ⟨s, pc⟩, showPc, decls⟩ := st
  unfold State.directive
  simp only at hcode ⊢
  rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress exe pc) = Kraken.Executable.codeAt exe pc from by
    unfold Kraken.Executable.codeAt
    congr 1, hcode]
  rfl

/-- An instruction step at a thread state's pc finds its directive. -/
theorem directive_isSome_of_instrStepEnv {E : SharedEnv} {e : Kraken.Executable Directive} {st : State}
    {g : E.State} {R : MachineState × E.State → Prop} (he : st.exe = e) (h : e.instrStepEnv E (st.st, g) R) :
    st.directive.isSome := by
  obtain ⟨d, z, rest, hcode, -⟩ := h
  rw [← he] at hcode
  rw [directive_of_codeAt hcode]; rfl

/-- At the end address the thread has no instruction. -/
theorem exec_eq_none_of_end {st : State} (h : st.st.2 = st.endPc) : isa.exec st = none := by
  show exec st = none
  unfold exec
  simp [h]

/-- **`done` from a `Safely` judgment, for any environment**: a halted
thread whose `Safely` state allows no step at `endPc` (`hstuck`) is at its
postcondition (elsewhere a halted thread has no directive). The shared body
of the `post_of_halted_Q…` lemmas. -/
theorem post_of_halted_env {E : SharedEnv} {e : Kraken.Executable Directive} {endPc : Int64}
    {post : MachineState × E.State → Prop} (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv E x R)
    {t : Thread isa} {σ : E.State} (he : t.st.exe = e) (hend : t.st.endPc = endPc)
    (hsafe : Safely (e.instrStepEnv E) post (t.st.st, σ)) (hh : t.halted = true) :
    post (t.st.st, σ) := by
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

/-- A thread state with a tree is at a code cell. -/
theorem codeAt_of_exec {st : State} {tree : EvTree State} (h : isa.exec st = some tree) :
    ∃ d z rest, Kraken.Executable.codeAt st.exe st.st.2 = (d, z) :: rest := by
  have h' : exec st = some tree := h
  unfold exec at h'
  split at h'
  · cases h'
  · next hc =>
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hc
    have hd := hc.2
    unfold State.directive at hd
    rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress st.exe st.st.2) =
      Kraken.Executable.codeAt st.exe st.st.2 from by unfold Kraken.Executable.codeAt; congr 1] at hd
    cases hc' : Kraken.Executable.codeAt st.exe st.st.2 with
    | nil => rw [hc'] at hd; simp at hd
    | cons x rest => exact ⟨x.1, x.2, rest, rfl⟩

/-- The cell `codeAt` finds is a cell of the executable. -/
theorem mem_of_codeAt {e : Kraken.Executable Directive} {pc : Int64} {d : Directive} {z : Nat}
    {rest : List (Directive × Nat)} (h : e.codeAt pc = (d, z) :: rest) : (d, z) ∈ e.2 := by
  obtain ⟨start, ds⟩ := e
  obtain ⟨a', ds', hW, hsuf⟩ := dropWhile_withAddresses (fun x => decide (x.1 ≠ pc)) ds start
  have hfrom : Kraken.Executable.directivesFromAddress (start, ds) pc = ds' := by
    unfold Kraken.Executable.directivesFromAddress
    rw [hW, Kraken.Executable.withAddresses_map_snd]
  unfold Kraken.Executable.codeAt at h
  rw [hfrom] at h
  have hm : (d, z) ∈ ds'.dropWhile (fun c => c.1.isLabel) := by rw [h]; exact List.mem_cons_self
  exact hsuf.subset ((List.dropWhile_suffix _).subset hm)

/-- A per-directive property `Φ` of the adapter's tree, closed under
`EvTree.map`, holds of every tree of a thread running `e` with no
declarations (`SafelyBridge.tree_of_codeAt`, x64). -/
theorem tree_of_codeAt {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
    {Φ : ∀ {σ : Type}, EvTree σ → Prop} (hmap : ∀ {σ τ : Type} (f : σ → τ) (t : EvTree σ), Φ t → Φ (t.map f))
    (hd : ∀ d z, (d, z) ∈ e.2 → ∀ (s : MachineData) (pc : Int64),
      Φ (toEv {} (@Directive.interp (_root_.Executable.labels e) d s (.mk pc (pc + .ofNat z))
        (fun s' => .done (s', pc + .ofNat z)) (fun pc' s' => .done (s', pc')))))
    {st : State} (he : st.exe = e) (hds : st.decls = {}) {tree : EvTree State} (htree : isa.exec st = some tree) :
    Φ tree := by
  obtain ⟨d, z, rest, hcode⟩ := codeAt_of_exec htree
  have hdir := directive_of_codeAt hcode
  have hmem := mem_of_codeAt hcode
  rw [he] at hcode hmem
  obtain ⟨ls, hat, hls⟩ := directivesAtAddress_of_codeAt hcode
  obtain ⟨exe, endPc, ⟨s, pc⟩, showPc, decls⟩ := st
  simp only at he hds hcode hat hdir ⊢
  subst he hds
  simp only [isa, exec, hdir, Option.isNone_some, Bool.or_false] at htree
  split at htree
  · cases htree
  · cases htree
    refine hmap _ _ ?_
    unfold Executable.step
    letI := Executable.labels exe
    simp only
    rw [hat, Directives.interp_label_prefix ls _ _ _ _ hls]
    simp only [Directives.interp]
    exact hd d z hmem s pc

/-- **The thread's tree is fault-free** at a pc whose directive has a
fault-free tree (`DirNoFault`), with no declarations
(`A64NoFault.noFault_of_codeAt`, x64). -/
theorem noFault_of_exec {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {st : State}
    (he : st.exe = e) (hds : st.decls = {}) (hnf : DirsNoFault e) :
    ∀ tree, isa.exec st = some tree → tree.NoFault := fun _ htree =>
  tree_of_codeAt (Φ := EvTree.NoFault) (fun f t ht => (EvTree.noFault_map f t).mpr ht)
    (fun d z hm => hnf d z hm) he hds htree

/-! ## The phase-1 shape, per directive -/

/-- `EnvG`'s phase-1 shape of the code, x64 (`A64Link.Phase1Tree`). -/
def Phase1TreeX (A : Arch) (e : Kraken.Executable Directive) : Prop :=
  ∀ st : State, st.exe = e → st.decls = {} → ∀ tree, isa.exec st = some tree → Phase1Shape A tree

/-- The phase-1 shape with release-kind RMWs, x64 (`A64LinkR.Phase1TreeR`). -/
def Phase1TreeRX (A : Arch) (e : Kraken.Executable Directive) : Prop :=
  ∀ st : State, st.exe = e → st.decls = {} → ∀ tree, isa.exec st = some tree → Phase1ShapeR A tree

theorem Phase1TreeX.toR {A : Arch} {e : Kraken.Executable Directive} (h : Phase1TreeX A e) : Phase1TreeRX A e :=
  fun st he hds tree hex => (h st he hds tree hex).toR

/-- The adapter's tree of the directive `d` of size `z` is phase-1, from
every machine state and pc. -/
def DirPhase1X (A : Arch) (e : _root_.Executable) (d : Directive) (z : Nat) : Prop :=
  ∀ (s : MachineData) (pc : Int64),
    Phase1Shape A (toEv {} (@Directive.interp (_root_.Executable.labels e) d s (.mk pc (pc + .ofNat z))
      (fun s' => .done (s', pc + .ofNat z)) (fun pc' s' => .done (s', pc'))))

/-- The same with release-kind RMWs. -/
def DirPhase1RX (A : Arch) (e : _root_.Executable) (d : Directive) (z : Nat) : Prop :=
  ∀ (s : MachineData) (pc : Int64),
    Phase1ShapeR A (toEv {} (@Directive.interp (_root_.Executable.labels e) d s (.mk pc (pc + .ofNat z))
      (fun s' => .done (s', pc + .ofNat z)) (fun pc' s' => .done (s', pc'))))

def DirsPhase1X (A : Arch) (e : _root_.Executable) : Prop := ∀ d z, (d, z) ∈ e.2 → DirPhase1X A e d z

def DirsPhase1RX (A : Arch) (e : _root_.Executable) : Prop := ∀ d z, (d, z) ∈ e.2 → DirPhase1RX A e d z

theorem phase1TreeX_of_dirs {A : Arch} {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
    (h : DirsPhase1X A e) : Phase1TreeX A e :=
  fun _ he hds _ htree => tree_of_codeAt (Φ := Phase1Shape A) (fun f _ ht => phase1Shape_map f ht)
    (fun d z hm => h d z hm) he hds htree

theorem phase1TreeRX_of_dirs {A : Arch} {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
    (h : DirsPhase1RX A e) : Phase1TreeRX A e :=
  fun _ he hds _ htree => tree_of_codeAt (Φ := Phase1ShapeR A) (fun f _ ht => phase1ShapeR_map f ht)
    (fun d z hm => h d z hm) he hds htree

theorem dirsPhase1X_layout [layout : _root_.Layout] {A : Arch} {p : Program}
    (h : ∀ d ∈ p, ∀ (e : _root_.Executable) z, DirPhase1X A e d z) : DirsPhase1X A (layout p) := by
  intro d z hm
  obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact h _ (List.getElem_mem hi) _ _

theorem dirsPhase1RX_layout [layout : _root_.Layout] {A : Arch} {p : Program}
    (h : ∀ d ∈ p, ∀ (e : _root_.Executable) z, DirPhase1RX A e d z) : DirsPhase1RX A (layout p) := by
  intro d z hm
  obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact h _ (List.getElem_mem hi) _ _

set_option hygiene false in
/-- `dirs_phase1X p` proves `DirsPhase1X A (layout p)` for an x64 program
`p` (a definition) whose instructions make at most one access,
deterministically, with no release-kind RMW (under `Arch.tso` no RMW at all):
one `simp` per directive, as `dirs_no_fault`. -/
macro "dirs_phase1X " p:ident : tactic => `(tactic| (
  refine Kraken.Promising.X64.EnvG.dirsPhase1X_layout (p := $p) ?_
  intro d hd e z s pc
  simp only [$p:ident, List.mem_cons, List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals simp [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    Kraken.Promising.X64.toEv, Kraken.Promising.SLR.EnvG.Phase1Shape, Kraken.Promising.SLR.EnvG.DetAccess,
    Kraken.Promising.SLR.EnvG.SingleAccessS, Kraken.Promising.SLR.EnvG.AccessFree,
    _root_.MachineData.load, _root_.MachineData.store,
    _root_.MachineData.rmwK, _root_.RegOrMem.interp, _root_.Operand.interp, _root_.MachineData.set,
    _root_.RegOrMem.rmw, Kraken.Promising.EvTree.access_empty]
  all_goals (repeat' (first | split |
    simp [Kraken.Promising.X64.toEv, Kraken.Promising.SLR.EnvG.Phase1Shape, Kraken.Promising.SLR.EnvG.DetAccess,
      Kraken.Promising.SLR.EnvG.SingleAccessS, Kraken.Promising.SLR.EnvG.AccessFree,
      Kraken.Promising.EvTree.access_empty]))))

set_option hygiene false in
/-- `dirs_phase1RX p` proves `DirsPhase1RX A (layout p)` for an x64 program
`p` whose instructions make at most one access, deterministically, and whose
release-kind RMWs never fail (`xchg`, `lock xadd`; not `lock cmpxchg`).
Jump targets are unfolded too (`RelRegOrMem.interp`, not a `kstep`
definition; added, so that `jmp` needs no follow-up `simp`). -/
macro "dirs_phase1RX " p:ident : tactic => `(tactic| (
  refine Kraken.Promising.X64.EnvG.dirsPhase1RX_layout (p := $p) ?_
  intro d hd e z s pc
  simp only [$p:ident, List.mem_cons, List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals simp [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    Kraken.Promising.X64.toEv, Kraken.Promising.SLR.EnvG.Phase1ShapeR, Kraken.Promising.SLR.EnvG.DetAccess,
    Kraken.Promising.SLR.EnvG.SingleAccessS2, Kraken.Promising.SLR.EnvG.AccessFree,
    _root_.MachineData.load, _root_.MachineData.store,
    _root_.MachineData.rmwK, _root_.RegOrMem.interp, _root_.Operand.interp, _root_.MachineData.set,
    _root_.RegOrMem.rmw, _root_.RelRegOrMem.interp, Kraken.Promising.EvTree.access_empty]
  all_goals (repeat' (first | split |
    simp [Kraken.Promising.X64.toEv, Kraken.Promising.SLR.EnvG.Phase1ShapeR,
      Kraken.Promising.SLR.EnvG.DetAccess, Kraken.Promising.SLR.EnvG.SingleAccessS2,
      Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty]))))

/-! ## The environment and the invariant -/

/-- **`EnvG` for x64**, restricted to the shared layout `S`. -/
abbrev EnvGX (A : Arch) (tid : Nat) (pl : Plan) (S : SharedEnv.Layout) : SharedEnv :=
  (Kraken.Promising.SLR.EnvG isa A tid pl).within S

/-- `EnvG`'s state for x64. -/
abbrev EStateX : Type := Kraken.Promising.SLR.EnvG.State isa

/-- **The thread-local invariant, x64**: the code, no declarations, the end
address, a private memory split from `S`, and the `Safely` judgment of
`EnvGX` at the machine state. -/
def QX64 (A : Arch) (tid : Nat) (pl : Plan) (S : SharedEnv.Layout) (e : Kraken.Executable Directive)
    (endPc : Int64) (post : MachineState × EStateX → Prop) (st : State) (σ : EStateX) : Prop :=
  st.exe = e ∧ st.decls = {} ∧ st.endPc = endPc ∧ Split S st.st.1.dmem ∧
    Safely (e.instrStepEnv (EnvGX A tid pl S)) post (st.st, σ)

/-- `QX64` with the env's release predicates fixed (`A64LinkR.QA64R`). -/
def QX64R (A : Arch) (tid : Nat) (pl : Plan) (S : SharedEnv.Layout) (e : Kraken.Executable Directive)
    (endPc : Int64) (post : MachineState × EStateX → Prop) (rel₀ : Loc → Pred) (st : State) (σ : EStateX) : Prop :=
  QX64 A tid pl S e endPc post st σ ∧ σ.g.rel = rel₀

/-! ## The no-fault rule with release-kind RMWs (copy of the ISA-neutral
`A64LinkR.noFaultRule_ofEnvGR_struct`) -/

section RuleR

-- Statement-preserving aliases of the ISA-neutral originals in
-- `EnvG/LinkRNoFault.lean` (formerly copies).
hoist_alias [Kraken.Promising.SLR.EnvG.InvGR.q_at ↦ Kraken.Promising.X64.EnvG.InvGR.q_atX,
  Kraken.Promising.SLR.EnvG.noFaultRule_ofEnvGR_struct ↦ Kraken.Promising.X64.EnvG.noFaultRule_ofEnvGR_structX]

end RuleR

/-! ## The link -/

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout} {e : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateX → Prop}

/-- The link step at `QX64` (both links). -/
theorem link_QX64 (hS : Le16 S) (hpost : ∀ y, post y → y.1.2 = endPc) :
    ∀ (J : TreeJLive (Kraken.Promising.SLR.EnvG isa A tid pl) isa.State) st σ tree,
      QX64 A tid pl S e endPc post st σ → isa.exec st = some tree →
      (∀ st' σ', QX64 A tid pl S e endPc post st' σ' → J.Post st' σ') → J.W tree σ := by
  intro J st σ tree h hex hJ
  obtain ⟨he, hds, hend, hs, hsafe⟩ := h
  rcases hsafe.unfold with hp | ⟨R, hR, hk⟩
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · exact exec_treeJLive_of_instrStepEnvW J hS he hds hs hR
      (fun m g' hz hs' => hJ _ _ ⟨he, hds, hend, hs', hk _ hz⟩) tree hex

/-- **The link hypotheses at `QX64`** (`linkHyps_QA64`, x64). -/
theorem linkHyps_QX64 (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeX A e)
    (hpost : ∀ y, post y → y.1.2 = endPc) : LinkHyps (I := isa) A tid pl (QX64 A tid pl S e endPc post) where
  valid := hpl
  shape st _ h tree hex := hshape st h.1 h.2.1 tree hex
  link := link_QX64 hS hpost

/-- **The link hypotheses with release-kind RMWs at `QX64R`**
(`linkHypsR_QA64`, x64). -/
theorem linkHypsR_QX64 {rel₀ : Loc → Pred} (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeRX A e)
    (hG : RelRmwGiveOk isa pl rel₀) (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsR (I := isa) A tid pl (QX64R A tid pl S e endPc post rel₀) where
  valid := hpl
  shape st _ h tree hex := hshape st h.1.1 h.1.2.1 tree hex
  giveOk _ _ h := h.2 ▸ hG
  link := link_relFix rel₀ (link_QX64 hS hpost)

omit [Kraken.Executable.ValidLayout e] in
/-- **`done` at `QX64`**: a halted thread's `Safely` state is at its
postcondition (`post_of_halted_QA64`, x64). -/
theorem post_of_halted_QX64 (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGX A tid pl S) x R)
    {t : Thread isa} {σ : EStateX} (hQ : QX64 A tid pl S e endPc post t.st σ) (hh : t.halted = true) :
    post (t.st.st, σ) := by
  obtain ⟨he, -, hend, -, hsafe⟩ := hQ
  exact post_of_halted_env hstuck he hend hsafe hh

/-- **`ThreadRuleRX.ofSafelyEnvGX`**: the x64 rule link (`ofSafelyEnvG`,
x64). A thread whose code has phase-1 trees, proved by a `Safely` judgment
of `EnvGX A tid pl S` (`Le16 S`) with postcondition `post` only at `endPc`
(and no step at `endPc`), satisfies `ThreadRuleRX A B tid` for every `B`
that `post` gives at a halted thread with no promise. No `rmwLive` check
(every x64 tree is live). Under `Arch.tso` `Phase1TreeX` admits no RMW: use
`ofSafelyEnvGRX`. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvGX {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeX A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRX A B tid :=
  ThreadRuleRX.ofEnvG (linkHyps_QX64 (tid := tid) hpl hS hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QX64 hstuck hQ hh) hp hrel hcl

/-- **`NPSafe` from a `Safely` judgment of `EnvGX`** (`npSafe_of_safelyEnvG`, x64). -/
theorem npSafe_of_safelyEnvGX {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeX A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvG (I := isa) A tid pl (QX64 A tid pl S e endPc post) cl c r g) :
    NPSafe (model isa) A B tid n m cl c r g :=
  NPSafe.of_ruleRX (ThreadRuleRX.ofSafelyEnvGX hpl hS hshape hpost hstuck hB) n m cl c r g h

/-- **Every tree from a `QX64`-state is fault-free**, for fault-free code
(`noFault_QA64`, x64). -/
theorem noFault_QX64 (hnf : DirsNoFault e) (hpost : ∀ y, post y → y.1.2 = endPc) :
    ∀ st σ tree, QX64 A tid pl S e endPc post st σ → isa.exec st = some tree → tree.NoFault := by
  intro st σ tree h hex
  obtain ⟨he, hds, hend, -, hsafe⟩ := h
  rcases hsafe.unfold with hp | -
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · exact noFault_of_exec he hds hnf tree hex

/-- **The x64 no-fault rule**, unconditional in the thread's promises
(`noFaultRule_ofSafelyEnvG_struct`, x64). -/
theorem noFaultRule_ofSafelyEnvGX_struct {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeX A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRule (ThreadRuleRX.ofSafelyEnvGX hpl hS hshape hpost hstuck hB) :=
  noFaultRule_ofEnvG_struct _ _ (noFault_QX64 hnf hpost)

variable {rel₀ : Loc → Pred}

/-- **`ThreadRuleRX.ofSafelyEnvGRX`**: the x64 rule link with release-kind
RMWs (`ofSafelyEnvGR`, x64): `ofSafelyEnvGX` with `Phase1TreeRX`, the
give-away side condition at the release predicates `rel₀`, and the invariant
`QX64R`. The form x64 needs: under `Arch.tso` every x64 RMW is
release-kind. Phase-1 limits: an in-flight release RMW never fails (no
`lock cmpxchg` release), planned-release RMWs claim nothing given away. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvGRX
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeRX A e) (hG : RelRmwGiveOk isa pl rel₀)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRX A B tid :=
  ThreadRuleRX.ofEnvGR (linkHypsR_QX64 (tid := tid) hpl hS hshape hG hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QX64 hstuck hQ.1 hh) hp hrel hcl

/-- **`NPSafe` from a `Safely` judgment of `EnvGX` with release-kind RMWs**. -/
theorem npSafe_of_safelyEnvGRX {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeRX A e) (hG : RelRmwGiveOk isa pl rel₀)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvGR (I := isa) tid pl (QX64R A tid pl S e endPc post rel₀) cl c r g) :
    NPSafe (model isa) A B tid n m cl c r g :=
  NPSafe.of_ruleRX (ThreadRuleRX.ofSafelyEnvGRX hpl hS hshape hG hpost hstuck hB) n m cl c r g h

/-- **The x64 no-fault rule with release-kind RMWs** for fault-free code. -/
theorem noFaultRule_ofSafelyEnvGRX_struct {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : Phase1TreeRX A e) (hG : RelRmwGiveOk isa pl rel₀)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRule (ThreadRuleRX.ofSafelyEnvGRX hpl hS hshape hG hpost hstuck hB) :=
  noFaultRule_ofEnvGR_structX _ _ fun st σ tree hQ hex => noFault_QX64 hnf hpost st σ tree hQ.1 hex

end Link

/-! ## From `vcgen` triples to `QX64` -/

section Triple

variable {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout}

/-- The postcondition `Program.instrStepEnv_of_partialTripleEnv` gives with
no exceptional exit: the end of `p`'s text and `Q`. -/
def postOfX [layout : _root_.Layout] (p : Program) (Q : MachineData → EStateX → Prop) :
    MachineState × EStateX → Prop :=
  fun x => (x.1.2 = (layout p).addrOf p.length ∧ Q x.1.1 x.2) ∨ False

theorem postOfX_end [layout : _root_.Layout] {p : Program} {Q : MachineData → EStateX → Prop} :
    ∀ y, postOfX p Q y → y.1.2 = (layout p).addrOf p.length :=
  fun _ h => h.elim And.left False.elim

/-- **`QX64` from a partial triple** in `EnvGX` at a thread state at the
start of `p` with a split private memory, whose exceptional exit `E` never
holds (`qa64_of_partialTripleEnv`, x64). -/
theorem qx64_of_partialTripleEnv [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Kraken.Executable.ValidLayout (layout p)] {P Q : MachineData → EStateX → Prop}
    {E : Int64 → MachineData → EStateX → Prop} (ht : MachineWP.PartialTripleEnv (EnvGX A tid pl S) P p Q E)
    (henv : cenv = layout p) {st : State} (he : st.exe = layout p) (hds : st.decls = {})
    (hend : st.endPc = (layout p).addrOf p.length) (hpc : st.st.2 = (layout p).addrOf 0)
    (hs : Split S st.st.1.dmem) {σ : EStateX}
    (hP : P st.st.1 σ) (hE : ∀ a s g, ¬ E a s g := by simp) :
    QX64 A tid pl S (layout p) ((layout p).addrOf p.length) (postOfX p Q) st σ := by
  refine ⟨he, hds, hend, hs, ?_⟩
  have hst : st.st = (st.st.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hpc, Executable.addrOf_zero, Layout.apply_fst]
  rw [hst]
  exact (Program.instrStepEnv_of_partialTripleEnv ht hP henv).mono fun _ h => h.imp id (hE _ _ _)

end Triple

/-! ## The initial state -/

section Init

variable {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout}

/-- **The env state at a thread's start** (`σInit`, x64). -/
def σInitX (c : Config isa) (r : Res) (g : Ghost) : EStateX := { snap := c, vs := {}, r, g, cl := True }

theorem coreAtX_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = []) :
    CoreAt A tid pl True (Config.init ss m) r g (σInitX (Config.init ss m) r g) (Thread.init s) := by
  have ht : (Config.init ss m : Config isa).threads[tid]? = some (Thread.init s) := by simp [Config.init, hs]
  refine ⟨⟨ht, SnapLe.refl _ _, Ghost.Le.refl g, ?_, Config.init_bnd ss m tid _ ht,
    .inl ⟨rfl, fun _ h => (by cases h)⟩, fun _ => trivial, ⟨fun h => (by cases h), fun h => (by cases h)⟩⟩,
    fun ts h => (by rw [hpend] at h; cases h), fun ts _ _ h => (by cases h)⟩
  refine ⟨fun l => by simp [σInitX, Thread.init, Views.getCoh], Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
    Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, fun l => ?_, ?_⟩ <;>
    simp [σInitX, Thread.init, Views.getFwd, Sim.FwdLe, Sim.XclLe]

theorem coreAtRX_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = []) :
    CoreAtR tid pl True (Config.init ss m) r g (σInitX (Config.init ss m) r g) (Thread.init s) := by
  have ht : (Config.init ss m : Config isa).threads[tid]? = some (Thread.init s) := by simp [Config.init, hs]
  refine ⟨⟨ht, SnapLe.refl _ _, Ghost.Le.refl g, ?_, Config.init_bnd ss m tid _ ht,
    .inl ⟨rfl, fun _ h => (by cases h)⟩, fun _ => trivial, ⟨fun h => (by cases h), fun h => (by cases h)⟩⟩,
    fun ts h => (by rw [hpend] at h; cases h), fun ts _ _ h => (by cases h)⟩
  refine ⟨fun l => by simp [σInitX, Thread.init, Views.getCoh], Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
    Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, fun l => ?_, ?_⟩ <;>
    simp [σInitX, Thread.init, Views.getFwd, Sim.FwdLe, Sim.XclLe]

/-- **The rule's invariant at the initial configuration** from `QX64` at
`σInitX` (`invG_init`, x64). -/
theorem invGX_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = []) {e : Kraken.Executable Directive} {endPc : Int64}
    {post : MachineState × EStateX → Prop} (hQ : QX64 A tid pl S e endPc post s (σInitX (Config.init ss m) r g)) :
    InvG (I := isa) A tid pl (QX64 A tid pl S e endPc post) True (Config.init ss m) r g :=
  ⟨_, _, coreAtX_init hs hpend, hQ⟩

/-- **The rule's invariant with release-kind RMWs at the initial
configuration** (`invGR_init`, x64; the release predicates are the
ghost's). -/
theorem invGRX_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = []) {e : Kraken.Executable Directive} {endPc : Int64}
    {post : MachineState × EStateX → Prop} (hQ : QX64 A tid pl S e endPc post s (σInitX (Config.init ss m) r g)) :
    InvGR (I := isa) tid pl (QX64R A tid pl S e endPc post g.rel) True (Config.init ss m) r g :=
  ⟨σInitX (Config.init ss m) r g, Thread.init s, coreAtRX_init hs hpend, hQ, rfl⟩

end Init

end Kraken.Promising.X64.EnvG
