/-
Whole-thread environment: **the x64 link of `EnvGLR`**
(`LRRule.lean` at x64 types, `X64Link.lean`'s `EnvGX`/`QX64` with `EnvGLR`
in place of `EnvG`).

On x64 every store is release-kind (`Arch.tso`), so a tree that loads and
then stores, e.g. the unlocked read-modify-write forms `incl (m)`,
`addl $1,(m)`, `andl %eax,(m)` (`MachineData.rmwPlain`: a load, then a
store of the new value to the same address), is neither phase-1 (two
accesses) nor phase-2 (`NoRelWrite`). It is an `LRStoreShape` tree, and
`EnvGLR`'s rule link (`ThreadRuleRX.ofEnvGLR`) covers it.

- `EnvGLRX A tid pl S := (EnvGLR isa A tid pl).within S`, `QX64LR` (`QX64`
  with `EnvGLRX`).
- Shapes: `LRTreeX`, `DirLRX`, `DirsLRX`, `lrTreeX_of_dirs`,
  `dirsLRX_layout`, tactic `dirs_lrX p` (phase-1 `simp`, else phase-2,
  else: split every `match` of the tree and close each branch as phase-1,
  phase-2 or load-then-store).
- `link_QX64LR` (the proof of `link_QX64`, unchanged: the x64 run lemma is
  generic in the env), `linkHypsLR_QX64`, `post_of_halted_QX64LR`.
- `ThreadRuleRX.ofSafelyEnvGLRX`, `npSafe_of_safelyEnvGLRX`,
  `noFaultRule_ofSafelyEnvGLRX_struct`.
- The start: `qx64LR_of_partialTripleEnv`, `coreAtLRX_init`, `invGLRX_init`.

`EnvGLR`'s limits apply (`LRRule.lean`): its loads keep `cl` (no clean
erasure from a load), no release-kind RMW (x64 `lock` RMWs stay on
`ofSafelyEnvGRX`), and a load-then-store tree stores to one location on
every path.

Smoke test: `LRX64Smoke.lean`.
-/
import Kraken.Promising.SLR.EnvG.MultiX64
import Kraken.Promising.SLR.EnvG.LRRule

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## Shapes -/

/-- `LRShape` along `EvTree.map`. -/
theorem lrShape_map {A : Arch} {σ τ : Type} (f : σ → τ) {t : EvTree σ} (h : LRShape A t) :
    LRShape A (t.map f) := by
  rcases h with h | h | ⟨l, h⟩
  · exact .inl (phase1Shape_map f h)
  · exact .inr (.inl (phase2Shape_map f h))
  · exact .inr (.inr ⟨l, multiAccessS_map f t h⟩)

/-- **The `EnvGLR` shape of the code, x64**: every tree of a thread state
running `e` with no declarations is `LRShape`. -/
def LRTreeX (A : Arch) (e : Kraken.Executable Directive) : Prop :=
  ∀ st : State, st.exe = e → st.decls = {} → ∀ tree, isa.exec st = some tree → LRShape A tree

/-- Phase-2 code is `EnvGLR` code. -/
theorem Phase2TreeX.toLR {A : Arch} {e : Kraken.Executable Directive} (h : Phase2TreeX A e) : LRTreeX A e :=
  fun st he hds tree hex => (h st he hds tree hex).elim .inl (fun h => .inr (.inl h))

/-- The adapter's tree of the directive `d` of size `z` is `LRShape`, from
every machine state and pc (as `DirPhase2X`). -/
def DirLRX (A : Arch) (e : _root_.Executable) (d : Directive) (z : Nat) : Prop :=
  ∀ (s : MachineData) (pc : Int64),
    LRShape A (toEv {} (@Directive.interp (_root_.Executable.labels e) d s (.mk pc (pc + .ofNat z))
      (fun s' => .done (s', pc + .ofNat z)) (fun pc' s' => .done (s', pc'))))

/-- Every directive of the text has an `LRShape` tree. -/
def DirsLRX (A : Arch) (e : _root_.Executable) : Prop := ∀ d z, (d, z) ∈ e.2 → DirLRX A e d z

/-- **`LRTreeX` from the per-directive check.** -/
theorem lrTreeX_of_dirs {A : Arch} {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
    (h : DirsLRX A e) : LRTreeX A e :=
  fun _ he hds _ htree => tree_of_codeAt (Φ := fun t => LRShape A t)
    (fun f _ ht => lrShape_map f ht) (fun d z hm => h d z hm) he hds htree

/-- The directives of a laid-out program are the program's. -/
theorem dirsLRX_layout [layout : _root_.Layout] {A : Arch} {p : Program}
    (h : ∀ d ∈ p, ∀ (e : _root_.Executable) z, DirLRX A e d z) : DirsLRX A (layout p) := by
  intro d z hm
  obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact h _ (List.getElem_mem hi) _ _

set_option hygiene false in
/-- `cells_lrX p hd` is `dirs_lrX`'s per-directive script: given
`hd : d ∈ p` (`p` a list of directives, a definition) and the goal
`DirLRX A e d z s pc`, it splits `hd` into the cells of `p` and closes each
as phase-1, phase-2 or a load-then-store tree (jump targets of
`RelRegOrMem` operands are unfolded). Also used directly on fragments of
an image (`X64MpInclAbsMask.writerFragV_dirsLRX`). -/
macro "cells_lrX " p:ident hd:ident : tactic => `(tactic| (
  simp only [$p:ident, List.mem_cons, List.not_mem_nil, or_false] at $hd:ident
  repeat' (rcases $hd:ident with rfl | $hd:ident)
  repeat' (rcases hd with rfl | hd)
  all_goals simp only [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    _root_.MachineData.load, _root_.MachineData.store, _root_.MachineData.rmwPlain,
    _root_.MachineData.rmwK, _root_.RegOrMem.interp, _root_.Operand.interp, _root_.MachineData.set,
    _root_.RegOrMem.rmw, _root_.AvxOperation.interp, _root_.AvxRegOrMem.interp, _root_.MachineData.loadAvx,
    _root_.MachineData.storeAvx, _root_.MachineData.setAvx, _root_.MachineData.setAvxLegacy,
    _root_.RelRegOrMem.interp]
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
    | (refine Or.inr (Or.inl ?_)
       simp [Kraken.Promising.X64.toEv, Kraken.Promising.SLR.EnvG.Phase2Shape,
         Kraken.Promising.SLR.EnvG.MultiAccessS, Kraken.Promising.SLR.EnvG.NoRelWrite,
         Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty,
         Kraken.Promising.X64.loadPieces, Kraken.Promising.X64.storePieces]
       repeat' (first | split |
         simp [Kraken.Promising.X64.toEv, Kraken.Promising.SLR.EnvG.Phase2Shape,
           Kraken.Promising.SLR.EnvG.MultiAccessS, Kraken.Promising.SLR.EnvG.NoRelWrite,
           Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty,
           Kraken.Promising.X64.loadPieces, Kraken.Promising.X64.storePieces])
       done)
    | (repeat' split
       all_goals first
         | (exfalso; simp_all; done)
         | (refine Or.inl ?_
            simp [Kraken.Promising.X64.toEv, Kraken.Promising.SLR.EnvG.Phase1Shape,
              Kraken.Promising.SLR.EnvG.DetAccess, Kraken.Promising.SLR.EnvG.SingleAccessS,
              Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty, *]
            done)
         | (simp only [Kraken.Promising.X64.toEv, Kraken.Promising.EvTree.access_empty, *]
            refine Kraken.Promising.SLR.EnvG.LRShape.of_load fun _ => ?_
            simp [Kraken.Promising.X64.toEv, Kraken.Promising.SLR.EnvG.MultiAccessS,
              Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty, *]
            repeat' (first | split |
              simp [Kraken.Promising.X64.toEv, Kraken.Promising.SLR.EnvG.MultiAccessS,
                Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty, *])
            done))))

set_option hygiene false in
/-- `dirs_lrX p` proves `DirsLRX A (layout p)` for an x64 program `p` (a
definition): per directive, the phase-1 `simp` of `dirs_phase1X`, else the
phase-2 one of `dirs_phase2X`, else every `match` of the tree is split and
each branch is closed as phase-1, phase-2 or a load-then-store tree
(`LRStoreShape`, its location found by unification). -/
macro "dirs_lrX " p:ident : tactic => `(tactic| (
  refine Kraken.Promising.X64.EnvG.dirsLRX_layout (p := $p) ?_
  intro d hd e z s pc
  cells_lrX $p hd))

/-! ## The environment and the invariant -/

/-- **`EnvGLR` for x64**, restricted to the shared layout `S`. -/
abbrev EnvGLRX (A : Arch) (tid : Nat) (pl : Plan) (S : SharedEnv.Layout) : SharedEnv :=
  (Kraken.Promising.SLR.EnvGLR isa A tid pl).within S

/-- **The thread-local invariant of `EnvGLR`, x64** (`QX64` with `EnvGLRX`). -/
def QX64LR (A : Arch) (tid : Nat) (pl : Plan) (S : SharedEnv.Layout) (e : Kraken.Executable Directive)
    (endPc : Int64) (post : MachineState × EStateX → Prop) (st : State) (σ : EStateX) : Prop :=
  st.exe = e ∧ st.decls = {} ∧ st.endPc = endPc ∧ Split S st.st.1.dmem ∧
    Safely (e.instrStepEnv (EnvGLRX A tid pl S)) post (st.st, σ)

/-! ## The link -/

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout} {e : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateX → Prop}

/-- The link step at `QX64LR` (`link_QX64`'s proof). -/
theorem link_QX64LR (hS : Le16 S) (hpost : ∀ y, post y → y.1.2 = endPc) :
    ∀ (J : TreeJLive (Kraken.Promising.SLR.EnvGLR isa A tid pl) isa.State) st σ tree,
      QX64LR A tid pl S e endPc post st σ → isa.exec st = some tree →
      (∀ st' σ', QX64LR A tid pl S e endPc post st' σ' → J.Post st' σ') → J.W tree σ := by
  intro J st σ tree h hex hJ
  obtain ⟨he, hds, hend, hs, hsafe⟩ := h
  rcases hsafe.unfold with hp | ⟨R, hR, hk⟩
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · exact exec_treeJLive_of_instrStepEnvW J hS he hds hs hR
      (fun m g' hz hs' => hJ _ _ ⟨he, hds, hend, hs', hk _ hz⟩) tree hex

/-- **The `EnvGLR` link hypotheses at `QX64LR`.** -/
theorem linkHypsLR_QX64 (hpl : pl.Valid) (hS : Le16 S) (hshape : LRTreeX A e)
    (hpost : ∀ y, post y → y.1.2 = endPc) : LinkHypsLR (I := isa) A tid pl (QX64LR A tid pl S e endPc post) where
  valid := hpl
  shape st _ h tree hex := hshape st h.1 h.2.1 tree hex
  link := link_QX64LR hS hpost

omit [Kraken.Executable.ValidLayout e] in
/-- **`done` at `QX64LR`** (`post_of_halted_QX64`). -/
theorem post_of_halted_QX64LR (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGLRX A tid pl S) x R)
    {t : Thread isa} {σ : EStateX} (hQ : QX64LR A tid pl S e endPc post t.st σ) (hh : t.halted = true) :
    post (t.st.st, σ) := by
  obtain ⟨he, -, hend, -, hsafe⟩ := hQ
  exact post_of_halted_env hstuck he hend hsafe hh

/-- **`ThreadRuleRX.ofSafelyEnvGLRX`**: the x64 rule link of `EnvGLR`
(`ofSafelyEnvGX` with `EnvGLRX` and `LRTreeX`). A thread whose trees are
phase-1, phase-2 or load-then-store, proved by a `Safely` judgment of
`EnvGLRX A tid pl S`, satisfies `ThreadRuleRX A B tid` for every `B` that
`post` gives at a halted thread with no promise. -/
def _root_.Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvGLRX
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : LRTreeX A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGLRX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRX A B tid :=
  ThreadRuleRX.ofEnvGLR (linkHypsLR_QX64 (tid := tid) hpl hS hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QX64LR hstuck hQ hh) hp hrel hcl

/-- **`NPSafe` from a `Safely` judgment of `EnvGLRX`**. -/
theorem npSafe_of_safelyEnvGLRX {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : LRTreeX A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGLRX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvGLR (I := isa) A tid pl (QX64LR A tid pl S e endPc post) cl c r g) :
    NPSafe (model isa) A B tid n m cl c r g :=
  NPSafe.of_ruleRX (ThreadRuleRX.ofSafelyEnvGLRX hpl hS hshape hpost hstuck hB) n m cl c r g h

/-- **Every tree from a `QX64LR`-state is fault-free**, for fault-free code. -/
theorem noFault_QX64LR (hnf : DirsNoFault e) (hpost : ∀ y, post y → y.1.2 = endPc) :
    ∀ st σ tree, QX64LR A tid pl S e endPc post st σ → isa.exec st = some tree → tree.NoFault := by
  intro st σ tree h hex
  obtain ⟨he, hds, hend, -, hsafe⟩ := h
  rcases hsafe.unfold with hp | -
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · exact noFault_of_exec he hds hnf tree hex

/-- **The x64 `EnvGLR` no-fault rule** for fault-free code, unconditional in
the thread's promises. -/
theorem noFaultRule_ofSafelyEnvGLRX_struct {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hS : Le16 S) (hshape : LRTreeX A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGLRX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) :
    NoFaultRule (ThreadRuleRX.ofSafelyEnvGLRX hpl hS hshape hpost hstuck hB) :=
  noFaultRule_ofEnvGLR_struct _ _ (noFault_QX64LR hnf hpost)

end Link

/-! ## From `vcgen` triples to `QX64LR` -/

section Triple

variable {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout}

/-- **`QX64LR` from a partial triple** in `EnvGLRX` (`qx64_of_partialTripleEnv`). -/
theorem qx64LR_of_partialTripleEnv [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Kraken.Executable.ValidLayout (layout p)] {P Q : MachineData → EStateX → Prop}
    {E : Int64 → MachineData → EStateX → Prop} (ht : MachineWP.PartialTripleEnv (EnvGLRX A tid pl S) P p Q E)
    (henv : cenv = layout p) {st : State} (he : st.exe = layout p) (hds : st.decls = {})
    (hend : st.endPc = (layout p).addrOf p.length) (hpc : st.st.2 = (layout p).addrOf 0)
    (hs : Split S st.st.1.dmem) {σ : EStateX}
    (hP : P st.st.1 σ) (hE : ∀ a s g, ¬ E a s g := by simp) :
    QX64LR A tid pl S (layout p) ((layout p).addrOf p.length) (postOfX p Q) st σ := by
  refine ⟨he, hds, hend, hs, ?_⟩
  have hst : st.st = (st.st.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hpc, Executable.addrOf_zero, Layout.apply_fst]
  rw [hst]
  exact (Program.instrStepEnv_of_partialTripleEnv ht hP henv).mono fun _ h => h.imp id (hE _ _ _)

end Triple

/-! ## The initial state -/

section Init

variable {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout}

/-- **`CoreAtLR` at a thread's start** (`coreAtX_init`'s proof). -/
theorem coreAtLRX_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = []) :
    CoreAtLR A tid pl True (Config.init ss m) r g (σInitX (Config.init ss m) r g) (Thread.init s) := by
  have ht : (Config.init ss m : Config isa).threads[tid]? = some (Thread.init s) := by simp [Config.init, hs]
  refine ⟨⟨ht, SnapLe.refl _ _, Ghost.Le.refl g, ?_, Config.init_bnd ss m tid _ ht,
    .inl ⟨rfl, fun _ h => (by cases h)⟩, fun _ => trivial, ⟨fun h => (by cases h), fun h => (by cases h)⟩⟩,
    fun ts h => (by rw [hpend] at h; cases h), fun ts _ _ h => (by cases h)⟩
  refine ⟨fun l => by simp [σInitX, Thread.init, Views.getCoh], Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
    Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, fun l => ?_, ?_⟩ <;>
    simp [σInitX, Thread.init, Views.getFwd, Sim.FwdLe, Sim.XclLe]

/-- **The `EnvGLR` rule's invariant at the initial configuration** from
`QX64LR` at `σInitX` (`invGX_init`). -/
theorem invGLRX_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = []) {e : Kraken.Executable Directive} {endPc : Int64}
    {post : MachineState × EStateX → Prop}
    (hQ : QX64LR A tid pl S e endPc post s (σInitX (Config.init ss m) r g)) :
    InvGLR (I := isa) A tid pl (QX64LR A tid pl S e endPc post) True (Config.init ss m) r g :=
  ⟨_, _, coreAtLRX_init hs hpend, hQ⟩

end Init

end Kraken.Promising.X64.EnvG
