/-
Whole-thread environment (`EnvG`)P2: **the bridge from `vcgen`
triples to `ThreadRuleRX.ofSafelyEnvG`** (AArch64, reusable for every
program).

- `qa64_of_partialTripleEnv`: a `PartialTripleEnv` in `EnvGA A tid pl` of a
  laid-out program `p` (a total `TripleEnv` through `TripleEnv.partial`)
  gives `QA64` at a thread state at the start of `p` (the pattern of
  `InvLinkAArch64.ThreadSpec.ofTripleEnv_holds`); the postcondition is
  `postOf p Q`: the end of the text and `Q`.
- `coreAt_init`, `invG_init`: the rule's invariant at `Config.init` from
  `QA64` at the start env state `σInit` (the initial configuration as the
  anchor, the initial thread's views, no pending mark).
- **The phase-1 shape check** `Phase1Tree A e` (a hypothesis of
  `ofSafelyEnvG`), per directive like `DirsNoFault`: `DirsPhase1 A e`
  (`phase1Tree_of_dirs`, through `tree_of_codeAt`: a per-directive property
  closed under `EvTree.map` holds of every tree of a thread running `e`),
  discharged by the `dirs_phase1 p` tactic (one `simp` per directive through
  the instruction semantics and `toEv`, as `dirs_no_fault`). `DirsPhase1`
  is `Phase1Tree` read per code cell, at every machine state and pc; it
  rejects exactly the cells some state of which has a multi-access,
  non-deterministic-access or release-RMW tree.

- `dirs_no_fault' p`: an alias of `dirs_no_fault` (which now unfolds the
  store addressing; it used to leave a plain `STR` goal open).

No fault: `noFaultRule_ofSafelyEnvG_struct` (`EnvG/A64Answers.lean`).

Phase-1 limits apply (single-access trees, read-side acquire only, releases
are stores).
-/
import Kraken.Promising.SLR.EnvG.A64NoFault
import Kraken.AArch64.EnvCfg
import Kraken.Promising.SLR.EnvG.TreeMap

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## Tree shapes along `EvTree.map`: `EnvG/TreeMap.lean` (moved there) -/

/-! ## The thread's tree is a code cell's tree -/

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

/-- A per-directive property `Pd e d z` of the code that holds of the
adapter's tree at every code cell holds of every tree of a thread running
`e` with no declarations (the argument of `noFault_of_codeAt`). -/
theorem tree_of_codeAt {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
    {Φ : ∀ {σ : Type}, EvTree σ → Prop} (hmap : ∀ {σ τ : Type} (f : σ → τ) (t : EvTree σ), Φ t → Φ (t.map f))
    (hd : ∀ d z, (d, z) ∈ e.2 → ∀ (s : MachineData) (pc : Int64),
      Φ (toEv {} (@Directive.interp (_root_.Executable.labels e) d s (.mk pc (pc + .ofNat z))
        (fun s' => .done (s', pc + .ofNat z)) (fun pc' s' => .done (s', pc')))))
    {st : State} (he : st.exe = e) (hds : st.decls = {}) {tree : EvTree State} (htree : isa.exec st = some tree) :
    Φ tree := by
  obtain ⟨d, z, rest, hcode⟩ := codeAt_of_exec htree
  have hmem := mem_of_codeAt hcode
  rw [he] at hcode hmem
  obtain ⟨ls, hat, hls⟩ := directivesAtAddress_of_codeAt hcode
  obtain ⟨exe, endPc, ⟨s, pc⟩, showPc, decls⟩ := st
  simp only at he hds hcode hat ⊢
  subst he hds
  have hdir : ({ exe, endPc, st := (s, pc), showPc, decls := {} } : State).directive = some d := by
    unfold State.directive
    simp only
    rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress exe pc) = Kraken.Executable.codeAt exe pc from by
      unfold Kraken.Executable.codeAt
      congr 1, hcode]
    rfl
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

/-! ## The phase-1 shape, per directive -/

/-- The adapter's tree of the directive `d` of size `z` is phase-1, from
every machine state and pc (as `DirNoFault`). -/
def DirPhase1 (A : Arch) (e : _root_.Executable) (d : Directive) (z : Nat) : Prop :=
  ∀ (s : MachineData) (pc : Int64),
    Phase1Shape A (toEv {} (@Directive.interp (_root_.Executable.labels e) d s (.mk pc (pc + .ofNat z))
      (fun s' => .done (s', pc + .ofNat z)) (fun pc' s' => .done (s', pc'))))

/-- Every directive of the text has a phase-1 tree. -/
def DirsPhase1 (A : Arch) (e : _root_.Executable) : Prop :=
  ∀ d z, (d, z) ∈ e.2 → DirPhase1 A e d z

/-- **`Phase1Tree` from the per-directive check.** -/
theorem phase1Tree_of_dirs {A : Arch} {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
    (h : DirsPhase1 A e) : Phase1Tree A e :=
  fun _ he hds _ htree => tree_of_codeAt (Φ := Phase1Shape A) (fun f _ ht => phase1Shape_map f ht)
    (fun d z hm => h d z hm) he hds htree

/-- The directives of a laid-out program are the program's (as
`dirsNoFault_layout`). -/
theorem dirsPhase1_layout [layout : _root_.Layout] {A : Arch} {p : Program}
    (h : ∀ d ∈ p, ∀ (e : _root_.Executable) z, DirPhase1 A e d z) : DirsPhase1 A (layout p) := by
  intro d z hm
  obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact h _ (List.getElem_mem hi) _ _

set_option hygiene false in
/-- `dirs_phase1 p` proves `DirsPhase1 A (layout p)` for a program `p` (a
definition) whose instructions make at most one access, deterministically,
with no release-kind RMW: one `simp` per directive, as `dirs_no_fault`. -/
macro "dirs_phase1 " p:ident : tactic => `(tactic| (
  refine Kraken.Promising.AArch64.EnvG.dirsPhase1_layout (p := $p) ?_
  intro d hd e z s pc
  simp only [$p:ident, List.mem_cons, List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals simp [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    Kraken.Promising.AArch64.toEv, Kraken.Promising.SLR.EnvG.Phase1Shape, Kraken.Promising.SLR.EnvG.DetAccess,
    Kraken.Promising.SLR.EnvG.SingleAccessS, Kraken.Promising.SLR.EnvG.AccessFree,
    _root_.MachineData.load, _root_.MachineData.store,
    _root_.MachineData.loadK, _root_.MachineData.storeK, _root_.MachineData.rmwK,
    _root_.MachineData.setRegOrZr, _root_.MachineData.setRegOrSp, _root_.RegOrSp.interpBase,
    _root_.AddrExpr.checkSPAlignment, _root_.AddrExpr.interpLoad, _root_.AddrExpr.interpStore,
    _root_.UnscaledAddrExpr.interpStore,
    _root_.UnscaledAddrExpr.checkSPAlignment, _root_.UnscaledAddrExpr.interpLoad,
    _root_.Literal.interpLoad, _root_.AddrOrLit.interpLoad,
    Kraken.Promising.EvTree.access_empty]
  all_goals (repeat' (first | split |
    simp [Kraken.Promising.AArch64.toEv, Kraken.Promising.SLR.EnvG.Phase1Shape, Kraken.Promising.SLR.EnvG.DetAccess,
      Kraken.Promising.SLR.EnvG.SingleAccessS, Kraken.Promising.SLR.EnvG.AccessFree,
      Kraken.Promising.EvTree.access_empty]))))

/-- `dirs_no_fault' p`: an alias of `dirs_no_fault p` (`EnvLinkTermAArch64.lean`),
which now unfolds the store addressing (`AddrExpr.interpStore`,
`UnscaledAddrExpr.interpStore`) too; it used to leave a plain `STR` unsolved. -/
macro "dirs_no_fault' " p:ident : tactic => `(tactic| dirs_no_fault $p)

/-! ## From `vcgen` triples to `QA64` -/

section Triple

variable {A : Arch} {tid : Nat} {pl : Plan}

/-- The postcondition `Program.instrStepEnv_of_(partial)tripleEnv` gives with
no exceptional exit: the end of `p`'s text and `Q`. -/
def postOf [layout : _root_.Layout] (p : Program) (Q : MachineData → EStateA → Prop) :
    MachineState × EStateA → Prop :=
  fun x => (x.1.2 = (layout p).addrOf p.length ∧ Q x.1.1 x.2) ∨ False

theorem postOf_end [layout : _root_.Layout] {p : Program} {Q : MachineData → EStateA → Prop} :
    ∀ y, postOf p Q y → y.1.2 = (layout p).addrOf p.length :=
  fun _ h => h.elim And.left False.elim

/-- **`QA64` from a partial triple** at a thread state at the start of `p`,
whose exceptional exit `E` never holds. -/
theorem qa64_of_partialTripleEnv [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Kraken.Executable.ValidLayout (layout p)] {P Q : MachineData → EStateA → Prop}
    {E : Int64 → MachineData → EStateA → Prop} (ht : MachineWP.PartialTripleEnv (EnvGA A tid pl) P p Q E)
    (henv : cenv = layout p) {st : State} (he : st.exe = layout p) (hds : st.decls = {})
    (hend : st.endPc = (layout p).addrOf p.length) (hpc : st.st.2 = (layout p).addrOf 0) {σ : EStateA}
    (hP : P st.st.1 σ) (hE : ∀ a s g, ¬ E a s g := by simp) :
    QA64 A tid pl (layout p) ((layout p).addrOf p.length) (postOf p Q) st σ := by
  refine ⟨he, hds, hend, ?_⟩
  have hst : st.st = (st.st.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hpc, Executable.addrOf_zero, Layout.apply_fst]
  rw [hst]
  exact (Program.instrStepEnv_of_partialTripleEnv ht hP henv).mono fun _ h => h.imp id (hE _ _ _)

end Triple

/-! ## The initial state -/

section Init

variable {A : Arch} {tid : Nat} {pl : Plan}

/-- **The env state at a thread's start**: the configuration as the anchor,
the initial thread's views, resource `r`, ghost `g`. -/
def σInit (c : Config isa) (r : Res) (g : Ghost) : EStateA := { snap := c, vs := {}, r, g, cl := True }

/-- **The invariant core at the initial configuration**, with no pending
mark. -/
theorem coreAt_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = []) :
    CoreAt A tid pl True (Config.init ss m) r g (σInit (Config.init ss m) r g) (Thread.init s) := by
  have ht : (Config.init ss m : Config isa).threads[tid]? = some (Thread.init s) := by simp [Config.init, hs]
  refine ⟨⟨ht, SnapLe.refl _ _, Ghost.Le.refl g, ?_, Config.init_bnd ss m tid _ ht,
    .inl ⟨rfl, fun _ h => (by cases h)⟩, fun _ => trivial, ⟨fun h => (by cases h), fun h => (by cases h)⟩⟩,
    fun ts h => (by rw [hpend] at h; cases h), fun ts _ _ h => (by cases h)⟩
  refine ⟨fun l => by simp [σInit, Thread.init, Views.getCoh], Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
    Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, fun l => ?_, ?_⟩ <;>
    simp [σInit, Thread.init, Views.getFwd, Sim.FwdLe, Sim.XclLe]

/-- **The rule's invariant at the initial configuration** from `QA64` at
`σInit`. -/
theorem invG_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = []) {e : Kraken.Executable Directive} {endPc : Int64}
    {post : MachineState × EStateA → Prop} (hQ : QA64 A tid pl e endPc post s (σInit (Config.init ss m) r g)) :
    InvG (I := isa) A tid pl (QA64 A tid pl e endPc post) True (Config.init ss m) r g :=
  ⟨_, _, coreAt_init hs hpend, hQ⟩

end Init

end Kraken.Promising.AArch64.EnvG
