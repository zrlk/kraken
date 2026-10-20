/-
Termination on the Promising machine through the environment, x64 (design note
`Kraken/Promising/EnvWP.md`,
"Termination").

`env_link_halt` constrains the promise-free runs that reach `endPc`; it says
nothing about runs that never get there. From a *total* environment judgment
(`Eventually (instrStepEnv (lastWrite L)) P` from the start) this file proves
two statements about the promise-free one-thread machine (`fuel` arbitrary:
it does not affect a promise-free step, `Kraken.Promising.SeqLinkTerm`):

- `env_link_no_div` (no hypothesis beyond `env_link_halt`'s, minus `hstop`):
  `Eventually (StepPF A fuel) (EndIn L endPc P)` from the start
  configuration. Every maximal promise-free run either reaches a
  configuration whose thread is at `endPc` with `P` holding (for an
  environment state related to the memory), or **stops** before (has no
  promise-free successor). There is no infinite promise-free run, and some
  `n` bounds the length of every run before it reaches `endPc` or stops
  (`eventually_stepPF_bounded`). A stopped run is one whose thread faults: the
  adapter turns an `undefined` register/flags value, or a line-crossing vector
  piece, into `.fault`, while `AllEnv` lets the value be arbitrary.
- `env_link_terminates`: with `hstuck` (no environment step at `endPc`, as
  `env_link_halt_safe`) and `DirsNoFault e` (the adapter's tree of every
  directive of the text has no fault leaf), `Eventually (StepPF' A fuel)
  (EndIn L endPc P)`: every maximal promise-free run is finite and ends at
  `endPc` in `P`; none stops before. `DirsNoFault` is per directive and
  independent of the judgment; `dirNoFault_*` below discharge it for the
  instructions of the examples.
-/
import Kraken.Promising.EnvLinkSafeX64
import Kraken.Promising.SeqLinkTerm

open Kraken

namespace Kraken.Promising.X64

/-- The thread of the one-thread configuration `c` is at `endPc`, and `P`
holds of its state with an environment state related to the memory. -/
def EndIn (L : SharedLayout) (endPc : Int64) (P : MachineState × (SharedEnv.lastWrite L).State → Prop)
    (c : Config isa) : Prop :=
  ∃ t', c.threads = #[t'] ∧ t'.st.st.2 = endPc ∧ ∃ g', envRel L g' c.mem ∧ P ((t'.st.st.1, endPc), g')

/-- The adapter's event tree of the directive `d` of size `z`, run at `pc`
with the continuations `Executable.step` gives it, has no fault leaf, from
every machine state. -/
def DirNoFault (e : _root_.Executable) (d : Directive) (z : Nat) : Prop :=
  ∀ (s : MachineData) (pc : Int64),
    (toEv {} (@Directive.interp (_root_.Executable.labels e) d s (.mk pc (pc + .ofNat z))
      (fun s' => .done (s', pc + .ofNat z)) (fun pc' s' => .done (s', pc')))).NoFault

/-- Every directive of the text has a fault-free tree. -/
def DirsNoFault (e : _root_.Executable) : Prop :=
  ∀ d z, (d, z) ∈ e.2 → DirNoFault e d z

/-- **No divergence through the environment.** A total judgment in the
`lastWrite` environment about the thread's split start state, with the
environment state holding the memory's initial values: every maximal
promise-free run of the one-thread machine reaches `endPc` with `P` holding,
or stops before (no promise-free successor; e.g. the thread faults on an
`undefined` value). -/
def EnvLinkNoDiv : Prop :=
  ∀ [_root_.Layout] (L : SharedLayout) (e : Kraken.Executable Directive) [Kraken.Executable.ValidLayout e],
    L.WF →
    ∀ (A : Arch) (fuel : Nat) (endPc : Int64) (showPc : Int64 → String) (s : MachineData) (pc : Int64)
      (mem : Memory) (g : BitVec 64 → BitVec 128)
      (P : MachineState × (SharedEnv.lastWrite L).State → Prop),
      mem.msgs = #[] → (∀ k, L.Covers k → s.dmem.get? k = none) → envRel L g mem →
      (∀ x, P x → x.1.2 = endPc) →
      Eventually (e.instrStepEnv (SharedEnv.lastWrite L)) P ((s, pc), g) →
      Eventually (StepPF A fuel) (EndIn L endPc P)
        ⟨#[Thread.init ({ exe := e, endPc, st := (s, pc), showPc } : State)], mem⟩

/-- **Termination through the environment.** `EnvLinkNoDiv`, and no run
stops before `endPc`, given that there is no environment step at `endPc`
(`hstuck`) and the text's trees are fault-free (`DirsNoFault`). -/
def EnvLinkTerminates : Prop :=
  ∀ [_root_.Layout] (L : SharedLayout) (e : Kraken.Executable Directive) [Kraken.Executable.ValidLayout e],
    L.WF →
    ∀ (A : Arch) (fuel : Nat) (endPc : Int64) (showPc : Int64 → String) (s : MachineData) (pc : Int64)
      (mem : Memory) (g : BitVec 64 → BitVec 128)
      (P : MachineState × (SharedEnv.lastWrite L).State → Prop),
      mem.msgs = #[] → (∀ k, L.Covers k → s.dmem.get? k = none) → envRel L g mem →
      (∀ x, P x → x.1.2 = endPc) →
      (∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (SharedEnv.lastWrite L) x R) →
      DirsNoFault e →
      Eventually (e.instrStepEnv (SharedEnv.lastWrite L)) P ((s, pc), g) →
      Eventually (StepPF' A fuel) (EndIn L endPc P)
        ⟨#[Thread.init ({ exe := e, endPc, st := (s, pc), showPc } : State)], mem⟩

/-- The start of both links: the thread's start state is related to the split
start state. -/
private theorem relEnv_start {L : SharedLayout} (hL : L.WF) {e : _root_.Executable} {endPc : Int64}
    {showPc : Int64 → String} {s : MachineData} {pc : Int64} {mem : Memory} {g : BitVec 64 → BitVec 128}
    (hsplit : ∀ k, L.Covers k → s.dmem.get? k = none) (henv : envRel L g mem) :
    RelEnv L e endPc (({ exe := e, endPc, st := (s, pc), showPc } : State), mem) ((s, pc), g) := by
  obtain ⟨D, hpriv, hsh⟩ := exists_merge hL g s.dmem L fun _ h => h
  have hmr : MergeRel L s.dmem g D := ⟨hpriv, hsplit, hsh⟩
  have hrel : MemRel L s.dmem mem D := (memRel_iff_mergeRel L s.dmem D mem g hL henv).mpr hmr
  obtain ⟨r, z, f, d⟩ := s
  exact ⟨(⟨r, z, f, D⟩, pc), ⟨rfl, rfl, rfl, rfl, rfl, rfl, hrel, rfl⟩, ⟨rfl, rfl, rfl, rfl, hmr⟩⟩

/-- The end of both links: a configuration related to a `P` state is `EndIn`. -/
private theorem endIn_of_rel {L : SharedLayout} {e : _root_.Executable} {endPc : Int64}
    {P : MachineState × (SharedEnv.lastWrite L).State → Prop} (hPend : ∀ x, P x → x.1.2 = endPc)
    {c : Config isa}
    (h : ∃ t' y', c.threads = #[t'] ∧ t'.Seq 0 c.mem ∧ RelEnv L e endPc (t'.st, c.mem) y' ∧ P y') :
    EndIn L endPc P c := by
  obtain ⟨t', ⟨⟨zs, zpc⟩, zg⟩, ht, -, hz, hP⟩ := h
  obtain ⟨h1, h2, h3⟩ := hz.split
  have hpc : zpc = endPc := hPend _ hP
  simp only at h1 h2 h3 hpc
  subst h1 h2
  refine ⟨t', ht, hpc, zg, h3, ?_⟩
  rw [← hpc]
  exact hP

theorem env_link_no_div : EnvLinkNoDiv := by
  intro _ L e _ hL A fuel endPc showPc s pc mem g P hm hsplit henv hPend hev
  exact eventually_weaken _ _ _ _ (fun _ h => endIn_of_rel hPend h)
    (reachablePF_sim_noDiv A fuel (seqSim_env hL e endPc) hm (relEnv_start hL hsplit henv) hev)

/-- At a thread state related to a split state with an environment step, the
thread's instruction tree is the adapter's tree of the directive at the pc. -/
theorem exec_of_instrStepEnv [_root_.Layout] {L : SharedLayout} {e : Kraken.Executable Directive}
    [Kraken.Executable.ValidLayout e] {endPc : Int64} {x : State × Memory}
    {z : MachineState × (SharedEnv.lastWrite L).State} {R : MachineState × (SharedEnv.lastWrite L).State → Prop}
    (hxz : RelEnv L e endPc x z) (hne : x.1.st.2 ≠ endPc)
    (h : e.instrStepEnv (SharedEnv.lastWrite L) z R) :
    ∃ d sz, (d, sz) ∈ e.2 ∧ isa.exec x.1 = some ((toEv {} (@Directive.interp (_root_.Executable.labels e) d
      x.1.st.1 (.mk x.1.st.2 (x.1.st.2 + .ofNat sz)) (fun s' => .done (s', x.1.st.2 + .ofNat sz))
      (fun pc' s' => .done (s', pc')))).map fun st => { x.1 with st }) := by
  obtain ⟨d, sz, rest, hcode, -⟩ := h
  obtain ⟨-, hpc, -⟩ := hxz.split
  obtain ⟨y, ⟨he, hend, -, -, -, -, -, hds⟩, -⟩ := hxz
  rw [hpc] at hcode
  obtain ⟨ls, hat, hls⟩ := directivesAtAddress_of_codeAt hcode
  refine ⟨d, sz, mem_of_mem_directivesAtAddress (a := x.1.st.2) (by rw [hat]; simp), ?_⟩
  obtain ⟨⟨exe, endPc', ⟨s, pc⟩, showPc, decls⟩, m⟩ := x
  simp only at he hend hds hne hcode hat ⊢
  subst he hend hds
  have hdir : ({ exe, endPc := endPc', st := (s, pc), showPc, decls := {} } : State).directive = some d := by
    unfold State.directive
    simp only
    rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress exe pc) = Kraken.Executable.codeAt exe pc from by
      unfold Kraken.Executable.codeAt
      congr 1, hcode]
    rfl
  have hpc' : (pc == endPc') = false := by simpa using hne
  simp only [isa, exec, hdir, hpc', Option.isNone_some, Bool.or_false, Bool.false_eq_true, ite_false]
  congr 2
  unfold Executable.step
  letI := Executable.labels exe
  simp only
  rw [hat, Directives.interp_label_prefix ls _ _ _ _ hls]
  simp only [Directives.interp]

theorem env_link_terminates : EnvLinkTerminates := by
  intro _ L e _ hL A fuel endPc showPc s pc mem g P hm hsplit henv hPend hstuck hnf hev
  refine eventually_weaken _ _ _ _ (fun _ h => endIn_of_rel hPend h)
    (reachablePF_sim_term A fuel (seqSim_env hL e endPc) ?_ hm (relEnv_start hL hsplit henv) hev)
  intro x z R hxz hT
  have hne : x.1.st.2 ≠ endPc := by
    intro h
    exact hstuck z R (hxz.split.2.1.trans h) hT
  obtain ⟨d, sz, hmem, hex⟩ := exec_of_instrStepEnv hxz hne hT
  exact ⟨_, hex, (EvTree.seqOk_map 0 _ _ _).mpr ((hnf d sz hmem x.1.st.1 x.1.st.2).seqOk 0 _)⟩

/-! ## Discharging `DirsNoFault` -/

/-- The directives of a laid-out program are the program's. The hypothesis
is for every executable (only its label table matters), so that a proof of
it never computes the layout. -/
theorem dirsNoFault_layout [layout : _root_.Layout] {p : Program}
    (h : ∀ d ∈ p, ∀ (e : _root_.Executable) z, DirNoFault e d z) : DirsNoFault (layout p) := by
  intro d z hm
  obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact h _ (List.getElem_mem hi) _ _

set_option hygiene false in
/-- `dirs_no_fault p` proves `DirsNoFault (layout p)` for a program `p` (a
definition) whose instructions emit no `undefined` value of a register,
vector or flags type and no vector piece access: one `simp` per directive
through the instruction semantics and `toEv`, splitting on whether an
access is mapped. A flag test that `split` and `simp` leave (`je`'s
`CondCode.interp` decidability instance) is closed by `prop_ite`
(the x64 Treiber proof's `dirs_no_faultX` steps, shared; each first `simp`
is under `try`). (Unhygienic, with qualified names: the hygienic expansion
of the `simp` calls runs into a `whnf` timeout.) -/
macro "dirs_no_fault " p:ident : tactic => `(tactic| (
  refine Kraken.Promising.X64.dirsNoFault_layout (p := $p) ?_
  intro d hd e z s pc
  simp only [$p:ident, List.mem_cons, List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals try simp [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    Kraken.Promising.X64.toEv, Kraken.Promising.EvTree.NoFault, _root_.MachineData.load, _root_.MachineData.store,
    _root_.MachineData.rmwK, _root_.RegOrMem.interp, _root_.Operand.interp, _root_.MachineData.set,
    _root_.RegOrMem.rmw, Kraken.Promising.EvTree.access_empty, _root_.RelRegOrMem.interp]
  all_goals (repeat' (first | split |
    simp [Kraken.Promising.X64.toEv, Kraken.Promising.EvTree.NoFault, Kraken.Promising.EvTree.access_empty]))
  all_goals try (refine Kraken.Promising.prop_ite (P := fun x =>
                Kraken.Promising.EvTree.NoFault (Kraken.Promising.X64.toEv {} x)) ?_ ?_ <;>
    simp [Kraken.Promising.X64.toEv, Kraken.Promising.EvTree.NoFault])))

end Kraken.Promising.X64
