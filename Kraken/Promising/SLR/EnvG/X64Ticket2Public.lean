/-
**`counter = N` for the x64 ticket lock
with an unlocked release, verbatim** (`X64/ticketlock2.kl`'s worker as
written: `EnvG/X64Ticket2VCGen.lean`), with no declarations
(`ticket2_counter_envG_verbatim`) and with the `.kl` runner's strict sized
declarations (`ticket2_counter_envG_runner`).

The release `incl (owner)` is a plain load and a plain store, not an atomic
increment, so the dispenser route of `ticketlock3.kl`
(`EnvG/TicketXPublic.lean`) does not apply. The proof tracks per thread the
timestamps of its accesses (`EnvG/TicketX2Env.lean`, `TicketX2Reach.lean`,
`TicketX2Final.lean`):

- **Specification** (`SpTk2`): `QX64MD ds (tk2Env x o c) (tkS x o c) e e
  (labTk2 "done") postTk2` (`EnvG/X64DeclsLink.lean`): the image, the
  declarations, the end, the split private memory, and the `Safely` run of
  the worker in the protocol environment `tk2Env` (phase `6` at `done`).
- **One instruction** (`treeJ_of_QX64MD`, `runOK_of_QX64MD`): from
  `QX64MD` every tree of the thread satisfies a tree judgment with leaves at
  `QX64MD` (through `exec_treeJ_of_instrStepEnv` and, for strict sized
  declarations, `exec_treeJ_of_underDecls`, as `TicketX.dispSpecX_stepD`); at
  `TreeJ.runJ` of a `RunSim` it is `RunOK`, and with `runSim` this is
  `StepOK` (`stepOK_tk2`).
- **Start** (`spTk2_start`): `tk2WorkerV_envG` uncounted.
- **Final** (`ticket2_counter_envG_of`): `inv_reachable` gives every thread
  of a reachable configuration a protocol state with `SpTk2` and `JTk`; at a
  final configuration each thread is halted (`post_of_halted_QX64MD`: phase
  `6`) with no promise, which is `FinW`, and `FinW.finalVal` is the counter.
-/
import Kraken.Promising.SLR.EnvG.X64Ticket2VCGen
import Kraken.Promising.SLR.EnvG.TicketX2Reach

namespace Kraken.Promising.X64.EnvG.TicketX2

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvSpike Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.EnvG.TicketX2
open Kraken.Promising.X64.EnvG.TicketX (tkS FrameTk tkS_le16)

/-! ## One instruction -/

-- `treeJ_of_QX64MD` (same name) moved to `EnvG/X64DeclsLink.lean`.

/-- **One instruction from `QX64MD`, as a `RunOK` tree**: under a per-access
simulation `RunSim` of `E`, every tree of a thread at `QX64MD` keeps `JC`
and ends at `QX64MD` again (`treeJ_of_QX64MD` at `TreeJ.runJ`). -/
theorem runOK_of_QX64MD {tid : Nat} {E : SharedEnv} {JC : E.State → Ctx → Prop} (hR : RunSim Arch.tso tid E JC)
    {ds : Decls} (hsz : ds.Sized ∨ ds = {}) {S : SharedEnv.Layout} (hS : Le16 S) {e : Kraken.Executable Directive}
    [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × E.State → Prop}
    (hpost : ∀ y, post y → y.1.2 = endPc) {st : State} {g : E.State} (h : QX64MD ds E S e e endPc post st g)
    (tree : EvTree State) (hex : isa.exec st = some tree) :
    RunOK Arch.tso tid JC (fun s g' => QX64MD ds E S e e endPc post s g') tree g :=
  treeJ_of_QX64MD (TreeJ.runJ hR (fun s g' => QX64MD ds E S e e endPc post s g')) hsz hS (fun _ _ h => h) hpost h
    tree hex

/-! ## The image -/

section Image

variable [layout : _root_.Layout] [Executable.ValidLayout (layout tk2ImageV)]

/-- The exit label `done` is the address of the trailer's first data cell. -/
theorem labTk2_done : labTk2 "done" = (layout tk2ImageV).addrOf 13 := by
  have hd : (_root_.Executable.labels (layout tk2ImageV)).label "done" = (layout tk2ImageV).addrOf 12 :=
    Program.label_addrOf_drop tk2ImageV_wf.nodup (by decide) (by decide)
  have h12 : (layout tk2ImageV).2[12]? = some (Directive.label "done", Kraken.Layout.size Directive 12) := by
    simp [Layout.apply_snd, Layout.frag, tk2ImageV, tk2WorkerV, tk2DataV]
  rw [Executable.addrOf_succ _ h12, Executable.ValidLayout.label_size 12 "done" _ h12]
  simpa using hd

/-- No instruction steps at the exit label. -/
theorem tk2ImageV_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labTk2 "done" → ¬ (layout tk2ImageV).instrStepEnv env x R := by
  rw [labTk2_done]
  exact not_instrStepEnv_of_byteArray (i := 13) (b := .mk #[]) env (by decide)

/-! ## The specification -/

/-- The worker's postcondition: the exit label and phase `6`. -/
abbrev postTk2 : MachineState × TkSt → Prop :=
  fun y => ∃ _ : Nat, (y.1.2 = labTk2 "done" ∧ y.2.k = 6) ∨ False

omit [Executable.ValidLayout (layout tk2ImageV)] in
theorem postTk2_end : ∀ y, postTk2 y → y.1.2 = labTk2 "done" :=
  fun _ ⟨_, h⟩ => h.elim And.left False.elim

/-- **The worker's specification** with declarations `ds`, on the words `x`,
`o`, `c`. -/
abbrev SpTk2 (ds : Decls) (x o c : BitVec 64) (_tid : Nat) (g : TkSt) (st : State) : Prop :=
  QX64MD ds (tk2Env x o c) (tkS x o c) (layout tk2ImageV) (layout tk2ImageV) (labTk2 "done") postTk2 st g

/-- **The specification's obligation `StepOK`** (`runOK_of_QX64MD` with
`runSim`). -/
theorem stepOK_tk2 {ds : Decls} (hsz : ds.Sized ∨ ds = {}) {x o c : BitVec 64} (hxo : x ≠ o) (hxc : x ≠ c)
    (hoc : o ≠ c) : @StepOK isa x o c (SpTk2 ds x o c) :=
  fun _ _ _ tree M0 h hex =>
    runOK_of_QX64MD (runSim hxo hxc hoc M0) hsz (tkS_le16 x o c) postTk2_end h tree hex

/-- A halted thread at the specification is in phase `6`. -/
theorem SpTk2.fin {ds : Decls} {x o c : BitVec 64} {tid : Nat} {g : TkSt} {t : Thread isa}
    (h : SpTk2 ds x o c tid g t.st) (hh : t.halted = true) : g.k = 6 := by
  obtain ⟨_, hp⟩ := post_of_halted_QX64MD (MaskOf.refl _) (tk2ImageV_stuck _) h hh
  exact (hp.resolve_right id).2

/-! ## The start -/

/-- **A verbatim `ticketlock2` worker at its start with declarations `ds`**,
as the `.kl` runner sets it up: the laid-out image, the pc at the entry label
`worker`, the end at the exit label `done`, and none of the three words in
the private memory. No register is constrained. -/
structure StartStateTk2 (ds : Decls) (s : State) : Prop where
  exe : s.exe = layout tk2ImageV
  decls : s.decls = ds
  pc : s.st.2 = (_root_.Executable.labels s.exe).label "worker"
  endPc : s.endPc = (_root_.Executable.labels s.exe).label "done"
  split : Split (tkS (symTk2 "next") (symTk2 "owner") (symTk2 "counter")) s.st.1.dmem

omit [Executable.ValidLayout (layout tk2ImageV)] in
theorem StartStateTk2.frame {ds : Decls} {s : State} (h : StartStateTk2 ds s) :
    FrameTk (symTk2 "next") (symTk2 "owner") (symTk2 "counter") s.st.1 :=
  ⟨h.split.loadInt_none (by simp) (by decide) (by decide), h.split.loadInt_none (by simp) (by decide) (by decide),
    h.split.loadInt_none (by simp) (by decide) (by decide)⟩

omit [Executable.ValidLayout (layout tk2ImageV)] in
theorem StartStateTk2.st {ds : Decls} {s : State} (h : StartStateTk2 ds s) : s.st = (s.st.1, labTk2 "worker") := by
  refine Prod.ext rfl ?_; rw [h.pc, h.exe]

omit [Executable.ValidLayout (layout tk2ImageV)] in
theorem StartStateTk2.end {ds : Decls} {s : State} (h : StartStateTk2 ds s) : s.endPc = labTk2 "done" := by
  rw [h.endPc, h.exe]

/-- **The specification at a start state**, in the initial protocol state
(`tk2WorkerV_envG`, uncounted). -/
theorem spTk2_start {ds : Decls} {tid : Nat} {s : State} (h : StartStateTk2 ds s) :
    SpTk2 ds (symTk2 "next") (symTk2 "owner") (symTk2 "counter") tid TkSt.start s := by
  refine ⟨h.exe, h.decls, h.end, h.split, ?_⟩
  rw [h.st]
  exact _root_.Safely.uncountEnv
    (tk2WorkerV_envG _ _ _ rfl rfl rfl s.st.1 (TkSt.start, 0) ⟨h.frame, rfl⟩)

/-! ## The theorems -/

/-- **`counter = N` for `N` verbatim `ticketlock2` workers with
declarations `ds`, strict sized or none** (the common proof of
`ticket2_counter_envG_verbatim` and `ticket2_counter_envG_runner`). -/
theorem ticket2_counter_envG_of {fuel : Nat} {ds : Decls} (hsz : ds.Sized ∨ ds = {}) (N : Nat)
    (hxo : Decls.overlaps (symTk2 "next") 4 (symTk2 "owner") 4 = false)
    (hxc : Decls.overlaps (symTk2 "next") 4 (symTk2 "counter") 4 = false)
    (hoc : Decls.overlaps (symTk2 "owner") 4 (symTk2 "counter") 4 = false) (hN32 : N + 1 < 2 ^ 32)
    {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, StartStateTk2 ds s) (hN : states.length = N)
    (hX0 : (Config.init states initMem).mem.initVal ⟨symTk2 "next", 4⟩ = 0)
    (hO0 : (Config.init states initMem).mem.initVal ⟨symTk2 "owner", 4⟩ = 0)
    (hC0 : (Config.init states initMem).mem.initVal ⟨symTk2 "counter", 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) cfg)
    (hf : cfg.final = true) :
    cfg.mem.finalVal ⟨symTk2 "counter", 4⟩ = BitVec.ofNat 128 N := by
  have hxo' : symTk2 "next" ≠ symTk2 "owner" := by intro h; rw [h] at hxo; simp [Decls.overlaps] at hxo
  have hxc' : symTk2 "next" ≠ symTk2 "counter" := by intro h; rw [h] at hxc; simp [Decls.overlaps] at hxc
  have hoc' : symTk2 "owner" ≠ symTk2 "counter" := by intro h; rw [h] at hoc; simp [Decls.overlaps] at hoc
  obtain ⟨hmsg, hini, hth⟩ := SLR.EnvG.TicketX2.inv_reachable (stepOK_tk2 hsz hxo' hxc' hoc')
    (SLR.EnvG.TicketX2.inv_init (initMem := initMem) fun _ s hs => spTk2_start (hst s (List.mem_of_getElem? hs))) hc
  have hsize : cfg.threads.size = N := by rw [SLR.Reachable.size_eq hc, SLR.Config.init_size, hN]
  -- each thread's final protocol state and history
  have hgh : ∀ j, ∃ gh : TkSt × Hist, j < N →
      gh.1.k = 6 ∧ (∃ V, Facts (symTk2 "next") (symTk2 "owner") (symTk2 "counter") j cfg.mem V gh.1 gh.2) ∧
        Bk j cfg.mem [] gh.1 gh.2 := by
    intro j
    by_cases hj : j < N
    · have ht : cfg.threads[j]? = some cfg.threads[j] := Array.getElem?_eq_getElem (by omega)
      obtain ⟨g, hSp, h, hF, hB⟩ := hth j _ ht
      have hp := Config.final_prom hf ht
      rw [hp] at hB
      exact ⟨(g, h), fun _ => ⟨hSp.fin (Config.final_halted hf ht), ⟨_, hF⟩, hB⟩⟩
    · exact ⟨(TkSt.start, ⟨0, 0, 0, 0, 0, 0, 0⟩), fun h => absurd h hj⟩
  have hiv : ∀ l, cfg.mem.initVal l = (Config.init states initMem).mem.initVal l := by
    intro l; unfold Memory.initVal; rw [hini]; rfl
  let F := fun j => Classical.choose (hgh j)
  have hF : ∀ j < N, _ := fun j => Classical.choose_spec (hgh j)
  exact FinW.finalVal (G := fun j => (F j).1) (H := fun j => (F j).2)
    { xo := hxo', xc := hxc', oc := hoc', bound := by omega
      x0 := (hiv _).trans hX0, o0 := (hiv _).trans hO0, c0 := (hiv _).trans hC0
      msg := fun ts m hg => hsize ▸ hmsg ts m hg
      fin := fun j hj => (hF j hj).1
      facts := fun j hj => (hF j hj).2.1
      bk := fun j hj => (hF j hj).2.2 }

/-- **`counter = N` for `N` x64 ticket lock workers running
`ticketlock2.kl`'s code verbatim, under `Arch.tso`**.

For every valid layout of the worker's image `tk2ImageV` (the `code` block,
then the `.kl` runner's data trailer that places the symbols `next`, `owner`
and `counter`), every number of threads `N` with `N + 1 < 2 ^ 32`, if the
symbols' 4-byte words are pairwise disjoint, `states` consists of `N`
threads each at the entry label `worker` with its end at `done`, no
declarations and none of the words in its private memory (`StartStateTk2 {}`;
no register is assumed), and the initial memory has the three words at `0`,
then every configuration `Reachable` under `Arch.tso` that is final has the
counter word at `N`.

The release is the unlocked `incl (owner)` (a plain load and a plain store).
Proved by one `vcgen` call for the run in the protocol environment
(`tk2WorkerV_envG`), the per-thread timestamp invariant at every reachable
configuration (`inv_reachable`), and the final counting (`FinW.finalVal`).
Not covered (as for `ticket3_counter_envG_verbatim`): the disjointness
hypotheses for the model's mixed-size gap, final configurations only. -/
theorem ticket2_counter_envG_verbatim {fuel : Nat} (N : Nat)
    (hxo : Decls.overlaps (symTk2 "next") 4 (symTk2 "owner") 4 = false)
    (hxc : Decls.overlaps (symTk2 "next") 4 (symTk2 "counter") 4 = false)
    (hoc : Decls.overlaps (symTk2 "owner") 4 (symTk2 "counter") 4 = false) (hN32 : N + 1 < 2 ^ 32)
    {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, StartStateTk2 {} s) (hN : states.length = N)
    (hX0 : (Config.init states initMem).mem.initVal ⟨symTk2 "next", 4⟩ = 0)
    (hO0 : (Config.init states initMem).mem.initVal ⟨symTk2 "owner", 4⟩ = 0)
    (hC0 : (Config.init states initMem).mem.initVal ⟨symTk2 "counter", 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) cfg)
    (hf : cfg.final = true) :
    cfg.mem.finalVal ⟨symTk2 "counter", 4⟩ = BitVec.ofNat 128 N :=
  ticket2_counter_envG_of (Or.inr rfl) N hxo hxc hoc hN32 hst hN hX0 hO0 hC0 hc hf

/-- **`counter = N` for `N` verbatim `ticketlock2` workers with the runner's
declarations**: `ticket2_counter_envG_verbatim` for threads whose
declarations are strict sized (`ds.Sized`: the `.kl` runner's, from the
typed header). -/
theorem ticket2_counter_envG_runner {fuel : Nat} {ds : Decls} (hsz : ds.Sized) (N : Nat)
    (hxo : Decls.overlaps (symTk2 "next") 4 (symTk2 "owner") 4 = false)
    (hxc : Decls.overlaps (symTk2 "next") 4 (symTk2 "counter") 4 = false)
    (hoc : Decls.overlaps (symTk2 "owner") 4 (symTk2 "counter") 4 = false) (hN32 : N + 1 < 2 ^ 32)
    {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, StartStateTk2 ds s) (hN : states.length = N)
    (hX0 : (Config.init states initMem).mem.initVal ⟨symTk2 "next", 4⟩ = 0)
    (hO0 : (Config.init states initMem).mem.initVal ⟨symTk2 "owner", 4⟩ = 0)
    (hC0 : (Config.init states initMem).mem.initVal ⟨symTk2 "counter", 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) cfg)
    (hf : cfg.final = true) :
    cfg.mem.finalVal ⟨symTk2 "counter", 4⟩ = BitVec.ofNat 128 N :=
  ticket2_counter_envG_of (Or.inl hsz) N hxo hxc hoc hN32 hst hN hX0 hO0 hC0 hc hf

end Image

end Kraken.Promising.X64.EnvG.TicketX2

#print axioms Kraken.Promising.X64.EnvG.TicketX2.runOK_of_QX64MD
#print axioms Kraken.Promising.X64.EnvG.TicketX2.ticket2_counter_envG_verbatim
#print axioms Kraken.Promising.X64.EnvG.TicketX2.ticket2_counter_envG_runner
