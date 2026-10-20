/-
**Part 2: `counter = N` for the x64 ticket
lock, verbatim** (`X64/ticketlock3.kl`'s worker as written:
`EnvG/TicketXVCGen.lean`), with no declarations
(`ticket3_counter_envG_verbatim`) and with the `.kl` runner's strict sized
declarations (`ticket3_counter_envG_runner`).

- **Invariant**: `QX64MD ds (EnvGTDR isa Arch.tso tid (tkPlan P) (disp P _))
  (tkS x o c) e e (labTk "done") (postTk3 P tid)` (`EnvG/X64DeclsLink.lean`;
  at `ds = {}` it is `QX64TDR`). `linkHypsTDR_QX64MDX` gives `LinkHypsTDR`
  for `ds` strict sized (`QX64MD.link`/`QX64MD.shape`) or `{}`
  (`linkHypsTDR_QX64TDR`).
- **Rule** (`ruleTk3`): `ThreadRuleRXGSXE.ofEnvGTDR`, the image phase-1
  (`tk3ImageV_phase1`), the halt at `done` from the trailer's first data cell
  (`tk3ImageV_stuck`), `hB_tk3` (`TicketLock.hB_tk` at `postTk3`).
- **Start** (`invTk3_init`): `coreAtRX_init` with `tk3WorkerV_envG` from
  `Start` at `σInitX` (`start_initX`, `TicketLock.start_init` for x64).
- **Purity and phases** (`tk3DispSpec`, `tk3DispSpec_holds`):
  `tk3WorkerV_dispPure`.
- **Assembly**: `ticket_counter_ofX` (`EnvG/TicketXPure.lean`).
- **No fault** at `decls = {}`: `ruleTk3_noFault` (`DirsNoFaultCode`: the
  thread never runs the trailer's data cells). As in `X64DeclsLink`, the
  no-fault side at `decls = ds` is not covered.
-/
import Kraken.Promising.SLR.EnvG.TicketXVCGen
import Kraken.Promising.SLR.EnvG.X64ImageNoFault

namespace Kraken.Promising.X64.EnvG.TicketX

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.TicketLock
open Kraken.Promising.X64.EnvG

/-! ## The link with declarations `ds`, strict sized or none -/

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {D : Dispenser} {S : SharedEnv.Layout}
  {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {endPc : Int64}
  {post : MachineState × EStateX → Prop}

/-- **The link hypotheses of the ticket rule with a release-kind ticket RMW
at `QX64MD`**, for strict sized declarations (`linkHypsTDR_QX64MD`,
`EnvG/X64DeclsLink.lean`, at `MaskOf.refl`) or none (`QX64MD {}` is
`QX64TDR`: `linkHypsTDR_QX64TDR`). -/
theorem linkHypsTDR_QX64MDX {ds : Decls} (hsz : ds.Sized ∨ ds = {}) (hpl : pl.Valid) (hS : Le16 S)
    (hshape : Phase1TreeRX A e) (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsTDR (I := isa) A tid pl D (QX64MD ds (Kraken.Promising.SLR.EnvGTDR isa A tid pl D) S e e endPc post) := by
  rcases hsz with hsz | rfl
  · exact linkHypsTDR_QX64MD hsz (MaskOf.refl _) hpl hS hshape hpost
  · exact linkHypsTDR_QX64TDR hpl hS hshape hpost

end Link

/-! ## The image -/

section Image

variable [layout : _root_.Layout] [Executable.ValidLayout (layout tk3ImageV)]

/-- The image's trees are phase-1 with release-kind RMWs (`lock xaddl`;
the trailer's data cells have no access). -/
theorem tk3ImageV_phase1 : Phase1TreeRX Arch.tso (layout tk3ImageV) := by
  refine phase1TreeRX_of_dirs (dirsPhase1RX_layout ?_)
  intro d hd e z s pc
  simp only [tk3ImageV, tk3WorkerV, tk3DataV, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals simp [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    Kraken.Promising.X64.toEv, Kraken.Promising.SLR.EnvG.Phase1ShapeR, Kraken.Promising.SLR.EnvG.DetAccess,
    Kraken.Promising.SLR.EnvG.SingleAccessS2, _root_.MachineData.load, _root_.MachineData.store,
    _root_.MachineData.rmwK, _root_.RegOrMem.interp, _root_.Operand.interp, _root_.MachineData.set,
    _root_.RegOrMem.rmw, _root_.RelRegOrMem.interp]
  all_goals (repeat' (first | split |
    simp [Kraken.Promising.X64.toEv,
      Kraken.Promising.SLR.EnvG.DetAccess, Kraken.Promising.SLR.EnvG.SingleAccessS2,
      Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty]))

/-- The exit label `done` is the address of the trailer's first data cell. -/
theorem labTk_done : labTk "done" = (layout tk3ImageV).addrOf 14 := by
  have hd : (_root_.Executable.labels (layout tk3ImageV)).label "done" = (layout tk3ImageV).addrOf 13 :=
    Program.label_addrOf_drop tk3ImageV_wf.nodup (by decide) (by decide)
  have h13 : (layout tk3ImageV).2[13]? = some (Directive.label "done", Kraken.Layout.size Directive 13) := by
    simp [Layout.apply_snd, Layout.frag, tk3ImageV, tk3WorkerV, tk3DataV]
  rw [Executable.addrOf_succ _ h13, Executable.ValidLayout.label_size 13 "done" _ h13]
  simpa using hd

/-- No instruction steps at the exit label. -/
theorem tk3ImageV_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labTk "done" → ¬ (layout tk3ImageV).instrStepEnv env x R := by
  rw [labTk_done]
  exact not_instrStepEnv_of_byteArray (i := 14) (b := .mk #[]) env (by decide)

omit [Executable.ValidLayout (layout tk3ImageV)] in
/-- The image's non-data cells are fault-free. -/
theorem tk3ImageV_noFaultCode : DirsNoFaultCode (layout tk3ImageV) := by
  dirs_no_fault_code tk3ImageV tk3WorkerV tk3DataV

end Image

/-! ## The rule -/

section Rule

variable [layout : _root_.Layout] [Executable.ValidLayout (layout tk3ImageV)]

omit layout in
theorem tkS_le16 (x o c : BitVec 64) : Le16 (tkS x o c) := fun y hy => by
  simp only [tkS, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl <;> exact (by decide : 4 ≤ 16)

/-- The worker's postcondition: the exit label and `QEnd`. -/
abbrev postTk3 (P : Sys) (tid : Nat) : MachineState × EStateX → Prop :=
  fun y => ∃ _ : Nat, (y.1.2 = labTk "done" ∧ QEnd P tid y.2) ∨ False

omit [Executable.ValidLayout (layout tk3ImageV)] in
theorem postTk3_end (P : Sys) (tid : Nat) : ∀ y, postTk3 P tid y → y.1.2 = labTk "done" :=
  fun _ ⟨_, h⟩ => h.elim And.left False.elim

omit [Executable.ValidLayout (layout tk3ImageV)] in
/-- **`hB` for the verbatim worker**: `TPost` from `QEnd` under the clean
flag (`TicketLock.hB_tk` at `postTk3`). -/
theorem hB_tk3 (P : Sys) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postTk3 P tid (t.st.st, σ) → t.prom = [] → EnvRel tid (tkPlan P) σ c t r g cl → cl → TPost P c r := by
  rintro c t r g cl σ ⟨_, hpost⟩ hp hrel hcl
  obtain ⟨-, -, hQ⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · obtain ⟨hO, hK, tw, w, hw, hl, ht, ts, v, hr, hv⟩ := hQ (hrel.cl hcl)
    exact ⟨hO, tid, hK, tw, w, Memory.get?_of_prefix hrel.snap.msgs hw, hl, ht, ts, v, hrel.snap.read? hr, hv⟩
  · rw [hp] at hts; cases hts

/-- The worker's thread-local invariant, with declarations `ds`. -/
abbrev QTk3 (ds : Decls) (N : Nat) (x o c : BitVec 64) (hL : Locs (tkSysX N x o c)) (tid : Nat) :
    State → EStateX → Prop :=
  QX64MD ds (Kraken.Promising.SLR.EnvGTDR isa Arch.tso tid (tkPlan (tkSysX N x o c)) (disp (tkSysX N x o c) hL.xo))
    (tkS x o c) (layout tk3ImageV) (layout tk3ImageV) (labTk "done") (postTk3 (tkSysX N x o c) tid)

theorem linkHypsTDR_QTk3 {ds : Decls} (hsz : ds.Sized ∨ ds = {}) (N : Nat) (x o c : BitVec 64)
    (hL : Locs (tkSysX N x o c)) (tid : Nat) :
    LinkHypsTDR (I := isa) Arch.tso tid (tkPlan (tkSysX N x o c)) (disp (tkSysX N x o c) hL.xo)
      (QTk3 ds N x o c hL tid) :=
  linkHypsTDR_QX64MDX hsz (tkPlan_valid _) (tkS_le16 x o c) tk3ImageV_phase1 (postTk3_end _ tid)

theorem hB_QTk3 {ds : Decls} (N : Nat) (x o c : BitVec 64) (hL : Locs (tkSysX N x o c)) (tid : Nat) :
    ∀ (c' : Config isa) (t : Thread isa) r g cl σ, QTk3 ds N x o c hL tid t.st σ → t.halted = true → t.prom = [] →
      EnvRel tid (tkPlan (tkSysX N x o c)) σ c' t r g cl → cl → TPost (tkSysX N x o c) c' r :=
  fun c' t r g cl σ hQ hh hp hrel hcl =>
    hB_tk3 _ tid c' t r g cl σ (post_of_halted_QX64MD (MaskOf.refl _) (tk3ImageV_stuck _) hQ hh) hp hrel hcl

/-- **The verbatim x64 ticket lock worker's rule** (`Arch.tso`, the thread's
declarations `ds` strict sized or none). -/
noncomputable def ruleTk3 {ds : Decls} (hsz : ds.Sized ∨ ds = {}) (N : Nat) (x o c : BitVec 64)
    (hL : Locs (tkSysX N x o c)) (tid : Nat) :
    ThreadRuleRXGSXE (I := isa) G₀ (disp (tkSysX N x o c) hL.xo).TX Arch.tso
      (fun c' r _ => TPost (tkSysX N x o c) c' r) tid :=
  ThreadRuleRXGSXE.ofEnvGTDR (linkHypsTDR_QTk3 hsz N x o c hL tid) (hB_QTk3 N x o c hL tid)

/-- **The verbatim worker's rule excludes faults** at `decls = {}`
(`DirsNoFaultCode`; unconditional in the thread's promises). -/
theorem ruleTk3_noFault (N : Nat) (x o c : BitVec 64) (hL : Locs (tkSysX N x o c)) (tid : Nat) :
    NoFaultRuleSXE (ruleTk3 (Or.inr rfl) N x o c hL tid) :=
  NoFaultRuleSXE.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp => by
    obtain ⟨σ, hQ⟩ := InvGTDR.q_at rF t h he hg ht E hnp
    obtain ⟨he', hds, hend, -, hsafe⟩ := hQ
    rcases hsafe.unfold with hp | ⟨R, hR, -⟩
    · have := exec_eq_none_of_end (st := t.st) (by rw [hend]; exact postTk3_end _ _ _ hp)
      rw [this] at hex; cases hex
    · exact noFault_of_exec_step he' hds tk3ImageV_noFaultCode hR tree hex

end Rule

/-! ## The start -/

/-- `Start` at the initial `σInitX` (`TicketLock.start_init` for x64). -/
theorem start_initX {N : Nat} {x o c : BitVec 64} (hL : Locs (tkSysX N x o c)) (m : Memory) (tid : Nat)
    (snap : Config isa) :
    Start (tkSysX N x o c) tid (σInitX snap (thRes m (tkSysX N x o c) tid) (tkGhost m (tkSysX N x o c))) :=
  start_initG hL m tid snap

section Start

variable [layout : _root_.Layout] [Executable.ValidLayout (layout tk3ImageV)]

/-- **A verbatim ticket lock worker at its start with declarations `ds`**, as
the `.kl` runner sets it up: the laid-out image, the pc at the entry label
`worker`, the end at the exit label `done`, and none of the three words in
the private memory. No register is constrained. -/
structure StartStateTk (ds : Decls) (s : State) : Prop where
  exe : s.exe = layout tk3ImageV
  decls : s.decls = ds
  pc : s.st.2 = (_root_.Executable.labels s.exe).label "worker"
  endPc : s.endPc = (_root_.Executable.labels s.exe).label "done"
  split : Split (tkS (symTk "next") (symTk "owner") (symTk "counter")) s.st.1.dmem

omit [Executable.ValidLayout (layout tk3ImageV)] in
theorem StartStateTk.frame {ds : Decls} {s : State} (h : StartStateTk ds s) :
    FrameTk (symTk "next") (symTk "owner") (symTk "counter") s.st.1 :=
  ⟨h.split.loadInt_none (by simp) (by decide) (by decide), h.split.loadInt_none (by simp) (by decide) (by decide),
    h.split.loadInt_none (by simp) (by decide) (by decide)⟩

omit [Executable.ValidLayout (layout tk3ImageV)] in
theorem StartStateTk.st {ds : Decls} {s : State} (h : StartStateTk ds s) : s.st = (s.st.1, labTk "worker") := by
  refine Prod.ext rfl ?_; rw [h.pc, h.exe]

omit [Executable.ValidLayout (layout tk3ImageV)] in
theorem StartStateTk.end {ds : Decls} {s : State} (h : StartStateTk ds s) : s.endPc = labTk "done" := by
  rw [h.endPc, h.exe]

/-- **The verbatim worker's initial invariant** (thread `tid`). -/
theorem invTk3_init {ds : Decls} {N : Nat} (hL : Locs (tkSysX N (symTk "next") (symTk "owner") (symTk "counter")))
    {tid : Nat} {states : List isa.State} {initMem : List (Loc × Val)} {s : isa.State} (hs : states[tid]? = some s)
    (hst : StartStateTk ds s) :
    InvGTDR (I := isa) tid (tkPlan (tkSysX N (symTk "next") (symTk "owner") (symTk "counter")))
      (disp (tkSysX N (symTk "next") (symTk "owner") (symTk "counter")) hL.xo)
      (QTk3 ds N (symTk "next") (symTk "owner") (symTk "counter") hL tid) True (Config.init states initMem)
      (thRes (Config.init states initMem).mem (tkSysX N (symTk "next") (symTk "owner") (symTk "counter")) tid)
      (tkGhost (Config.init states initMem).mem (tkSysX N (symTk "next") (symTk "owner") (symTk "counter"))) := by
  have hsafe := _root_.Safely.uncountEnv
    (tk3WorkerV_envG N _ _ _ rfl rfl rfl hL tid s.st.1 (_, 0) ⟨hst.frame, start_initX hL (Config.init states initMem).mem tid
      (Config.init states initMem)⟩)
  rw [← hst.st] at hsafe
  exact ⟨_, _, coreAtRX_init hs rfl, ⟨hst.exe, hst.decls, hst.end, hst.split, hsafe⟩,
    fun _ => by simp [Thread.init, Views.getCoh]⟩

/-! ## Purity and phases -/

/-- The verbatim worker's all-release purity-and-phase specification (the
image, ending at `done`). -/
noncomputable def tk3DispSpec (N : Nat) :
    DispSpecX Arch.tso (fun _ _ => False) ⟨symTk "next", 4⟩ (N + 1) where
  S := tkS (symTk "next") (symTk "owner") (symTk "counter")
  le16 := tkS_le16 _ _ _
  e := layout tk3ImageV
  valid := inferInstance
  endPc := labTk "done"
  post y := ∃ _ : Nat, (y.1.2 = labTk "done" ∧ y.2 = true) ∨ False
  post_end _ h := h.elim fun _ h => h.elim And.left False.elim

/-- **The specification holds at a start state**, before the hand-out. -/
theorem tk3DispSpec_holds {ds : Decls} {N : Nat} (hN : N + 1 < 2 ^ 32) (hxo : symTk "next" ≠ symTk "owner")
    (hxc : symTk "next" ≠ symTk "counter") {s : isa.State} (h : StartStateTk ds s) :
    (tk3DispSpec N).HoldsD ds false s := by
  refine ⟨h.exe, h.end, h.decls, h.split, ?_⟩
  rw [h.st]
  exact _root_.Safely.uncountEnv
    (tk3WorkerV_dispPure N _ _ _ rfl rfl rfl hN hxo hxc s.st.1 (false, 0) ⟨h.frame, rfl⟩)

/-! ## The theorems -/

/-- **`counter = N` for `N` verbatim x64 ticket lock workers with
declarations `ds`, strict sized or none** (the common proof of
`ticket3_counter_envG_verbatim` and `ticket3_counter_envG_runner`). -/
theorem ticket3_counter_envG_of {fuel : Nat} {ds : Decls} (hsz : ds.Sized ∨ ds = {}) (N : Nat)
    (hxo : Decls.overlaps (symTk "next") 4 (symTk "owner") 4 = false)
    (hxc : Decls.overlaps (symTk "next") 4 (symTk "counter") 4 = false)
    (hoc : Decls.overlaps (symTk "owner") 4 (symTk "counter") 4 = false) (hN32 : N + 1 < 2 ^ 32)
    {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, StartStateTk ds s) (hN : states.length = N)
    (hX0 : (Config.init states initMem).mem.initVal ⟨symTk "next", 4⟩ = 0)
    (hO0 : (Config.init states initMem).mem.initVal ⟨symTk "owner", 4⟩ = 0)
    (hC0 : (Config.init states initMem).mem.initVal ⟨symTk "counter", 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) cfg)
    (hf : cfg.final = true) :
    cfg.mem.finalVal ⟨symTk "counter", 4⟩ = BitVec.ofNat 128 N := by
  have hxo' : symTk "next" ≠ symTk "owner" := by intro h; rw [h] at hxo; simp [Decls.overlaps] at hxo
  have hxc' : symTk "next" ≠ symTk "counter" := by intro h; rw [h] at hxc; simp [Decls.overlaps] at hxc
  exact ticket_counter_ofX N _ _ _ hxo hxc hoc hN32 hN hX0 hO0 hC0 (tk3DispSpec N) (fun _ => ds) (fun _ => hsz)
    (fun _ s hs => tk3DispSpec_holds hN32 hxo' hxc' (hst s (List.mem_of_getElem? hs)))
    (fun hL tid s hs n m => npSafeP_of_envGTDR (linkHypsTDR_QTk3 hsz N _ _ _ hL tid) (hB_QTk3 N _ _ _ hL tid) n m
      (invTk3_init hL hs (hst s (List.mem_of_getElem? hs))))
    hc hf

/-- **`counter = N` for `N` x64 ticket lock workers running
`ticketlock3.kl`'s code verbatim, under `Arch.tso`**.

For every valid layout of the worker's image `tk3ImageV` (the `code` block,
then the `.kl` runner's data trailer that places the symbols `next`, `owner`
and `counter`), every number of threads `N` with `N + 1 < 2 ^ 32`, if the
symbols' 4-byte words are pairwise disjoint, `states` consists of `N`
threads each at the entry label `worker` with its end at `done`, no
declarations and none of the words in its private memory (`StartStateTk {}`;
no register is assumed), and the initial memory has the three words at `0`,
then every configuration `Reachable` under `Arch.tso` that is final has the
counter word at `N`.

Proved on the ticket environment with a release-kind ticket RMW `EnvGTDR`
(`lock xaddl` is a release-kind RMW): one `vcgen` call for the run
(`tk3WorkerV_envG`), one for purity and the dispenser phases
(`tk3WorkerV_dispPure`), `ThreadRuleRXGSXE.ofEnvGTDR` (`ruleTk3`) and
`ticket_counter_ofX`. Not covered (as for `TicketLock.ticket_counter_envG`):
the disjointness hypotheses for the model's mixed-size gap, final
configurations only. No fault for the worker's rule: `ruleTk3_noFault`. -/
theorem ticket3_counter_envG_verbatim {fuel : Nat} (N : Nat)
    (hxo : Decls.overlaps (symTk "next") 4 (symTk "owner") 4 = false)
    (hxc : Decls.overlaps (symTk "next") 4 (symTk "counter") 4 = false)
    (hoc : Decls.overlaps (symTk "owner") 4 (symTk "counter") 4 = false) (hN32 : N + 1 < 2 ^ 32)
    {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, StartStateTk {} s) (hN : states.length = N)
    (hX0 : (Config.init states initMem).mem.initVal ⟨symTk "next", 4⟩ = 0)
    (hO0 : (Config.init states initMem).mem.initVal ⟨symTk "owner", 4⟩ = 0)
    (hC0 : (Config.init states initMem).mem.initVal ⟨symTk "counter", 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) cfg)
    (hf : cfg.final = true) :
    cfg.mem.finalVal ⟨symTk "counter", 4⟩ = BitVec.ofNat 128 N :=
  ticket3_counter_envG_of (Or.inr rfl) N hxo hxc hoc hN32 hst hN hX0 hO0 hC0 hc hf

/-- **`counter = N` for `N` verbatim x64 ticket lock workers with the
runner's declarations**: `ticket3_counter_envG_verbatim` for threads whose
declarations are strict sized (`ds.Sized`: the `.kl` runner's, from the
typed header). -/
theorem ticket3_counter_envG_runner {fuel : Nat} {ds : Decls} (hsz : ds.Sized) (N : Nat)
    (hxo : Decls.overlaps (symTk "next") 4 (symTk "owner") 4 = false)
    (hxc : Decls.overlaps (symTk "next") 4 (symTk "counter") 4 = false)
    (hoc : Decls.overlaps (symTk "owner") 4 (symTk "counter") 4 = false) (hN32 : N + 1 < 2 ^ 32)
    {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, StartStateTk ds s) (hN : states.length = N)
    (hX0 : (Config.init states initMem).mem.initVal ⟨symTk "next", 4⟩ = 0)
    (hO0 : (Config.init states initMem).mem.initVal ⟨symTk "owner", 4⟩ = 0)
    (hC0 : (Config.init states initMem).mem.initVal ⟨symTk "counter", 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) cfg)
    (hf : cfg.final = true) :
    cfg.mem.finalVal ⟨symTk "counter", 4⟩ = BitVec.ofNat 128 N :=
  ticket3_counter_envG_of (Or.inl hsz) N hxo hxc hoc hN32 hst hN hX0 hO0 hC0 hc hf

end Start

end Kraken.Promising.X64.EnvG.TicketX

#print axioms Kraken.Promising.X64.EnvG.TicketX.ticket3_counter_envG_verbatim
#print axioms Kraken.Promising.X64.EnvG.TicketX.ticket3_counter_envG_runner
#print axioms Kraken.Promising.X64.EnvG.TicketX.ruleTk3_noFault
