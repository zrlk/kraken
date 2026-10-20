/-
**The x64 xchg spinlock on `EnvG`, verbatim: the public theorem**:
`x64_spin_counter_envG_verbatim`, `counter = N` for `N` workers
running `spinlock2.kl`'s code as written (`spinWorkerV`, absolute operands
`(lock)`/`(counter)`), in the shape of the x64 `xchg` lock proof's
`SpinPublicG.x64_spin_counter_envG` (which proves the rewritten worker
`spinWorkerG`, `(%rdi)`/`(%rsi)`, from `%rdi = l`, `%rsi = c`; it stays
unchanged).

Each thread runs the image `spinImageV` (the code, then the `.kl` runner's
data trailer: `EnvG/X64SpinAbsVCGen.lean`) under any valid layout; the lock
and the counter are the symbols' addresses `symV "lock"`, `symV "counter"`,
fixed by the executable (no register holds them). A thread starts at the
entry label `worker` and halts at the exit label `done`, as the runner sets
it up (`StartStateV`).

- **Rule** (`spinRuleV_envG`): `ThreadRuleRX.ofSafelyEnvGRX` at the image,
  `Phase1TreeRX` per directive (`spinImageV_phase1`; the trailer's data cells
  have no access), the halt at `done` from the trailer's first data cell
  (`not_instrStepEnv_of_byteArray`), `hB` as `SpinLink.hB_spin`.
- **Start** (`spinInvV_init`): `invGRX_init` from `spinWorkerV_envG`
  (uncounted, `Safely.uncountV`) at the initial ghost of
  `SpinPublicG.spinInv_init`.
- **Purity** (`spinNoNTSpecV`): the image's all-release specification from
  `spinWorkerV_noNT`.
- **Assembly**: `final_of_relPureSafelyQX_tso` and `Spinlock.adequacy`, as
  `x64_spin_counter_envG`.

Not covered here (as for `x64_spin_counter_envG`): the declarations
(`decls = {}`; the runner declares the symbols' locations, which only adds
mixed-size checks), `hdisj` for the model's mixed-size gap, final
configurations only. No-fault, as for `x64_spin_counter_envG`, is the rule's
fact `spinRuleV_envG_noFault`: the trailer's data cells are `unimplemented`,
so `DirsNoFault` of the whole executable fails, but the thread never runs
them (`EnvG/X64ImageNoFault.lean`: `DirsNoFaultCode`, `noFault_QX64_code`).
-/
import Kraken.Promising.SLR.EnvG.X64SpinAbsVCGen
import Kraken.Promising.SLR.EnvG.X64SpinPublicG
import Kraken.Promising.SLR.EnvG.X64ImageNoFault

namespace Kraken.Promising.X64.EnvG.SpinAbs

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Spin Kraken.Promising.X64.EnvG.SpinLink
open Kraken.Promising.X64.EnvG.SpinRelPure Kraken.Promising.X64.EnvG.SpinPublicG
open Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon Kraken.Promising.SLR.EnvG.X64Spin

/-! ## Forgetting the access counter of a `Safely` judgment -/

/-- A `Safely` judgment in `SharedEnv.counted env` is one in `env`
(`PartialTripleEnv.uncount`, at a machine state). -/
theorem Safely.uncountV {e : Kraken.Executable Directive} {env : SharedEnv}
    {post : MachineState × (SharedEnv.counted env).State → Prop} {x : MachineState}
    {g : (SharedEnv.counted env).State} (h : Safely (e.instrStepEnv (SharedEnv.counted env)) post (x, g)) :
    Safely (e.instrStepEnv env) (fun y => ∃ n : Nat, post (y.1, (y.2, n))) (x, g.1) :=
  _root_.Safely.uncountEnv h

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spinImageV)]

/-! ## The rule -/

/-- The image's trees are phase-1 (`dirs_phase1RX` over the code and the
trailer). -/
theorem spinImageV_phase1 : Phase1TreeRX Arch.tso (layout spinImageV) := by
  refine phase1TreeRX_of_dirs (dirsPhase1RX_layout ?_)
  intro d hd e z s pc
  simp only [spinImageV, spinWorkerV, spinDataV, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals simp [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    Kraken.Promising.X64.toEv, Kraken.Promising.SLR.EnvG.Phase1ShapeR, Kraken.Promising.SLR.EnvG.DetAccess,
    Kraken.Promising.SLR.EnvG.SingleAccessS2, Kraken.Promising.SLR.EnvG.AccessFree,
    _root_.MachineData.load, _root_.MachineData.store,
    _root_.MachineData.rmwK, _root_.RegOrMem.interp, _root_.Operand.interp, _root_.MachineData.set,
    _root_.RegOrMem.rmw, _root_.RelRegOrMem.interp]
  all_goals (repeat' (first | split |
    simp [Kraken.Promising.X64.toEv,
      Kraken.Promising.SLR.EnvG.DetAccess, Kraken.Promising.SLR.EnvG.SingleAccessS2,
      Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty]))

/-- The exit label `done` is the address of the trailer's first data cell. -/
theorem labV_done : labV "done" = (layout spinImageV).addrOf 14 := by
  have hd : (_root_.Executable.labels (layout spinImageV)).label "done" = (layout spinImageV).addrOf 13 :=
    Program.label_addrOf_drop spinImageV_wf.nodup (by decide) (by decide)
  have h13 : (layout spinImageV).2[13]? = some (Directive.label "done", Kraken.Layout.size Directive 13) := by
    simp [Layout.apply_snd, Layout.frag, spinImageV, spinWorkerV, spinDataV]
  rw [Executable.addrOf_succ _ h13, Executable.ValidLayout.label_size 13 "done" _ h13]
  simpa using hd

/-- No instruction steps at the exit label. -/
theorem spinImageV_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labV "done" → ¬ (layout spinImageV).instrStepEnv env x R := by
  rw [labV_done]
  exact not_instrStepEnv_of_byteArray (i := 14) (b := .mk #[]) env (by decide)

/-- The worker's postcondition: the exit label and `QEnd`. -/
abbrev postSpinV (P : Sys) : MachineState × EStateX → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labV "done" ∧ QEnd P x.2) ∨ False

omit [Executable.ValidLayout (layout spinImageV)] in
theorem postSpinV_end (P : Sys) : ∀ y, postSpinV P y → y.1.2 = labV "done" :=
  fun _ ⟨_, h⟩ => h.elim And.left False.elim

omit [Executable.ValidLayout (layout spinImageV)] in
/-- **`hB` for the verbatim worker** (`SpinLink.hB_spin`). -/
theorem hB_spinV (P : Sys) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postSpinV P (t.st.st, σ) → t.prom = [] → EnvRel tid (xlockPlan P tid) σ c t r g cl → cl →
      Post P.N P.Lk P.K r := by
  rintro c t r g cl σ ⟨_, hpost⟩ hp hrel hcl
  obtain ⟨-, -, hQ⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact hQ (hrel.cl hcl)
  · rw [hp] at hts; cases hts

/-- **The verbatim x64 spinlock worker's rule on `EnvG`** (`Arch.tso`), at
the release predicates `rel₀`. -/
noncomputable def spinRuleV_envG (P : Sys) (tid : Nat) (l c : BitVec 64) (rel₀ : Loc → Pred) :
    ThreadRuleRX (I := isa) Arch.tso (fun _ r _ => Post P.N P.Lk P.K r) tid :=
  ThreadRuleRX.ofSafelyEnvGRX (S := spinS l c) (post := postSpinV P) (rel₀ := rel₀) (xlockPlan_valid P tid)
    (spinS_le16 l c) spinImageV_phase1 (RelRmwGiveOk.of_gives_nil (xlockPlan_gives P tid))
    (postSpinV_end P) (spinImageV_stuck _) (hB_spinV P tid)

omit [Executable.ValidLayout (layout spinImageV)] in
/-- The image's non-data cells are fault-free. -/
theorem spinImageV_noFaultCode : DirsNoFaultCode (layout spinImageV) := by
  dirs_no_fault_code spinImageV spinWorkerV spinDataV

/-- **The verbatim worker's rule excludes faults** (`DirsNoFaultCode`: the
thread never runs the trailer's data cells). -/
theorem spinRuleV_envG_noFault (P : Sys) (tid : Nat) (l c : BitVec 64) (rel₀ : Loc → Pred) :
    NoFaultRule (spinRuleV_envG P tid l c rel₀) := by
  unfold spinRuleV_envG ThreadRuleRX.ofSafelyEnvGRX
  exact noFaultRule_ofEnvGR_structX _ _ fun st σ tree hQ hex =>
    noFault_QX64_code spinImageV_noFaultCode (postSpinV_end P) st σ tree hQ.1 hex

/-! ## The start -/

/-- **A verbatim spinlock worker at its start**, as the `.kl` runner sets it
up: the laid-out image, no declarations, the pc at the entry label `worker`,
the end at the exit label `done`, and neither symbol's word in the private
memory. No register is constrained. -/
structure StartStateV (s : State) : Prop where
  exe : s.exe = layout spinImageV
  decls : s.decls = {}
  pc : s.st.2 = (_root_.Executable.labels s.exe).label "worker"
  endPc : s.endPc = (_root_.Executable.labels s.exe).label "done"
  split : Split [(symV "lock", 4), (symV "counter", 4)] s.st.1.dmem

omit [Executable.ValidLayout (layout spinImageV)] in
theorem StartStateV.frame {s : State} (h : StartStateV s) : FrameV (symV "lock") (symV "counter") s.st.1 :=
  ⟨split_dl h.split, split_dc h.split⟩

omit [Executable.ValidLayout (layout spinImageV)] in
theorem StartStateV.st {s : State} (h : StartStateV s) : s.st = (s.st.1, labV "worker") := by
  refine Prod.ext rfl ?_; rw [h.pc, h.exe]

/-- **The verbatim worker's initial invariant** (thread `tid` of `N`). -/
theorem spinInvV_init {N : Nat} (hlc : symV "lock" ≠ symV "counter") (hN32 : N < 2 ^ 32) {tid : Nat}
    (htid : tid < N) {states : List isa.State} {initMem : List (Loc × Val)} {s : isa.State}
    (hs : states[tid]? = some s) (hst : StartStateV s)
    (hLk0 : (Config.init states initMem).mem.initVal ⟨symV "lock", 4⟩ = 0) :
    (spinRuleV_envG (ghostSys N (symV "lock") (symV "counter")) tid (symV "lock") (symV "counter")
      (ghost0 N (symV "lock") (symV "counter") (Config.init states initMem).mem).rel).Inv True
      (Config.init states initMem)
      (threadRes (Config.init states initMem).mem N ⟨symV "lock", 4⟩ (ghostSys N (symV "lock") (symV "counter")).K
        (ghostSys N (symV "lock") (symV "counter")).F tid)
      (ghost0 N (symV "lock") (symV "counter") (Config.init states initMem).mem) := by
  have hL := ghostSys_spinLocs (N := N) hlc
  have hN0 : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) htid
  have hend : s.endPc = labV "done" := by rw [hst.endPc, hst.exe]
  have hFr : Fr (ghostSys N (symV "lock") (symV "counter")) tid (σInitX (Config.init states initMem)
      (threadRes (Config.init states initMem).mem N ⟨symV "lock", 4⟩ (ghostSys N (symV "lock") (symV "counter")).K
        (ghostSys N (symV "lock") (symV "counter")).F tid)
      (ghost0 N (symV "lock") (symV "counter") (Config.init states initMem).mem)) := by
    refine ⟨world_spinGhost' hL.lk_c, threadRes_fresh' hL htid, ?_, threadRes_lkLe hLk0 _⟩
    intro f hf
    simp [σInitX, Views.getFwd] at hf
  have hsafe := Safely.uncountV
    (spinWorkerV_envG (ghostSys N (symV "lock") (symV "counter")) tid _ _ rfl rfl rfl rfl hL hN0 htid hN32
      s.st.1 (_, 0) ⟨hst.frame, hFr⟩)
  rw [← hst.st] at hsafe
  exact invGRX_init (S := spinS (symV "lock") (symV "counter")) (e := layout spinImageV) (endPc := labV "done")
    (post := postSpinV (ghostSys N (symV "lock") (symV "counter"))) hs rfl
    ⟨hst.exe, hst.decls, hend, hst.split, hsafe⟩

/-! ## Scope and purity -/

/-- The verbatim worker's all-release specification (the image, ending at
`done`). -/
noncomputable def spinNoNTSpecV : RelPureSpecQX Arch.tso fun _ _ => False where
  S := spinS (symV "lock") (symV "counter")
  le16 := spinS_le16 _ _
  e := layout spinImageV
  valid := inferInstance
  endPc := labV "done"
  post x := ∃ _ : Nat, (x.1.2 = labV "done" ∧ True) ∨ False
  post_end _ h := h.elim fun _ h => h.elim And.left False.elim

/-- **The all-release specification holds at a start state.** -/
theorem spinNoNTSpecV_holds {s : isa.State} (h : StartStateV s) : spinNoNTSpecV.Holds s := by
  refine ⟨h.exe, by rw [h.endPc, h.exe]; rfl, h.decls, h.split, ?_⟩
  rw [h.st]
  exact Safely.uncountV (spinWorkerV_noNT _ _ rfl rfl s.st.1 ((), 0) h.frame)

/-! ## The theorem -/

/-- **`counter = N` for `N` x64 xchg-spinlock workers running
`spinlock2.kl`'s code verbatim, under `Arch.tso`, on `EnvG`**: the statement
of `SpinPublicG.x64_spin_counter_envG` for the worker as written, with
`(lock)` and `(counter)` (absolute operands).

For every valid layout of the worker's image `spinImageV` (the `code` block,
then the `.kl` runner's data trailer that places the symbols `lock` and
`counter`), every number of threads `N < 2 ^ 32`, if the symbols' 4-byte words
are disjoint, `states` consists of `N` threads each at the entry label
`worker` with its end at `done` and neither word in its private memory
(`StartStateV`; no register is assumed), and the initial memory has both words
at `0`, then every configuration `Reachable` under `Arch.tso` that is final has
the counter word at `N`. -/
theorem x64_spin_counter_envG_verbatim {fuel : Nat} (N : Nat) (hdisj : Decls.overlaps (symV "lock") 4 (symV "counter") 4 = false)
    (hN32 : N < 2 ^ 32) {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, StartStateV s) (hN : states.length = N)
    (hC0 : (Config.init states initMem).mem.initVal ⟨symV "counter", 4⟩ = 0)
    (hLk0 : (Config.init states initMem).mem.initVal ⟨symV "lock", 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) cfg)
    (hf : cfg.final = true) :
    cfg.mem.finalVal ⟨symV "counter", 4⟩ = BitVec.ofNat 128 N :=
  CasSmoke.spin_counter_core N hdisj hN hC0 hc hf fun hlc hN0 hfin =>
    final_of_relPureSafelyQX_tso fuel
      (B := fun _ r _ => Post N ⟨symV "lock", 4⟩ (ghostSys N (symV "lock") (symV "counter")).K r)
      (Φ := fun cfg => cfg.mem.finalVal ⟨symV "counter", 4⟩ = BitVec.ofNat 128 N)
      (erase_init_lockPred (C := ⟨symV "counter", 4⟩) _ (ghostSys_spinLocs hlc) hN hN0 hC0 hLk0)
      pend_init
      (fun _ => spinNoNTSpecV)
      (fun _ s hs => spinNoNTSpecV_holds (hst s (List.mem_of_getElem? hs)))
      (fun tid htid n m => by
        obtain ⟨s, hs⟩ : ∃ s, states[tid]? = some s := ⟨_, List.getElem?_eq_getElem htid⟩
        exact NPSafe.of_ruleRX _ n m _ _ _ _
          (spinInvV_init hlc hN32 (hN ▸ htid) hs (hst s (List.mem_of_getElem? hs)) hLk0))
      hc hf hfin

end Kraken.Promising.X64.EnvG.SpinAbs

#print axioms Kraken.Promising.X64.EnvG.SpinAbs.x64_spin_counter_envG_verbatim
#print axioms Kraken.Promising.X64.EnvG.SpinAbs.spinRuleV_envG_noFault
