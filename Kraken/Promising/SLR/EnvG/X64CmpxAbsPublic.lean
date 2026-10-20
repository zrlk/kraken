/-
**The x64 `lock cmpxchg` spinlock on `EnvG`, verbatim: the public theorem**
`x64_cmpx_counter_envG_verbatim`, `counter = N` for
`N` workers running `spinlock_cmpxchg2.kl`'s code as written (`cmpxWorkerV`,
absolute operands `(lock)`/`(counter)`), in the shape of the x64 `cmpxchg` lock proof's
`CmpxPublic.x64_cmpx_counter_envG'` (which proves the rewritten worker
`cmpxWorkerG`, `(%rdi)`/`(%rsi)`, from `%rdi = l`, `%rsi = c`; it stays
unchanged). Unconditional: the `F` chain is `theorem1FChain`.

Each thread runs the image `cmpxImageV` (`EnvG/X64CmpxAbsVCGen.lean`) under
any valid layout; the lock and the counter are the symbols' addresses
`symC "lock"`, `symC "counter"`. A thread starts at the entry label `worker`
and halts at the exit label `done` (`StartStateCV`); no register is assumed.

- **Rule** (`cmpxRuleV_envGF`): `ThreadRuleRXF.ofSafelyEnvGFX` at the image,
  `Phase1TreeFX` per directive (`cmpxImageV_phase1`), the halt at `done` from
  the trailer's first data cell (`not_instrStepEnv_of_byteArray`), `hB` as
  `CmpxLink.hB_cmpx`.
- **Start** (`cmpxInvV_init`): `invGFX_init` from `cmpxWorkerV_envG`
  (uncounted) at the initial ghost of `CmpxPublic.cmpxInv_init`.
- **Purity** (`cmpxNoNTSpecV`): from `cmpxWorkerV_noNT`.
- **Assembly**: `final_of_relPureSafelyQX_tsoF (theorem1FChain …)` and
  `Spinlock.adequacy`, as `x64_cmpx_counter_envG'`.

Not covered here (as for `x64_cmpx_counter_envG'`): the declarations
(`decls = {}`), `hdisj` for the model's mixed-size gap, final configurations
only. No-fault is the rule's fact `cmpxRuleV_envGF_noFault`
(`EnvG/X64ImageNoFault.lean`).
-/
import Kraken.Promising.SLR.EnvG.X64CmpxAbsVCGen
import Kraken.Promising.SLR.EnvG.X64CmpxFinal
import Kraken.Promising.SLR.EnvG.X64SpinAbsPublic
import Kraken.Promising.SLR.EnvG.X64ImageNoFault

namespace Kraken.Promising.X64.EnvG.CmpxAbs

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Spin Kraken.Promising.X64.EnvG.SpinLink
open Kraken.Promising.X64.EnvG.SpinRelPure Kraken.Promising.X64.EnvG.SpinPublicG
open Kraken.Promising.X64.EnvG.CmpxPublic Kraken.Promising.X64.EnvG.SpinAbs
open Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon Kraken.Promising.SLR.EnvG.X64Spin

variable [layout : _root_.Layout] [Executable.ValidLayout (layout cmpxImageV)]

/-! ## The rule -/

/-- The image's trees are phase-1 with failing RMWs (over the code and the
trailer). -/
theorem cmpxImageV_phase1 : Phase1TreeFX (layout cmpxImageV) := by
  refine phase1TreeFX_of_dirs (dirsPhase1FX_layout ?_)
  intro d hd e z s pc
  simp only [cmpxImageV, cmpxWorkerV, spinDataV, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals simp [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    Kraken.Promising.X64.toEv, Kraken.Promising.SLR.EnvG.Phase1ShapeF, Kraken.Promising.SLR.EnvG.DetAccess,
    Kraken.Promising.SLR.EnvG.SingleAccessS2, Kraken.Promising.SLR.EnvG.AccessFree,
    _root_.MachineData.load, _root_.MachineData.store,
    _root_.MachineData.rmwK, _root_.RegOrMem.interp, _root_.Operand.interp, _root_.MachineData.set,
    _root_.RegOrMem.rmw, _root_.RelRegOrMem.interp]
  all_goals (repeat' (first | split |
    simp [Kraken.Promising.X64.toEv, Kraken.Promising.SLR.EnvG.DetAccess, Kraken.Promising.SLR.EnvG.SingleAccessS2,
      Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty]))

/-- The exit label `done` is the address of the trailer's first data cell. -/
theorem labC_done : labC "done" = (layout cmpxImageV).addrOf 11 := by
  have hd : (_root_.Executable.labels (layout cmpxImageV)).label "done" = (layout cmpxImageV).addrOf 10 :=
    Program.label_addrOf_drop cmpxImageV_wf.nodup (by decide) (by decide)
  have h10 : (layout cmpxImageV).2[10]? = some (Directive.label "done", Kraken.Layout.size Directive 10) := by
    simp [Layout.apply_snd, Layout.frag, cmpxImageV, cmpxWorkerV, spinDataV]
  rw [Executable.addrOf_succ _ h10, Executable.ValidLayout.label_size 10 "done" _ h10]
  simpa using hd

/-- No instruction steps at the exit label. -/
theorem cmpxImageV_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labC "done" → ¬ (layout cmpxImageV).instrStepEnv env x R := by
  rw [labC_done]
  exact not_instrStepEnv_of_byteArray (i := 11) (b := .mk #[]) env (by decide)

/-- The worker's postcondition: the exit label and `QEnd`. -/
abbrev postCmpxV (P : Sys) : MachineState × EStateX → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labC "done" ∧ QEnd P x.2) ∨ False

omit [Executable.ValidLayout (layout cmpxImageV)] in
theorem postCmpxV_end (P : Sys) : ∀ y, postCmpxV P y → y.1.2 = labC "done" :=
  fun _ ⟨_, h⟩ => h.elim And.left False.elim

omit [Executable.ValidLayout (layout cmpxImageV)] in
/-- **`hB` for the verbatim worker** (`CmpxLink.hB_cmpx`). -/
theorem hB_cmpxV (P : Sys) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postCmpxV P (t.st.st, σ) → t.prom = [] → EnvRel tid (xlockPlan P tid) σ c t r g cl → cl →
      Post P.N P.Lk P.K r := by
  rintro c t r g cl σ ⟨_, hpost⟩ hp hrel hcl
  obtain ⟨-, -, hQ⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact hQ (hrel.cl hcl)
  · rw [hp] at hts; cases hts

/-- **The verbatim x64 `lock cmpxchg` spinlock worker's rule on `EnvG`**
(`Arch.tso`, failing release RMWs), at the release predicates `rel₀`. -/
noncomputable def cmpxRuleV_envGF (P : Sys) (tid : Nat) (l c : BitVec 64) (rel₀ : Loc → Pred) :
    ThreadRuleRXF (I := isa) Arch.tso (fun _ r _ => Post P.N P.Lk P.K r) tid :=
  ThreadRuleRXF.ofSafelyEnvGFX (S := spinS l c) (post := postCmpxV P) (rel₀ := rel₀) (xlockPlan_valid P tid)
    (spinS_le16 l c) cmpxImageV_phase1 (RelRmwGiveOk.of_gives_nil (xlockPlan_gives P tid))
    (postCmpxV_end P) (cmpxImageV_stuck _) (hB_cmpxV P tid)

omit [Executable.ValidLayout (layout cmpxImageV)] in
/-- The image's non-data cells are fault-free. -/
theorem cmpxImageV_noFaultCode : DirsNoFaultCode (layout cmpxImageV) := by
  dirs_no_fault_code cmpxImageV cmpxWorkerV spinDataV

/-- **The verbatim worker's rule excludes faults** (`DirsNoFaultCode`: the
thread never runs the trailer's data cells). -/
theorem cmpxRuleV_envGF_noFault (P : Sys) (tid : Nat) (l c : BitVec 64) (rel₀ : Loc → Pred) :
    NoFaultRuleF (cmpxRuleV_envGF P tid l c rel₀) := by
  unfold cmpxRuleV_envGF ThreadRuleRXF.ofSafelyEnvGFX
  exact noFaultRuleF_ofEnvGF_struct _ _ fun st σ tree hQ hex =>
    noFault_QX64_code cmpxImageV_noFaultCode (postCmpxV_end P) st σ tree hQ.1 hex

/-! ## The start -/

/-- **A verbatim `lock cmpxchg` spinlock worker at its start**, as the `.kl`
runner sets it up: the laid-out image, no declarations, the pc at the entry
label `worker`, the end at the exit label `done`, and neither symbol's word
in the private memory. No register is constrained. -/
structure StartStateCV (s : State) : Prop where
  exe : s.exe = layout cmpxImageV
  decls : s.decls = {}
  pc : s.st.2 = (_root_.Executable.labels s.exe).label "worker"
  endPc : s.endPc = (_root_.Executable.labels s.exe).label "done"
  split : Split [(symC "lock", 4), (symC "counter", 4)] s.st.1.dmem

omit [Executable.ValidLayout (layout cmpxImageV)] in
theorem StartStateCV.frame {s : State} (h : StartStateCV s) : FrameV (symC "lock") (symC "counter") s.st.1 :=
  ⟨split_dl h.split, split_dc h.split⟩

omit [Executable.ValidLayout (layout cmpxImageV)] in
theorem StartStateCV.st {s : State} (h : StartStateCV s) : s.st = (s.st.1, labC "worker") := by
  refine Prod.ext rfl ?_; rw [h.pc, h.exe]

/-- **The verbatim worker's initial invariant** (thread `tid` of `N`). -/
theorem cmpxInvV_init {N : Nat} (hlc : symC "lock" ≠ symC "counter") (hN32 : N < 2 ^ 32) {tid : Nat}
    (htid : tid < N) {states : List isa.State} {initMem : List (Loc × Val)} {s : isa.State}
    (hs : states[tid]? = some s) (hst : StartStateCV s)
    (hLk0 : (Config.init states initMem).mem.initVal ⟨symC "lock", 4⟩ = 0) :
    (cmpxRuleV_envGF (ghostSys N (symC "lock") (symC "counter")) tid (symC "lock") (symC "counter")
      (ghost0 N (symC "lock") (symC "counter") (Config.init states initMem).mem).rel).Inv True
      (Config.init states initMem)
      (threadRes (Config.init states initMem).mem N ⟨symC "lock", 4⟩ (ghostSys N (symC "lock") (symC "counter")).K
        (ghostSys N (symC "lock") (symC "counter")).F tid)
      (ghost0 N (symC "lock") (symC "counter") (Config.init states initMem).mem) := by
  have hL := ghostSys_spinLocs (N := N) hlc
  have hN0 : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) htid
  have hend : s.endPc = labC "done" := by rw [hst.endPc, hst.exe]
  have hFr : Fr (ghostSys N (symC "lock") (symC "counter")) tid (σInitX (Config.init states initMem)
      (threadRes (Config.init states initMem).mem N ⟨symC "lock", 4⟩ (ghostSys N (symC "lock") (symC "counter")).K
        (ghostSys N (symC "lock") (symC "counter")).F tid)
      (ghost0 N (symC "lock") (symC "counter") (Config.init states initMem).mem)) := by
    refine ⟨world_spinGhost' hL.lk_c, threadRes_fresh' hL htid, ?_, threadRes_lkLe hLk0 _⟩
    intro f hf
    simp [σInitX, Views.getFwd] at hf
  have hsafe := Safely.uncountV
    (cmpxWorkerV_envG (ghostSys N (symC "lock") (symC "counter")) tid _ _ rfl rfl rfl rfl hL hN0 htid hN32
      s.st.1 (_, 0) ⟨hst.frame, hFr⟩)
  rw [← hst.st] at hsafe
  exact invGFX_init (S := spinS (symC "lock") (symC "counter")) (e := layout cmpxImageV) (endPc := labC "done")
    (post := postCmpxV (ghostSys N (symC "lock") (symC "counter"))) hs rfl
    ⟨hst.exe, hst.decls, hend, hst.split, hsafe⟩

/-! ## Scope and purity -/

/-- The verbatim worker's all-release specification (the image, ending at
`done`). -/
noncomputable def cmpxNoNTSpecV : RelPureSpecQX Arch.tso fun _ _ => False where
  S := spinS (symC "lock") (symC "counter")
  le16 := spinS_le16 _ _
  e := layout cmpxImageV
  valid := inferInstance
  endPc := labC "done"
  post x := ∃ _ : Nat, (x.1.2 = labC "done" ∧ True) ∨ False
  post_end _ h := h.elim fun _ h => h.elim And.left False.elim

/-- **The all-release specification holds at a start state.** -/
theorem cmpxNoNTSpecV_holds {s : isa.State} (h : StartStateCV s) : cmpxNoNTSpecV.Holds s := by
  refine ⟨h.exe, by rw [h.endPc, h.exe]; rfl, h.decls, h.split, ?_⟩
  rw [h.st]
  exact Safely.uncountV (cmpxWorkerV_noNT _ _ rfl rfl s.st.1 ((), 0) h.frame)

/-! ## The theorem -/

/-- **`counter = N` for `N` x64 `lock cmpxchg` spinlock workers running
`spinlock_cmpxchg2.kl`'s code verbatim, under `Arch.tso`, on `EnvG`**: the
statement of `CmpxPublic.x64_cmpx_counter_envG'` for the worker as written,
with `(lock)` and `(counter)` (absolute operands).

For every valid layout of the worker's image `cmpxImageV` (the `code` block,
then the `.kl` runner's data trailer that places the symbols `lock` and
`counter`), every number of threads `N < 2 ^ 32`, if the symbols' 4-byte words
are disjoint, `states` consists of `N` threads each at the entry label
`worker` with its end at `done` and neither word in its private memory
(`StartStateCV`; no register is assumed), and the initial memory has both
words at `0`, then every configuration `Reachable` under `Arch.tso` that is
final has the counter word at `N`. -/
theorem x64_cmpx_counter_envG_verbatim {fuel : Nat} (N : Nat)
    (hdisj : Decls.overlaps (symC "lock") 4 (symC "counter") 4 = false)
    (hN32 : N < 2 ^ 32) {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, StartStateCV s) (hN : states.length = N)
    (hC0 : (Config.init states initMem).mem.initVal ⟨symC "counter", 4⟩ = 0)
    (hLk0 : (Config.init states initMem).mem.initVal ⟨symC "lock", 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) cfg)
    (hf : cfg.final = true) :
    cfg.mem.finalVal ⟨symC "counter", 4⟩ = BitVec.ofNat 128 N :=
  CasSmoke.spin_counter_core N hdisj hN hC0 hc hf fun hlc hN0 hfin =>
    final_of_relPureSafelyQX_tsoF (theorem1FChain Arch.tso fuel)
      (B := fun _ r _ => Post N ⟨symC "lock", 4⟩ (ghostSys N (symC "lock") (symC "counter")).K r)
      (Φ := fun cfg => cfg.mem.finalVal ⟨symC "counter", 4⟩ = BitVec.ofNat 128 N)
      (erase_init_lockPred (C := ⟨symC "counter", 4⟩) _ (ghostSys_spinLocs hlc) hN hN0 hC0 hLk0) pend_init
      (fun _ => cmpxNoNTSpecV)
      (fun _ s hs => cmpxNoNTSpecV_holds (hst s (List.mem_of_getElem? hs)))
      (fun tid htid n m => by
        obtain ⟨s, hs⟩ : ∃ s, states[tid]? = some s := ⟨_, List.getElem?_eq_getElem htid⟩
        exact NPSafeF.of_ruleRXF _ n m _ _ _ _
          (cmpxInvV_init hlc hN32 (hN ▸ htid) hs (hst s (List.mem_of_getElem? hs)) hLk0))
      hc hf hfin

end Kraken.Promising.X64.EnvG.CmpxAbs

#print axioms Kraken.Promising.X64.EnvG.CmpxAbs.x64_cmpx_counter_envG_verbatim
#print axioms Kraken.Promising.X64.EnvG.CmpxAbs.cmpxRuleV_envGF_noFault
