/-
**Dekker with `mfence` on x64, verbatim: the public theorem**: `x64_dekker_public_verbatim`, the property of
`Kraken/Examples/LockFree/X64/dekker_mfence.kl` for its code as written
(`dkWorkerV`, the absolute operand `(counter)`), in the shape of
the Dekker proof's `Dekker.x64_dekker_public` (which proves the rewritten worker
`worker`, `(%rbx)`, from `%rbx = C`; it stays unchanged).

Both threads run the image `dkImageV` (the code, then the `.kl` runner's data
trailer: `EnvG/DekkerAbsVCGen.lean`) under one valid layout, as the runner
lays them out; the flags and the counter are the symbols' addresses
`symD "flag0"`, `symD "flag1"`, `symD "counter"`. As the `.kl` sets it up
(`0:rsi=flag0; 0:rdi=flag1; 1:rsi=flag1; 1:rdi=flag0`), thread `0` starts
with `%rsi`/`%rdi` at `flag0`/`flag1` and thread `1` the other way round,
each at the entry label `worker` with its end at the exit label `done`
(`StartDV`).

- **Rule** (`dkRuleV`): `ThreadRuleRX.ofSafelyEnvGX` at the image,
  `Phase1TreeX` per directive (`dkImageV_phase1`), the halt at `done` from the
  trailer's first data cell (`not_instrStepEnv_of_byteArray`), `hB` as
  `Dekker.hB_D`.
- **Start** (`invDV_init`): `invGX_init` from `dkWorkerV_envG` (uncounted).
- **Purity** (`dkNoNTSpecV`): from `dkWorkerV_noNT`.
- **Assembly**: `final_of_relPureSafelyQX_tso` with the Dekker proof's initial
  erasure (`erase_dkInit`) and final argument (`dk_final`).

Not covered here (as for `x64_dekker_public`): the declarations (`decls =
{}`), final configurations only. No-fault is the rule's fact
`dkRuleV_noFault` (`EnvG/X64ImageNoFault.lean`: the thread never runs the
trailer's `unimplemented` data cells).
-/
import Kraken.Promising.SLR.EnvG.DekkerAbsVCGen
import Kraken.Promising.SLR.EnvG.DekkerPublicX
import Kraken.Promising.SLR.EnvG.X64SpinAbsPublic
import Kraken.Promising.SLR.EnvG.X64ImageNoFault

namespace Kraken.Promising.X64.EnvG.DekkerAbs

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.EnvG.Dekker
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Dekker

variable [layout : _root_.Layout] [Executable.ValidLayout (layout dkImageV)]

/-! ## The rule -/

/-- The image's trees are phase-1 (over the code and the trailer). -/
theorem dkImageV_phase1 : Phase1TreeX Arch.tso (layout dkImageV) := by
  refine phase1TreeX_of_dirs (dirsPhase1X_layout ?_)
  intro d hd e z s pc
  simp only [dkImageV, dkWorkerV, dkDataV, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals simp [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    Kraken.Promising.X64.toEv, Kraken.Promising.SLR.EnvG.Phase1Shape, Kraken.Promising.SLR.EnvG.DetAccess,
    Kraken.Promising.SLR.EnvG.SingleAccessS, Kraken.Promising.SLR.EnvG.AccessFree,
    _root_.MachineData.load, _root_.MachineData.store,
    _root_.RegOrMem.interp, _root_.Operand.interp, _root_.MachineData.set, _root_.RelRegOrMem.interp]
  all_goals (repeat' (first | split |
    simp [Kraken.Promising.X64.toEv, Kraken.Promising.SLR.EnvG.DetAccess,
      Kraken.Promising.SLR.EnvG.SingleAccessS, Kraken.Promising.SLR.EnvG.AccessFree,
      Kraken.Promising.EvTree.access_empty]))

/-- The exit label `done` is the address of the trailer's first data cell. -/
theorem labD_done : labD "done" = (layout dkImageV).addrOf 14 := by
  have hd : (_root_.Executable.labels (layout dkImageV)).label "done" = (layout dkImageV).addrOf 13 :=
    Program.label_addrOf_drop dkImageV_wf.nodup (by decide) (by decide)
  have h13 : (layout dkImageV).2[13]? = some (Directive.label "done", Kraken.Layout.size Directive 13) := by
    simp [Layout.apply_snd, Layout.frag, dkImageV, dkWorkerV, dkDataV]
  rw [Executable.addrOf_succ _ h13, Executable.ValidLayout.label_size 13 "done" _ h13]
  simpa using hd

/-- No instruction steps at the exit label. -/
theorem dkImageV_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labD "done" → ¬ (layout dkImageV).instrStepEnv env x R := by
  rw [labD_done]
  exact not_instrStepEnv_of_byteArray (i := 14) (b := .mk #[]) env (by decide)

/-- The worker's postcondition: the exit label and `edx = 1 → D6`. -/
abbrev postDV (tid : Nat) (f o c : BitVec 64) : MachineState × EStateX → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labD "done" ∧ ((x.1.1.regs.get64 .rdx).setWidth 32 = 1 → D6 tid f o c x.2)) ∨ False

omit [Executable.ValidLayout (layout dkImageV)] in
theorem postDV_end (tid : Nat) (f o c : BitVec 64) : ∀ y, postDV tid f o c y → y.1.2 = labD "done" :=
  fun _ ⟨_, h⟩ => h.elim And.left False.elim

omit [Executable.ValidLayout (layout dkImageV)] in
/-- **`hB` for the verbatim worker** (`Dekker.hB_D`). -/
theorem hB_DV (tid : Nat) (f o c : BitVec 64) : ∀ (cfg : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postDV tid f o c (t.st.st, σ) → t.prom = [] → EnvRel tid dkPlan σ cfg t r g cl → cl →
      DkThreadEnd tid f o c cfg r := by
  rintro cfg t r g cl σ ⟨_, hpost⟩ hp hrel - th hth hrdx
  obtain ⟨-, hD⟩ := hpost.resolve_right id
  obtain rfl : r = σ.r := by
    rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
    · rfl
    · rw [hp] at hts; cases hts
  obtain rfl : th = t := Option.some.inj (hth.symm.trans hrel.ht)
  obtain ⟨t', rr, trc, a, tc, u, he, hres⟩ := hD hrdx
  exact ⟨t', rr, trc, a, tc, u, (memLe_snap hrel.snap).entered he, hres.qF, hres.xF, hres.qC, hres.xC⟩

/-- **Dekker's verbatim worker rule on `EnvG`** (`Arch.tso`), for any shared
postcondition `B` implied by the thread's `DkThreadEnd`. -/
def dkRuleV (tid : Nat) (f o c : BitVec 64)
    {B : Config isa → Res → Ghost → Prop} (hB : ∀ cfg r g, DkThreadEnd tid f o c cfg r → B cfg r g) :
    ThreadRuleRX (I := isa) Arch.tso B tid :=
  ThreadRuleRX.ofSafelyEnvGX (S := dkS f o c) (post := postDV tid f o c) dkPlan_valid (dkS_le16 f o c)
    dkImageV_phase1 (postDV_end tid f o c) (dkImageV_stuck _)
    (fun cfg t r g cl σ h1 h2 h3 h4 => hB cfg r g (hB_DV tid f o c cfg t r g cl σ h1 h2 h3 h4))

omit [Executable.ValidLayout (layout dkImageV)] in
/-- The image's non-data cells are fault-free. -/
theorem dkImageV_noFaultCode : DirsNoFaultCode (layout dkImageV) := by
  dirs_no_fault_code dkImageV dkWorkerV dkDataV

/-- **The verbatim worker's rule excludes faults** (`DirsNoFaultCode`: the
thread never runs the trailer's data cells). -/
theorem dkRuleV_noFault (tid : Nat) (f o c : BitVec 64)
    {B : Config isa → Res → Ghost → Prop} (hB : ∀ cfg r g, DkThreadEnd tid f o c cfg r → B cfg r g) :
    NoFaultRule (dkRuleV tid f o c hB) := by
  unfold dkRuleV ThreadRuleRX.ofSafelyEnvGX
  exact noFaultRule_ofEnvG_struct _ _ (noFault_QX64_code dkImageV_noFaultCode (postDV_end tid f o c))

/-! ## The start -/

/-- **A verbatim Dekker worker at its start**, as the `.kl` runner sets it
up: the laid-out image, no declarations, the pc at the entry label `worker`,
the end at the exit label `done`, `%rsi` its own flag `f`, `%rdi` the other
flag `o`, and none of the three words (the counter is the symbol) in the
private memory. -/
structure StartDV (f o : BitVec 64) (s : State) : Prop where
  exe : s.exe = layout dkImageV
  decls : s.decls = {}
  pc : s.st.2 = (_root_.Executable.labels s.exe).label "worker"
  endPc : s.endPc = (_root_.Executable.labels s.exe).label "done"
  rsi : s.st.1.regs.get64 .rsi = f
  rdi : s.st.1.regs.get64 .rdi = o
  split : Split (dkS f o (symD "counter")) s.st.1.dmem

omit [Executable.ValidLayout (layout dkImageV)] in
theorem StartDV.frame {f o : BitVec 64} {s : State} (h : StartDV f o s) :
    FrameDV f o (symD "counter") s.st.1 :=
  ⟨h.rsi, h.rdi, h.split.loadInt_none (by simp) (by decide) (by decide),
    h.split.loadInt_none (by simp) (by decide) (by decide), h.split.loadInt_none (by simp) (by decide) (by decide)⟩

omit [Executable.ValidLayout (layout dkImageV)] in
theorem StartDV.st {f o : BitVec 64} {s : State} (h : StartDV f o s) : s.st = (s.st.1, labD "worker") := by
  refine Prod.ext rfl ?_; rw [h.pc, h.exe]

/-- **A verbatim worker's initial invariant**. -/
theorem invDV_init (tid : Nat) {f o : BitVec 64} (hL : Locs f o (symD "counter"))
    {B : Config isa → Res → Ghost → Prop} (hB : ∀ cfg r g, DkThreadEnd tid f o (symD "counter") cfg r → B cfg r g)
    {ss : List isa.State} {initMem : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    (hS : StartDV f o s) (hf0 : (Config.init ss initMem).mem.initVal ⟨f, 4⟩ = 0)
    (hc0 : (Config.init ss initMem).mem.initVal ⟨symD "counter", 4⟩ = 0) :
    (dkRuleV tid f o (symD "counter") hB).Inv True (Config.init ss initMem)
      (Res.initOf (Config.init ss initMem).mem (dkFrac ⟨f, 4⟩ ⟨symD "counter", 4⟩) (dkFrac_nonneg _ _))
      dkGhost := by
  have hend : s.endPc = labD "done" := by rw [hS.endPc, hS.exe]
  have hsafe := SpinAbs.Safely.uncountV
    (dkWorkerV_envG tid f o (symD "counter") rfl hL s.st.1
      (σInitX (Config.init ss initMem)
        (Res.initOf (Config.init ss initMem).mem (dkFrac ⟨f, 4⟩ ⟨symD "counter", 4⟩) (dkFrac_nonneg _ _))
        dkGhost, 0)
      ⟨hS.frame, d0_init (g := dkGhost) hL (fun _ => rfl) hf0 hc0⟩)
  rw [← hS.st] at hsafe
  exact invGX_init (S := dkS f o (symD "counter")) (e := layout dkImageV) (endPc := labD "done")
    (post := postDV tid f o (symD "counter")) hs rfl ⟨hS.exe, hS.decls, hend, hS.split, hsafe⟩

/-! ## `NPSafe` -/

/-- **The `NPSafe` side for verbatim Dekker**: thread `0` with own flag
`flag0`, thread `1` with own flag `flag1`. -/
theorem x64_dekker_npSafe_verbatim (hL : Locs (symD "flag0") (symD "flag1") (symD "counter"))
    {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartDV (symD "flag0") (symD "flag1") s0) (h1 : StartDV (symD "flag1") (symD "flag0") s1)
    (hF0 : (Config.init [s0, s1] initMem).mem.initVal ⟨symD "flag0", 4⟩ = 0)
    (hF1 : (Config.init [s0, s1] initMem).mem.initVal ⟨symD "flag1", 4⟩ = 0)
    (hC : (Config.init [s0, s1] initMem).mem.initVal ⟨symD "counter", 4⟩ = 0) :
    ∀ tid, tid < [s0, s1].length → ∀ n m,
      NPSafe (model isa) Arch.tso (DkB (symD "flag0") (symD "flag1") (symD "counter")) tid n m True
        (Config.init [s0, s1] initMem)
        (dkRes (Config.init [s0, s1] initMem).mem ⟨symD "flag0", 4⟩ ⟨symD "flag1", 4⟩ ⟨symD "counter", 4⟩ tid)
        dkGhost := by
  intro tid htid n m
  rcases tid with _ | _ | k
  · exact NPSafe.of_ruleRX _ n m _ _ _ _ (invDV_init 0 hL (fun _ _ _ h => .inl h) rfl h0 hF0 hC)
  · exact NPSafe.of_ruleRX _ n m _ _ _ _
      (invDV_init 1 ⟨Ne.symm hL.fo, hL.oc, hL.fc⟩ (fun _ _ _ h => .inr h) rfl h1 hF1 hC)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-! ## Scope and purity -/

/-- The verbatim worker's all-release specification (own flag `f`, other
flag `o`; the image, ending at `done`). -/
noncomputable def dkNoNTSpecV (f o : BitVec 64) : RelPureSpecQX Arch.tso fun _ _ => False where
  S := dkS f o (symD "counter")
  le16 := dkS_le16 _ _ _
  e := layout dkImageV
  valid := inferInstance
  endPc := labD "done"
  post x := ∃ _ : Nat, (x.1.2 = labD "done" ∧ True) ∨ False
  post_end _ h := h.elim fun _ h => h.elim And.left False.elim

/-- **The all-release specification holds at a start state.** -/
theorem dkNoNTSpecV_holds {f o : BitVec 64} {s : isa.State} (h : StartDV f o s) : (dkNoNTSpecV f o).Holds s := by
  refine ⟨h.exe, by rw [h.endPc, h.exe]; rfl, h.decls, h.split, ?_⟩
  rw [h.st]
  exact SpinAbs.Safely.uncountV (dkWorkerV_noNT _ _ _ rfl s.st.1 ((), 0) h.frame)

/-- The two threads' specifications. -/
noncomputable def dkNoNTSpecsV : Nat → RelPureSpecQX Arch.tso fun _ _ => False
  | 0 => dkNoNTSpecV (symD "flag0") (symD "flag1")
  | _ + 1 => dkNoNTSpecV (symD "flag1") (symD "flag0")

theorem dkNoNTSpecsV_init {s0 s1 : isa.State}
    (h0 : StartDV (symD "flag0") (symD "flag1") s0) (h1 : StartDV (symD "flag1") (symD "flag0") s1) :
    ∀ tid s, [s0, s1][tid]? = some s → (dkNoNTSpecsV tid).Holds s
  | 0, s, hs => by cases hs; exact dkNoNTSpecV_holds h0
  | 1, s, hs => by cases hs; exact dkNoNTSpecV_holds h1
  | _ + 2, _, hs => by cases hs

/-! ## The theorem -/

/-- **Dekker with `mfence` for x64 under `Arch.tso`, `dekker_mfence.kl`'s code
verbatim, on `EnvG`** (`~exists (0:edx=1 /\ 1:edx=1 /\ [counter]=1)`): the
statement of `Dekker.x64_dekker_public` for the worker as written, with
`(counter)` (absolute operand).

For every valid layout of the worker's image `dkImageV` (the `code` block,
then the `.kl` runner's data trailer that places `flag0`, `flag1`,
`counter`): if the three symbols' 4-byte words are distinct (`Locs`), thread
`0` starts with `%rsi = flag0`, `%rdi = flag1` and thread `1` with
`%rsi = flag1`, `%rdi = flag0` (as the `.kl` sets them), each at the entry
label `worker` with its end at `done` and none of the words in its private
memory (`StartDV`), and the three words are initially `0`, then no final
configuration `Reachable` under `Arch.tso` has both threads' `edx` at `1` and
the counter at `1`. -/
theorem x64_dekker_public_verbatim {fuel : Nat} (hL : Locs (symD "flag0") (symD "flag1") (symD "counter"))
    {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartDV (symD "flag0") (symD "flag1") s0) (h1 : StartDV (symD "flag1") (symD "flag0") s1)
    (hF0 : (Config.init [s0, s1] initMem).mem.initVal ⟨symD "flag0", 4⟩ = 0)
    (hF1 : (Config.init [s0, s1] initMem).mem.initVal ⟨symD "flag1", 4⟩ = 0)
    (hC : (Config.init [s0, s1] initMem).mem.initVal ⟨symD "counter", 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) :
    ¬ ((∃ t, cfg.threads[0]? = some t ∧ (t.st.st.1.regs.get64 .rdx).setWidth 32 = 1) ∧
      (∃ t, cfg.threads[1]? = some t ∧ (t.st.st.1.regs.get64 .rdx).setWidth 32 = 1) ∧
      cfg.mem.finalVal ⟨symD "counter", 4⟩ = 1) :=
  final_of_relPureSafelyQX_tso fuel (B := DkB (symD "flag0") (symD "flag1") (symD "counter"))
    (Φ := fun c => ¬ ((∃ t, c.threads[0]? = some t ∧ (t.st.st.1.regs.get64 .rdx).setWidth 32 = 1) ∧
      (∃ t, c.threads[1]? = some t ∧ (t.st.st.1.regs.get64 .rdx).setWidth 32 = 1) ∧
      c.mem.finalVal ⟨symD "counter", 4⟩ = 1))
    (erase_dkInit _ hL) pend_dkGhost dkNoNTSpecsV (dkNoNTSpecsV_init h0 h1)
    (x64_dekker_npSafe_verbatim hL h0 h1 hF0 hF1 hC) hc hf
    fun _ _ E' _ hsize hB ⟨e0, e1, hv⟩ => dk_final hL E' hf hsize hB e0 e1 hv

end Kraken.Promising.X64.EnvG.DekkerAbs

#print axioms Kraken.Promising.X64.EnvG.DekkerAbs.x64_dekker_public_verbatim
#print axioms Kraken.Promising.X64.EnvG.DekkerAbs.dkRuleV_noFault
