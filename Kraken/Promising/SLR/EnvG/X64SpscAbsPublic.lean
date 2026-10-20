/-
**The x64 SPSC queue, `spsc_queue.kl`'s code verbatim**:
`SpscAbs.x64_spsc_envG_verbatim`, the statement of the x64 SPSC proof's
`SpscX.x64_spsc_envG` (`1:r12d=1 ∧ 1:r13d=2 ∧ 1:r14d=3`, the `.kl`'s
`forall`) for the threads as the `.kl` runner runs them: both in the image
`spscImageV` (the `code` block, then the data trailer placing `buf0`,
`buf1`, `head`, `tail`), thread `0` from `producer` to `pdone`, thread `1`
from `consumer` to `cdone`, with the `.kl`'s `rbx = buf0` and `(tail)`,
`(head)` absolute.

- **Both threads on the take route over their masks**:
  `ThreadRuleRXGS.ofSafelyEnvGTXM` (`EnvG/X64MaskLinkTake.lean`) from
  `spscProducerP_envGT`/`spscConsumerC_envGT` (`EnvG/X64SpscAbsVCGen.lean`);
  the phase-1 shapes and the halts are the masks', the fault-freedom the
  image's (`spscImageV_noFaultCode`).
- **Purity**: `spscProducerV_noNT`/`spscConsumerV_noNT` at the unmasked image.
- **Final argument**: the x64 SPSC proof's (`SpscX.spsc_final`, `erase_spscInit`),
  unchanged.
-/
import Kraken.Promising.SLR.EnvG.X64SpscAbsVCGen
import Kraken.Promising.SLR.EnvG.X64SpscPublic
import Kraken.Promising.SLR.EnvG.X64MpInclAbsMask

namespace Kraken.Promising.X64.EnvG.SpscAbs

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.SpscX Kraken.Promising.X64.EnvG.TreiberX

/-- A `Safely` judgment in `SharedEnv.counted env` is one in `env` (a copy of
`MpInclAbs.Safely.uncountM`). -/
theorem Safely.uncountS {e : Kraken.Executable Directive} {env : SharedEnv}
    {post : MachineState × (SharedEnv.counted env).State → Prop} {x : MachineState}
    {g : (SharedEnv.counted env).State} (h : Safely (e.instrStepEnv (SharedEnv.counted env)) post (x, g)) :
    Safely (e.instrStepEnv env) (fun y => ∃ n : Nat, post (y.1, (y.2, n))) (x, g.1) :=
  _root_.Safely.uncountEnv h

/-! ## The masks' shapes (any layout) -/

/-- The producer's cells are phase-1 (`MpInclAbs.readerFragV_dirsPhase1X`'s
script). -/
theorem producerFragV_dirsPhase1X : ∀ d ∈ producerFragV, ∀ (e : _root_.Executable) z,
    DirPhase1X Arch.tso e d z := by
  intro d hd e z s pc
  simp only [producerFragV, spscImageV, spscCodeV, spscDataV, List.cons_append, List.take_succ_cons,
    List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  cells_phase1X

/-- The consumer's cells are phase-1 (the same script). -/
theorem consumerFragV_dirsPhase1X : ∀ d ∈ consumerFragV, ∀ (e : _root_.Executable) z,
    DirPhase1X Arch.tso e d z := by
  intro d hd e z s pc
  simp only [consumerFragV, spscImageV, spscCodeV, spscDataV, List.cons_append, List.drop_succ_cons,
    List.drop_zero, List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  cells_phase1X

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spscImageV)]

/-- **The producer's mask is phase-1** (its kept cells are the producer's;
the consumer's code is masked). -/
theorem spscImageP_phase1 : Phase1TreeX Arch.tso (layout spscImageP) := by
  haveI := spscImageP_valid (layout := layout)
  refine phase1TreeX_of_dirs (dirsPhase1X_layout (mem_maskKeep_range
    (Φd := fun d => ∀ (e : _root_.Executable) z, DirPhase1X Arch.tso e d z) ?_ ?_ ?_))
  · rw [show (spscImageV.drop 0).take (20 - 0) = producerFragV by decide]
    exact producerFragV_dirsPhase1X
  · intro l e z s pc
    simp [_root_.Directive.interp, Kraken.Promising.X64.toEv, Phase1Shape, DetAccess, SingleAccessS, AccessFree]
  · intro e z s pc
    simp [_root_.Directive.interp, Kraken.Promising.X64.toEv, Phase1Shape, DetAccess, SingleAccessS, AccessFree]

/-- **The consumer's mask is phase-1** (its kept cells are the consumer's). -/
theorem spscImageC_phase1 : Phase1TreeX Arch.tso (layout spscImageC) := by
  haveI := spscImageC_valid (layout := layout)
  refine phase1TreeX_of_dirs (dirsPhase1X_layout (mem_maskKeep_range
    (Φd := fun d => ∀ (e : _root_.Executable) z, DirPhase1X Arch.tso e d z) ?_ ?_ ?_))
  · rw [show (spscImageV.drop 20).take (54 - 20) = consumerFragV by decide]
    exact consumerFragV_dirsPhase1X
  · intro l e z s pc
    simp [_root_.Directive.interp, Kraken.Promising.X64.toEv, Phase1Shape, DetAccess, SingleAccessS, AccessFree]
  · intro e z s pc
    simp [_root_.Directive.interp, Kraken.Promising.X64.toEv, Phase1Shape, DetAccess, SingleAccessS, AccessFree]

omit [Executable.ValidLayout (layout spscImageV)] in
/-- The image's non-data cells are fault-free. -/
theorem spscImageV_noFaultCode : DirsNoFaultCode (layout spscImageV) := by
  dirs_no_fault_code spscImageV spscCodeV spscDataV

/-! ## The halts -/

set_option maxRecDepth 8192 in
omit [Executable.ValidLayout (layout spscImageV)] in
/-- `pdone`'s address is the producer's mask's cell `21` (behind the labels
`pdone:` and `consumer:`). -/
theorem labS_pdone [Executable.ValidLayout (layout spscImageV)] :
    labS "pdone" = (layout spscImageP).addrOf 21 := by
  have hd : labS "pdone" = (layout spscImageV).addrOf 19 :=
    Program.label_addrOf_drop spscImageV_wf.nodup (by decide) (by decide)
  have h19 : (layout spscImageV).2[19]? = some (Directive.label "pdone", Kraken.Layout.size Directive 19) := by
    simp [Layout.apply_snd, Layout.frag, spscImageV, spscCodeV, spscDataV]
  have h20 : (layout spscImageV).2[20]? = some (Directive.label "consumer", Kraken.Layout.size Directive 20) := by
    simp [Layout.apply_snd, Layout.frag, spscImageV, spscCodeV, spscDataV]
  rw [addrOf_mask spscImageP_mask, Executable.addrOf_succ _ h20,
    Executable.ValidLayout.label_size 20 "consumer" _ h20, Executable.addrOf_succ _ h19,
    Executable.ValidLayout.label_size 19 "pdone" _ h19, hd]
  simp

/-- **No step of the producer's mask at the exit label `pdone`.** -/
theorem prodP_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labS "pdone" → ¬ (layout spscImageP).instrStepEnv env x R := by
  haveI := spscImageP_valid (layout := layout)
  rw [labS_pdone]
  exact not_instrStepEnv_of_byteArray (i := 21) (b := .mk #[]) env spscImageP_21

set_option maxRecDepth 8192 in
omit [Executable.ValidLayout (layout spscImageV)] in
/-- `cdone`'s address is the consumer's mask's cell `54`. -/
theorem labS_cdone [Executable.ValidLayout (layout spscImageV)] :
    labS "cdone" = (layout spscImageC).addrOf 54 := by
  have hd : labS "cdone" = (layout spscImageV).addrOf 53 :=
    Program.label_addrOf_drop spscImageV_wf.nodup (by decide) (by decide)
  have h53 : (layout spscImageV).2[53]? = some (Directive.label "cdone", Kraken.Layout.size Directive 53) := by
    simp [Layout.apply_snd, Layout.frag, spscImageV, spscCodeV, spscDataV]
  rw [addrOf_mask spscImageC_mask, Executable.addrOf_succ _ h53,
    Executable.ValidLayout.label_size 53 "cdone" _ h53, hd]
  simp

/-- **No step of the consumer's mask at the exit label `cdone`.** -/
theorem consC_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labS "cdone" → ¬ (layout spscImageC).instrStepEnv env x R := by
  haveI := spscImageC_valid (layout := layout)
  rw [labS_cdone]
  exact not_instrStepEnv_of_byteArray (i := 54) (b := .mk #[]) env spscImageC_54

/-! ## The rules -/

/-- The producer's postcondition: the exit label and all of `T` (the
counter projected away). -/
abbrev postPA (P : SP) : MachineState × EStateX → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labS "pdone" ∧ (x.2.r.wr P.T).q = 1) ∨ False

omit [Executable.ValidLayout (layout spscImageV)] in
theorem postPA_end (P : SP) : ∀ y, postPA P y → y.1.2 = labS "pdone" :=
  fun _ ⟨_, h⟩ => h.elim And.left False.elim

omit [Executable.ValidLayout (layout spscImageV)] in
/-- **`hB` for the verbatim producer** (`SpscX.hB_P`'s proof). -/
theorem hB_PA (P : SP) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postPA P (t.st.st, σ) → t.prom = [] → EnvRel tid (prodPlan P) σ c t r g cl → cl → SpscPost P c r g := by
  rintro c t r g cl σ ⟨_, hpost⟩ hp hrel -
  obtain ⟨-, hq⟩ := hpost.resolve_right id
  obtain rfl : r = σ.r := by
    rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
    · rfl
    · rw [hp] at hts; cases hts
  exact .inl (by rw [hq]; decide)

/-- **The verbatim producer's rule** (take route, over its mask). -/
def prodRuleA (P : SP) (hL : SpscLocs P) (tid : Nat) : ThreadRuleRXGS (I := isa) G₀ Arch.tso (SpscPost P) tid :=
  ThreadRuleRXGS.ofSafelyEnvGTXM (S := spscS P) (post := postPA P) spscImageP_mask (prodPlan_valid hL)
    (spscS_le16 P) spscImageP_phase1 (postPA_end P) (prodP_stuck _) (hB_PA P tid)

/-- **The verbatim producer's rule excludes faults.** -/
theorem prodRuleA_noFault (P : SP) (hL : SpscLocs P) (tid : Nat) : NoFaultRuleSX (prodRuleA P hL tid) :=
  noFaultRule_ofSafelyEnvGTXM _ _ _ _ _ _ _ spscImageV_noFaultCode

/-- The consumer's postcondition: the exit label and, under the clean flag,
`Got 3`. -/
abbrev postCA : MachineState × EStateX → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labS "cdone" ∧ (x.2.cl → Got 3 x.1.1)) ∨ False

omit [Executable.ValidLayout (layout spscImageV)] in
theorem postCA_end : ∀ y, postCA y → y.1.2 = labS "cdone" :=
  fun _ ⟨_, h⟩ => h.elim And.left False.elim

omit [Executable.ValidLayout (layout spscImageV)] in
/-- **`hB` for the verbatim consumer** (`SpscX.hB_C`'s proof). -/
theorem hB_CA (P : SP) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postCA (t.st.st, σ) → t.prom = [] → EnvRel 1 (consPlan P) σ c t r g cl → cl → SpscPost P c r g := by
  rintro c t r g cl σ ⟨_, hpost⟩ - hrel hcl
  obtain ⟨-, hx⟩ := hpost.resolve_right id
  obtain ⟨h12, h13, h14⟩ := hx (hrel.cl hcl)
  exact .inr ⟨t, hrel.ht, h12 (by decide), h13 (by decide), h14 (by decide)⟩

/-- **The verbatim consumer's rule** (take route, over its mask, thread `1`). -/
def consRuleA (P : SP) (hL : SpscLocs P) : ThreadRuleRXGS (I := isa) G₀ Arch.tso (SpscPost P) 1 :=
  ThreadRuleRXGS.ofSafelyEnvGTXM (S := spscS P) (post := postCA) spscImageC_mask (consPlan_valid hL)
    (spscS_le16 P) spscImageC_phase1 postCA_end (consC_stuck _) (hB_CA P)

/-- **The verbatim consumer's rule excludes faults.** -/
theorem consRuleA_noFault (P : SP) (hL : SpscLocs P) : NoFaultRuleSX (consRuleA P hL) :=
  noFaultRule_ofSafelyEnvGTXM _ _ _ _ _ _ _ spscImageV_noFaultCode

/-! ## The start -/

/-- **The verbatim producer at its start**, as the runner sets it up: the
image, no declarations, pc at `producer`, end at `pdone`, the `.kl`'s
`0:rbx=buf0`, and a private memory that maps no byte. -/
structure StartPV (s : State) : Prop where
  exe : s.exe = layout spscImageV
  decls : s.decls = {}
  pc : s.st.2 = labS "producer"
  endPc : s.endPc = labS "pdone"
  rbx : s.st.1.regs.get64 .rbx = symS "buf0"
  dmem : ∀ k, s.st.1.dmem.get? k = none

/-- **The verbatim consumer at its start**: pc at `consumer`, end at
`cdone`, the `.kl`'s `1:rbx=buf0`. -/
structure StartCV (s : State) : Prop where
  exe : s.exe = layout spscImageV
  decls : s.decls = {}
  pc : s.st.2 = labS "consumer"
  endPc : s.endPc = labS "cdone"
  rbx : s.st.1.regs.get64 .rbx = symS "buf0"
  dmem : ∀ k, s.st.1.dmem.get? k = none

/-- The queue's words at the image's symbols. -/
abbrev spscP : SP := ⟨symS "buf0", symS "head", symS "tail"⟩

section Start

variable {sP sC : isa.State} {initMem : List (Loc × Val)}

/-- **The verbatim producer's initial invariant** (thread `0`). -/
theorem invPA_init (hL : SpscLocs spscP) (hP : StartPV sP)
    (hT0 : (Config.init [sP, sC] initMem).mem.initVal ⟨symS "tail", 4⟩ = 0)
    (hH0 : (Config.init [sP, sC] initMem).mem.initVal ⟨symS "head", 4⟩ = 0) :
    (prodRuleA spscP hL 0).Inv True (Config.init [sP, sC] initMem)
      (spscRes (Config.init [sP, sC] initMem).mem spscP 0) (spscGhost spscP) := by
  have hst : sP.st = (sP.st.1, labS "producer") := Prod.ext rfl hP.pc
  refine invGTXM_init (s := sP) rfl rfl ⟨hP.exe, hP.decls, hP.endPc, split_of_empty hP.dmem, ?_⟩
  rw [hst]
  exact Safely.uncountS (spscProducerP_envGT spscP hL 0 rfl rfl sP.st.1
    (σInitX (Config.init [sP, sC] initMem) (spscRes (Config.init [sP, sC] initMem).mem spscP 0) (spscGhost spscP), 0)
    ⟨⟨hP.rbx, dFrame_of_empty hP.dmem⟩, PR_init hL hT0 hH0⟩)

/-- **The verbatim consumer's initial invariant** (thread `1`). -/
theorem invCA_init (hL : SpscLocs spscP) (hC : StartCV sC)
    (hT0 : (Config.init [sP, sC] initMem).mem.initVal ⟨symS "tail", 4⟩ = 0)
    (hH0 : (Config.init [sP, sC] initMem).mem.initVal ⟨symS "head", 4⟩ = 0) :
    (consRuleA spscP hL).Inv True (Config.init [sP, sC] initMem)
      (spscRes (Config.init [sP, sC] initMem).mem spscP 1) (spscGhost spscP) := by
  have hst : sC.st = (sC.st.1, labS "consumer") := Prod.ext rfl hC.pc
  refine invGTXM_init (s := sC) rfl rfl ⟨hC.exe, hC.decls, hC.endPc, split_of_empty hC.dmem, ?_⟩
  rw [hst]
  exact Safely.uncountS (spscConsumerC_envGT spscP hL 1 rfl rfl sC.st.1
    (σInitX (Config.init [sP, sC] initMem) (spscRes (Config.init [sP, sC] initMem).mem spscP 1) (spscGhost spscP), 0)
    ⟨⟨hC.rbx, dFrame_of_empty hC.dmem⟩, CS_init hL hT0 hH0⟩)

/-- **The `NPSafeP` side** for the verbatim threads. -/
theorem spscV_npSafe (hL : SpscLocs spscP) (hP : StartPV sP) (hC : StartCV sC)
    (hT0 : (Config.init [sP, sC] initMem).mem.initVal ⟨symS "tail", 4⟩ = 0)
    (hH0 : (Config.init [sP, sC] initMem).mem.initVal ⟨symS "head", 4⟩ = 0) :
    ∀ tid, tid < [sP, sC].length → ∀ n m, NPSafeP (model isa) Arch.tso (SpscPost spscP) tid G₀
      (K2Scope (model isa) AllocIds) n m True (Config.init [sP, sC] initMem)
      (spscRes (Config.init [sP, sC] initMem).mem spscP tid) (spscGhost spscP) := by
  intro tid htid n m
  rcases tid with _ | _ | k
  · exact NPSafeP.of_ruleRXGS (prodRuleA spscP hL 0) n m _ _ _ _ (invPA_init hL hP hT0 hH0)
  · exact NPSafeP.of_ruleRXGS (consRuleA spscP hL) n m _ _ _ _ (invCA_init hL hC hT0 hH0)
  · simp only [List.length_cons, List.length_nil] at htid; omega

end Start

/-! ## Purity -/

/-- The verbatim threads' all-release specifications (the image, unmasked,
both at `sAll`). -/
noncomputable def spscNoNTSpecV : Nat → RelPureSpecQX Arch.tso fun _ _ => False
  | 0 =>
    { S := sAll
      le16 := sAll_le16
      e := layout spscImageV
      valid := inferInstance
      endPc := labS "pdone"
      post := fun x => ∃ _ : Nat, (x.1.2 = labS "pdone" ∧ True) ∨ False
      post_end := fun _ h => h.elim fun _ h => h.elim And.left False.elim }
  | _ + 1 =>
    { S := sAll
      le16 := sAll_le16
      e := layout spscImageV
      valid := inferInstance
      endPc := labS "cdone"
      post := fun x => ∃ _ : Nat, (x.1.2 = labS "cdone" ∧ True) ∨ False
      post_end := fun _ h => h.elim fun _ h => h.elim And.left False.elim }

/-- **The all-release specifications hold at the start states.** -/
theorem spscNoNTSpecV_init {sP sC : State} (hP : StartPV sP) (hC : StartCV sC) :
    ∀ tid s, [sP, sC][tid]? = some s → (spscNoNTSpecV tid).Holds s
  | 0, s, hs => by
    cases hs
    refine ⟨hP.exe, hP.endPc, hP.decls, split_of_empty hP.dmem, ?_⟩
    rw [show sP.st = (sP.st.1, labS "producer") from Prod.ext rfl hP.pc]
    exact Safely.uncountS (spscProducerV_noNT sP.st.1 ((), 0) (dFrame_of_empty hP.dmem))
  | 1, s, hs => by
    cases hs
    refine ⟨hC.exe, hC.endPc, hC.decls, split_of_empty hC.dmem, ?_⟩
    rw [show sC.st = (sC.st.1, labS "consumer") from Prod.ext rfl hC.pc]
    exact Safely.uncountS (spscConsumerV_noNT sC.st.1 ((), 0) (dFrame_of_empty hC.dmem))
  | _ + 2, _, hs => by cases hs

/-! ## The theorem -/

/-- **The x64 SPSC queue under `Arch.tso`, `spsc_queue.kl`'s code verbatim**
(`SpscX.x64_spsc_envG` for the runner's threads).

For every valid layout of the image `spscImageV` (the `code` block, then
the runner's data trailer placing `buf0`, `buf1`, `head`, `tail`): if the
words at `buf0`, `buf0 + 256`, `head`, `tail` are pairwise distinct
(`SpscLocs`), thread `0` starts at `producer` with end `pdone` and thread
`1` at `consumer` with end `cdone`, both with `rbx = buf0` and a private
memory that maps no byte (`StartPV`, `StartCV`), and `tail`, `head` are
initially `0`, then every final configuration reachable under `Arch.tso`
has the consumer's `r12d = 1`, `r13d = 2`, `r14d = 3` (the `.kl`'s
`forall (1:r12=1 /\ 1:r13=2 /\ 1:r14=3)`, on the low 32 bits).

Frame, as against `SpscX.x64_spsc_envG`: no hypothesis on `rdi`/`rsi`
(`(tail)`/`(head)` are absolute here, and the `.kl` does not set those
registers); the threads' frame is `FrameA` (`rbx = buf0`, no 4-byte word in
the private memory). -/
theorem x64_spsc_envG_verbatim {fuel : Nat} (hL : SpscLocs spscP)
    {sP sC : isa.State} {initMem : List (Loc × Val)} (hP : StartPV sP) (hC : StartCV sC)
    (hT0 : (Config.init [sP, sC] initMem).mem.initVal ⟨symS "tail", 4⟩ = 0)
    (hH0 : (Config.init [sP, sC] initMem).mem.initVal ⟨symS "head", 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [sP, sC] initMem) cfg)
    (hf : cfg.final = true) :
    ∃ th, cfg.threads[1]? = some th ∧ BitVec.setWidth 32 (th.st.st.1.regs.get64 .r12) = 1 ∧
      BitVec.setWidth 32 (th.st.st.1.regs.get64 .r13) = 2 ∧ BitVec.setWidth 32 (th.st.st.1.regs.get64 .r14) = 3 :=
  final_of_relPureSafelyQX_tsoS fuel (B := SpscPost spscP) (Φ := ConsDone)
    (erase_spscInit hL _ hT0 hH0) pend_spscGhost spscNoNTSpecV (spscNoNTSpecV_init hP hC)
    (spscV_npSafe hL hP hC hT0 hH0) hc hf
    fun _ _ E' _ hsize hB => spsc_final E' hf hsize hB

end Kraken.Promising.X64.EnvG.SpscAbs

#print axioms Kraken.Promising.X64.EnvG.SpscAbs.x64_spsc_envG_verbatim
#print axioms Kraken.Promising.X64.EnvG.SpscAbs.prodRuleA_noFault
#print axioms Kraken.Promising.X64.EnvG.SpscAbs.consRuleA_noFault
