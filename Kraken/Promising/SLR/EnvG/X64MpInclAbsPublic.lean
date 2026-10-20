/-
**x64 MP with an unlocked `incl` release, `mp_incl.kl`'s code verbatim, with
the flag's final value**:
`MpInclAbs.x64_mp_incl_envGV_verbatim`, the statement of
`MpIncV.x64_mp_incl_envGV` (`1:ebx=42 ∧ [d]=42 ∧ [f]=1`, the `.kl`'s full
`forall`) for the threads as the `.kl` runner runs them: both in the image
`mpInclImageV` (the x64 absolute-address proofs': the `code` block, then the data trailer placing
`d` and `f`), thread `0` from `writer` to `wdone`, thread `1` from `reader`
to `rdone`, with the `.kl`'s registers `%rdi = f`, `%rsi = d`.

- **Writer**: `ThreadRuleRX.ofSafelyEnvGLRVXM` (`EnvG/X64MaskLinkMore.lean`)
  over the writer's mask `mpInclImageW`, from `writerW_envG`
  (`EnvG/X64MpInclAbsMask.lean`), with `MpPostF`.
- **Reader**: `ThreadRuleRX.ofSafelyEnvGXM` over the reader's mask
  `mpInclImageR`, from `readerR_envG`.
- **Purity**: the x64 absolute-address proofs' `writerV_noNT`/`readerV_noNT` at the unmasked image.
- **Final argument**: the existing one (`MpInc.mp_finalI`, `MpIncV.flag_finalF`),
  unchanged.
-/
import Kraken.Promising.SLR.EnvG.X64MpInclAbsMask
import Kraken.Promising.SLR.EnvG.LRValMpIncPublic

namespace Kraken.Promising.X64.EnvG.MpInclAbs

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Mp Kraken.Promising.X64.EnvG.MpSmoke
open Kraken.Promising.X64.EnvG.MpLink Kraken.Promising.X64.EnvG.MpRelPure Kraken.Promising.X64.EnvG.MpPublic
open Kraken.Promising.X64.EnvG.MpInc Kraken.Promising.X64.EnvG.MpIncV

/-- A `Safely` judgment in `SharedEnv.counted env` is one in `env` (a copy of
`SpinAbs.Safely.uncountV`, `EnvG/X64SpinAbsPublic.lean`). -/
theorem Safely.uncountM {e : Kraken.Executable Directive} {env : SharedEnv}
    {post : MachineState × (SharedEnv.counted env).State → Prop} {x : MachineState}
    {g : (SharedEnv.counted env).State} (h : Safely (e.instrStepEnv (SharedEnv.counted env)) post (x, g)) :
    Safely (e.instrStepEnv env) (fun y => ∃ n : Nat, post (y.1, (y.2, n))) (x, g.1) :=
  _root_.Safely.uncountEnv h

variable [layout : _root_.Layout] [Executable.ValidLayout (layout mpInclImageV)]

/-! ## The rules -/

/-- The writer's postcondition: the exit label and `W3V`. -/
abbrev postWM (P : Params) : MachineState × EStateX → Prop :=
  fun x => (x.1.2 = labM "wdone" ∧ W3V P x.2) ∨ False

omit [Executable.ValidLayout (layout mpInclImageV)] in
theorem postWM_end (P : Params) : ∀ y, postWM P y → y.1.2 = labM "wdone" :=
  fun _ h => h.elim And.left False.elim

omit [Executable.ValidLayout (layout mpInclImageV)] in
/-- **`hB` for the verbatim writer** (`MpIncV.hB_WF`'s proof). -/
theorem hB_WM (P : Params) (tid rd : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postWM P (t.st.st, σ) → t.prom = [] → EnvRel tid (mpIncPlan P) σ c t r g cl → cl → MpPostF P rd c r g := by
  rintro c t r g cl σ hpost hp hrel hcl
  obtain ⟨-, hW, hF⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inl ⟨hW.2, hF (hrel.cl hcl)⟩
  · rw [hp] at hts; cases hts

/-- **The verbatim writer's rule on `EnvGLRV`**, over its mask. -/
def mpInclRuleWM (P : Params) (hL : MpLocs P) (tid rd : Nat) :
    ThreadRuleRX (I := isa) Arch.tso (MpPostF P rd) tid :=
  ThreadRuleRX.ofSafelyEnvGLRVXM (S := mpS P) (post := postWM P) mpInclImageW_mask (mpIncPlan_valid hL)
    (mpIncPlan_whole P) (mpS_le16 P) mpInclImageW_lr (postWM_end P) (writerW_stuck _) (hB_WM P tid rd)

/-- **The verbatim writer's rule excludes faults.** -/
theorem mpInclRuleWM_noFault (P : Params) (hL : MpLocs P) (tid rd : Nat) :
    NoFaultRule (mpInclRuleWM P hL tid rd) :=
  noFaultRule_ofSafelyEnvGLRVXM _ _ _ _ _ _ _ _ mpInclImageV_noFaultCode

/-- The reader's postcondition: the exit label, `R4I`, and `ebx = 42` under
the clean flag. -/
abbrev postRM (P : Params) : MachineState × EStateX → Prop :=
  fun x => ∃ _ : Nat,
    (x.1.2 = labM "rdone" ∧ (R4I P x.2 ∧ (x.2.cl → (x.1.1.regs.get64 .rbx).setWidth 32 = 42))) ∨ False

omit [Executable.ValidLayout (layout mpInclImageV)] in
theorem postRM_end (P : Params) : ∀ y, postRM P y → y.1.2 = labM "rdone" :=
  fun _ ⟨_, h⟩ => h.elim And.left False.elim

omit [Executable.ValidLayout (layout mpInclImageV)] in
/-- **`hB` for the verbatim reader** (`MpIncV.hB_RF`'s proof). -/
theorem hB_RM (P : Params) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postRM P (t.st.st, σ) → t.prom = [] → EnvRel tid (mpPlan P) σ c t r g cl → cl → MpPostF P tid c r g := by
  rintro c t r g cl σ ⟨_, hpost⟩ hp hrel hcl
  obtain ⟨-, ⟨hw, tsF, vF, hrd, hv⟩, hx⟩ := hpost.resolve_right id
  obtain rfl : r = σ.r := by
    rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
    · rfl
    · rw [hp] at hts; cases hts
  exact .inr ⟨⟨⟨t, hrel.ht, hx (hrel.cl hcl)⟩, tsF, vF, hrel.snap.read? hrd, hv⟩, (hw.mono hrel.ghost).2⟩

/-- **The verbatim reader's rule on `EnvG`**, over its mask. -/
def mpInclRuleRM (P : Params) (hL : MpLocs P) (tid : Nat) :
    ThreadRuleRX (I := isa) Arch.tso (MpPostF P tid) tid :=
  ThreadRuleRX.ofSafelyEnvGXM (S := mpS P) (post := postRM P) mpInclImageR_mask (mpPlan_valid hL) (mpS_le16 P)
    mpInclImageR_phase1 (postRM_end P) (readerR_stuck _) (hB_RM P tid)

/-- **The verbatim reader's rule excludes faults.** -/
theorem mpInclRuleRM_noFault (P : Params) (hL : MpLocs P) (tid : Nat) : NoFaultRule (mpInclRuleRM P hL tid) :=
  noFaultRule_ofSafelyEnvGXM _ _ _ _ _ _ _ mpInclImageV_noFaultCode

/-! ## The start -/

/-- **The verbatim writer at its start**, as the runner sets it up: the
image, no declarations, pc at `writer`, end at `wdone`, the `.kl`'s
`0:rdi=f; 0:rsi=d`, and neither word in the private memory. -/
structure StartWM (s : State) : Prop where
  exe : s.exe = layout mpInclImageV
  decls : s.decls = {}
  pc : s.st.2 = labM "writer"
  endPc : s.endPc = labM "wdone"
  rdi : s.st.1.regs.get64 .rdi = symM "f"
  rsi : s.st.1.regs.get64 .rsi = symM "d"
  split : Split [(symM "f", 4), (symM "d", 4)] s.st.1.dmem

/-- **The verbatim reader at its start**: pc at `reader`, end at `rdone`,
the `.kl`'s `1:rdi=f; 1:rsi=d`. -/
structure StartRM (s : State) : Prop where
  exe : s.exe = layout mpInclImageV
  decls : s.decls = {}
  pc : s.st.2 = labM "reader"
  endPc : s.endPc = labM "rdone"
  rdi : s.st.1.regs.get64 .rdi = symM "f"
  rsi : s.st.1.regs.get64 .rsi = symM "d"
  split : Split [(symM "f", 4), (symM "d", 4)] s.st.1.dmem

section Start

variable {sW sR : isa.State} {initMem : List (Loc × Val)}

/-- **The verbatim writer's initial invariant** (thread `0`;
`MpIncV.invWIXV_init`'s precondition proof). -/
theorem invWM_init (hfd : symM "f" ≠ symM "d") (hW : StartWM sW)
    (hF0 : (Config.init [sW, sR] initMem).mem.initVal ⟨symM "f", 4⟩ = 0) :
    (mpInclRuleWM (ghostParams (symM "f") (symM "d")) (ghostParams_mpLocs hfd) 0 1).Inv True
      (Config.init [sW, sR] initMem)
      (mpRes (Config.init [sW, sR] initMem).mem (ghostParams (symM "f") (symM "d")) 0)
      (mpGhostI (ghostParams (symM "f") (symM "d"))) := by
  have hL := ghostParams_mpLocs hfd
  have hst : sW.st = (sW.st.1, labM "writer") := Prod.ext rfl hW.pc
  refine invGLRVXM_init (s := sW) rfl rfl ⟨hW.exe, hW.decls, hW.endPc, hW.split, ?_⟩
  rw [hst]
  refine writerW_envG _ hL 0 sW.st.1 _
    ⟨⟨hW.rdi, hW.rsi, split_df hW.split, split_dd hW.split⟩, ⟨⟨⟨mpGhostI_rel_Fl, fun v => ?_⟩, ?_⟩, ?_⟩⟩
  · show Pred.Pure ((mpGhostI _).rel _) v
    rw [mpGhostI_rel_ne (Ne.symm hL.fl_dt)]; exact Pred.emp_pure v
  · simp only [σInitX, Own0, mpRes, ↓reduceIte, writerRes, Res.initOf, Perm.init, writerFrac]
    exact ⟨by simp, fun p hp => by rw [hp.2], by simp, by simp <;> decide⟩
  · simp only [σInitX, FlInit, mpRes, ↓reduceIte, writerRes, Res.initOf, Perm.init, writerFrac]
    refine ⟨by simp, fun p hp => ?_⟩
    rw [hp.2]
    simp only [Prod.mk.injEq, and_true]
    exact hF0

/-- **The verbatim reader's initial invariant** (thread `1`;
`MpInc.invRIX_init`'s precondition proof). -/
theorem invRM_init (hfd : symM "f" ≠ symM "d") (hR : StartRM sR) :
    (mpInclRuleRM (ghostParams (symM "f") (symM "d")) (ghostParams_mpLocs hfd) 1).Inv True
      (Config.init [sW, sR] initMem)
      (mpRes (Config.init [sW, sR] initMem).mem (ghostParams (symM "f") (symM "d")) 1)
      (mpGhostI (ghostParams (symM "f") (symM "d"))) := by
  have hst : sR.st = (sR.st.1, labM "reader") := Prod.ext rfl hR.pc
  refine invGXM_init (s := sR) rfl rfl ⟨hR.exe, hR.decls, hR.endPc, hR.split, ?_⟩
  rw [hst]
  refine Safely.uncountM (readerR_envG _ 1 sR.st.1 (σInitX (Config.init [sW, sR] initMem)
    (mpRes (Config.init [sW, sR] initMem).mem (ghostParams (symM "f") (symM "d")) 1)
    (mpGhostI (ghostParams (symM "f") (symM "d"))), 0)
    ⟨⟨hR.rdi, hR.rsi, split_df hR.split, split_dd hR.split⟩, ⟨mpGhostI_rel_Fl, 0, Nat.zero_lt_one, rfl, ?_⟩, ?_⟩)
  · simp [σInitX, mpRes, readerRes]
  · simp [σInitX, Views.getFwd]

/-- **The `NPSafe` side** for the verbatim threads. -/
theorem mpInclV_npSafe (hfd : symM "f" ≠ symM "d") (hW : StartWM sW) (hR : StartRM sR)
    (hF0 : (Config.init [sW, sR] initMem).mem.initVal ⟨symM "f", 4⟩ = 0) :
    ∀ tid, tid < [sW, sR].length → ∀ n m,
      NPSafe (model isa) Arch.tso (MpPostF (ghostParams (symM "f") (symM "d")) 1) tid n m True
        (Config.init [sW, sR] initMem) (mpRes (Config.init [sW, sR] initMem).mem (ghostParams (symM "f") (symM "d")) tid)
        (mpGhostI (ghostParams (symM "f") (symM "d"))) := by
  intro tid htid n m
  rcases tid with _ | _ | k
  · exact NPSafe.of_ruleRX _ n m _ _ _ _ (invWM_init hfd hW hF0)
  · exact NPSafe.of_ruleRX _ n m _ _ _ _ (invRM_init hfd hR)
  · simp only [List.length_cons, List.length_nil] at htid; omega

end Start

/-! ## Purity -/

/-- The verbatim threads' all-release specifications (the image, unmasked). -/
noncomputable def mpInclNoNTSpecV : Nat → RelPureSpecQX Arch.tso fun _ _ => False
  | 0 =>
    { S := [(symM "f", 4), (symM "d", 4)]
      le16 := mpS_le16 ⟨symM "f", symM "d", ⟨0, 5⟩⟩
      e := layout mpInclImageV
      valid := inferInstance
      endPc := labM "wdone"
      post := fun x => (x.1.2 = labM "wdone" ∧ True) ∨ False
      post_end := fun _ h => h.elim And.left False.elim }
  | _ + 1 =>
    { S := [(symM "f", 4), (symM "d", 4)]
      le16 := mpS_le16 ⟨symM "f", symM "d", ⟨0, 5⟩⟩
      e := layout mpInclImageV
      valid := inferInstance
      endPc := labM "rdone"
      post := fun x => ∃ _ : Nat, (x.1.2 = labM "rdone" ∧ True) ∨ False
      post_end := fun _ h => h.elim fun _ h => h.elim And.left False.elim }

/-- **The all-release specifications hold at the start states.** -/
theorem mpInclNoNTSpecV_init {sW sR : State} (hW : StartWM sW) (hR : StartRM sR) :
    ∀ tid s, [sW, sR][tid]? = some s → (mpInclNoNTSpecV tid).Holds s
  | 0, s, hs => by
    cases hs
    refine ⟨hW.exe, hW.endPc, hW.decls, hW.split, ?_⟩
    rw [show sW.st = (sW.st.1, labM "writer") from Prod.ext rfl hW.pc]
    exact writerV_noNT _ _ sW.st.1 () ⟨hW.rdi, hW.rsi, split_df hW.split, split_dd hW.split⟩
  | 1, s, hs => by
    cases hs
    refine ⟨hR.exe, hR.endPc, hR.decls, hR.split, ?_⟩
    rw [show sR.st = (sR.st.1, labM "reader") from Prod.ext rfl hR.pc]
    exact Safely.uncountM (readerV_noNT _ _ sR.st.1 ((), 0) ⟨hR.rdi, hR.rsi, split_df hR.split, split_dd hR.split⟩)
  | _ + 2, _, hs => by cases hs

/-! ## The theorem -/

/-- **Message passing for x64 under `Arch.tso` with an unlocked `incl`
release, `mp_incl.kl`'s code verbatim, with the flag's final value**
(`MpIncV.x64_mp_incl_envGV` for the runner's threads).

For every valid layout of the image `mpInclImageV` (the `code` block, then
the runner's data trailer placing `d` and `f`): if the symbols differ,
thread `0` starts at `writer` with end `wdone` and thread `1` at `reader`
with end `rdone`, both with `%rdi = f`, `%rsi = d` and neither word in the
private memory (`StartWM`, `StartRM`), and the flag word is initially `0`,
then every final configuration reachable under `Arch.tso` has the reader's
`ebx = 42`, `[d] = 42` and `[f] = 1` (the `.kl`'s
`forall (1:ebx=42 /\ [d]=42 /\ [f]=1)`). -/
theorem x64_mp_incl_envGV_verbatim {fuel : Nat} (hfd : symM "f" ≠ symM "d")
    {sW sR : isa.State} {initMem : List (Loc × Val)} (hW : StartWM sW) (hR : StartRM sR)
    (hF0 : (Config.init [sW, sR] initMem).mem.initVal ⟨symM "f", 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [sW, sR] initMem) cfg)
    (hf : cfg.final = true) :
    (∃ t, cfg.threads[1]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 42) ∧
      cfg.mem.finalVal ⟨symM "d", 4⟩ = 42#128 ∧ cfg.mem.finalVal ⟨symM "f", 4⟩ = 1#128 :=
  final_of_relPureSafelyQX_tso fuel (B := MpPostF (ghostParams (symM "f") (symM "d")) 1)
    (Φ := fun c => (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 42) ∧
      c.mem.finalVal ⟨symM "d", 4⟩ = 42#128 ∧ c.mem.finalVal ⟨symM "f", 4⟩ = 1#128)
    (erase_mpIncInit _ _ hF0) pend_mpGhostI mpInclNoNTSpecV (mpInclNoNTSpecV_init hW hR)
    (mpInclV_npSafe hfd hW hR hF0) hc hf
    fun _ _ E' hle hsize hB =>
      have hrel : _ := by rw [hle.rel]; exact mpGhostI_rel_Fl
      have h := mp_finalI E' hf hsize hrel fun tid hd => (hB tid hd).toI
      ⟨h.1, h.2, flag_finalF E' hf hsize hrel hB⟩

end Kraken.Promising.X64.EnvG.MpInclAbs

#print axioms Kraken.Promising.X64.EnvG.MpInclAbs.x64_mp_incl_envGV_verbatim
#print axioms Kraken.Promising.X64.EnvG.MpInclAbs.mpInclRuleWM_noFault
#print axioms Kraken.Promising.X64.EnvG.MpInclAbs.mpInclRuleRM_noFault
