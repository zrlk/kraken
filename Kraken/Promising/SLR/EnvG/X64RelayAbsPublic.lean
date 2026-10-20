/-
**The x64 three-thread relay through `xchg`, `mp_relay3_xchg.kl`'s code
verbatim**: `RelayAbs.mp_relay3_xchg_envG_verbatim`,
the statement of the x64 claim-conditional RMW proof's
`RelayX.mp_relay3_xchg_envG` (`2:ebx=43 ∧ [d]=43`,
the `.kl`'s `forall`) for the threads as the `.kl` runner runs them: all
three in the image `relayImageV` (the `code` block, then the data trailer
placing `d`, `f1`, `f2`), thread `0` from `writer` to `wdone`, thread `1`
from `relay` to `rdone`, thread `2` from `reader` to `ddone`, with the
`.kl`'s registers.

- **Writer**: `ThreadRuleRX.ofSafelyEnvGXM` (`EnvG/X64MaskLinkMore.lean`) over
  the writer's mask, from `writerW_envG` (`EnvG/X64RelayAbsVCGen.lean`); into
  the take route by `NPSafe.toP`.
- **Relay**: `ThreadRuleRXGS.ofSafelyEnvGTRCXM` (`EnvG/X64MaskLinkRmw.lean`)
  over the relay's mask, from `relayY_envGTC`.
- **Reader**: `ThreadRuleRXGS.ofSafelyEnvGTXM` (`EnvG/X64MaskLinkTake.lean`)
  over the reader's mask (where the relay's `xchgl` is a data cell), from
  `readerR_envGT`.
- **Purity**: `writerV_noNT`, `relayV_noNT`, `readerV_noNT` at the unmasked
  image.
- **Final argument**: the x64 claim-conditional RMW proof's
  (`RelayX.relay_final`, `erase_relayInit`),
  unchanged.
-/
import Kraken.Promising.SLR.EnvG.X64RelayAbsVCGen
import Kraken.Promising.SLR.EnvG.X64RelayXchgPublic

namespace Kraken.Promising.X64.EnvG.RelayAbs

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Mp Kraken.Promising.X64.EnvG.MpSmoke
open Kraken.Promising.X64.EnvG.MpLink Kraken.Promising.X64.EnvG.MpRelPure Kraken.Promising.X64.EnvG.MpPublic
open Kraken.Promising.X64.EnvG.TakeMp Kraken.Promising.X64.EnvG.RelayX

-- The shape scripts are copies of the `dirs_phase1X`/`dirs_phase1RX` macros, whose simp sets
-- are generic.
set_option linter.unusedSimpArgs false

/-- A `Safely` judgment in `SharedEnv.counted env` is one in `env` (a copy of
`MpInclAbs.Safely.uncountM`). -/
theorem Safely.uncountR {e : Kraken.Executable Directive} {env : SharedEnv}
    {post : MachineState × (SharedEnv.counted env).State → Prop} {x : MachineState}
    {g : (SharedEnv.counted env).State} (h : Safely (e.instrStepEnv (SharedEnv.counted env)) post (x, g)) :
    Safely (e.instrStepEnv env) (fun y => ∃ n : Nat, post (y.1, (y.2, n))) (x, g.1) :=
  _root_.Safely.uncountEnv h

/-! ## The masks' shapes (any layout) -/

/-- The writer's cells are phase-1 (`dirs_phase1X`'s script). -/
theorem writerFragV_dirsPhase1X : ∀ d ∈ writerFragV, ∀ (e : _root_.Executable) z, DirPhase1X Arch.tso e d z := by
  intro d hd e z s pc
  simp only [writerFragV, List.mem_cons, List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals simp [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    Kraken.Promising.X64.toEv, Kraken.Promising.SLR.EnvG.Phase1Shape, Kraken.Promising.SLR.EnvG.DetAccess,
    Kraken.Promising.SLR.EnvG.SingleAccessS, Kraken.Promising.SLR.EnvG.AccessFree,
    _root_.MachineData.load, _root_.MachineData.store,
    _root_.MachineData.rmwK, _root_.RegOrMem.interp, _root_.Operand.interp, _root_.MachineData.set,
    _root_.RegOrMem.rmw, _root_.RelRegOrMem.interp, Kraken.Promising.EvTree.access_empty]
  all_goals (repeat' (first | split |
    simp [Kraken.Promising.X64.toEv, Kraken.Promising.SLR.EnvG.Phase1Shape, Kraken.Promising.SLR.EnvG.DetAccess,
      Kraken.Promising.SLR.EnvG.SingleAccessS, Kraken.Promising.SLR.EnvG.AccessFree,
      Kraken.Promising.EvTree.access_empty]))

/-- The relay's cells are phase-1 with release-kind RMWs (`dirs_phase1RX`'s
script; `je relay`'s branch as in `RelayX.relayX_phase1`). -/
theorem relayFragV_dirsPhase1RX : ∀ d ∈ relayFragV, ∀ (e : _root_.Executable) z, DirPhase1RX Arch.tso e d z := by
  intro d hd e z s pc
  simp only [relayFragV, List.mem_cons, List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals simp [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    Kraken.Promising.X64.toEv, Kraken.Promising.SLR.EnvG.Phase1ShapeR, Kraken.Promising.SLR.EnvG.DetAccess,
    Kraken.Promising.SLR.EnvG.SingleAccessS2, Kraken.Promising.SLR.EnvG.AccessFree,
    _root_.MachineData.load, _root_.MachineData.store,
    _root_.MachineData.rmwK, _root_.RegOrMem.interp, _root_.Operand.interp, _root_.MachineData.set,
    _root_.RegOrMem.rmw, _root_.RelRegOrMem.interp, Kraken.Promising.EvTree.access_empty]
  all_goals (repeat' (first | split |
    simp [Kraken.Promising.X64.toEv, Kraken.Promising.SLR.EnvG.Phase1ShapeR,
      Kraken.Promising.SLR.EnvG.DetAccess, Kraken.Promising.SLR.EnvG.SingleAccessS2,
      Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty]))
  all_goals by_cases h : s.status.zf = true <;>
    simp [h, Kraken.Promising.X64.toEv, DetAccess, SingleAccessS2]

/-- The reader's cells are phase-1 (`MpInclAbs.readerFragV_dirsPhase1X`'s
script). -/
theorem readerFragV_dirsPhase1X : ∀ d ∈ readerFragV, ∀ (e : _root_.Executable) z, DirPhase1X Arch.tso e d z := by
  intro d hd e z s pc
  simp only [readerFragV, List.mem_cons, List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  cells_phase1X

variable [layout : _root_.Layout] [Executable.ValidLayout (layout relayImageV)]

/-- **The writer's mask is phase-1.** -/
theorem relayImageW_phase1 : Phase1TreeX Arch.tso (layout relayImageW) := by
  haveI := relayImageW_valid (layout := layout)
  refine phase1TreeX_of_dirs (dirsPhase1X_layout (mem_maskKeep_range
    (Φd := fun d => ∀ (e : _root_.Executable) z, DirPhase1X Arch.tso e d z) ?_ ?_ ?_))
  · rw [writerFragV_eq]; exact writerFragV_dirsPhase1X
  · intro l e z s pc
    simp [_root_.Directive.interp, Kraken.Promising.X64.toEv, Phase1Shape, DetAccess, SingleAccessS, AccessFree]
  · intro e z s pc
    simp [_root_.Directive.interp, Kraken.Promising.X64.toEv, Phase1Shape, DetAccess, SingleAccessS, AccessFree]

/-- **The relay's mask is phase-1 with release-kind RMWs.** -/
theorem relayImageY_phase1 : Phase1TreeRX Arch.tso (layout relayImageY) := by
  haveI := relayImageY_valid (layout := layout)
  refine phase1TreeRX_of_dirs (dirsPhase1RX_layout (mem_maskKeep_range
    (Φd := fun d => ∀ (e : _root_.Executable) z, DirPhase1RX Arch.tso e d z) ?_ ?_ ?_))
  · rw [relayFragV_eq]; exact relayFragV_dirsPhase1RX
  · intro l e z s pc
    simp [_root_.Directive.interp, Kraken.Promising.X64.toEv, Phase1ShapeR, DetAccess, SingleAccessS2, AccessFree]
  · intro e z s pc
    simp [_root_.Directive.interp, Kraken.Promising.X64.toEv, Phase1ShapeR, DetAccess, SingleAccessS2, AccessFree]

/-- **The reader's mask is phase-1** (the relay's `xchgl` is masked). -/
theorem relayImageR_phase1 : Phase1TreeX Arch.tso (layout relayImageR) := by
  haveI := relayImageR_valid (layout := layout)
  refine phase1TreeX_of_dirs (dirsPhase1X_layout (mem_maskKeep_range
    (Φd := fun d => ∀ (e : _root_.Executable) z, DirPhase1X Arch.tso e d z) ?_ ?_ ?_))
  · rw [readerFragV_eq]; exact readerFragV_dirsPhase1X
  · intro l e z s pc
    simp [_root_.Directive.interp, Kraken.Promising.X64.toEv, Phase1Shape, DetAccess, SingleAccessS, AccessFree]
  · intro e z s pc
    simp [_root_.Directive.interp, Kraken.Promising.X64.toEv, Phase1Shape, DetAccess, SingleAccessS, AccessFree]

omit [Executable.ValidLayout (layout relayImageV)] in
/-- The image's non-data cells are fault-free. -/
theorem relayImageV_noFaultCode : DirsNoFaultCode (layout relayImageV) := by
  dirs_no_fault_code relayImageV relayCodeV relayDataV

/-! ## The halts -/

set_option maxRecDepth 8192 in
omit [Executable.ValidLayout (layout relayImageV)] in
/-- `wdone`'s address is the writer's mask's cell `7`. -/
theorem labY_wdone [Executable.ValidLayout (layout relayImageV)] :
    labY "wdone" = (layout relayImageW).addrOf 7 := by
  have hd : labY "wdone" = (layout relayImageV).addrOf 6 :=
    Program.label_addrOf_drop relayImageV_wf.nodup (by decide) (by decide)
  have h6 : (layout relayImageV).2[6]? = some (Directive.label "wdone", Kraken.Layout.size Directive 6) := by
    simp [Layout.apply_snd, Layout.frag, relayImageV, relayCodeV, relayDataV]
  rw [addrOf_mask relayImageW_mask, Executable.addrOf_succ _ h6,
    Executable.ValidLayout.label_size 6 "wdone" _ h6, hd]
  simp

/-- **No step of the writer's mask at `wdone`.** -/
theorem writerW_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labY "wdone" → ¬ (layout relayImageW).instrStepEnv env x R := by
  haveI := relayImageW_valid (layout := layout)
  rw [labY_wdone]
  exact not_instrStepEnv_of_byteArray (i := 7) (b := .mk #[]) env relayImageW_7

set_option maxRecDepth 8192 in
omit [Executable.ValidLayout (layout relayImageV)] in
/-- `rdone`'s address is the relay's mask's cell `17`. -/
theorem labY_rdone [Executable.ValidLayout (layout relayImageV)] :
    labY "rdone" = (layout relayImageY).addrOf 17 := by
  have hd : labY "rdone" = (layout relayImageV).addrOf 16 :=
    Program.label_addrOf_drop relayImageV_wf.nodup (by decide) (by decide)
  have h16 : (layout relayImageV).2[16]? = some (Directive.label "rdone", Kraken.Layout.size Directive 16) := by
    simp [Layout.apply_snd, Layout.frag, relayImageV, relayCodeV, relayDataV]
  rw [addrOf_mask relayImageY_mask, Executable.addrOf_succ _ h16,
    Executable.ValidLayout.label_size 16 "rdone" _ h16, hd]
  simp

/-- **No step of the relay's mask at `rdone`.** -/
theorem relayY_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labY "rdone" → ¬ (layout relayImageY).instrStepEnv env x R := by
  haveI := relayImageY_valid (layout := layout)
  rw [labY_rdone]
  exact not_instrStepEnv_of_byteArray (i := 17) (b := .mk #[]) env relayImageY_17

set_option maxRecDepth 8192 in
omit [Executable.ValidLayout (layout relayImageV)] in
/-- `ddone`'s address is the reader's mask's cell `25`. -/
theorem labY_ddone [Executable.ValidLayout (layout relayImageV)] :
    labY "ddone" = (layout relayImageR).addrOf 25 := by
  have hd : labY "ddone" = (layout relayImageV).addrOf 24 :=
    Program.label_addrOf_drop relayImageV_wf.nodup (by decide) (by decide)
  have h24 : (layout relayImageV).2[24]? = some (Directive.label "ddone", Kraken.Layout.size Directive 24) := by
    simp [Layout.apply_snd, Layout.frag, relayImageV, relayCodeV, relayDataV]
  rw [addrOf_mask relayImageR_mask, Executable.addrOf_succ _ h24,
    Executable.ValidLayout.label_size 24 "ddone" _ h24, hd]
  simp

/-- **No step of the reader's mask at `ddone`.** -/
theorem readerR_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labY "ddone" → ¬ (layout relayImageR).instrStepEnv env x R := by
  haveI := relayImageR_valid (layout := layout)
  rw [labY_ddone]
  exact not_instrStepEnv_of_byteArray (i := 25) (b := .mk #[]) env relayImageR_25

/-! ## The rules -/

/-- The writer's postcondition: the exit label and `W3`. -/
abbrev postWV (rp : RP) : MachineState × EStateX → Prop :=
  fun x => (x.1.2 = labY "wdone" ∧ W3 rp.P x.2) ∨ False

omit [Executable.ValidLayout (layout relayImageV)] in
theorem postWV_end (rp : RP) : ∀ y, postWV rp y → y.1.2 = labY "wdone" :=
  fun _ h => h.elim And.left False.elim

omit [Executable.ValidLayout (layout relayImageV)] in
/-- **`hB` for the verbatim writer** (`RelayX.hB_YW`'s proof). -/
theorem hB_WV (rp : RP) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postWV rp (t.st.st, σ) → t.prom = [] → EnvRel tid (mpPlan rp.P) σ c t r g cl → cl → YPost rp c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, hW⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inl hW.2
  · rw [hp] at hts; cases hts

/-- **The verbatim writer's rule** (`EnvGX`, over its mask). -/
def relayRuleWV (rp : RP) (hL : MpLocs rp.P) (tid : Nat) : ThreadRuleRX (I := isa) Arch.tso (YPost rp) tid :=
  ThreadRuleRX.ofSafelyEnvGXM (S := mpS rp.P) (post := postWV rp) relayImageW_mask (mpPlan_valid hL)
    (mpS_le16 rp.P) relayImageW_phase1 (postWV_end rp) (writerW_stuck _) (hB_WV rp tid)

/-- **The verbatim writer's rule excludes faults.** -/
theorem relayRuleWV_noFault (rp : RP) (hL : MpLocs rp.P) (tid : Nat) : NoFaultRule (relayRuleWV rp hL tid) :=
  noFaultRule_ofSafelyEnvGXM _ _ _ _ _ _ _ relayImageV_noFaultCode

/-- The relay's postcondition: the exit label and `RK4` (the counter
projected away). -/
abbrev postYV (rp : RP) : MachineState × EStateX → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labY "rdone" ∧ RK4 rp x.2) ∨ False

omit [Executable.ValidLayout (layout relayImageV)] in
theorem postYV_end (rp : RP) : ∀ y, postYV rp y → y.1.2 = labY "rdone" :=
  fun _ ⟨_, h⟩ => h.elim And.left False.elim

omit [Executable.ValidLayout (layout relayImageV)] in
/-- **`hB` for the verbatim relay** (`RelayX.hB_YX`'s proof). -/
theorem hB_YV (rp : RP) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postYV rp (t.st.st, σ) → t.prom = [] → EnvRel tid (mpPlan rp.Q) σ c t r g cl → cl → YPost rp c r g := by
  rintro c t r g cl σ ⟨_, hpost⟩ hp hrel -
  obtain ⟨-, hW⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inr (.inl hW)
  · rw [hp] at hts; cases hts

/-- **The verbatim relay's rule** (`EnvGTCX`, over its mask). -/
def relayRuleYV (rp : RP) (hL : MpLocs rp.Q) (tid : Nat) : ThreadRuleRXGS (I := isa) G₀ Arch.tso (YPost rp) tid :=
  ThreadRuleRXGS.ofSafelyEnvGTRCXM (S := relayS rp) (post := postYV rp) relayImageY_mask (mpPlan_valid hL)
    (relayS_le16 rp) relayImageY_phase1 (postYV_end rp) (relayY_stuck _) (hB_YV rp tid)

/-- **The verbatim relay's rule excludes faults.** -/
theorem relayRuleYV_noFault (rp : RP) (hL : MpLocs rp.Q) (tid : Nat) : NoFaultRuleSX (relayRuleYV rp hL tid) :=
  noFaultRule_ofSafelyEnvGTRCXM _ _ _ _ _ _ _ relayImageV_noFaultCode

/-- The reader's postcondition: the exit label, `Own43`, and `ebx = 43`
under the clean flag (the counter projected away). -/
abbrev postDV (rp : RP) : MachineState × EStateX → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labY "ddone" ∧
    (Own43 rp.Q x.2.r ∧ (x.2.cl → (x.1.1.regs.get64 .rbx).setWidth 32 = 43))) ∨ False

omit [Executable.ValidLayout (layout relayImageV)] in
theorem postDV_end (rp : RP) : ∀ y, postDV rp y → y.1.2 = labY "ddone" :=
  fun _ ⟨_, h⟩ => h.elim And.left False.elim

omit [Executable.ValidLayout (layout relayImageV)] in
/-- **`hB` for the verbatim reader** (thread `2`; `RelayX.hB_DX`'s proof). -/
theorem hB_DV (rp : RP) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postDV rp (t.st.st, σ) → t.prom = [] → EnvRel 2 rdPlanX σ c t r g cl → cl → YPost rp c r g := by
  rintro c t r g cl σ ⟨_, hpost⟩ hp hrel hcl
  obtain ⟨-, hown, hx⟩ := hpost.resolve_right id
  obtain rfl : r = σ.r := by
    rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
    · rfl
    · rw [hp] at hts; cases hts
  exact .inr (.inr ⟨⟨t, hrel.ht, hx (hrel.cl hcl)⟩, hown⟩)

/-- **The verbatim reader's rule** (take route, over its mask, thread `2`). -/
def relayRuleDV (rp : RP) : ThreadRuleRXGS (I := isa) G₀ Arch.tso (YPost rp) 2 :=
  ThreadRuleRXGS.ofSafelyEnvGTXM (S := mpS rp.Q) (post := postDV rp) relayImageR_mask rdPlanX_valid
    (mpS_le16 rp.Q) relayImageR_phase1 (postDV_end rp) (readerR_stuck _) (hB_DV rp)

/-- **The verbatim reader's rule excludes faults.** -/
theorem relayRuleDV_noFault (rp : RP) : NoFaultRuleSX (relayRuleDV rp) :=
  noFaultRule_ofSafelyEnvGTXM _ _ _ _ _ _ _ relayImageV_noFaultCode

/-! ## The start -/

/-- **The verbatim writer at its start**, as the runner sets it up: the
image, no declarations, pc at `writer`, end at `wdone`, the `.kl`'s
`0:rdi=f1; 0:rsi=d`, neither word in the private memory. -/
structure StartWV (s : State) : Prop where
  exe : s.exe = layout relayImageV
  decls : s.decls = {}
  pc : s.st.2 = labY "writer"
  endPc : s.endPc = labY "wdone"
  rdi : s.st.1.regs.get64 .rdi = symY "f1"
  rsi : s.st.1.regs.get64 .rsi = symY "d"
  split : Split [(symY "f1", 4), (symY "d", 4)] s.st.1.dmem

/-- **The verbatim relay at its start**: pc at `relay`, end at `rdone`, the
`.kl`'s `1:rdi=f1; 1:rsi=d; 1:rdx=f2`. -/
structure StartYV (s : State) : Prop where
  exe : s.exe = layout relayImageV
  decls : s.decls = {}
  pc : s.st.2 = labY "relay"
  endPc : s.endPc = labY "rdone"
  rdi : s.st.1.regs.get64 .rdi = symY "f1"
  rsi : s.st.1.regs.get64 .rsi = symY "d"
  rdx : s.st.1.regs.get64 .rdx = symY "f2"
  split : Split [(symY "f1", 4), (symY "d", 4), (symY "f2", 4)] s.st.1.dmem

/-- **The verbatim reader at its start**: pc at `reader`, end at `ddone`,
the `.kl`'s `2:rdi=f2; 2:rsi=d`. -/
structure StartRV (s : State) : Prop where
  exe : s.exe = layout relayImageV
  decls : s.decls = {}
  pc : s.st.2 = labY "reader"
  endPc : s.endPc = labY "ddone"
  rdi : s.st.1.regs.get64 .rdi = symY "f2"
  rsi : s.st.1.regs.get64 .rsi = symY "d"
  split : Split [(symY "f2", 4), (symY "d", 4)] s.st.1.dmem

/-- The relay's parameters at the image's symbols. -/
abbrev rpV : RP := relayParams (symY "f1") (symY "f2") (symY "d")

section Inv

variable {sW sY sR : isa.State} {initMem : List (Loc × Val)}

/-- **The verbatim writer's initial invariant** (thread `0`). -/
theorem invWV_init (hL : RelayLocs (symY "f1") (symY "f2") (symY "d")) (hW : StartWV sW) :
    (relayRuleWV rpV hL.P 0).Inv True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem rpV 0) (relayGhost rpV) := by
  have hst : sW.st = (sW.st.1, labY "writer") := Prod.ext rfl hW.pc
  refine invGXM_init (s := sW) rfl rfl ⟨hW.exe, hW.decls, hW.endPc, hW.split, ?_⟩
  rw [hst]
  refine writerW_envG _ hL.P 0 sW.st.1 _ ⟨⟨hW.rdi, hW.rsi, split_df hW.split, split_dd hW.split⟩,
    ⟨relayGhost_rel_F1 _, relayGhost_rel_Dt hL⟩, ?_⟩
  simp only [σInitX, Own0, relayRes, ↓reduceIte, writerRes, Res.initOf, Perm.init, writerFrac]
  exact ⟨by simp, fun p hp => by rw [hp.2], by simp, by simp <;> decide⟩

/-- **The verbatim relay's initial invariant** (thread `1`). -/
theorem invYV_init (hL : RelayLocs (symY "f1") (symY "f2") (symY "d")) (hY : StartYV sY) :
    (relayRuleYV rpV hL.Q 1).Inv True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem rpV 1) (relayGhost rpV) := by
  have hst : sY.st = (sY.st.1, labY "relay") := Prod.ext rfl hY.pc
  refine invGTRCXM_init (s := sY) rfl rfl ⟨hY.exe, hY.decls, hY.endPc, hY.split, ?_⟩
  rw [hst]
  refine Safely.uncountR (relayY_envGTC _ hL.Q 1 sY.st.1 (σInitX (Config.init [sW, sY, sR] initMem)
    (relayRes (Config.init [sW, sY, sR] initMem).mem rpV 1) (relayGhost rpV), 0)
    ⟨⟨hY.rdi, hY.rsi, hY.rdx, split3_f1 hY.split, split3_d hY.split, split3_f2 hY.split⟩,
      ⟨relayGhost_rel_F1 _, relayGhost_rel_Dt hL, ?_, 0, by show 0 < 2; decide, ?_, OkPred.flag⟩,
      relayGhost_rel_F2 hL.q_ne, ?_, ?_⟩)
  · simp [σInitX, Views.getFwd]
  · simp [σInitX, relayRes, relayThreadRes]
  · simp [σInitX, relayRes, relayThreadRes, Res.initOf, Perm.init, yFrac]; grind
  · simp [σInitX, relayRes, relayThreadRes, Res.initOf, Perm.init, yFrac]

/-- **The verbatim reader's initial invariant** (thread `2`). -/
theorem invDV_init (hL : RelayLocs (symY "f1") (symY "f2") (symY "d")) (hR : StartRV sR) :
    (relayRuleDV rpV).Inv True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem rpV 2) (relayGhost rpV) := by
  have hst : sR.st = (sR.st.1, labY "reader") := Prod.ext rfl hR.pc
  refine invGTXM_init (s := sR) rfl rfl ⟨hR.exe, hR.decls, hR.endPc, hR.split, ?_⟩
  rw [hst]
  refine Safely.uncountR (readerR_envGT _ 2 sR.st.1 (σInitX (Config.init [sW, sY, sR] initMem)
    (relayRes (Config.init [sW, sY, sR] initMem).mem rpV 2) (relayGhost rpV), 0)
    ⟨⟨hR.rdi, hR.rsi, split_df hR.split, split_dd hR.split⟩,
      relayGhost_rel_F2 hL.q_ne, ?_, 1, by show 1 < 2; decide, ?_, OkPred43.flag⟩)
  · simp [σInitX, Views.getFwd]
  · simp [σInitX, relayRes, readerThreadRes]

/-- **The `NPSafeP` side** for the verbatim threads. -/
theorem relayV_npSafe (hL : RelayLocs (symY "f1") (symY "f2") (symY "d")) (hW : StartWV sW) (hY : StartYV sY)
    (hR : StartRV sR) :
    ∀ tid, tid < [sW, sY, sR].length → ∀ n m, NPSafeP (model isa) Arch.tso (YPost rpV) tid G₀
      (K2Scope (model isa) AllocIds) n m True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem rpV tid) (relayGhost rpV) := by
  intro tid htid n m
  match tid, htid with
  | 0, _ =>
    exact NPSafe.toP (fun _ _ _ _ _ h => h) (fun _ _ _ h => K2₀.toScope _ h)
      (NPSafe.of_ruleRX (relayRuleWV rpV hL.P 0) n m _ _ _ _ (invWV_init hL hW))
  | 1, _ => exact NPSafeP.of_ruleRXGS (relayRuleYV rpV hL.Q 1) n m _ _ _ _ (invYV_init hL hY)
  | 2, _ => exact NPSafeP.of_ruleRXGS (relayRuleDV rpV) n m _ _ _ _ (invDV_init hL hR)
  | _ + 3, h => simp only [List.length_cons, List.length_nil] at h; omega

end Inv

/-! ## Purity -/

/-- The verbatim threads' all-release specifications (the image, unmasked). -/
noncomputable def relayNoNTSpecV : Nat → RelPureSpecQX Arch.tso fun _ _ => False
  | 0 =>
    { S := [(symY "f1", 4), (symY "d", 4)]
      le16 := mpS_le16 ⟨symY "f1", symY "d", ⟨0, 5⟩⟩
      e := layout relayImageV
      valid := inferInstance
      endPc := labY "wdone"
      post := fun x => (x.1.2 = labY "wdone" ∧ True) ∨ False
      post_end := fun _ h => h.elim And.left False.elim }
  | 1 =>
    { S := [(symY "f1", 4), (symY "d", 4), (symY "f2", 4)]
      le16 := relayS_le16 rpV
      e := layout relayImageV
      valid := inferInstance
      endPc := labY "rdone"
      post := fun x => ∃ _ : Nat, (x.1.2 = labY "rdone" ∧ True) ∨ False
      post_end := fun _ h => h.elim fun _ h => h.elim And.left False.elim }
  | _ + 2 =>
    { S := [(symY "f2", 4), (symY "d", 4)]
      le16 := mpS_le16 ⟨symY "f2", symY "d", ⟨0, 6⟩⟩
      e := layout relayImageV
      valid := inferInstance
      endPc := labY "ddone"
      post := fun x => ∃ _ : Nat, (x.1.2 = labY "ddone" ∧ True) ∨ False
      post_end := fun _ h => h.elim fun _ h => h.elim And.left False.elim }

/-- **The all-release specifications hold at the start states.** -/
theorem relayNoNTSpecV_init {sW sY sR : State} (hW : StartWV sW) (hY : StartYV sY) (hR : StartRV sR) :
    ∀ tid s, [sW, sY, sR][tid]? = some s → (relayNoNTSpecV tid).Holds s
  | 0, s, hs => by
    cases hs
    refine ⟨hW.exe, hW.endPc, hW.decls, hW.split, ?_⟩
    rw [show sW.st = (sW.st.1, labY "writer") from Prod.ext rfl hW.pc]
    exact writerV_noNT _ _ sW.st.1 () ⟨hW.rdi, hW.rsi, split_df hW.split, split_dd hW.split⟩
  | 1, s, hs => by
    cases hs
    refine ⟨hY.exe, hY.endPc, hY.decls, hY.split, ?_⟩
    rw [show sY.st = (sY.st.1, labY "relay") from Prod.ext rfl hY.pc]
    exact Safely.uncountR (relayV_noNT _ _ _ sY.st.1 ((), 0)
      ⟨hY.rdi, hY.rsi, hY.rdx, split3_f1 hY.split, split3_d hY.split, split3_f2 hY.split⟩)
  | 2, s, hs => by
    cases hs
    refine ⟨hR.exe, hR.endPc, hR.decls, hR.split, ?_⟩
    rw [show sR.st = (sR.st.1, labY "reader") from Prod.ext rfl hR.pc]
    exact Safely.uncountR (readerV_noNT _ _ sR.st.1 ((), 0) ⟨hR.rdi, hR.rsi, split_df hR.split, split_dd hR.split⟩)
  | _ + 3, _, hs => by cases hs

/-! ## The theorem -/

/-- **A three-thread ownership relay through `xchg`, for x64 under
`Arch.tso`, `mp_relay3_xchg.kl`'s code verbatim**
(`RelayX.mp_relay3_xchg_envG` for the runner's threads).

For every valid layout of the image `relayImageV` (the `code` block, then the
runner's data trailer placing `d`, `f1`, `f2`): if the three symbols differ
(`RelayLocs`), thread `0` starts at `writer` with end `wdone` (`rdi = f1`,
`rsi = d`), thread `1` at `relay` with end `rdone` (`rdi = f1`, `rsi = d`,
`rdx = f2`), thread `2` at `reader` with end `ddone` (`rdi = f2`, `rsi = d`),
none of a thread's words in its private memory (`StartWV`, `StartYV`,
`StartRV`), and both flags are initially `0`, then every final configuration
reachable under `Arch.tso` has the reader's `ebx = 43` and `[d] = 43` (the
`.kl`'s `forall (2:ebx=43 /\ [d]=43)`). -/
theorem mp_relay3_xchg_envG_verbatim {fuel : Nat} (hL : RelayLocs (symY "f1") (symY "f2") (symY "d"))
    {sW sY sR : isa.State} {initMem : List (Loc × Val)} (hW : StartWV sW) (hY : StartYV sY) (hR : StartRV sR)
    (hF1 : (Config.init [sW, sY, sR] initMem).mem.initVal ⟨symY "f1", 4⟩ = 0)
    (hF2 : (Config.init [sW, sY, sR] initMem).mem.initVal ⟨symY "f2", 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [sW, sY, sR] initMem) cfg)
    (hf : cfg.final = true) :
    (∃ t, cfg.threads[2]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 43) ∧
      cfg.mem.finalVal ⟨symY "d", 4⟩ = 43#128 :=
  final_of_relPureSafelyQX_tsoS fuel (B := YPost rpV)
    (Φ := fun c => (∃ t, c.threads[2]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 43) ∧
      c.mem.finalVal ⟨symY "d", 4⟩ = 43#128)
    (erase_relayInit hL _ hF1 hF2) initGhost_pend relayNoNTSpecV (relayNoNTSpecV_init hW hY hR)
    (relayV_npSafe hL hW hY hR) hc hf
    fun _ _ E' _ hsize hB => relay_final E' hf hsize hB

end Kraken.Promising.X64.EnvG.RelayAbs

#print axioms Kraken.Promising.X64.EnvG.RelayAbs.mp_relay3_xchg_envG_verbatim
#print axioms Kraken.Promising.X64.EnvG.RelayAbs.relayRuleWV_noFault
#print axioms Kraken.Promising.X64.EnvG.RelayAbs.relayRuleYV_noFault
#print axioms Kraken.Promising.X64.EnvG.RelayAbs.relayRuleDV_noFault
