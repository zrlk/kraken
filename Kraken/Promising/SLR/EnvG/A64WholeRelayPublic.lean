/-
**`mp_relay3.kl` whole image, part 2: the
three-thread relay with every thread running the whole `.kl` image** (under
`Arch.armv8`). Additive: `Relay.mp_relay3_envG`
(`EnvG/RelayPublic.lean`) is unchanged.

**`mp_relay3_envG_whole`**: `mp_relay3_envG`'s conclusion (at every
reachable final configuration the reader's `W4` is `43` and the data word's
final value is `43`), with the three threads' executable the whole `code`
block `relay3Img` under one layout: the writer from `writer` to `wdone`, the
relay from `relay` to `rdone`, the reader from `reader` to `ddone` (as
`Kraken.Litmus.AArch64.prepareProgram` sets them up).

- **Writer**: `ThreadRuleRX.ofSafelyEnvGM` (`EnvG/A64MaskLink.lean`) over the
  mask `relay3ImgW`, from `writerW3_envG`; into the take route by
  `NPSafe.toP`.
- **Relay**: `ThreadRuleRXGS.ofSafelyEnvGTM` over the mask `relay3ImgY`, from
  `relayY3_envGT`.
- **Reader**: `ThreadRuleRXGS.ofSafelyEnvGTM` at the trivial mask
  (`MaskOf.refl`): its exit `ddone` ends the image.
- **Ghost, resources, initial erasure and final argument**: the relay proof's
  (`relayParams`, `relayGhost`, `relayRes`, `erase_relayInit`, `YPost`,
  `relay_final`), unchanged; the start-resource computations are those of
  `invYW_init`, `invY_init` and `invD_init`.
- **Purity**: `writer3_relPure`, `relay3_relPure`, `reader3_relPure` at the
  unmasked image.
-/
import Kraken.Promising.SLR.EnvG.A64WholeRelayVCGen
import Kraken.Promising.SLR.EnvG.RelayPublic
import Kraken.Promising.SLR.EnvG.A64MaskHelpers

namespace Kraken.Promising.SLR.EnvG.Relay

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Mp Kraken.Promising.SLR.MpTrees
open Kraken.Promising.SLR.EnvG.MpSmoke Kraken.Promising.SLR.EnvG.MpLink Kraken.Promising.SLR.MpPublic
open Kraken.Promising.SLR.EnvG.MpRelPure Kraken.Promising.SLR.EnvG.TakeSmoke Kraken.Promising.SLR.EnvG.TakeMp

set_option linter.unusedSimpArgs false

/-! ## The image's static facts -/

/-- Every cell of the image is phase-1 (`dirs_phase1`'s script, for every
ambient executable). -/
theorem relay3Img_dirsPhase1 : ∀ d ∈ relay3Img, ∀ (e : _root_.Executable) z, DirPhase1 Arch.armv8 e d z := by
  dirs_phase1_any relay3Img

/-- A label cell is phase-1 (`label_dirPhase1_any`). -/
theorem label_dirPhase1Y (l : Label) (e : _root_.Executable) (z : Nat) : DirPhase1 Arch.armv8 e (.label l) z :=
  label_dirPhase1_any Arch.armv8 l e z

/-- A data cell is phase-1 (`byteArray_dirPhase1_any`). -/
theorem byteArray_dirPhase1Y (b : ByteArray) (e : _root_.Executable) (z : Nat) :
    DirPhase1 Arch.armv8 e (.byteArray b) z :=
  byteArray_dirPhase1_any Arch.armv8 b e z

section Static

variable [layout : _root_.Layout] [Executable.ValidLayout (layout relay3Img)]

omit [Executable.ValidLayout (layout relay3Img)] in
theorem relay3Img_rmwLive : (layout relay3Img).rmwLive = true := by rw [Layout.apply_rmwLive]; decide

/-- The image is phase-1 (the reader's obligation). -/
theorem relay3Img_phase1 : Phase1Tree Arch.armv8 (layout relay3Img) :=
  phase1Tree_of_dirs (dirsPhase1_layout relay3Img_dirsPhase1)

/-- The writer's mask is phase-1. -/
theorem relay3ImgW_phase1 : Phase1Tree Arch.armv8 (layout relay3ImgW) :=
  haveI := relay3ImgW_valid (layout := layout)
  phase1Tree_of_dirs (dirsPhase1_layout (mem_maskKeep_range (Φd := fun d => ∀ e z, DirPhase1 Arch.armv8 e d z)
    (fun d hd => relay3Img_dirsPhase1 d (List.mem_of_mem_drop (List.mem_of_mem_take hd)))
    (fun l => label_dirPhase1Y l) (byteArray_dirPhase1Y _)))

/-- The relay's mask is phase-1. -/
theorem relay3ImgY_phase1 : Phase1Tree Arch.armv8 (layout relay3ImgY) :=
  haveI := relay3ImgY_valid (layout := layout)
  phase1Tree_of_dirs (dirsPhase1_layout (mem_maskKeep_range (Φd := fun d => ∀ e z, DirPhase1 Arch.armv8 e d z)
    (fun d hd => relay3Img_dirsPhase1 d (List.mem_of_mem_drop (List.mem_of_mem_take hd)))
    (fun l => label_dirPhase1Y l) (byteArray_dirPhase1Y _)))

omit [Executable.ValidLayout (layout relay3Img)] in
theorem relay3Img_noFault : DirsNoFault (layout relay3Img) := by dirs_no_fault' relay3Img

/-! ## The halts -/

set_option maxRecDepth 8192 in
/-- `wdone`'s address is the writer's mask's cell `7` (the masked `NOP`). -/
theorem labY3_wdone : labY3 "wdone" = (layout relay3ImgW).addrOf 7 := by
  have hd : labY3 "wdone" = (layout relay3Img).addrOf 6 :=
    Program.label_addrOf_drop relay3Img_wf.nodup (by decide) (by decide)
  have h6 : (layout relay3Img).2[6]? = some (Directive.label "wdone", Kraken.Layout.size Directive 6) := by
    simp [Layout.apply_snd, Layout.frag, relay3Img]
  rw [addrOf_mask relay3ImgW_mask, Executable.addrOf_succ _ h6,
    Executable.ValidLayout.label_size 6 "wdone" _ h6, hd]
  simp

/-- **No step of the writer's mask at its exit label `wdone`.** -/
theorem writerW3_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labY3 "wdone" → ¬ (layout relay3ImgW).instrStepEnv env x R := by
  haveI := relay3ImgW_valid (layout := layout)
  rw [labY3_wdone]
  exact not_instrStepEnv_of_byteArray (i := 7) (b := .mk #[]) env relay3ImgW_7

set_option maxRecDepth 8192 in
/-- `rdone`'s address is the relay's mask's cell `17` (the masked `NOP`). -/
theorem labY3_rdone : labY3 "rdone" = (layout relay3ImgY).addrOf 17 := by
  have hd : labY3 "rdone" = (layout relay3Img).addrOf 16 :=
    Program.label_addrOf_drop relay3Img_wf.nodup (by decide) (by decide)
  have h16 : (layout relay3Img).2[16]? = some (Directive.label "rdone", Kraken.Layout.size Directive 16) := by
    simp [Layout.apply_snd, Layout.frag, relay3Img]
  rw [addrOf_mask relay3ImgY_mask, Executable.addrOf_succ _ h16,
    Executable.ValidLayout.label_size 16 "rdone" _ h16, hd]
  simp

/-- **No step of the relay's mask at its exit label `rdone`.** -/
theorem relayY3_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labY3 "rdone" → ¬ (layout relay3ImgY).instrStepEnv env x R := by
  haveI := relay3ImgY_valid (layout := layout)
  rw [labY3_rdone]
  exact not_instrStepEnv_of_byteArray (i := 17) (b := .mk #[]) env relay3ImgY_17

set_option maxRecDepth 8192 in
/-- `ddone`'s address is the end of the image. -/
theorem labY3_ddone : labY3 "ddone" = (layout relay3Img).addrOf relay3Img.length := by
  have hd : labY3 "ddone" = (layout relay3Img).addrOf 23 :=
    Program.label_addrOf_drop relay3Img_wf.nodup (by decide) (by decide)
  have h23 : (layout relay3Img).2[23]? = some (Directive.label "ddone", Kraken.Layout.size Directive 23) := by
    simp [Layout.apply_snd, Layout.frag, relay3Img]
  rw [show relay3Img.length = 23 + 1 from rfl, Executable.addrOf_succ _ h23,
    Executable.ValidLayout.label_size 23 "ddone" _ h23, hd]
  simp

/-- **No step of the image at the reader's exit label `ddone`.** -/
theorem readerD3_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labY3 "ddone" → ¬ (layout relay3Img).instrStepEnv env x R := by
  rw [labY3_ddone]
  exact not_instrStepEnv_of_end_labels env 1

end Static

/-! ## The rules -/

section Rules

variable [layout : _root_.Layout] [Executable.ValidLayout (layout relay3Img)]

/-- The whole-image writer's postcondition: its exit label and `W3`. -/
abbrev postW3 (rp : RP) : MachineState × EStateA → Prop :=
  fun x => (x.1.2 = labY3 "wdone" ∧ W3 rp.P x.2) ∨ False

omit [Executable.ValidLayout (layout relay3Img)] in
theorem postW3_end (rp : RP) : ∀ y, postW3 rp y → y.1.2 = labY3 "wdone" :=
  fun _ h => h.elim And.left False.elim

omit [Executable.ValidLayout (layout relay3Img)] in
/-- **`hB` for the whole-image writer** (`hB_YW`'s proof): it keeps the token
`W`. -/
theorem hB_W3 (rp : RP) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postW3 rp (t.st.st, σ) → t.prom = [] → EnvRel tid (mpPlan rp.P) σ c t r g cl → cl → YPost rp c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, hW⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inl hW.2
  · rw [hp] at hts; cases hts

/-- **The whole-image writer's rule** (`EnvG`, over its mask). -/
def relayRuleW3 (rp : RP) (hL : MpLocs rp.P) (tid : Nat) : ThreadRuleRX (I := isa) Arch.armv8 (YPost rp) tid :=
  ThreadRuleRX.ofSafelyEnvGM (post := postW3 rp) relay3ImgW_mask (mpPlan_valid hL) relay3Img_rmwLive
    relay3ImgW_phase1 (postW3_end rp) (writerW3_stuck _) (hB_W3 rp tid)

/-- **The whole-image writer's rule excludes faults.** -/
theorem relayRuleW3_noFault (rp : RP) (hL : MpLocs rp.P) (tid : Nat) : NoFaultRule (relayRuleW3 rp hL tid) :=
  noFaultRule_ofSafelyEnvGM _ _ _ _ _ _ _ relay3Img_noFault

/-- The whole-image relay's postcondition: its exit label and `RK4` (the
counter projected away). -/
abbrev postY3 (rp : RP) : MachineState × EStateA → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labY3 "rdone" ∧ RK4 rp x.2) ∨ False

omit [Executable.ValidLayout (layout relay3Img)] in
theorem postY3_end (rp : RP) : ∀ y, postY3 rp y → y.1.2 = labY3 "rdone" :=
  fun _ ⟨_, h⟩ => h.elim And.left False.elim

omit [Executable.ValidLayout (layout relay3Img)] in
/-- **`hB` for the whole-image relay** (`hB_Y`'s proof): it keeps the token
`W2`. -/
theorem hB_Y3 (rp : RP) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postY3 rp (t.st.st, σ) → t.prom = [] → EnvRel tid (mpPlan rp.Q) σ c t r g cl → cl → YPost rp c r g := by
  rintro c t r g cl σ ⟨_, hpost⟩ hp hrel -
  obtain ⟨-, hW⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inr (.inl hW)
  · rw [hp] at hts; cases hts

/-- **The whole-image relay's rule** (`EnvGT`, over its mask). -/
def relayRuleY3 (rp : RP) (hL : MpLocs rp.Q) (tid : Nat) : ThreadRuleRXGS (I := isa) G₀ Arch.armv8 (YPost rp) tid :=
  ThreadRuleRXGS.ofSafelyEnvGTM (post := postY3 rp) relay3ImgY_mask (mpPlan_valid hL) relay3Img_rmwLive
    relay3ImgY_phase1 (postY3_end rp) (relayY3_stuck _) (hB_Y3 rp tid)

/-- **The whole-image relay's rule excludes faults.** -/
theorem relayRuleY3_noFault (rp : RP) (hL : MpLocs rp.Q) (tid : Nat) : NoFaultRuleS (relayRuleY3 rp hL tid) :=
  noFaultRule_ofSafelyEnvGTM _ _ _ _ _ _ _ relay3Img_noFault

/-- The whole-image reader's postcondition: its exit label, `Own43`, and
`W4 = 43` under the clean flag (the counter projected away). -/
abbrev postD3 (rp : RP) : MachineState × EStateA → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labY3 "ddone" ∧
    (Own43 rp.Q x.2.r ∧ (x.2.cl → x.1.1.regs.X4.toBitVec.setWidth 32 = 43))) ∨ False

omit [Executable.ValidLayout (layout relay3Img)] in
theorem postD3_end (rp : RP) : ∀ y, postD3 rp y → y.1.2 = labY3 "ddone" :=
  fun _ ⟨_, h⟩ => h.elim And.left False.elim

omit [Executable.ValidLayout (layout relay3Img)] in
/-- **`hB` for the whole-image reader** (thread `2`; `hB_D`'s proof). -/
theorem hB_D3 (rp : RP) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postD3 rp (t.st.st, σ) → t.prom = [] → EnvRel 2 rdPlan σ c t r g cl → cl → YPost rp c r g := by
  rintro c t r g cl σ ⟨_, hpost⟩ hp hrel hcl
  obtain ⟨-, hown, hx4⟩ := hpost.resolve_right id
  obtain rfl : r = σ.r := by
    rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
    · rfl
    · rw [hp] at hts; cases hts
  exact .inr (.inr ⟨⟨t, hrel.ht, hx4 (hrel.cl hcl)⟩, hown⟩)

/-- **The whole-image reader's rule** (`EnvGT`, thread `2`, the image itself
as its mask). -/
def relayRuleD3 (rp : RP) : ThreadRuleRXGS (I := isa) G₀ Arch.armv8 (YPost rp) 2 :=
  ThreadRuleRXGS.ofSafelyEnvGTM (post := postD3 rp) (MaskOf.refl _) rdPlan_valid relay3Img_rmwLive
    relay3Img_phase1 (postD3_end rp) (readerD3_stuck _) (hB_D3 rp)

/-- **The whole-image reader's rule excludes faults.** -/
theorem relayRuleD3_noFault (rp : RP) : NoFaultRuleS (relayRuleD3 rp) :=
  noFaultRule_ofSafelyEnvGTM _ _ _ _ _ _ _ relay3Img_noFault

end Rules

/-! ## The start -/

/-- **The writer at its start in the whole image**, as the runner sets it up
(`0:X0=f1; 0:X1=d`): the image, no declarations, pc at `writer`, end at
`wdone`, neither word in `dmem`. -/
structure StartW3 [layout : _root_.Layout] (f1 d : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout relay3Img
  decls : s.decls = {}
  pc : s.st.2 = labY3 "writer"
  endPc : s.endPc = labY3 "wdone"
  x0 : s.st.1.regs.X0.toBitVec = f1
  x1 : s.st.1.regs.X1.toBitVec = d
  df : Mem.loadInt s.st.1.dmem f1 4 = none
  dd : Mem.loadInt s.st.1.dmem d 4 = none

/-- **The relay at its start in the whole image** (`1:X0=f1; 1:X1=d;
1:X2=f2`): pc at `relay`, end at `rdone`, none of the three words in
`dmem`. -/
structure StartY3 [layout : _root_.Layout] (f1 f2 d : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout relay3Img
  decls : s.decls = {}
  pc : s.st.2 = labY3 "relay"
  endPc : s.endPc = labY3 "rdone"
  x0 : s.st.1.regs.X0.toBitVec = f1
  x1 : s.st.1.regs.X1.toBitVec = d
  x2 : s.st.1.regs.X2.toBitVec = f2
  df1 : Mem.loadInt s.st.1.dmem f1 4 = none
  dd : Mem.loadInt s.st.1.dmem d 4 = none
  df2 : Mem.loadInt s.st.1.dmem f2 4 = none

/-- **The reader at its start in the whole image** (`2:X0=f2; 2:X1=d`): pc
at `reader`, end at `ddone`, neither word in `dmem`. -/
structure StartD3 [layout : _root_.Layout] (f2 d : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout relay3Img
  decls : s.decls = {}
  pc : s.st.2 = labY3 "reader"
  endPc : s.endPc = labY3 "ddone"
  x0 : s.st.1.regs.X0.toBitVec = f2
  x1 : s.st.1.regs.X1.toBitVec = d
  df : Mem.loadInt s.st.1.dmem f2 4 = none
  dd : Mem.loadInt s.st.1.dmem d 4 = none

section Inv

variable [layout : _root_.Layout] [Executable.ValidLayout (layout relay3Img)] {f1 f2 d : BitVec 64}
  {sW sY sR : isa.State} {initMem : List (Loc × Val)}

/-- **The whole-image writer's initial invariant** (thread `0`;
`invYW_init`'s resource computation). -/
theorem invW3_init (hL : RelayLocs f1 f2 d) (hW : StartW3 f1 d sW) :
    (relayRuleW3 (relayParams f1 f2 d) hL.P 0).Inv True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) 0) (relayGhost (relayParams f1 f2 d)) := by
  refine invGM_init (s := sW) rfl rfl ⟨hW.exe, hW.decls, hW.endPc, ?_⟩
  rw [show sW.st = (sW.st.1, labY3 "writer") from Prod.ext rfl hW.pc]
  refine writerW3_envG _ hL.P 0 _ _ ⟨⟨hW.x0, hW.x1, hW.df, hW.dd⟩,
    .inl ⟨rfl, ⟨relayGhost_rel_F1 _, relayGhost_rel_Dt hL⟩, ?_⟩⟩
  simp only [σInit, Own0, relayRes, ↓reduceIte, writerRes, Res.initOf, Perm.init, writerFrac]
  exact ⟨by simp, fun p hp => by rw [hp.2], by simp, by simp <;> decide⟩

/-- **The whole-image relay's initial invariant** (thread `1`; `invY_init`'s
resource computation). -/
theorem invY3_init (hL : RelayLocs f1 f2 d) (hY : StartY3 f1 f2 d sY) :
    (relayRuleY3 (relayParams f1 f2 d) hL.Q 1).Inv True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) 1) (relayGhost (relayParams f1 f2 d)) := by
  refine invGTM_init (s := sY) rfl rfl ⟨hY.exe, hY.decls, hY.endPc, ?_⟩
  rw [show sY.st = (sY.st.1, labY3 "relay") from Prod.ext rfl hY.pc]
  refine Safely.uncountA (relayY3_envGT _ hL.Q 1 _ (_, 0) ⟨⟨hY.x0, hY.x1, hY.x2, hY.df1, hY.dd, hY.df2⟩,
    .inl ⟨rfl, ⟨relayGhost_rel_F1 _, relayGhost_rel_Dt hL, ?_, 0, by show 0 < 2; decide, ?_, OkPred.flag⟩,
      relayGhost_rel_F2 hL.q_ne, ?_, ?_⟩⟩)
  · simp [σInit, Views.getFwd]
  · simp [σInit, relayRes, relayThreadRes]
  · simp [σInit, relayRes, relayThreadRes, Res.initOf, Perm.init, yFrac]; grind
  · simp [σInit, relayRes, relayThreadRes, Res.initOf, Perm.init, yFrac]

/-- **The whole-image reader's initial invariant** (thread `2`;
`invD_init`'s resource computation). -/
theorem invD3_init (hL : RelayLocs f1 f2 d) (hR : StartD3 f2 d sR) :
    (relayRuleD3 (relayParams f1 f2 d)).Inv True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) 2) (relayGhost (relayParams f1 f2 d)) := by
  refine invGTM_init (s := sR) rfl rfl ⟨hR.exe, hR.decls, hR.endPc, ?_⟩
  rw [show sR.st = (sR.st.1, labY3 "reader") from Prod.ext rfl hR.pc]
  refine Safely.uncountA (readerD3_envGT (relayParams f1 f2 d).Q 2 _ (σInit (Config.init [sW, sY, sR] initMem)
    (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) 2) (relayGhost (relayParams f1 f2 d)), 0)
    ⟨hR.x0, hR.x1, hR.df, hR.dd,
    .inl ⟨rfl, relayGhost_rel_F2 hL.q_ne, ?_, 1, by show 1 < 2; decide, ?_, OkPred43.flag⟩⟩)
  · simp [σInit, Views.getFwd]
  · simp [σInit, relayRes, readerThreadRes]

end Inv

/-! ## `NPSafeP`, purity and the theorem -/

/-- **The `NPSafeP` side, whole image**: the writer through its
`ThreadRuleRX` (`NPSafe.toP`), the relay and the reader through the take
route. -/
theorem relay3_whole_npSafe (l : _root_.Layout) [Executable.ValidLayout (l relay3Img)] {f1 f2 d : BitVec 64}
    (hL : RelayLocs f1 f2 d) {sW sY sR : isa.State} {initMem : List (Loc × Val)}
    (hW : StartW3 (layout := l) f1 d sW) (hY : StartY3 (layout := l) f1 f2 d sY)
    (hR : StartD3 (layout := l) f2 d sR) :
    ∀ tid, tid < [sW, sY, sR].length → ∀ n m, NPSafeP (model isa) Arch.armv8 (YPost (relayParams f1 f2 d)) tid G₀
      (K2Scope (model isa) AllocIds) n m True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) tid)
      (relayGhost (relayParams f1 f2 d)) := by
  intro tid htid n m
  match tid, htid with
  | 0, _ =>
    exact NPSafe.toP (fun _ _ _ _ _ h => h) (fun _ _ _ h => K2₀.toScope _ h)
      (NPSafe.of_ruleRX (relayRuleW3 (layout := l) _ hL.P 0) n m _ _ _ _ (invW3_init (layout := l) hL hW))
  | 1, _ => exact NPSafeP.of_ruleRXGS (relayRuleY3 (layout := l) _ hL.Q 1) n m _ _ _ _ (invY3_init (layout := l) hL hY)
  | 2, _ => exact NPSafeP.of_ruleRXGS (relayRuleD3 (layout := l) _) n m _ _ _ _ (invD3_init (layout := l) hL hR)
  | _ + 3, h => simp only [List.length_cons, List.length_nil] at h; omega

/-- The threads' purity specifications in the whole image: the writer's run
to `wdone` at thread `0`, the relay's to `rdone` at thread `1`, the reader's
to `ddone` elsewhere. -/
def relay3PureSpecW (l : _root_.Layout) [hv : Executable.ValidLayout (l relay3Img)] (rel : Loc → Pred) :
    Nat → RelPureSpec Arch.armv8 rel
  | 0 => { e := l relay3Img, valid := hv, endPc := labY3 (layout := l) "wdone",
           post := fun x => (x.1.2 = labY3 (layout := l) "wdone" ∧ True) ∨ False,
           post_end := fun _ h => h.elim And.left False.elim }
  | 1 => { e := l relay3Img, valid := hv, endPc := labY3 (layout := l) "rdone",
           post := fun x => ∃ _ : Nat, (x.1.2 = labY3 (layout := l) "rdone" ∧ True) ∨ False,
           post_end := fun _ ⟨_, h⟩ => h.elim And.left False.elim }
  | _ + 2 => { e := l relay3Img, valid := hv, endPc := labY3 (layout := l) "ddone",
               post := fun x => ∃ _ : Nat, (x.1.2 = labY3 (layout := l) "ddone" ∧ True) ∨ False,
               post_end := fun _ ⟨_, h⟩ => h.elim And.left False.elim }

/-- **The purity specifications hold at the start states.** -/
theorem relay3PureSpecW_init (l : _root_.Layout) [Executable.ValidLayout (l relay3Img)] {f1 f2 d : BitVec 64}
    (hL : RelayLocs f1 f2 d) {sW sY sR : isa.State} (hW : StartW3 (layout := l) f1 d sW)
    (hY : StartY3 (layout := l) f1 f2 d sY) (hR : StartD3 (layout := l) f2 d sR) :
    ∀ tid s, [sW, sY, sR][tid]? = some s →
      (relay3PureSpecW l (relayGhost (relayParams f1 f2 d)).rel tid).Holds s
  | 0, s, hs => by
    cases hs
    refine ⟨hW.exe, hW.endPc, hW.decls, ?_⟩
    rw [show sW.st = (sW.st.1, labY3 (layout := l) "writer") from Prod.ext rfl hW.pc]
    exact writer3_relPure (layout := l) _ f1 d (relayGhost_rel_Dt hL) _ () fun _ => ⟨hW.x0, hW.x1, hW.df, hW.dd⟩
  | 1, s, hs => by
    cases hs
    refine ⟨hY.exe, hY.endPc, hY.decls, ?_⟩
    rw [show sY.st = (sY.st.1, labY3 (layout := l) "relay") from Prod.ext rfl hY.pc]
    exact Safely.uncountA (relay3_relPure (layout := l) _ f1 d f2 (relayGhost_rel_Dt hL) _ ((), 0)
      fun _ => ⟨hY.x0, hY.x1, hY.x2, hY.df1, hY.dd, hY.df2⟩)
  | 2, s, hs => by
    cases hs
    refine ⟨hR.exe, hR.endPc, hR.decls, ?_⟩
    rw [show sR.st = (sR.st.1, labY3 (layout := l) "reader") from Prod.ext rfl hR.pc]
    exact Safely.uncountA (reader3_relPure (layout := l) _ f2 _ ((), 0) fun _ => ⟨hR.x0, hR.df⟩)
  | _ + 3, _, hs => by cases hs

/-- **A three-thread ownership relay `mp_relay3.kl` for AArch64 under
`Arch.armv8`, every thread running the whole `.kl` image**
(`forall (2:X4=43 /\ [d]=43)`).

For a valid layout `l` of the `.kl`'s `code` block `relay3Img` and distinct
addresses `f1`, `f2`, `d` (`RelayLocs`): if thread `0` runs the image from
`writer` to `wdone` with `x0 = f1`, `x1 = d`, thread `1` from `relay` to
`rdone` with `x0 = f1`, `x1 = d`, `x2 = f2`, thread `2` from `reader` to
`ddone` with `x0 = f2`, `x1 = d`, each with no declarations and none of its
words in its private memory (`StartW3`, `StartY3`, `StartD3`), and both flags
are initially `0`, then every final configuration reachable under
`Arch.armv8` has the reader's `W4 = 43` and `[d] = 43`.

This is `mp_relay3_envG` with the runner's executable: the dead `NOP`s
behind `wdone:` and `rdone:` (which would break the writer's and the relay's
halts) are handled by the writer's and the relay's masks
(`EnvG/A64MaskLink.lean`). As there, only final configurations are
constrained, faults are covered by `relayRuleW3_noFault`,
`relayRuleY3_noFault` and `relayRuleD3_noFault`, and the threads have no
declarations (the runner sets `decls` from the init block). -/
theorem mp_relay3_envG_whole {fuel : Nat} (l : _root_.Layout) [Executable.ValidLayout (l relay3Img)]
    (f1 f2 d : BitVec 64) (hL : RelayLocs f1 f2 d) {sW sY sR : isa.State} {initMem : List (Loc × Val)}
    (hW : StartW3 (layout := l) f1 d sW) (hY : StartY3 (layout := l) f1 f2 d sY)
    (hR : StartD3 (layout := l) f2 d sR)
    (hF1 : (Config.init [sW, sY, sR] initMem).mem.initVal ⟨f1, 4⟩ = 0)
    (hF2 : (Config.init [sW, sY, sR] initMem).mem.initVal ⟨f2, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [sW, sY, sR] initMem) cfg)
    (hf : cfg.final = true) :
    (∃ t, cfg.threads[2]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 43) ∧
      cfg.mem.finalVal ⟨d, 4⟩ = 43#128 :=
  final_of_relPureSafelyS Arch.armv8 fuel (B := YPost (relayParams f1 f2 d))
    (Φ := fun c => (∃ t, c.threads[2]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 43) ∧
      c.mem.finalVal ⟨d, 4⟩ = 43#128)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_relayInit hL _ hF1 hF2) initGhost_pend
    (relay3PureSpecW l _) (relay3PureSpecW_init l hL hW hY hR) (relay3_whole_npSafe l hL hW hY hR) hc hf
    fun _ _ E' _ hsize hB => relay_final E' hf hsize hB

end Kraken.Promising.SLR.EnvG.Relay

#print axioms Kraken.Promising.SLR.EnvG.Relay.mp_relay3_envG_whole
#print axioms Kraken.Promising.SLR.EnvG.Relay.relayRuleW3_noFault
#print axioms Kraken.Promising.SLR.EnvG.Relay.relayRuleY3_noFault
#print axioms Kraken.Promising.SLR.EnvG.Relay.relayRuleD3_noFault
