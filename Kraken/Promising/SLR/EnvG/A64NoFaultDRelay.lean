/-
**No fault at the runner's declarations for the AArch64 ownership relay**
`mp_relay3.kl`, `mp_relay3_swpl.kl`.

Per role: the role text's **address run** in `SharedEnv.invTop S` over the
role's executable (the writer's and the relay's masks, the reader's image),
by `cfgEnv_partial_at` with a register-only table at the role's entry label
(`X0`/`X1`/`X2` hold the role's shared words, the private memory maps none),
giving `AddrSafeA` at the role's start; the role's rule with the address run
(`…MAD`, `EnvG/A64NoFaultD.lean`; same `B` as the existing `…_decls` rule); its
initial invariant at the runner's start (`inv…3_init_declsA`); and the rule's
no-fault at `decls = ds` for declarations agreeing on `f1`, `d`, `f2`
(`…_runner_noFault`), with concrete instances at the runner's declarations.
-/
import Kraken.Promising.SLR.EnvG.A64NoFaultD
import Kraken.Promising.SLR.EnvG.A64WholeRelayRunner
import Kraken.Promising.SLR.EnvG.A64WholeRelaySwplRunner

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP

namespace Kraken.Promising.SLR.EnvG.Relay

open Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Mp Kraken.Promising.SLR.MpTrees
open Kraken.Promising.SLR.EnvG.MpSmoke Kraken.Promising.SLR.EnvG.MpLink Kraken.Promising.SLR.MpPublic
open Kraken.Promising.SLR.EnvG.MpRelPure Kraken.Promising.SLR.EnvG.TakeSmoke Kraken.Promising.SLR.EnvG.TakeMp
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- The relay's layout: the flags `f1`, `f2` and the data `d`, 4-byte words. -/
abbrev relayS (f1 f2 d : BitVec 64) : SharedEnv.Layout := [(f1, 4), (d, 4), (f2, 4)]

/-! ## The role texts' address runs -/

section RunsAt

variable [CodeEnv]

/-- The writer's address table: at `writer`, `X0 = f1`, `X1 = d`, unmapped. -/
abbrev writerAddrTable3 (f1 f2 d : BitVec 64) :
    Label → MachineData → (SharedEnv.invTop (relayS f1 f2 d)).State → Prop :=
  fun lb s _ => lb = "writer" → s.regs.X0.toBitVec = f1 ∧ s.regs.X1.toBitVec = d ∧
    Mem.loadInt s.dmem f1 4 = none ∧ Mem.loadInt s.dmem d 4 = none

/-- **The writer's address run in any ambient code** in which `writerT3` is
`PlacedIn`. -/
theorem writerT3_addr_at (f1 f2 d : BitVec 64) (hpl : Program.PlacedIn writerT3) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt writerT3 l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, writerAddrTable3 f1 f2 d "writer" s g →
      Safely (cenv.instrStepEnv (SharedEnv.invTop (relayS f1 f2 d)))
        (fun x => (x.1.2 = endA ∧ True) ∨ False) ((s, (_root_.Executable.labels cenv).label "writer"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.invTop (relayS f1 f2 d)) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (writerAddrTable3 f1 f2 d) ?_ writerT3_eq writerT3_wf hpl hlast s g hsg
  cfg_cases_env [writerT3]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨hT, rfl, rfl⟩ := ‹(_ → _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [forall_const] at hT
  case vc6 => exact Table.ofLabelsEnv_at ⟨by decide, fun h => absurd h (by decide), .inl (by decide)⟩
  all_goals simp_all [SharedEnv.inv, Reg64s.setXReg]

/-- The relay's address table: at `relay`, `X0 = f1`, `X1 = d`, `X2 = f2`,
unmapped. -/
abbrev relayAddrTable3 (f1 f2 d : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (SharedEnv.invTop (relayS f1 f2 d))).State → Prop :=
  fun lb s _ => lb = "relay" → s.regs.X0.toBitVec = f1 ∧ s.regs.X1.toBitVec = d ∧ s.regs.X2.toBitVec = f2 ∧
    Mem.loadInt s.dmem f1 4 = none ∧ Mem.loadInt s.dmem d 4 = none ∧ Mem.loadInt s.dmem f2 4 = none

/-- **The relay's address run in any ambient code** in which `relayT3` is
`PlacedIn` (counted: the spin's back edge). -/
theorem relayT3_addr_at (f1 f2 d : BitVec 64) (hpl : Program.PlacedIn relayT3) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt relayT3 l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, relayAddrTable3 f1 f2 d "relay" s g →
      Safely (cenv.instrStepEnv (SharedEnv.counted (SharedEnv.invTop (relayS f1 f2 d))))
        (fun x => (x.1.2 = endA ∧ True) ∨ False) ((s, (_root_.Executable.labels cenv).label "relay"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (SharedEnv.invTop (relayS f1 f2 d)))
    (Q := fun _ _ => True) (E := fun _ _ _ => False) (relayAddrTable3 f1 f2 d) ?_ relayT3_eq relayT3_wf hpl hlast
    s g hsg
  cfg_cases_env [relayT3]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨hT, rfl, rfl⟩ := ‹(_ → _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [forall_const] at hT
  all_goals simp only [SharedEnv.counted_ok] at *
  case vc4 =>
    -- the back edge (`cbz` taken): the counter moved
    have hn := (‹(SharedEnv.counted _).step _ _ _ _›).2
    refine Table.ofLabelsEnv_at ⟨by decide, fun _ => ?_, .inr fun ⟨_, hg⟩ => ?_⟩
    · simp_all
    · subst hg; simp at hn
  case vc10 => exact Table.ofLabelsEnv_at ⟨by decide, fun h => absurd h (by decide), .inl (by decide)⟩
  all_goals simp_all [SharedEnv.inv, Reg64s.setXReg]

/-- The reader's address table: at `reader`, `X0 = f2`, `X1 = d`, unmapped. -/
abbrev readerAddrTable3 (f1 f2 d : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (SharedEnv.invTop (relayS f1 f2 d))).State → Prop :=
  fun lb s _ => lb = "reader" → s.regs.X0.toBitVec = f2 ∧ s.regs.X1.toBitVec = d ∧
    Mem.loadInt s.dmem f2 4 = none ∧ Mem.loadInt s.dmem d 4 = none

/-- **The reader's address run in any ambient code** in which `readerT3` is
`PlacedIn` (counted: the spin's back edge). -/
theorem readerT3_addr_at (f1 f2 d : BitVec 64) (hpl : Program.PlacedIn readerT3) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt readerT3 l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, readerAddrTable3 f1 f2 d "reader" s g →
      Safely (cenv.instrStepEnv (SharedEnv.counted (SharedEnv.invTop (relayS f1 f2 d))))
        (fun x => (x.1.2 = endA ∧ True) ∨ False) ((s, (_root_.Executable.labels cenv).label "reader"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (SharedEnv.invTop (relayS f1 f2 d)))
    (Q := fun _ _ => True) (E := fun _ _ _ => False) (readerAddrTable3 f1 f2 d) ?_ readerT3_eq readerT3_wf hpl
    hlast s g hsg
  cfg_cases_env [readerT3]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨hT, rfl, rfl⟩ := ‹(_ → _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [forall_const] at hT
  all_goals simp only [SharedEnv.counted_ok] at *
  case vc4 =>
    -- the back edge (`cbz` taken): the counter moved
    have hn := (‹(SharedEnv.counted _).step _ _ _ _›).2
    refine Table.ofLabelsEnv_at ⟨by decide, fun _ => ?_, .inr fun ⟨_, hg⟩ => ?_⟩
    · simp_all
    · subst hg; simp at hn
  case vc7 => exact Table.ofLabelsEnv_at ⟨by decide, fun h => absurd h (by decide), .inl (by decide)⟩
  all_goals simp_all [SharedEnv.inv, Reg64s.setXReg]

end RunsAt

/-! ## The roles' address runs at the image's labels -/

section Lay

variable [layout : _root_.Layout] [Executable.ValidLayout (layout relay3Img)]

/-- **The writer's address run over its mask**, at the image's labels. -/
theorem writerW3_addr (f1 f2 d : BitVec 64) :
    ∀ s g, writerAddrTable3 f1 f2 d "writer" s g →
      Safely ((layout relay3ImgW).instrStepEnv (SharedEnv.invTop (relayS f1 f2 d)))
        (fun x => (x.1.2 = labY3 "wdone" ∧ True) ∨ False) ((s, labY3 "writer"), g) := by
  intro s g hsg
  have h : Safely ((layout relay3ImgW).instrStepEnv (SharedEnv.invTop (relayS f1 f2 d)))
      (fun x => (x.1.2 = (_root_.Executable.labels (layout relay3ImgW)).label "wdone" ∧ True) ∨ False)
      ((s, (_root_.Executable.labels (layout relay3ImgW)).label "writer"), g) :=
    letI : CodeEnv := ⟨layout relay3ImgW⟩
    writerT3_addr_at f1 f2 d writerW3_placedIn (Program.last_of_check writerT3_exit) s g hsg
  rw [labels_mask relay3ImgW_mask] at h
  exact h

/-- **The relay's address run over its mask**, at the image's labels. -/
theorem relayY3_addr (f1 f2 d : BitVec 64) :
    ∀ s g, relayAddrTable3 f1 f2 d "relay" s g →
      Safely ((layout relay3ImgY).instrStepEnv (SharedEnv.counted (SharedEnv.invTop (relayS f1 f2 d))))
        (fun x => (x.1.2 = labY3 "rdone" ∧ True) ∨ False) ((s, labY3 "relay"), g) := by
  intro s g hsg
  have h : Safely ((layout relay3ImgY).instrStepEnv (SharedEnv.counted (SharedEnv.invTop (relayS f1 f2 d))))
      (fun x => (x.1.2 = (_root_.Executable.labels (layout relay3ImgY)).label "rdone" ∧ True) ∨ False)
      ((s, (_root_.Executable.labels (layout relay3ImgY)).label "relay"), g) :=
    letI : CodeEnv := ⟨layout relay3ImgY⟩
    relayT3_addr_at f1 f2 d relayY3_placedIn (Program.last_of_check relayT3_exit) s g hsg
  rw [labels_mask relay3ImgY_mask] at h
  exact h

/-- **The reader's address run in the image.** -/
theorem readerD3_addr (f1 f2 d : BitVec 64) :
    ∀ s g, readerAddrTable3 f1 f2 d "reader" s g →
      Safely ((layout relay3Img).instrStepEnv (SharedEnv.counted (SharedEnv.invTop (relayS f1 f2 d))))
        (fun x => (x.1.2 = labY3 "ddone" ∧ True) ∨ False) ((s, labY3 "reader"), g) := by
  letI : CodeEnv := ⟨layout relay3Img⟩
  exact readerT3_addr_at f1 f2 d readerD3_placedIn (Program.last_of_check readerT3_exit)

end Lay

/-! ## The rules with the address run, and the start -/

section Rules

variable [layout : _root_.Layout] [Executable.ValidLayout (layout relay3Img)]

/-- **The whole-image writer's rule with the address run**
(`relayRuleW3_decls` through `ofSafelyEnvGMAD`). -/
def relayRuleW3_declsA {ds : Decls} (hsz : ds.StrictSized) (rp : RP) (hL : MpLocs rp.P) (tid : Nat)
    (f1 f2 d : BitVec 64) : ThreadRuleRX (I := isa) Arch.armv8 (YPost rp) tid :=
  ThreadRuleRX.ofSafelyEnvGMAD (post := postW3 rp) (relayS f1 f2 d) hsz relay3Img_noPairs relay3ImgW_mask
    (mpPlan_valid hL) relay3Img_rmwLive relay3ImgW_phase1 (postW3_end rp) (writerW3_stuck _) (hB_W3 rp tid)

/-- **The whole-image relay's rule with the address run**
(`relayRuleY3_decls` through `ofSafelyEnvGTMAD`). -/
def relayRuleY3_declsA {ds : Decls} (hsz : ds.StrictSized) (rp : RP) (hL : MpLocs rp.Q) (tid : Nat)
    (f1 f2 d : BitVec 64) : ThreadRuleRXGS (I := isa) G₀ Arch.armv8 (YPost rp) tid :=
  ThreadRuleRXGS.ofSafelyEnvGTMAD (post := postY3 rp) (relayS f1 f2 d) hsz relay3Img_noPairs relay3ImgY_mask
    (mpPlan_valid hL) relay3Img_rmwLive relay3ImgY_phase1 (postY3_end rp) (relayY3_stuck _) (hB_Y3 rp tid)

/-- **The whole-image reader's rule with the address run**
(`relayRuleD3_decls` through `ofSafelyEnvGTMAD`). -/
def relayRuleD3_declsA {ds : Decls} (hsz : ds.StrictSized) (rp : RP) (f1 f2 d : BitVec 64) :
    ThreadRuleRXGS (I := isa) G₀ Arch.armv8 (YPost rp) 2 :=
  ThreadRuleRXGS.ofSafelyEnvGTMAD (post := postD3 rp) (relayS f1 f2 d) hsz relay3Img_noPairs (MaskOf.refl _)
    rdPlan_valid relay3Img_rmwLive relay3Img_phase1 (postD3_end rp) (readerD3_stuck _) (hB_D3 rp)

end Rules

section Inv

variable [layout : _root_.Layout] [Executable.ValidLayout (layout relay3Img)] {ds : Decls} {f1 f2 d : BitVec 64}
  {sW sY sR : isa.State} {initMem : List (Loc × Val)}

theorem invW3_init_declsA (hsz : ds.StrictSized) (hL : RelayLocs f1 f2 d) (hW : WithDeclsD ds (StartW3 f1 d) sW) :
    (relayRuleW3_declsA hsz (relayParams f1 f2 d) hL.P 0 f1 f2 d).Inv True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) 0) (relayGhost (relayParams f1 f2 d)) := by
  obtain ⟨hds, hW⟩ := hW
  refine invGMAD_init (s := sW) rfl rfl ⟨QA64MD.of_noDecls hds ⟨hW.exe, hW.decls, hW.endPc, ?_⟩, ?addr⟩
  case addr =>
    unfold AddrSafeA
    rw [show sW.st = (sW.st.1, labY3 "writer") from Prod.ext rfl hW.pc]
    exact (writerW3_addr f1 f2 d _ () fun _ => ⟨hW.x0, hW.x1, hW.df, hW.dd⟩).mono
      fun _ h => h.elim And.left False.elim
  rw [show sW.noDecls.st = (sW.st.1, labY3 "writer") from Prod.ext rfl hW.pc]
  refine writerW3_envG _ hL.P 0 _ _ ⟨⟨hW.x0, hW.x1, hW.df, hW.dd⟩,
    .inl ⟨rfl, ⟨relayGhost_rel_F1 _, relayGhost_rel_Dt hL⟩, ?_⟩⟩
  simp only [σInit, Own0, relayRes, ↓reduceIte, writerRes, Res.initOf, Perm.init, writerFrac]
  exact ⟨by simp, fun p hp => by rw [hp.2], by simp, by simp <;> decide⟩

theorem invY3_init_declsA (hsz : ds.StrictSized) (hL : RelayLocs f1 f2 d)
    (hY : WithDeclsD ds (StartY3 f1 f2 d) sY) :
    (relayRuleY3_declsA hsz (relayParams f1 f2 d) hL.Q 1 f1 f2 d).Inv True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) 1) (relayGhost (relayParams f1 f2 d)) := by
  obtain ⟨hds, hY⟩ := hY
  refine invGTMAD_init (s := sY) rfl rfl ⟨QA64MD.of_noDecls hds ⟨hY.exe, hY.decls, hY.endPc, ?_⟩, ?addr⟩
  case addr =>
    unfold AddrSafeA
    rw [show sY.st = (sY.st.1, labY3 "relay") from Prod.ext rfl hY.pc]
    exact (Safely.uncountA (relayY3_addr f1 f2 d _ ((), 0)
      fun _ => ⟨hY.x0, hY.x1, hY.x2, hY.df1, hY.dd, hY.df2⟩)).mono fun _ ⟨_, h⟩ => h.elim And.left False.elim
  rw [show sY.noDecls.st = (sY.st.1, labY3 "relay") from Prod.ext rfl hY.pc]
  refine Safely.uncountA (relayY3_envGT _ hL.Q 1 _ (_, 0) ⟨⟨hY.x0, hY.x1, hY.x2, hY.df1, hY.dd, hY.df2⟩,
    .inl ⟨rfl, ⟨relayGhost_rel_F1 _, relayGhost_rel_Dt hL, ?_, 0, by show 0 < 2; decide, ?_, OkPred.flag⟩,
      relayGhost_rel_F2 hL.q_ne, ?_, ?_⟩⟩)
  · simp [Views.getFwd]
  · simp [relayRes, relayThreadRes]
  · simp [relayRes, relayThreadRes, Res.initOf, Perm.init, yFrac]; grind
  · simp [relayRes, relayThreadRes, Res.initOf, Perm.init, yFrac]

theorem invD3_init_declsA (hsz : ds.StrictSized) (hL : RelayLocs f1 f2 d) (hR : WithDeclsD ds (StartD3 f2 d) sR) :
    (relayRuleD3_declsA hsz (relayParams f1 f2 d) f1 f2 d).Inv True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) 2) (relayGhost (relayParams f1 f2 d)) := by
  obtain ⟨hds, hR⟩ := hR
  refine invGTMAD_init (s := sR) rfl rfl ⟨QA64MD.of_noDecls hds ⟨hR.exe, hR.decls, hR.endPc, ?_⟩, ?addr⟩
  case addr =>
    unfold AddrSafeA
    rw [show sR.st = (sR.st.1, labY3 "reader") from Prod.ext rfl hR.pc]
    exact (Safely.uncountA (readerD3_addr f1 f2 d _ ((), 0)
      fun _ => ⟨hR.x0, hR.x1, hR.df, hR.dd⟩)).mono fun _ ⟨_, h⟩ => h.elim And.left False.elim
  rw [show sR.noDecls.st = (sR.st.1, labY3 "reader") from Prod.ext rfl hR.pc]
  refine Safely.uncountA (readerD3_envGT (relayParams f1 f2 d).Q 2 _ (σInit (Config.init [sW, sY, sR] initMem)
    (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) 2) (relayGhost (relayParams f1 f2 d)), 0)
    ⟨hR.x0, hR.x1, hR.df, hR.dd,
    .inl ⟨rfl, relayGhost_rel_F2 hL.q_ne, ?_, 1, by show 1 < 2; decide, ?_, OkPred43.flag⟩⟩)
  · simp [σInit, Views.getFwd]
  · simp [σInit, relayRes, readerThreadRes]

end Inv

/-! ## No fault at the runner's declarations -/

section NoFault

variable [layout : _root_.Layout] [Executable.ValidLayout (layout relay3Img)] {ds : Decls}

/-- **No fault at the runner's declarations** for the whole-image writer's
rule: declarations agreeing on `f1`, `d`, `f2`. -/
theorem mp_relay3W_envG_runner_noFault (hsz : ds.StrictSized) (rp : RP) (hL : MpLocs rp.P) (tid : Nat)
    (f1 f2 d : BitVec 64) (hag : ds.AgreesOnA (relayS f1 f2 d)) :
    NoFaultRule (relayRuleW3_declsA hsz rp hL tid f1 f2 d) :=
  noFaultRule_ofSafelyEnvGMAD_rootD _ _ _ _ _ _ _ _ _ relay3Img_noFault hag

/-- **No fault at the runner's declarations** for the whole-image relay's
rule. -/
theorem mp_relay3Y_envG_runner_noFault (hsz : ds.StrictSized) (rp : RP) (hL : MpLocs rp.Q) (tid : Nat)
    (f1 f2 d : BitVec 64) (hag : ds.AgreesOnA (relayS f1 f2 d)) :
    NoFaultRuleS (relayRuleY3_declsA hsz rp hL tid f1 f2 d) :=
  noFaultRule_ofSafelyEnvGTMAD_rootD _ _ _ _ _ _ _ _ _ relay3Img_noFault hag

/-- **No fault at the runner's declarations** for the whole-image reader's
rule. -/
theorem mp_relay3D_envG_runner_noFault (hsz : ds.StrictSized) (rp : RP) (f1 f2 d : BitVec 64)
    (hag : ds.AgreesOnA (relayS f1 f2 d)) :
    NoFaultRuleS (relayRuleD3_declsA hsz rp f1 f2 d) :=
  noFaultRule_ofSafelyEnvGTMAD_rootD _ _ _ _ _ _ _ _ _ relay3Img_noFault hag

end NoFault

/-- The runner's declarations agree with `{}` on `f1`, `d`, `f2`. -/
theorem relay3DeclsD_agreesA : relay3DeclsD.AgreesOnA (relayS f1AddrY f2AddrY dAddrY) := by
  decls_agrees_on_a

/-- **No fault at the runner's declarations**, concrete: the three roles'
rules at `wLayoutY` and `relay3DeclsD`. -/
theorem mp_relay3_envG_runner_noFault_concrete (rp : RP) (hP : MpLocs rp.P) (hQ : MpLocs rp.Q) (tid : Nat) :
    NoFaultRule (relayRuleW3_declsA (layout := wLayoutY) relay3DeclsD_sized rp hP tid f1AddrY f2AddrY dAddrY) ∧
      NoFaultRuleS (relayRuleY3_declsA (layout := wLayoutY) relay3DeclsD_sized rp hQ tid f1AddrY f2AddrY dAddrY) ∧
      NoFaultRuleS (relayRuleD3_declsA (layout := wLayoutY) relay3DeclsD_sized rp f1AddrY f2AddrY dAddrY) :=
  ⟨mp_relay3W_envG_runner_noFault (layout := wLayoutY) _ _ _ _ _ _ _ relay3DeclsD_agreesA,
    mp_relay3Y_envG_runner_noFault (layout := wLayoutY) _ _ _ _ _ _ _ relay3DeclsD_agreesA,
    mp_relay3D_envG_runner_noFault (layout := wLayoutY) _ _ _ _ _ relay3DeclsD_agreesA⟩

/-! ## `mp_relay3_swpl.kl` -/

section Swpl

variable [layout : _root_.Layout] [Executable.ValidLayout (layout relaySwpl3Img)]

/-- **The `swpl` relay's address run over its mask**, at the mask's labels
(counted: the spin's back edge). -/
theorem relaySwplY3_addr' (f1 f2 d : BitVec 64) :
    letI : CodeEnv := ⟨layout relaySwpl3ImgY⟩
    ∀ s g, relayAddrTable3 f1 f2 d "relay" s g →
      Safely (cenv.instrStepEnv (SharedEnv.counted (SharedEnv.invTop (relayS f1 f2 d))))
        (fun x => (x.1.2 = (_root_.Executable.labels cenv).label "rdone" ∧ True) ∨ False)
        ((s, (_root_.Executable.labels cenv).label "relay"), g) := by
  letI : CodeEnv := ⟨layout relaySwpl3ImgY⟩
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (SharedEnv.invTop (relayS f1 f2 d)))
    (Q := fun _ _ => True) (E := fun _ _ _ => False) (relayAddrTable3 f1 f2 d) ?_ (by rfl) (by decide)
    relaySwplY3_placedIn (Program.last_of_check (lx := "rdone") (by decide)) s g hsg
  cfg_cases_env [relaySwplT3]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨hT, rfl, rfl⟩ := ‹(_ → _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [forall_const] at hT
  all_goals simp only [SharedEnv.counted_ok] at *
  all_goals first
    | exact Table.ofLabelsEnv_at ⟨by decide, fun h => absurd h (by decide), .inl (by decide)⟩
    | (have hn := (‹(SharedEnv.counted _).step _ _ _ _›).2
       refine Table.ofLabelsEnv_at ⟨by decide, fun _ => ?_, .inr fun ⟨_, hg⟩ => ?_⟩
       · simp_all
       · subst hg; simp at hn)
    | simp_all [SharedEnv.inv, Reg64s.setXReg]

/-- **The writer's address run over its mask**, at the image's labels. -/
theorem writerS3_addr (f1 f2 d : BitVec 64) :
    ∀ s g, writerAddrTable3 f1 f2 d "writer" s g →
      Safely ((layout relaySwpl3ImgW).instrStepEnv (SharedEnv.invTop (relayS f1 f2 d)))
        (fun x => (x.1.2 = labS3 "wdone" ∧ True) ∨ False) ((s, labS3 "writer"), g) := by
  haveI := ValidLayout.of_mask (maskOf_layout (layout := layout) (keepRange 0 7) relaySwpl3Img)
  letI : CodeEnv := ⟨layout relaySwpl3ImgW⟩
  intro s g hsg
  exact Safely.atImageLabels (maskOf_layout _ _) (writerT3_addr_at f1 f2 d (Program.PlacedIn.of_placedE
    (Program.placed_of_layout (p := relaySwpl3ImgW) (by decide) rfl (by decide)) (by decide))
    (Program.last_of_check (lx := "wdone") (by decide)) s g hsg)

/-- **The `swpl` relay's address run over its mask**, at the image's
labels. -/
theorem relaySwplY3_addr (f1 f2 d : BitVec 64) :
    ∀ s g, relayAddrTable3 f1 f2 d "relay" s g →
      Safely ((layout relaySwpl3ImgY).instrStepEnv (SharedEnv.counted (SharedEnv.invTop (relayS f1 f2 d))))
        (fun x => (x.1.2 = labS3 "rdone" ∧ True) ∨ False) ((s, labS3 "relay"), g) :=
  fun s g hsg => Safely.atImageLabels (maskOf_layout _ _) (relaySwplY3_addr' f1 f2 d s g hsg)

/-- **The reader's address run over its mask**, at the image's labels. -/
theorem readerS3_addr (f1 f2 d : BitVec 64) :
    ∀ s g, readerAddrTable3 f1 f2 d "reader" s g →
      Safely ((layout relaySwpl3ImgD).instrStepEnv (SharedEnv.counted (SharedEnv.invTop (relayS f1 f2 d))))
        (fun x => (x.1.2 = labS3 "ddone" ∧ True) ∨ False) ((s, labS3 "reader"), g) := by
  haveI := ValidLayout.of_mask (maskOf_layout (layout := layout) (keepRange 18 24) relaySwpl3Img)
  letI : CodeEnv := ⟨layout relaySwpl3ImgD⟩
  intro s g hsg
  exact Safely.atImageLabels (maskOf_layout _ _) (readerT3_addr_at f1 f2 d (Program.PlacedIn.of_placedE
    (Program.placed_of_layout (p := relaySwpl3ImgD) (by decide) rfl (by decide)) (by decide))
    (Program.last_of_check (lx := "ddone") (by decide)) s g hsg)

/-- **The whole-image writer's rule with the address run**
(`relayRuleWS3_decls` through `ofSafelyEnvGMAD`). -/
def relayRuleWS3_declsA {ds : Decls} (hsz : ds.StrictSized) (rp : RP) (hL : MpLocs rp.P) (tid : Nat)
    (f1 f2 d : BitVec 64) : ThreadRuleRX (I := isa) Arch.armv8 (YPost rp) tid :=
  ThreadRuleRX.ofSafelyEnvGMAD (post := postWS3 rp) (relayS f1 f2 d) hsz relaySwpl3Img_noPairs
    (maskOf_layout _ _) (mpPlan_valid hL) relaySwpl3Img_rmwLive relaySwpl3ImgW_phase1 (postWS3_end rp)
    (writerS3_stuck _) (hB_WS3 rp tid)

/-- **The whole-image `swpl` relay's rule with the address run**
(`relayRuleYS3_decls` through `ofSafelyEnvGTRCMAD`). -/
def relayRuleYS3_declsA {ds : Decls} (hsz : ds.StrictSized) (rp : RP) (hL : MpLocs rp.Q) (tid : Nat)
    (f1 f2 d : BitVec 64) : ThreadRuleRXGS (I := isa) G₀ Arch.armv8 (YPost rp) tid :=
  ThreadRuleRXGS.ofSafelyEnvGTRCMAD (post := postYS3 rp) (relayS f1 f2 d) hsz relaySwpl3Img_noPairs
    (maskOf_layout _ _) (mpPlan_valid hL) relaySwpl3Img_rmwLive relaySwpl3ImgY_phase1R (postYS3_end rp)
    (relayS3_stuck _) (hB_YS3 rp tid)

/-- **The whole-image reader's rule with the address run**
(`relayRuleDS3_decls` through `ofSafelyEnvGTMAD`). -/
def relayRuleDS3_declsA {ds : Decls} (hsz : ds.StrictSized) (rp : RP) (f1 f2 d : BitVec 64) :
    ThreadRuleRXGS (I := isa) G₀ Arch.armv8 (YPost rp) 2 :=
  ThreadRuleRXGS.ofSafelyEnvGTMAD (post := postDS3 rp) (relayS f1 f2 d) hsz relaySwpl3Img_noPairs
    (maskOf_layout _ _) rdPlan_valid relaySwpl3Img_rmwLive relaySwpl3ImgD_phase1 (postDS3_end rp)
    (readerS3_stuck _) (hB_DS3 rp)

variable {ds : Decls} {f1 f2 d : BitVec 64} {sW sY sR : isa.State} {initMem : List (Loc × Val)}

theorem invWS3_init_declsA (hsz : ds.StrictSized) (hL : RelayLocs f1 f2 d)
    (hW : WithDeclsD ds (StartWS3 f1 d) sW) :
    (relayRuleWS3_declsA hsz (relayParams f1 f2 d) hL.P 0 f1 f2 d).Inv True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) 0) (relayGhost (relayParams f1 f2 d)) := by
  obtain ⟨hds, hW⟩ := hW
  refine invGMAD_init (s := sW) rfl rfl ⟨QA64MD.of_noDecls hds ⟨hW.exe, hW.decls, hW.endPc, ?_⟩, ?addr⟩
  case addr =>
    unfold AddrSafeA
    rw [show sW.st = (sW.st.1, labS3 "writer") from Prod.ext rfl hW.pc]
    exact (writerS3_addr f1 f2 d _ () fun _ => ⟨hW.x0, hW.x1, hW.df, hW.dd⟩).mono
      fun _ h => h.elim And.left False.elim
  rw [show sW.noDecls.st = (sW.st.1, labS3 "writer") from Prod.ext rfl hW.pc]
  refine writerS3_envG _ hL.P 0 _ _ ⟨⟨hW.x0, hW.x1, hW.df, hW.dd⟩,
    .inl ⟨rfl, ⟨relayGhost_rel_F1 _, relayGhost_rel_Dt hL⟩, ?_⟩⟩
  simp only [σInit, Own0, relayRes, ↓reduceIte, writerRes, Res.initOf, Perm.init, writerFrac]
  exact ⟨by simp, fun p hp => by rw [hp.2], by simp, by simp <;> decide⟩

theorem invYS3_init_declsA (hsz : ds.StrictSized) (hL : RelayLocs f1 f2 d)
    (hY : WithDeclsD ds (StartYS3 f1 f2 d) sY) :
    (relayRuleYS3_declsA hsz (relayParams f1 f2 d) hL.Q 1 f1 f2 d).Inv True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) 1) (relayGhost (relayParams f1 f2 d)) := by
  obtain ⟨hds, hY⟩ := hY
  refine invGTRCMAD_init (s := sY) rfl rfl ⟨QA64MD.of_noDecls hds ⟨hY.exe, hY.decls, hY.endPc, ?_⟩, ?addr⟩
  case addr =>
    unfold AddrSafeA
    rw [show sY.st = (sY.st.1, labS3 "relay") from Prod.ext rfl hY.pc]
    exact (Safely.uncountA (relaySwplY3_addr f1 f2 d _ ((), 0)
      fun _ => ⟨hY.x0, hY.x1, hY.x2, hY.df1, hY.dd, hY.df2⟩)).mono fun _ ⟨_, h⟩ => h.elim And.left False.elim
  rw [show sY.noDecls.st = (sY.st.1, labS3 "relay") from Prod.ext rfl hY.pc]
  refine Safely.uncountA (relaySwplY3_envGTC _ hL.Q 1 _ (_, 0) ⟨⟨hY.x0, hY.x1, hY.x2, hY.df1, hY.dd, hY.df2⟩,
    .inl ⟨rfl, ⟨relayGhost_rel_F1 _, relayGhost_rel_Dt hL, ?_, 0, by show 0 < 2; decide, ?_, OkPred.flag⟩,
      relayGhost_rel_F2 hL.q_ne, ?_, ?_⟩⟩)
  · simp [Views.getFwd]
  · simp [relayRes, relayThreadRes]
  · simp [relayRes, relayThreadRes, Res.initOf, Perm.init, yFrac]; grind
  · simp [relayRes, relayThreadRes, Res.initOf, Perm.init, yFrac]

theorem invDS3_init_declsA (hsz : ds.StrictSized) (hL : RelayLocs f1 f2 d)
    (hR : WithDeclsD ds (StartDS3 f2 d) sR) :
    (relayRuleDS3_declsA hsz (relayParams f1 f2 d) f1 f2 d).Inv True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) 2) (relayGhost (relayParams f1 f2 d)) := by
  obtain ⟨hds, hR⟩ := hR
  refine invGTMAD_init (s := sR) rfl rfl ⟨QA64MD.of_noDecls hds ⟨hR.exe, hR.decls, hR.endPc, ?_⟩, ?addr⟩
  case addr =>
    unfold AddrSafeA
    rw [show sR.st = (sR.st.1, labS3 "reader") from Prod.ext rfl hR.pc]
    exact (Safely.uncountA (readerS3_addr f1 f2 d _ ((), 0)
      fun _ => ⟨hR.x0, hR.x1, hR.df, hR.dd⟩)).mono fun _ ⟨_, h⟩ => h.elim And.left False.elim
  rw [show sR.noDecls.st = (sR.st.1, labS3 "reader") from Prod.ext rfl hR.pc]
  refine Safely.uncountA (readerS3_envGT (relayParams f1 f2 d).Q 2 _ (σInit (Config.init [sW, sY, sR] initMem)
    (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) 2) (relayGhost (relayParams f1 f2 d)), 0)
    ⟨hR.x0, hR.x1, hR.df, hR.dd,
    .inl ⟨rfl, relayGhost_rel_F2 hL.q_ne, ?_, 1, by show 1 < 2; decide, ?_, OkPred43.flag⟩⟩)
  · simp [σInit, Views.getFwd]
  · simp [σInit, relayRes, readerThreadRes]

/-- **No fault at the runner's declarations** for the whole-image writer's
rule (`mp_relay3_swpl.kl`). -/
theorem mp_relay3_swplW_envG_runner_noFault (hsz : ds.StrictSized) (rp : RP) (hL : MpLocs rp.P) (tid : Nat)
    (f1 f2 d : BitVec 64) (hag : ds.AgreesOnA (relayS f1 f2 d)) :
    NoFaultRule (relayRuleWS3_declsA hsz rp hL tid f1 f2 d) :=
  noFaultRule_ofSafelyEnvGMAD_rootD _ _ _ _ _ _ _ _ _ relaySwpl3Img_noFault hag

/-- **No fault at the runner's declarations** for the whole-image `swpl`
relay's rule. -/
theorem mp_relay3_swplY_envG_runner_noFault (hsz : ds.StrictSized) (rp : RP) (hL : MpLocs rp.Q) (tid : Nat)
    (f1 f2 d : BitVec 64) (hag : ds.AgreesOnA (relayS f1 f2 d)) :
    NoFaultRuleS (relayRuleYS3_declsA hsz rp hL tid f1 f2 d) :=
  noFaultRule_ofSafelyEnvGTRCMAD_rootD _ _ _ _ _ _ _ _ _ relaySwpl3Img_noFault hag

/-- **No fault at the runner's declarations** for the whole-image reader's
rule (`mp_relay3_swpl.kl`). -/
theorem mp_relay3_swplD_envG_runner_noFault (hsz : ds.StrictSized) (rp : RP) (f1 f2 d : BitVec 64)
    (hag : ds.AgreesOnA (relayS f1 f2 d)) :
    NoFaultRuleS (relayRuleDS3_declsA hsz rp f1 f2 d) :=
  noFaultRule_ofSafelyEnvGTMAD_rootD _ _ _ _ _ _ _ _ _ relaySwpl3Img_noFault hag

end Swpl

/-- The runner's declarations agree with `{}` on `f1`, `d`, `f2`
(`mp_relay3_swpl.kl`: `f1 = 0x1100`, `f2 = 0x1200`, `d = 0x1000`). -/
theorem relaySwpl3DeclsD_agreesA : relaySwpl3DeclsD.AgreesOnA (relayS 0x1100 0x1200 0x1000) := by
  decls_agrees_on_a

/-- **No fault at the runner's declarations**, concrete: the three roles'
rules at `wLayoutS` and `relaySwpl3DeclsD`. -/
theorem mp_relay3_swpl_envG_runner_noFault_concrete (rp : RP) (hP : MpLocs rp.P) (hQ : MpLocs rp.Q) (tid : Nat) :
    NoFaultRule (relayRuleWS3_declsA (layout := wLayoutS) relaySwpl3DeclsD_sized rp hP tid 0x1100 0x1200 0x1000) ∧
      NoFaultRuleS (relayRuleYS3_declsA (layout := wLayoutS) relaySwpl3DeclsD_sized rp hQ tid 0x1100 0x1200 0x1000) ∧
      NoFaultRuleS (relayRuleDS3_declsA (layout := wLayoutS) relaySwpl3DeclsD_sized rp 0x1100 0x1200 0x1000) :=
  ⟨mp_relay3_swplW_envG_runner_noFault (layout := wLayoutS) _ _ _ _ _ _ _ relaySwpl3DeclsD_agreesA,
    mp_relay3_swplY_envG_runner_noFault (layout := wLayoutS) _ _ _ _ _ _ _ relaySwpl3DeclsD_agreesA,
    mp_relay3_swplD_envG_runner_noFault (layout := wLayoutS) _ _ _ _ _ relaySwpl3DeclsD_agreesA⟩

end Kraken.Promising.SLR.EnvG.Relay

#print axioms Kraken.Promising.SLR.EnvG.Relay.invW3_init_declsA
#print axioms Kraken.Promising.SLR.EnvG.Relay.invY3_init_declsA
#print axioms Kraken.Promising.SLR.EnvG.Relay.invD3_init_declsA
#print axioms Kraken.Promising.SLR.EnvG.Relay.mp_relay3_envG_runner_noFault_concrete
#print axioms Kraken.Promising.SLR.EnvG.Relay.invYS3_init_declsA
#print axioms Kraken.Promising.SLR.EnvG.Relay.mp_relay3_swpl_envG_runner_noFault_concrete
