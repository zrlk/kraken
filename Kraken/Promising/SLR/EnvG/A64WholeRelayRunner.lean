/-
**`mp_relay3.kl` for AArch64 from the runner's exact configuration**
`mp_relay3_envG_runner`, `mp_relay3_envG_whole`
for threads that carry the `.kl` runner's declarations (the typed header
`uint32_t d, f1, f2`: strict sized, `Decls.StrictSized`), and its concrete
instance `mp_relay3_envG_runner_concrete` (`runnerMatchesDY`: declarations
and initial memory included).

The proof is `A64WholeRelayPublic`'s with the D forms of
`EnvG/A64DeclsLink.lean`: the writer through `ThreadRuleRX.ofSafelyEnvGMD`,
the relay and the reader through `ThreadRuleRXGS.ofSafelyEnvGTMD`,
`invGMD_init`/`invGTMD_init`, `RelPureSpec.HoldsD`,
`final_of_relPureSafelySD`. The start states are the verbatim
`StartW3`/`StartY3`/`StartD3` with declarations (`A64Whole.WithDeclsD`). The
old theorems are unchanged. Faults are not covered (see
`EnvG/A64DeclsBridge.lean`).
-/
import Kraken.Promising.SLR.EnvG.A64WholeRelayConcrete
import Kraken.Promising.SLR.EnvG.A64DeclsRunner

namespace Kraken.Promising.SLR.EnvG.Relay

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Mp Kraken.Promising.SLR.MpTrees
open Kraken.Promising.SLR.EnvG.MpSmoke Kraken.Promising.SLR.EnvG.MpLink Kraken.Promising.SLR.MpPublic
open Kraken.Promising.SLR.EnvG.MpRelPure Kraken.Promising.SLR.EnvG.TakeSmoke Kraken.Promising.SLR.EnvG.TakeMp
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)

/-! ## The rules and the start, with declarations -/

section Rules

variable [layout : _root_.Layout] [Executable.ValidLayout (layout relay3Img)]

omit [Executable.ValidLayout (layout relay3Img)] in
/-- The image has no `LDXP`/`STXP`. -/
theorem relay3Img_noPairs : Kraken.Executable.noPairs (layout relay3Img) = true := by
  rw [Layout.apply_noPairs]; decide

/-- **The whole-image writer's rule with strict sized declarations `ds`**
(`relayRuleW3` through `ofSafelyEnvGMD`). -/
def relayRuleW3_decls {ds : Decls} (hsz : ds.StrictSized) (rp : RP) (hL : MpLocs rp.P) (tid : Nat) :
    ThreadRuleRX (I := isa) Arch.armv8 (YPost rp) tid :=
  ThreadRuleRX.ofSafelyEnvGMD (post := postW3 rp) hsz relay3Img_noPairs relay3ImgW_mask (mpPlan_valid hL)
    relay3Img_rmwLive relay3ImgW_phase1 (postW3_end rp) (writerW3_stuck _) (hB_W3 rp tid)

/-- **The whole-image relay's rule with declarations** (`ofSafelyEnvGTMD`). -/
def relayRuleY3_decls {ds : Decls} (hsz : ds.StrictSized) (rp : RP) (hL : MpLocs rp.Q) (tid : Nat) :
    ThreadRuleRXGS (I := isa) G₀ Arch.armv8 (YPost rp) tid :=
  ThreadRuleRXGS.ofSafelyEnvGTMD (post := postY3 rp) hsz relay3Img_noPairs relay3ImgY_mask (mpPlan_valid hL)
    relay3Img_rmwLive relay3ImgY_phase1 (postY3_end rp) (relayY3_stuck _) (hB_Y3 rp tid)

/-- **The whole-image reader's rule with declarations.** -/
def relayRuleD3_decls {ds : Decls} (hsz : ds.StrictSized) (rp : RP) :
    ThreadRuleRXGS (I := isa) G₀ Arch.armv8 (YPost rp) 2 :=
  ThreadRuleRXGS.ofSafelyEnvGTMD (post := postD3 rp) hsz relay3Img_noPairs (MaskOf.refl _) rdPlan_valid
    relay3Img_rmwLive relay3Img_phase1 (postD3_end rp) (readerD3_stuck _) (hB_D3 rp)

end Rules

section Inv

variable [layout : _root_.Layout] [Executable.ValidLayout (layout relay3Img)] {ds : Decls} {f1 f2 d : BitVec 64}
  {sW sY sR : isa.State} {initMem : List (Loc × Val)}

theorem invW3_init_decls (hsz : ds.StrictSized) (hL : RelayLocs f1 f2 d) (hW : WithDeclsD ds (StartW3 f1 d) sW) :
    (relayRuleW3_decls hsz (relayParams f1 f2 d) hL.P 0).Inv True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) 0) (relayGhost (relayParams f1 f2 d)) := by
  obtain ⟨hds, hW⟩ := hW
  refine invGMD_init (s := sW) rfl rfl (QA64MD.of_noDecls hds ⟨hW.exe, hW.decls, hW.endPc, ?_⟩)
  rw [show sW.noDecls.st = (sW.st.1, labY3 "writer") from Prod.ext rfl hW.pc]
  refine writerW3_envG _ hL.P 0 _ _ ⟨⟨hW.x0, hW.x1, hW.df, hW.dd⟩,
    .inl ⟨rfl, ⟨relayGhost_rel_F1 _, relayGhost_rel_Dt hL⟩, ?_⟩⟩
  simp only [σInit, Own0, relayRes, ↓reduceIte, writerRes, Res.initOf, Perm.init, writerFrac]
  exact ⟨by simp, fun p hp => by rw [hp.2], by simp, by simp <;> decide⟩

theorem invY3_init_decls (hsz : ds.StrictSized) (hL : RelayLocs f1 f2 d)
    (hY : WithDeclsD ds (StartY3 f1 f2 d) sY) :
    (relayRuleY3_decls hsz (relayParams f1 f2 d) hL.Q 1).Inv True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) 1) (relayGhost (relayParams f1 f2 d)) := by
  obtain ⟨hds, hY⟩ := hY
  refine invGTMD_init (s := sY) rfl rfl (QA64MD.of_noDecls hds ⟨hY.exe, hY.decls, hY.endPc, ?_⟩)
  rw [show sY.noDecls.st = (sY.st.1, labY3 "relay") from Prod.ext rfl hY.pc]
  refine Safely.uncountA (relayY3_envGT _ hL.Q 1 _ (_, 0) ⟨⟨hY.x0, hY.x1, hY.x2, hY.df1, hY.dd, hY.df2⟩,
    .inl ⟨rfl, ⟨relayGhost_rel_F1 _, relayGhost_rel_Dt hL, ?_, 0, by show 0 < 2; decide, ?_, OkPred.flag⟩,
      relayGhost_rel_F2 hL.q_ne, ?_, ?_⟩⟩)
  · simp [σInit, Views.getFwd]
  · simp [σInit, relayRes, relayThreadRes]
  · simp [σInit, relayRes, relayThreadRes, Res.initOf, Perm.init, yFrac]; grind
  · simp [σInit, relayRes, relayThreadRes, Res.initOf, Perm.init, yFrac]

theorem invD3_init_decls (hsz : ds.StrictSized) (hL : RelayLocs f1 f2 d) (hR : WithDeclsD ds (StartD3 f2 d) sR) :
    (relayRuleD3_decls hsz (relayParams f1 f2 d)).Inv True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) 2) (relayGhost (relayParams f1 f2 d)) := by
  obtain ⟨hds, hR⟩ := hR
  refine invGTMD_init (s := sR) rfl rfl (QA64MD.of_noDecls hds ⟨hR.exe, hR.decls, hR.endPc, ?_⟩)
  rw [show sR.noDecls.st = (sR.st.1, labY3 "reader") from Prod.ext rfl hR.pc]
  refine Safely.uncountA (readerD3_envGT (relayParams f1 f2 d).Q 2 _ (σInit (Config.init [sW, sY, sR] initMem)
    (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) 2) (relayGhost (relayParams f1 f2 d)), 0)
    ⟨hR.x0, hR.x1, hR.df, hR.dd,
    .inl ⟨rfl, relayGhost_rel_F2 hL.q_ne, ?_, 1, by show 1 < 2; decide, ?_, OkPred43.flag⟩⟩)
  · simp [σInit, Views.getFwd]
  · simp [σInit, relayRes, readerThreadRes]

end Inv

/-- **The `NPSafeP` side with declarations.** -/
theorem relay3_whole_npSafe_decls (l : _root_.Layout) [Executable.ValidLayout (l relay3Img)] {ds : Decls}
    (hsz : ds.StrictSized) {f1 f2 d : BitVec 64} (hL : RelayLocs f1 f2 d) {sW sY sR : isa.State}
    {initMem : List (Loc × Val)} (hW : WithDeclsD ds (StartW3 (layout := l) f1 d) sW)
    (hY : WithDeclsD ds (StartY3 (layout := l) f1 f2 d) sY) (hR : WithDeclsD ds (StartD3 (layout := l) f2 d) sR) :
    ∀ tid, tid < [sW, sY, sR].length → ∀ n m, NPSafeP (model isa) Arch.armv8 (YPost (relayParams f1 f2 d)) tid G₀
      (K2Scope (model isa) AllocIds) n m True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) tid)
      (relayGhost (relayParams f1 f2 d)) := by
  intro tid htid n m
  match tid, htid with
  | 0, _ =>
    exact NPSafe.toP (fun _ _ _ _ _ h => h) (fun _ _ _ h => K2₀.toScope _ h)
      (NPSafe.of_ruleRX (relayRuleW3_decls (layout := l) hsz _ hL.P 0) n m _ _ _ _
        (invW3_init_decls (layout := l) hsz hL hW))
  | 1, _ =>
    exact NPSafeP.of_ruleRXGS (relayRuleY3_decls (layout := l) hsz _ hL.Q 1) n m _ _ _ _
      (invY3_init_decls (layout := l) hsz hL hY)
  | 2, _ =>
    exact NPSafeP.of_ruleRXGS (relayRuleD3_decls (layout := l) hsz _) n m _ _ _ _
      (invD3_init_decls (layout := l) hsz hL hR)
  | _ + 3, h => simp only [List.length_cons, List.length_nil] at h; omega

/-- **A three-thread ownership relay `mp_relay3.kl` for AArch64 under
`Arch.armv8`, every thread running the whole `.kl` image, with the runner's
declarations**: `mp_relay3_envG_whole` for threads whose declarations are
strict sized (`ds.StrictSized`: the `.kl` runner's, from the typed header)
and which otherwise start as there (`StartW3`/`StartY3`/`StartD3` of the
thread with its declarations dropped). -/
theorem mp_relay3_envG_runner {fuel : Nat} (l : _root_.Layout) [Executable.ValidLayout (l relay3Img)]
    {ds : Decls} (hsz : ds.StrictSized) (f1 f2 d : BitVec 64) (hL : RelayLocs f1 f2 d) {sW sY sR : isa.State}
    {initMem : List (Loc × Val)} (hW : WithDeclsD ds (StartW3 (layout := l) f1 d) sW)
    (hY : WithDeclsD ds (StartY3 (layout := l) f1 f2 d) sY) (hR : WithDeclsD ds (StartD3 (layout := l) f2 d) sR)
    (hF1 : (Config.init [sW, sY, sR] initMem).mem.initVal ⟨f1, 4⟩ = 0)
    (hF2 : (Config.init [sW, sY, sR] initMem).mem.initVal ⟨f2, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [sW, sY, sR] initMem) cfg)
    (hf : cfg.final = true) :
    (∃ t, cfg.threads[2]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 43) ∧
      cfg.mem.finalVal ⟨d, 4⟩ = 43#128 :=
  final_of_relPureSafelySD Arch.armv8 fuel (B := YPost (relayParams f1 f2 d))
    (Φ := fun c => (∃ t, c.threads[2]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 43) ∧
      c.mem.finalVal ⟨d, 4⟩ = 43#128)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_relayInit hL _ hF1 hF2) initGhost_pend
    (relay3PureSpecW l _) (fun _ => ds) (fun _ => hsz)
    (fun tid => by rcases tid with _ | _ | _ <;> exact relay3Img_noPairs (layout := l))
    (RelPureSpec.holdsD_init (ss := [sW, sY, sR]) (List.forall_mem_cons.2 ⟨hW.1,
      List.forall_mem_cons.2 ⟨hY.1, List.forall_mem_cons.2 ⟨hR.1, fun _ h => nomatch h⟩⟩⟩)
      (relay3PureSpecW_init l hL hW.2 hY.2 hR.2))
    (relay3_whole_npSafe_decls l hsz hL hW hY hR) hc hf
    fun _ _ E' _ hsize hB => relay_final E' hf hsize hB

/-! ## The runner's configuration -/

/-- The runner's declarations for the typed `mp_relay3.kl`: `d`, `f1`, `f2`
4-byte words (strict). -/
def relay3DeclsD : Decls := { locs := [⟨dAddrY, 4⟩, ⟨f1AddrY, 4⟩, ⟨f2AddrY, 4⟩], unsizedDefault := false }

theorem relay3DeclsD_sized : relay3DeclsD.StrictSized := ⟨rfl, by decide⟩

/-- The threads as the runner prepares them, declarations included. -/
def writerDY0 : AArch64.State := { writerW0 with decls := relay3DeclsD }
def relayDY1 : AArch64.State := { relayW1 with decls := relay3DeclsD }
def readerDY2 : AArch64.State := { readerW2 with decls := relay3DeclsD }

/-- The runner's configuration is `Config.init [writerDY0, relayDY1,
readerDY2] relay3InitMem` in everything the theorem reads (declarations and
initial memory included: the typed header's initial memory is the existing
`relay3InitMem`). -/
def runnerMatchesDY (src : String) : Bool :=
  A64Whole.runnerIsD src [writerDY0, relayDY1, readerDY2] relay3InitMem

/-- info: true -/
#guard_msgs in
#eval runnerMatchesDY relay3Kl

/-- **`2:X4 = 43 ∧ [d] = 43`** for `mp_relay3.kl` under `Arch.armv8`, from
the runner's exact configuration (the whole `code` block at `0x100000`, the
typed header's declarations and initial memory): concrete instance of
`mp_relay3_envG_runner`. -/
theorem mp_relay3_envG_runner_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [writerDY0, relayDY1, readerDY2] relay3InitMem) c)
    (hf : c.final = true) :
    (∃ t, c.threads[2]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 43) ∧
      c.mem.finalVal ⟨dAddrY, 4⟩ = 43#128 :=
  mp_relay3_envG_runner wLayoutY relay3DeclsD_sized f1AddrY f2AddrY dAddrY ⟨by decide, by decide, by decide⟩
    (withDeclsD_of rfl writerW0_start) (withDeclsD_of rfl relayW1_start) (withDeclsD_of rfl readerW2_start)
    (by simp only [Config.init]; decide) (by simp only [Config.init]; decide) hc hf

end Kraken.Promising.SLR.EnvG.Relay

#print axioms Kraken.Promising.SLR.EnvG.Relay.mp_relay3_envG_runner
#print axioms Kraken.Promising.SLR.EnvG.Relay.mp_relay3_envG_runner_concrete
