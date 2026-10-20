/-
**`mp_relay3_xchg.kl` from the runner's exact configuration**: `mp_relay3_xchg_envG_runner`, `mp_relay3_xchg_envG_verbatim` for
threads that carry the `.kl` runner's declarations (the header types `d`,
`f1`, `f2` `uint32_t`: strict sized, `Decls.Sized`), and its concrete
instance `mp_relay3_xchg_envG_runner_concrete` (`runnerMatchesD`:
declarations and initial memory included).

The proof is `X64RelayAbsPublic`'s with the D forms of
`EnvG/X64DeclsLink.lean`: the writer on `EnvG` (`ofSafelyEnvGXMD`), the
relay on the take route with a claim-conditional RMW (`ofSafelyEnvGTRCXMD`),
the reader on the take route (`ofSafelyEnvGTXMD`), each over its mask; the
`invG…XMD_init`s, `RelPureSpecQX.HoldsD`, `final_of_relPureSafelyQX_tsoSD`.
The old theorems are unchanged.
-/
import Kraken.Promising.SLR.EnvG.X64RelayAbsPublic
import Kraken.Promising.SLR.EnvG.X64RelayAbsConcrete
import Kraken.Promising.SLR.EnvG.X64DeclsLink
import Kraken.Promising.SLR.EnvG.X64RunnerCommon

namespace Kraken.Promising.X64.EnvG.RelayAbs

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Mp Kraken.Promising.X64.EnvG.MpSmoke
open Kraken.Promising.X64.EnvG.MpLink Kraken.Promising.X64.EnvG.MpRelPure Kraken.Promising.X64.EnvG.MpPublic
open Kraken.Promising.X64.EnvG.TakeMp Kraken.Promising.X64.EnvG.RelayX

variable [layout : _root_.Layout] [Executable.ValidLayout (layout relayImageV)]

/-! ## The rules with declarations -/

/-- **The verbatim writer's rule with strict sized declarations `ds`**
(`relayRuleWV` through `ofSafelyEnvGXMD`). -/
def relayRuleWVD {ds : Decls} (hsz : ds.Sized) (rp : RP) (hL : MpLocs rp.P) (tid : Nat) :
    ThreadRuleRX (I := isa) Arch.tso (YPost rp) tid :=
  ThreadRuleRX.ofSafelyEnvGXMD (S := mpS rp.P) (post := postWV rp) hsz relayImageW_mask (mpPlan_valid hL)
    (mpS_le16 rp.P) relayImageW_phase1 (postWV_end rp) (writerW_stuck _) (hB_WV rp tid)

/-- **The verbatim relay's rule with strict sized declarations `ds`**
(`relayRuleYV` through `ofSafelyEnvGTRCXMD`). -/
def relayRuleYVD {ds : Decls} (hsz : ds.Sized) (rp : RP) (hL : MpLocs rp.Q) (tid : Nat) :
    ThreadRuleRXGS (I := isa) G₀ Arch.tso (YPost rp) tid :=
  ThreadRuleRXGS.ofSafelyEnvGTRCXMD (S := relayS rp) (post := postYV rp) hsz relayImageY_mask (mpPlan_valid hL)
    (relayS_le16 rp) relayImageY_phase1 (postYV_end rp) (relayY_stuck _) (hB_YV rp tid)

/-- **The verbatim reader's rule with strict sized declarations `ds`**
(`relayRuleDV` through `ofSafelyEnvGTXMD`). -/
def relayRuleDVD {ds : Decls} (hsz : ds.Sized) (rp : RP) : ThreadRuleRXGS (I := isa) G₀ Arch.tso (YPost rp) 2 :=
  ThreadRuleRXGS.ofSafelyEnvGTXMD (S := mpS rp.Q) (post := postDV rp) hsz relayImageR_mask rdPlanX_valid
    (mpS_le16 rp.Q) relayImageR_phase1 (postDV_end rp) (readerR_stuck _) (hB_DV rp)

/-! ## The start with declarations -/

/-- **The verbatim writer at its start with declarations `ds`** (`StartWV`
with `decls = ds`). -/
structure StartWVD (ds : Decls) (s : State) : Prop where
  exe : s.exe = layout relayImageV
  decls : s.decls = ds
  pc : s.st.2 = labY "writer"
  endPc : s.endPc = labY "wdone"
  rdi : s.st.1.regs.get64 .rdi = symY "f1"
  rsi : s.st.1.regs.get64 .rsi = symY "d"
  split : Split [(symY "f1", 4), (symY "d", 4)] s.st.1.dmem

/-- **The verbatim relay at its start with declarations `ds`** (`StartYV`
with `decls = ds`). -/
structure StartYVD (ds : Decls) (s : State) : Prop where
  exe : s.exe = layout relayImageV
  decls : s.decls = ds
  pc : s.st.2 = labY "relay"
  endPc : s.endPc = labY "rdone"
  rdi : s.st.1.regs.get64 .rdi = symY "f1"
  rsi : s.st.1.regs.get64 .rsi = symY "d"
  rdx : s.st.1.regs.get64 .rdx = symY "f2"
  split : Split [(symY "f1", 4), (symY "d", 4), (symY "f2", 4)] s.st.1.dmem

/-- **The verbatim reader at its start with declarations `ds`** (`StartRV`
with `decls = ds`). -/
structure StartRVD (ds : Decls) (s : State) : Prop where
  exe : s.exe = layout relayImageV
  decls : s.decls = ds
  pc : s.st.2 = labY "reader"
  endPc : s.endPc = labY "ddone"
  rdi : s.st.1.regs.get64 .rdi = symY "f2"
  rsi : s.st.1.regs.get64 .rsi = symY "d"
  split : Split [(symY "f2", 4), (symY "d", 4)] s.st.1.dmem

section Inv

variable {ds : Decls} {sW sY sR : isa.State} {initMem : List (Loc × Val)}

/-- **The verbatim writer's initial invariant with declarations.** -/
theorem invWV_initD (hsz : ds.Sized) (hL : RelayLocs (symY "f1") (symY "f2") (symY "d")) (hW : StartWVD ds sW) :
    (relayRuleWVD hsz rpV hL.P 0).Inv True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem rpV 0) (relayGhost rpV) := by
  have hst : sW.st = (sW.st.1, labY "writer") := Prod.ext rfl hW.pc
  refine invGXMD_init (s := sW) rfl rfl ⟨hW.exe, hW.decls, hW.endPc, hW.split, ?_⟩
  rw [hst]
  refine writerW_envG _ hL.P 0 sW.st.1 _ ⟨⟨hW.rdi, hW.rsi, split_df hW.split, split_dd hW.split⟩,
    ⟨relayGhost_rel_F1 _, relayGhost_rel_Dt hL⟩, ?_⟩
  simp only [σInitX, Own0, relayRes, ↓reduceIte, writerRes, Res.initOf, Perm.init, writerFrac]
  exact ⟨by simp, fun p hp => by rw [hp.2], by simp, by simp <;> decide⟩

/-- **The verbatim relay's initial invariant with declarations.** -/
theorem invYV_initD (hsz : ds.Sized) (hL : RelayLocs (symY "f1") (symY "f2") (symY "d")) (hY : StartYVD ds sY) :
    (relayRuleYVD hsz rpV hL.Q 1).Inv True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem rpV 1) (relayGhost rpV) := by
  have hst : sY.st = (sY.st.1, labY "relay") := Prod.ext rfl hY.pc
  refine invGTRCXMD_init (s := sY) rfl rfl ⟨hY.exe, hY.decls, hY.endPc, hY.split, ?_⟩
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

/-- **The verbatim reader's initial invariant with declarations.** -/
theorem invDV_initD (hsz : ds.Sized) (hL : RelayLocs (symY "f1") (symY "f2") (symY "d")) (hR : StartRVD ds sR) :
    (relayRuleDVD hsz rpV).Inv True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem rpV 2) (relayGhost rpV) := by
  have hst : sR.st = (sR.st.1, labY "reader") := Prod.ext rfl hR.pc
  refine invGTXMD_init (s := sR) rfl rfl ⟨hR.exe, hR.decls, hR.endPc, hR.split, ?_⟩
  rw [hst]
  refine Safely.uncountR (readerR_envGT _ 2 sR.st.1 (σInitX (Config.init [sW, sY, sR] initMem)
    (relayRes (Config.init [sW, sY, sR] initMem).mem rpV 2) (relayGhost rpV), 0)
    ⟨⟨hR.rdi, hR.rsi, split_df hR.split, split_dd hR.split⟩,
      relayGhost_rel_F2 hL.q_ne, ?_, 1, by show 1 < 2; decide, ?_, OkPred43.flag⟩)
  · simp [σInitX, Views.getFwd]
  · simp [σInitX, relayRes, readerThreadRes]

/-- **The `NPSafeP` side** for the verbatim threads with declarations. -/
theorem relayV_npSafeD (hsz : ds.Sized) (hL : RelayLocs (symY "f1") (symY "f2") (symY "d")) (hW : StartWVD ds sW)
    (hY : StartYVD ds sY) (hR : StartRVD ds sR) :
    ∀ tid, tid < [sW, sY, sR].length → ∀ n m, NPSafeP (model isa) Arch.tso (YPost rpV) tid G₀
      (K2Scope (model isa) AllocIds) n m True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem rpV tid) (relayGhost rpV) := by
  intro tid htid n m
  match tid, htid with
  | 0, _ =>
    exact NPSafe.toP (fun _ _ _ _ _ h => h) (fun _ _ _ h => K2₀.toScope _ h)
      (NPSafe.of_ruleRX (relayRuleWVD hsz rpV hL.P 0) n m _ _ _ _ (invWV_initD hsz hL hW))
  | 1, _ => exact NPSafeP.of_ruleRXGS (relayRuleYVD hsz rpV hL.Q 1) n m _ _ _ _ (invYV_initD hsz hL hY)
  | 2, _ => exact NPSafeP.of_ruleRXGS (relayRuleDVD hsz rpV) n m _ _ _ _ (invDV_initD hsz hL hR)
  | _ + 3, h => simp only [List.length_cons, List.length_nil] at h; omega

end Inv

/-- **The all-release specifications hold at the start states with
declarations.** -/
theorem relayNoNTSpecV_initD {ds : Decls} {sW sY sR : State} (hW : StartWVD ds sW) (hY : StartYVD ds sY)
    (hR : StartRVD ds sR) :
    ∀ tid s, [sW, sY, sR][tid]? = some s → (relayNoNTSpecV tid).HoldsD ds s
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
`Arch.tso`, `mp_relay3_xchg.kl`'s code verbatim, with the runner's
declarations**: `mp_relay3_xchg_envG_verbatim` for threads whose
declarations are strict sized (`ds.Sized`: the `.kl` runner's, from the
typed header). -/
theorem mp_relay3_xchg_envG_runner {fuel : Nat} {ds : Decls} (hsz : ds.Sized)
    (hL : RelayLocs (symY "f1") (symY "f2") (symY "d"))
    {sW sY sR : isa.State} {initMem : List (Loc × Val)} (hW : StartWVD ds sW) (hY : StartYVD ds sY)
    (hR : StartRVD ds sR)
    (hF1 : (Config.init [sW, sY, sR] initMem).mem.initVal ⟨symY "f1", 4⟩ = 0)
    (hF2 : (Config.init [sW, sY, sR] initMem).mem.initVal ⟨symY "f2", 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [sW, sY, sR] initMem) cfg)
    (hf : cfg.final = true) :
    (∃ t, cfg.threads[2]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 43) ∧
      cfg.mem.finalVal ⟨symY "d", 4⟩ = 43#128 :=
  final_of_relPureSafelyQX_tsoSD fuel (B := YPost rpV)
    (Φ := fun c => (∃ t, c.threads[2]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 43) ∧
      c.mem.finalVal ⟨symY "d", 4⟩ = 43#128)
    (erase_relayInit hL _ hF1 hF2) initGhost_pend relayNoNTSpecV (fun _ => ds) (fun _ => hsz)
    (relayNoNTSpecV_initD hW hY hR) (relayV_npSafeD hsz hL hW hY hR) hc hf
    fun _ _ E' _ hsize hB => relay_final E' hf hsize hB

end Kraken.Promising.X64.EnvG.RelayAbs

/-! ## The runner's configuration -/

namespace Kraken.Promising.X64.EnvG.RelayAbs.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.RelayAbs Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG.RelayX

/-- The runner's declarations for the typed `mp_relay3_xchg.kl`: `d`, `f1`,
`f2`, 4-byte words (strict). -/
def relayDeclsD : Decls := { locs := [⟨0x1000000, 4⟩, ⟨0x1000100, 4⟩, ⟨0x1000200, 4⟩], unsizedDefault := false }

theorem relayDeclsD_sized : relayDeclsD.Sized := ⟨rfl, by decide⟩

/-- The threads as the runner prepares them, declarations included. -/
def relayW0D : X64.State := { relayW0 with decls := relayDeclsD }
def relayY1D : X64.State := { relayY1 with decls := relayDeclsD }
def relayR2D : X64.State := { relayR2 with decls := relayDeclsD }

/-- The runner's configuration is `Config.init [relayW0D, relayY1D, relayR2D]
relayInitMemV` in everything the theorem reads (declarations and initial
memory included). -/
def runnerMatchesD (src : String) : Bool :=
  runnerMatchesDL src [relayW0D, relayY1D, relayR2D] relayInitMemV

/-- info: true -/
#guard_msgs in
#eval runnerMatchesD relayKl

section
attribute [local instance] relayLayoutV

theorem relayW0D_start : StartWVD relayDeclsD relayW0D :=
  ⟨rfl, rfl, by show (0x100000 : Int64) = labY "writer"; rw [labY_at 0]; decide,
    by show (0x100000 + 5 : Int64) = labY "wdone"; rw [labY_at 6]; decide,
    by rw [symY_f1]; simp [relayW0D, relayW0, relayThreadV, Reg64s.get64, Reg64s.set64],
    by rw [symY_d]; simp [relayW0D, relayW0, relayThreadV, Reg64s.get64, Reg64s.set64], Split.empty _⟩

theorem relayY1D_start : StartYVD relayDeclsD relayY1D :=
  ⟨rfl, rfl, by show (0x100000 + 6 : Int64) = labY "relay"; rw [labY_at 8]; decide,
    by show (0x100000 + 13 : Int64) = labY "rdone"; rw [labY_at 16]; decide,
    by rw [symY_f1]; simp [relayY1D, relayY1, relayThreadV, Reg64s.get64, Reg64s.set64],
    by rw [symY_d]; simp [relayY1D, relayY1, relayThreadV, Reg64s.get64, Reg64s.set64],
    by rw [symY_f2]; simp [relayY1D, relayY1, relayThreadV, Reg64s.get64, Reg64s.set64], Split.empty _⟩

theorem relayR2D_start : StartRVD relayDeclsD relayR2D :=
  ⟨rfl, rfl, by show (0x100000 + 14 : Int64) = labY "reader"; rw [labY_at 18]; decide,
    by show (0x100000 + 19 : Int64) = labY "ddone"; rw [labY_at 24]; decide,
    by rw [symY_f2]; simp [relayR2D, relayR2, relayThreadV, Reg64s.get64, Reg64s.set64],
    by rw [symY_d]; simp [relayR2D, relayR2, relayThreadV, Reg64s.get64, Reg64s.set64], Split.empty _⟩

/-- **The relay, `mp_relay3_xchg.kl`'s code verbatim, from the runner's
exact configuration**: every final configuration under `Arch.tso` has the
reader's `ebx = 43` and `[d] = 43`. -/
theorem mp_relay3_xchg_envG_runner_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [relayW0D, relayY1D, relayR2D] relayInitMemV) c)
    (hf : c.final = true) :
    (∃ t, c.threads[2]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 43) ∧
      c.mem.finalVal ⟨0x1000000, 4⟩ = 43#128 := by
  have h := mp_relay3_xchg_envG_runner (layout := relayLayoutV) relayDeclsD_sized
    ⟨by rw [symY_f1, symY_d]; decide, by rw [symY_f2, symY_d]; decide, by rw [symY_f1, symY_f2]; decide⟩
    relayW0D_start relayY1D_start relayR2D_start
    (by rw [symY_f1]; simp only [Config.init_mem]; decide)
    (by rw [symY_f2]; simp only [Config.init_mem]; decide) hc hf
  rwa [symY_d] at h

end

end Kraken.Promising.X64.EnvG.RelayAbs.Concrete

#print axioms Kraken.Promising.X64.EnvG.RelayAbs.mp_relay3_xchg_envG_runner
#print axioms Kraken.Promising.X64.EnvG.RelayAbs.Concrete.mp_relay3_xchg_envG_runner_concrete
