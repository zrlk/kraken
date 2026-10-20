/-
**`mp_incl.kl` from the runner's exact configuration**:
`x64_mp_incl_envGV_runner`, `x64_mp_incl_envGV_verbatim` for threads that
carry the `.kl` runner's declarations (the header types `d` and `f`
`uint32_t`: strict sized, `Decls.Sized`), and its concrete instance
`x64_mp_incl_envGV_runner_concrete` (`runnerMatchesD`: declarations and
initial memory included).

The proof is `X64MpInclAbsPublic`'s with the D forms of
`EnvG/X64DeclsLink.lean`: the writer on `EnvGLRV` over its mask
(`ThreadRuleRX.ofSafelyEnvGLRVXMD`), the reader on `EnvG` over its mask
(`ofSafelyEnvGXMD`), `invGLRVXMD_init`/`invGXMD_init`,
`RelPureSpecQX.HoldsD`, `final_of_relPureSafelyQX_tsoD`. The old theorems
are unchanged.
-/
import Kraken.Promising.SLR.EnvG.X64MpInclAbsPublic
import Kraken.Promising.SLR.EnvG.X64MpInclAbsConcrete
import Kraken.Promising.SLR.EnvG.X64DeclsLink
import Kraken.Promising.SLR.EnvG.X64RunnerCommon

namespace Kraken.Promising.X64.EnvG.MpInclAbs

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Mp Kraken.Promising.X64.EnvG.MpSmoke
open Kraken.Promising.X64.EnvG.MpLink Kraken.Promising.X64.EnvG.MpRelPure Kraken.Promising.X64.EnvG.MpPublic
open Kraken.Promising.X64.EnvG.MpInc Kraken.Promising.X64.EnvG.MpIncV

variable [layout : _root_.Layout] [Executable.ValidLayout (layout mpInclImageV)]

/-! ## The rules and the start, with declarations -/

/-- **The verbatim writer's rule on `EnvGLRV` with strict sized declarations
`ds`** (`mpInclRuleWM` through `ofSafelyEnvGLRVXMD`). -/
def mpInclRuleWMD {ds : Decls} (hsz : ds.Sized) (P : Params) (hL : MpLocs P) (tid rd : Nat) :
    ThreadRuleRX (I := isa) Arch.tso (MpPostF P rd) tid :=
  ThreadRuleRX.ofSafelyEnvGLRVXMD (S := mpS P) (post := postWM P) hsz mpInclImageW_mask (mpIncPlan_valid hL)
    (mpIncPlan_whole P) (mpS_le16 P) mpInclImageW_lr (postWM_end P) (writerW_stuck _) (hB_WM P tid rd)

/-- **The verbatim reader's rule on `EnvG` with strict sized declarations
`ds`** (`mpInclRuleRM` through `ofSafelyEnvGXMD`). -/
def mpInclRuleRMD {ds : Decls} (hsz : ds.Sized) (P : Params) (hL : MpLocs P) (tid : Nat) :
    ThreadRuleRX (I := isa) Arch.tso (MpPostF P tid) tid :=
  ThreadRuleRX.ofSafelyEnvGXMD (S := mpS P) (post := postRM P) hsz mpInclImageR_mask (mpPlan_valid hL) (mpS_le16 P)
    mpInclImageR_phase1 (postRM_end P) (readerR_stuck _) (hB_RM P tid)

/-- **The verbatim writer at its start with declarations `ds`** (`StartWM`
with `decls = ds`). -/
structure StartWMD (ds : Decls) (s : State) : Prop where
  exe : s.exe = layout mpInclImageV
  decls : s.decls = ds
  pc : s.st.2 = labM "writer"
  endPc : s.endPc = labM "wdone"
  rdi : s.st.1.regs.get64 .rdi = symM "f"
  rsi : s.st.1.regs.get64 .rsi = symM "d"
  split : Split [(symM "f", 4), (symM "d", 4)] s.st.1.dmem

/-- **The verbatim reader at its start with declarations `ds`** (`StartRM`
with `decls = ds`). -/
structure StartRMD (ds : Decls) (s : State) : Prop where
  exe : s.exe = layout mpInclImageV
  decls : s.decls = ds
  pc : s.st.2 = labM "reader"
  endPc : s.endPc = labM "rdone"
  rdi : s.st.1.regs.get64 .rdi = symM "f"
  rsi : s.st.1.regs.get64 .rsi = symM "d"
  split : Split [(symM "f", 4), (symM "d", 4)] s.st.1.dmem

section Start

variable {ds : Decls} {sW sR : isa.State} {initMem : List (Loc × Val)}

/-- **The verbatim writer's initial invariant with declarations.** -/
theorem invWM_initD (hsz : ds.Sized) (hfd : symM "f" ≠ symM "d") (hW : StartWMD ds sW)
    (hF0 : (Config.init [sW, sR] initMem).mem.initVal ⟨symM "f", 4⟩ = 0) :
    (mpInclRuleWMD hsz (ghostParams (symM "f") (symM "d")) (ghostParams_mpLocs hfd) 0 1).Inv True
      (Config.init [sW, sR] initMem)
      (mpRes (Config.init [sW, sR] initMem).mem (ghostParams (symM "f") (symM "d")) 0)
      (mpGhostI (ghostParams (symM "f") (symM "d"))) := by
  have hL := ghostParams_mpLocs hfd
  have hst : sW.st = (sW.st.1, labM "writer") := Prod.ext rfl hW.pc
  refine invGLRVXMD_init (s := sW) rfl rfl ⟨hW.exe, hW.decls, hW.endPc, hW.split, ?_⟩
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

/-- **The verbatim reader's initial invariant with declarations.** -/
theorem invRM_initD (hsz : ds.Sized) (hfd : symM "f" ≠ symM "d") (hR : StartRMD ds sR) :
    (mpInclRuleRMD hsz (ghostParams (symM "f") (symM "d")) (ghostParams_mpLocs hfd) 1).Inv True
      (Config.init [sW, sR] initMem)
      (mpRes (Config.init [sW, sR] initMem).mem (ghostParams (symM "f") (symM "d")) 1)
      (mpGhostI (ghostParams (symM "f") (symM "d"))) := by
  have hst : sR.st = (sR.st.1, labM "reader") := Prod.ext rfl hR.pc
  refine invGXMD_init (s := sR) rfl rfl ⟨hR.exe, hR.decls, hR.endPc, hR.split, ?_⟩
  rw [hst]
  refine Safely.uncountM (readerR_envG _ 1 sR.st.1 (σInitX (Config.init [sW, sR] initMem)
    (mpRes (Config.init [sW, sR] initMem).mem (ghostParams (symM "f") (symM "d")) 1)
    (mpGhostI (ghostParams (symM "f") (symM "d"))), 0)
    ⟨⟨hR.rdi, hR.rsi, split_df hR.split, split_dd hR.split⟩, ⟨mpGhostI_rel_Fl, 0, Nat.zero_lt_one, rfl, ?_⟩, ?_⟩)
  · simp [σInitX, mpRes, readerRes]
  · simp [σInitX, Views.getFwd]

/-- **The `NPSafe` side** for the verbatim threads with declarations. -/
theorem mpInclV_npSafeD (hsz : ds.Sized) (hfd : symM "f" ≠ symM "d") (hW : StartWMD ds sW) (hR : StartRMD ds sR)
    (hF0 : (Config.init [sW, sR] initMem).mem.initVal ⟨symM "f", 4⟩ = 0) :
    ∀ tid, tid < [sW, sR].length → ∀ n m,
      NPSafe (model isa) Arch.tso (MpPostF (ghostParams (symM "f") (symM "d")) 1) tid n m True
        (Config.init [sW, sR] initMem) (mpRes (Config.init [sW, sR] initMem).mem (ghostParams (symM "f") (symM "d")) tid)
        (mpGhostI (ghostParams (symM "f") (symM "d"))) := by
  intro tid htid n m
  rcases tid with _ | _ | k
  · exact NPSafe.of_ruleRX _ n m _ _ _ _ (invWM_initD hsz hfd hW hF0)
  · exact NPSafe.of_ruleRX _ n m _ _ _ _ (invRM_initD hsz hfd hR)
  · simp only [List.length_cons, List.length_nil] at htid; omega

end Start

/-- **The all-release specifications hold at the start states with
declarations.** -/
theorem mpInclNoNTSpecV_initD {ds : Decls} {sW sR : State} (hW : StartWMD ds sW) (hR : StartRMD ds sR) :
    ∀ tid s, [sW, sR][tid]? = some s → (mpInclNoNTSpecV tid).HoldsD ds s
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
release, `mp_incl.kl`'s code verbatim, with the runner's declarations**:
`x64_mp_incl_envGV_verbatim` for threads whose declarations are strict sized
(`ds.Sized`: the `.kl` runner's, from the typed header). -/
theorem x64_mp_incl_envGV_runner {fuel : Nat} {ds : Decls} (hsz : ds.Sized) (hfd : symM "f" ≠ symM "d")
    {sW sR : isa.State} {initMem : List (Loc × Val)} (hW : StartWMD ds sW) (hR : StartRMD ds sR)
    (hF0 : (Config.init [sW, sR] initMem).mem.initVal ⟨symM "f", 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [sW, sR] initMem) cfg)
    (hf : cfg.final = true) :
    (∃ t, cfg.threads[1]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 42) ∧
      cfg.mem.finalVal ⟨symM "d", 4⟩ = 42#128 ∧ cfg.mem.finalVal ⟨symM "f", 4⟩ = 1#128 :=
  final_of_relPureSafelyQX_tsoD fuel (B := MpPostF (ghostParams (symM "f") (symM "d")) 1)
    (Φ := fun c => (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 42) ∧
      c.mem.finalVal ⟨symM "d", 4⟩ = 42#128 ∧ c.mem.finalVal ⟨symM "f", 4⟩ = 1#128)
    (erase_mpIncInit _ _ hF0) pend_mpGhostI mpInclNoNTSpecV (fun _ => ds) (fun _ => hsz)
    (mpInclNoNTSpecV_initD hW hR) (mpInclV_npSafeD hsz hfd hW hR hF0) hc hf
    fun _ _ E' hle hsize hB =>
      have hrel : _ := by rw [hle.rel]; exact mpGhostI_rel_Fl
      have h := mp_finalI E' hf hsize hrel fun tid hd => (hB tid hd).toI
      ⟨h.1, h.2, flag_finalF E' hf hsize hrel hB⟩

end Kraken.Promising.X64.EnvG.MpInclAbs

/-! ## The runner's configuration -/

namespace Kraken.Promising.X64.EnvG.MpInclAbs.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.MpInclAbs Kraken.Promising.SLR.EnvG

/-- The runner's declarations for the typed `mp_incl.kl`: `d` and `f`, 4-byte
words (strict). -/
def mpInclDeclsD : Decls := { locs := [⟨0x1000000, 4⟩, ⟨0x1000100, 4⟩], unsizedDefault := false }

theorem mpInclDeclsD_sized : mpInclDeclsD.Sized := ⟨rfl, by decide⟩

/-- The threads as the runner prepares them, declarations included. -/
def mpInclW0D : X64.State := { mpInclW0 with decls := mpInclDeclsD }
def mpInclR1D : X64.State := { mpInclR1 with decls := mpInclDeclsD }

/-- The runner's configuration is `Config.init [mpInclW0D, mpInclR1D]
mpInclInitMemV` in everything the theorem reads (declarations and initial
memory included). -/
def runnerMatchesD (src : String) : Bool :=
  runnerMatchesDL src [mpInclW0D, mpInclR1D] mpInclInitMemV

/-- info: true -/
#guard_msgs in
#eval runnerMatchesD mpInclKl

section
attribute [local instance] mpInclLayoutV

theorem mpInclW0D_start : StartWMD mpInclDeclsD mpInclW0D :=
  ⟨rfl, rfl, by show (0x100000 : Int64) = labM "writer"; rw [labM_at 0]; decide,
    by show (0x100000 + 3 : Int64) = labM "wdone"; rw [labM_at 4]; decide,
    by rw [symM_f]; simp [mpInclW0D, mpInclW0, mpInclThreadV, Reg64s.get64, Reg64s.set64],
    by rw [symM_d]; simp [mpInclW0D, mpInclW0, mpInclThreadV, Reg64s.get64, Reg64s.set64], Split.empty _⟩

theorem mpInclR1D_start : StartRMD mpInclDeclsD mpInclR1D :=
  ⟨rfl, rfl, by show (0x100000 + 4 : Int64) = labM "reader"; rw [labM_at 6]; decide,
    by show (0x100000 + 9 : Int64) = labM "rdone"; rw [labM_at 12]; decide,
    by rw [symM_f]; simp [mpInclR1D, mpInclR1, mpInclThreadV, Reg64s.get64, Reg64s.set64],
    by rw [symM_d]; simp [mpInclR1D, mpInclR1, mpInclThreadV, Reg64s.get64, Reg64s.set64], Split.empty _⟩

end

/-- **`mp_incl.kl`'s code verbatim, from the runner's exact configuration**:
every final configuration under `Arch.tso` has the reader's `ebx = 42`,
`[d] = 42` and `[f] = 1`. -/
theorem x64_mp_incl_envGV_runner_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [mpInclW0D, mpInclR1D] mpInclInitMemV) c)
    (hf : c.final = true) :
    (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 42) ∧
      c.mem.finalVal ⟨0x1000000, 4⟩ = 42#128 ∧ c.mem.finalVal ⟨0x1000100, 4⟩ = 1#128 := by
  have h := x64_mp_incl_envGV_runner (layout := mpInclLayoutV) mpInclDeclsD_sized (by rw [symM_f, symM_d]; decide)
    mpInclW0D_start mpInclR1D_start (by rw [symM_f]; simp only [Config.init_mem]; decide) hc hf
  rwa [symM_d, symM_f] at h

end Kraken.Promising.X64.EnvG.MpInclAbs.Concrete

#print axioms Kraken.Promising.X64.EnvG.MpInclAbs.x64_mp_incl_envGV_runner
#print axioms Kraken.Promising.X64.EnvG.MpInclAbs.Concrete.x64_mp_incl_envGV_runner_concrete
