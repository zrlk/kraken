/-
**`spsc_queue.kl` from the runner's exact configuration**: `x64_spsc_envG_runner`, `x64_spsc_envG_verbatim` for threads that
carry the `.kl` runner's declarations (the header types `buf0`, `buf1`,
`head`, `tail` `uint32_t`: strict sized, `Decls.Sized`), and its concrete
instance `x64_spsc_envG_runner_concrete` (`runnerMatchesD`: declarations
and initial memory included).

The proof is `X64SpscAbsPublic`'s with the D forms of
`EnvG/X64DeclsLink.lean`: both threads on the take route over their masks
(`ThreadRuleRXGS.ofSafelyEnvGTXMD`), `invGTXMD_init`,
`RelPureSpecQX.HoldsD`, `final_of_relPureSafelyQX_tsoSD`. The old theorems
are unchanged.
-/
import Kraken.Promising.SLR.EnvG.X64SpscAbsPublic
import Kraken.Promising.SLR.EnvG.X64SpscAbsConcrete
import Kraken.Promising.SLR.EnvG.X64DeclsLink
import Kraken.Promising.SLR.EnvG.X64RunnerCommon

namespace Kraken.Promising.X64.EnvG.SpscAbs

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.SpscX Kraken.Promising.X64.EnvG.TreiberX

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spscImageV)]

/-! ## The rules and the start, with declarations -/

/-- **The verbatim producer's rule with strict sized declarations `ds`**
(`prodRuleA` through `ofSafelyEnvGTXMD`). -/
def prodRuleAD {ds : Decls} (hsz : ds.Sized) (P : SP) (hL : SpscLocs P) (tid : Nat) :
    ThreadRuleRXGS (I := isa) G₀ Arch.tso (SpscPost P) tid :=
  ThreadRuleRXGS.ofSafelyEnvGTXMD (S := spscS P) (post := postPA P) hsz spscImageP_mask (prodPlan_valid hL)
    (spscS_le16 P) spscImageP_phase1 (postPA_end P) (prodP_stuck _) (hB_PA P tid)

/-- **The verbatim consumer's rule with strict sized declarations `ds`**
(`consRuleA` through `ofSafelyEnvGTXMD`). -/
def consRuleAD {ds : Decls} (hsz : ds.Sized) (P : SP) (hL : SpscLocs P) :
    ThreadRuleRXGS (I := isa) G₀ Arch.tso (SpscPost P) 1 :=
  ThreadRuleRXGS.ofSafelyEnvGTXMD (S := spscS P) (post := postCA) hsz spscImageC_mask (consPlan_valid hL)
    (spscS_le16 P) spscImageC_phase1 postCA_end (consC_stuck _) (hB_CA P)

/-- **The verbatim producer at its start with declarations `ds`** (`StartPV`
with `decls = ds`). -/
structure StartPVD (ds : Decls) (s : State) : Prop where
  exe : s.exe = layout spscImageV
  decls : s.decls = ds
  pc : s.st.2 = labS "producer"
  endPc : s.endPc = labS "pdone"
  rbx : s.st.1.regs.get64 .rbx = symS "buf0"
  dmem : ∀ k, s.st.1.dmem.get? k = none

/-- **The verbatim consumer at its start with declarations `ds`** (`StartCV`
with `decls = ds`). -/
structure StartCVD (ds : Decls) (s : State) : Prop where
  exe : s.exe = layout spscImageV
  decls : s.decls = ds
  pc : s.st.2 = labS "consumer"
  endPc : s.endPc = labS "cdone"
  rbx : s.st.1.regs.get64 .rbx = symS "buf0"
  dmem : ∀ k, s.st.1.dmem.get? k = none

section Start

variable {ds : Decls} {sP sC : isa.State} {initMem : List (Loc × Val)}

/-- **The verbatim producer's initial invariant with declarations.** -/
theorem invPA_initD (hsz : ds.Sized) (hL : SpscLocs spscP) (hP : StartPVD ds sP)
    (hT0 : (Config.init [sP, sC] initMem).mem.initVal ⟨symS "tail", 4⟩ = 0)
    (hH0 : (Config.init [sP, sC] initMem).mem.initVal ⟨symS "head", 4⟩ = 0) :
    (prodRuleAD hsz spscP hL 0).Inv True (Config.init [sP, sC] initMem)
      (spscRes (Config.init [sP, sC] initMem).mem spscP 0) (spscGhost spscP) := by
  have hst : sP.st = (sP.st.1, labS "producer") := Prod.ext rfl hP.pc
  refine invGTXMD_init (s := sP) rfl rfl ⟨hP.exe, hP.decls, hP.endPc, split_of_empty hP.dmem, ?_⟩
  rw [hst]
  exact Safely.uncountS (spscProducerP_envGT spscP hL 0 rfl rfl sP.st.1
    (σInitX (Config.init [sP, sC] initMem) (spscRes (Config.init [sP, sC] initMem).mem spscP 0) (spscGhost spscP), 0)
    ⟨⟨hP.rbx, dFrame_of_empty hP.dmem⟩, PR_init hL hT0 hH0⟩)

/-- **The verbatim consumer's initial invariant with declarations.** -/
theorem invCA_initD (hsz : ds.Sized) (hL : SpscLocs spscP) (hC : StartCVD ds sC)
    (hT0 : (Config.init [sP, sC] initMem).mem.initVal ⟨symS "tail", 4⟩ = 0)
    (hH0 : (Config.init [sP, sC] initMem).mem.initVal ⟨symS "head", 4⟩ = 0) :
    (consRuleAD hsz spscP hL).Inv True (Config.init [sP, sC] initMem)
      (spscRes (Config.init [sP, sC] initMem).mem spscP 1) (spscGhost spscP) := by
  have hst : sC.st = (sC.st.1, labS "consumer") := Prod.ext rfl hC.pc
  refine invGTXMD_init (s := sC) rfl rfl ⟨hC.exe, hC.decls, hC.endPc, split_of_empty hC.dmem, ?_⟩
  rw [hst]
  exact Safely.uncountS (spscConsumerC_envGT spscP hL 1 rfl rfl sC.st.1
    (σInitX (Config.init [sP, sC] initMem) (spscRes (Config.init [sP, sC] initMem).mem spscP 1) (spscGhost spscP), 0)
    ⟨⟨hC.rbx, dFrame_of_empty hC.dmem⟩, CS_init hL hT0 hH0⟩)

/-- **The `NPSafeP` side** for the verbatim threads with declarations. -/
theorem spscV_npSafeD (hsz : ds.Sized) (hL : SpscLocs spscP) (hP : StartPVD ds sP) (hC : StartCVD ds sC)
    (hT0 : (Config.init [sP, sC] initMem).mem.initVal ⟨symS "tail", 4⟩ = 0)
    (hH0 : (Config.init [sP, sC] initMem).mem.initVal ⟨symS "head", 4⟩ = 0) :
    ∀ tid, tid < [sP, sC].length → ∀ n m, NPSafeP (model isa) Arch.tso (SpscPost spscP) tid G₀
      (K2Scope (model isa) AllocIds) n m True (Config.init [sP, sC] initMem)
      (spscRes (Config.init [sP, sC] initMem).mem spscP tid) (spscGhost spscP) := by
  intro tid htid n m
  rcases tid with _ | _ | k
  · exact NPSafeP.of_ruleRXGS (prodRuleAD hsz spscP hL 0) n m _ _ _ _ (invPA_initD hsz hL hP hT0 hH0)
  · exact NPSafeP.of_ruleRXGS (consRuleAD hsz spscP hL) n m _ _ _ _ (invCA_initD hsz hL hC hT0 hH0)
  · simp only [List.length_cons, List.length_nil] at htid; omega

end Start

/-- **The all-release specifications hold at the start states with
declarations.** -/
theorem spscNoNTSpecV_initD {ds : Decls} {sP sC : State} (hP : StartPVD ds sP) (hC : StartCVD ds sC) :
    ∀ tid s, [sP, sC][tid]? = some s → (spscNoNTSpecV tid).HoldsD ds s
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

/-- **The x64 SPSC queue under `Arch.tso`, `spsc_queue.kl`'s code verbatim,
with the runner's declarations**: `x64_spsc_envG_verbatim` for threads whose
declarations are strict sized (`ds.Sized`: the `.kl` runner's, from the
typed header). -/
theorem x64_spsc_envG_runner {fuel : Nat} {ds : Decls} (hsz : ds.Sized) (hL : SpscLocs spscP)
    {sP sC : isa.State} {initMem : List (Loc × Val)} (hP : StartPVD ds sP) (hC : StartCVD ds sC)
    (hT0 : (Config.init [sP, sC] initMem).mem.initVal ⟨symS "tail", 4⟩ = 0)
    (hH0 : (Config.init [sP, sC] initMem).mem.initVal ⟨symS "head", 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [sP, sC] initMem) cfg)
    (hf : cfg.final = true) :
    ∃ th, cfg.threads[1]? = some th ∧ BitVec.setWidth 32 (th.st.st.1.regs.get64 .r12) = 1 ∧
      BitVec.setWidth 32 (th.st.st.1.regs.get64 .r13) = 2 ∧ BitVec.setWidth 32 (th.st.st.1.regs.get64 .r14) = 3 :=
  final_of_relPureSafelyQX_tsoSD fuel (B := SpscPost spscP) (Φ := ConsDone)
    (erase_spscInit hL _ hT0 hH0) pend_spscGhost spscNoNTSpecV (fun _ => ds) (fun _ => hsz)
    (spscNoNTSpecV_initD hP hC) (spscV_npSafeD hsz hL hP hC hT0 hH0) hc hf
    fun _ _ E' _ hsize hB => spsc_final E' hf hsize hB

end Kraken.Promising.X64.EnvG.SpscAbs

/-! ## The runner's configuration -/

namespace Kraken.Promising.X64.EnvG.SpscAbs.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.SpscAbs Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG.SpscX

/-- The runner's declarations for the typed `spsc_queue.kl`: `buf0`, `buf1`,
`head`, `tail`, 4-byte words (strict). -/
def spscDeclsD : Decls :=
  { locs := [⟨0x1000000, 4⟩, ⟨0x1000100, 4⟩, ⟨0x1000200, 4⟩, ⟨0x1000300, 4⟩], unsizedDefault := false }

theorem spscDeclsD_sized : spscDeclsD.Sized := ⟨rfl, by decide⟩

/-- The threads as the runner prepares them, declarations included. -/
def spscP0D : X64.State := { spscP0 with decls := spscDeclsD }
def spscC1D : X64.State := { spscC1 with decls := spscDeclsD }

/-- The runner's configuration is `Config.init [spscP0D, spscC1D] spscInitMemV`
in everything the theorem reads (declarations and initial memory included). -/
def runnerMatchesD (src : String) : Bool :=
  runnerMatchesDL src [spscP0D, spscC1D] spscInitMemV

/-- info: true -/
#guard_msgs in
#eval runnerMatchesD spscKl

section
attribute [local instance] spscLayoutV

set_option maxRecDepth 8192 in
theorem spscP0D_start : StartPVD spscDeclsD spscP0D :=
  ⟨rfl, rfl, by show (0x100000 : Int64) = labS "producer"; rw [labS_at 0]; decide,
    by show (0x100000 + 16 : Int64) = labS "pdone"; rw [labS_at 19]; decide,
    by rw [symS_buf0]; simp [spscP0D, spscP0, spscThreadV, Reg64s.get64, Reg64s.set64],
    fun _ => by simp [spscP0D, spscP0, spscThreadV]⟩

set_option maxRecDepth 8192 in
theorem spscC1D_start : StartCVD spscDeclsD spscC1D :=
  ⟨rfl, rfl, by show (0x100000 + 16 : Int64) = labS "consumer"; rw [labS_at 20]; decide,
    by show (0x100000 + 45 : Int64) = labS "cdone"; rw [labS_at 53]; decide,
    by rw [symS_buf0]; simp [spscC1D, spscC1, spscThreadV, Reg64s.get64, Reg64s.set64],
    fun _ => by simp [spscC1D, spscC1, spscThreadV]⟩

/-- **The SPSC queue, `spsc_queue.kl`'s code verbatim, from the runner's
exact configuration**: every final configuration under `Arch.tso` has the
consumer's `r12d = 1`, `r13d = 2`, `r14d = 3`. -/
theorem x64_spsc_envG_runner_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [spscP0D, spscC1D] spscInitMemV) c)
    (hf : c.final = true) :
    ∃ th, c.threads[1]? = some th ∧ BitVec.setWidth 32 (th.st.st.1.regs.get64 .r12) = 1 ∧
      BitVec.setWidth 32 (th.st.st.1.regs.get64 .r13) = 2 ∧ BitVec.setWidth 32 (th.st.st.1.regs.get64 .r14) = 3 :=
  x64_spsc_envG_runner (layout := spscLayoutV) spscDeclsD_sized
    (by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [symS_buf0, symS_head, symS_tail] <;> decide)
    spscP0D_start spscC1D_start
    (by rw [symS_tail]; simp only [Config.init_mem]; decide)
    (by rw [symS_head]; simp only [Config.init_mem]; decide) hc hf

end

end Kraken.Promising.X64.EnvG.SpscAbs.Concrete

#print axioms Kraken.Promising.X64.EnvG.SpscAbs.x64_spsc_envG_runner
#print axioms Kraken.Promising.X64.EnvG.SpscAbs.Concrete.x64_spsc_envG_runner_concrete
