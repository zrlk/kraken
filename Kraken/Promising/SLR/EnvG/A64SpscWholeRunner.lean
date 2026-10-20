/-
**`spsc_queue.kl` for AArch64 from the runner's exact configuration**
`a64_spsc_envG_runner`, `a64_spsc_envG_whole` for
threads that carry the `.kl` runner's declarations (the typed header
`uint32_t buf; uint64_t head, tail`: strict sized, `Decls.StrictSized`), and
its concrete instance `a64_spsc_envG_runner_concrete` (`runnerMatchesDS`:
declarations and initial memory included).

The proof is `A64SpscWholePublic`'s with the D forms of
`EnvG/A64DeclsLink.lean`: both threads through
`ThreadRuleRXGS.ofSafelyEnvGTUMD` (the producer over its mask
`spscImageP_mask`, the consumer unmasked, `MaskOf.refl`), `invGTUMD_init`,
`RelPureSpec.HoldsD`, `final_of_relPureSafelySD`. The start states are the
verbatim `StartPW`/`StartCW` with declarations (`A64Whole.WithDeclsD`). The
old theorems are unchanged. Faults are not covered (see
`EnvG/A64DeclsBridge.lean`); `prodRuleW_noFault`/`consRuleW_noFault` stay at
`decls = {}`.
-/
import Kraken.Promising.SLR.EnvG.A64SpscWholeConcrete
import Kraken.Promising.SLR.EnvG.A64DeclsRunner

namespace Kraken.Promising.SLR.EnvG.SpscA

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)

/-! ## The rules and the start, with declarations -/

section Inv

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spscImageA)] {P : SP} {sP sC : isa.State}
  {initMem : List (Loc × Val)} {ds : Decls}

omit [Executable.ValidLayout (layout spscImageA)] in
/-- The image has no `LDXP`/`STXP`. -/
theorem spscImageA_noPairs : Kraken.Executable.noPairs (layout spscImageA) = true := by
  rw [Layout.apply_noPairs]; decide

/-- **`NPSafeP` for the whole-image producer with strict sized declarations
`ds`** (thread `0`; `prodW_npSafeP` through `ofSafelyEnvGTUMD`). -/
theorem prodW_npSafeP_decls (hsz : ds.StrictSized) (hL : SpscLocs P) (hP : WithDeclsD ds (StartPW P) sP)
    (hH0 : (Config.init [sP, sC] initMem).mem.initVal P.H = 0) (n m : Nat) :
    NPSafeP (model isa) Arch.armv8 (SpscPost P) 0 G₀ (K2Scope (model isa) AllocIds) n m True
      (Config.init [sP, sC] initMem) (spscRes (Config.init [sP, sC] initMem).mem P 0) (spscGhost P) := by
  obtain ⟨hds, he, hds0, hpc, hend, hfr⟩ := hP
  refine NPSafeP.of_ruleRXGS (ThreadRuleRXGS.ofSafelyEnvGTUMD (post := postPW P) hsz spscImageA_noPairs
    spscImageP_mask (prodPlan_valid hL) spscImageA_rmwLive spscImageP_phase1 (postPW_end P) (prodP_stuck _)
    (hB_PW P 0)) n m _ _ _ _ (invGTUMD_init (s := sP) rfl rfl (QA64MD.of_noDecls hds ⟨he, hds0, hend, ?_⟩))
  rw [show sP.noDecls.st = (sP.noDecls.st.1, labA "prod") from Prod.ext rfl hpc]
  exact Safely.uncountA (spscProdW_envGTU P hL 0 _ (_, 0) ⟨hfr, PR_init hL hH0⟩)

/-- **`NPSafeP` for the whole-image consumer with declarations** (thread
`1`). -/
theorem consW_npSafeP_decls (hsz : ds.StrictSized) (hL : SpscLocs P) (hC : WithDeclsD ds (StartCW P) sC)
    (hT0 : (Config.init [sP, sC] initMem).mem.initVal P.T = 0) (n m : Nat) :
    NPSafeP (model isa) Arch.armv8 (SpscPost P) 1 G₀ (K2Scope (model isa) AllocIds) n m True
      (Config.init [sP, sC] initMem) (spscRes (Config.init [sP, sC] initMem).mem P 1) (spscGhost P) := by
  obtain ⟨hds, he, hds0, hpc, hend, hfr⟩ := hC
  refine NPSafeP.of_ruleRXGS (ThreadRuleRXGS.ofSafelyEnvGTUMD (post := postCW) hsz spscImageA_noPairs
    (MaskOf.refl _) (consPlan_valid hL) spscImageA_rmwLive spscImageA_phase1 postCW_end (consA_stuck _)
    (hB_CW P)) n m _ _ _ _ (invGTUMD_init (s := sC) rfl rfl (QA64MD.of_noDecls hds ⟨he, hds0, hend, ?_⟩))
  rw [show sC.noDecls.st = (sC.noDecls.st.1, labA "cons") from Prod.ext rfl hpc]
  exact Safely.uncountA (spscConsW_envGTU P hL 1 _ (_, 0) ⟨hfr, CE_init hL hT0⟩)

end Inv

/-- **The `NPSafeP` side with declarations**, whole image. -/
theorem a64_spsc_whole_npSafe_decls (l : _root_.Layout) [Executable.ValidLayout (l spscImageA)] {ds : Decls}
    (hsz : ds.StrictSized) {P : SP} (hL : SpscLocs P) {sP sC : isa.State} {initMem : List (Loc × Val)}
    (hP : WithDeclsD ds (StartPW (layout := l) P) sP) (hC : WithDeclsD ds (StartCW (layout := l) P) sC)
    (hT0 : (Config.init [sP, sC] initMem).mem.initVal P.T = 0)
    (hH0 : (Config.init [sP, sC] initMem).mem.initVal P.H = 0) :
    ∀ tid, tid < [sP, sC].length → ∀ n m, NPSafeP (model isa) Arch.armv8 (SpscPost P) tid G₀
      (K2Scope (model isa) AllocIds) n m True (Config.init [sP, sC] initMem)
      (spscRes (Config.init [sP, sC] initMem).mem P tid) (spscGhost P) := by
  intro tid htid n m
  rcases tid with _ | _ | k
  · exact prodW_npSafeP_decls (layout := l) hsz hL hP hH0 n m
  · exact consW_npSafeP_decls (layout := l) hsz hL hC hT0 n m
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- **The AArch64 SPSC ring `spsc_queue.kl` under `Arch.armv8`, both threads
running the whole `.kl` image, with the runner's declarations**:
`a64_spsc_envG_whole` for threads whose declarations are strict sized
(`ds.StrictSized`: the `.kl` runner's, from the typed header) and which
otherwise start as there (`StartPW`/`StartCW` of the thread with its
declarations dropped). -/
theorem a64_spsc_envG_runner {fuel : Nat} (l : _root_.Layout) [Executable.ValidLayout (l spscImageA)]
    {ds : Decls} (hsz : ds.StrictSized) (b h t : BitVec 64) (hL : SpscLocs ⟨b, h, t⟩) {sP sC : isa.State}
    {initMem : List (Loc × Val)} (hP : WithDeclsD ds (StartPW (layout := l) ⟨b, h, t⟩) sP)
    (hC : WithDeclsD ds (StartCW (layout := l) ⟨b, h, t⟩) sC)
    (hT0 : (Config.init [sP, sC] initMem).mem.initVal ⟨t, 8⟩ = 0)
    (hH0 : (Config.init [sP, sC] initMem).mem.initVal ⟨h, 8⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [sP, sC] initMem) cfg)
    (hf : cfg.final = true) :
    ∃ th, cfg.threads[1]? = some th ∧ BitVec.setWidth 32 th.st.st.1.regs.X10.toBitVec = 1 ∧
      BitVec.setWidth 32 th.st.st.1.regs.X11.toBitVec = 2 ∧ BitVec.setWidth 32 th.st.st.1.regs.X12.toBitVec = 3 :=
  final_of_relPureSafelySD Arch.armv8 fuel (B := SpscPost ⟨b, h, t⟩) (Φ := ConsDone)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_spscInit hL _ hT0 hH0) pend_spscGhost
    (spscPureSpecW l _) (fun _ => ds) (fun _ => hsz)
    (fun tid => by rcases tid with _ | _ <;> exact spscImageA_noPairs (layout := l))
    (RelPureSpec.holdsD_init (ss := [sP, sC])
      (List.forall_mem_cons.2 ⟨hP.1, List.forall_mem_cons.2 ⟨hC.1, fun _ h => nomatch h⟩⟩)
      (spscPureSpecW_init l hL hP.2 hC.2))
    (a64_spsc_whole_npSafe_decls l hsz hL hP hC hT0 hH0) hc hf
    fun _ _ E' _ hsize hB => spsc_final E' hf hsize hB

/-! ## The runner's configuration -/

/-- The runner's declarations for the typed `spsc_queue.kl`: `buf` a 4-byte
word, `head`, `tail` 8-byte words (strict). -/
def spscDeclsD : Decls := { locs := [⟨bufA, 4⟩, ⟨headA, 8⟩, ⟨tailA, 8⟩], unsizedDefault := false }

theorem spscDeclsD_sized : spscDeclsD.StrictSized := ⟨rfl, by decide⟩

/-- The runner's initial memory for the typed `spsc_queue.kl`: the three
declared words `0` (slot `1` at `buf + 8` is undeclared, initially `0`). -/
def spscInitMemD : List (Loc × Val) := [(⟨bufA, 4⟩, 0), (⟨headA, 8⟩, 0), (⟨tailA, 8⟩, 0)]

/-- The threads as the runner prepares them, declarations included. -/
def spscProdWD0 : AArch64.State := { spscProdW0 with decls := spscDeclsD }
def spscConsWD1 : AArch64.State := { spscConsW1 with decls := spscDeclsD }

/-- The runner's configuration is `Config.init [spscProdWD0, spscConsWD1]
spscInitMemD` in everything the theorem reads (declarations and initial
memory included). -/
def runnerMatchesDS (src : String) : Bool :=
  A64Whole.runnerIsD src [spscProdWD0, spscConsWD1] spscInitMemD

/-- info: true -/
#guard_msgs in
#eval runnerMatchesDS spscKl

/-- **`forall (1:X10=1 /\ 1:X11=2 /\ 1:X12=3)`** for `spsc_queue.kl` under
`Arch.armv8`, from the runner's exact configuration (the whole `code` block
at `0x100000`, the typed header's declarations and initial memory): concrete
instance of `a64_spsc_envG_runner`. -/
theorem a64_spsc_envG_runner_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [spscProdWD0, spscConsWD1] spscInitMemD) c)
    (hf : c.final = true) :
    ∃ th, c.threads[1]? = some th ∧ BitVec.setWidth 32 th.st.st.1.regs.X10.toBitVec = 1 ∧
      BitVec.setWidth 32 th.st.st.1.regs.X11.toBitVec = 2 ∧ BitVec.setWidth 32 th.st.st.1.regs.X12.toBitVec = 3 :=
  a64_spsc_envG_runner wLayoutA spscDeclsD_sized bufA headA tailA spscLocsA
    (withDeclsD_of rfl spscProdW0_start) (withDeclsD_of rfl spscConsW1_start)
    (by simp only [Config.init]; decide) (by simp only [Config.init]; decide) hc hf

end Kraken.Promising.SLR.EnvG.SpscA

#print axioms Kraken.Promising.SLR.EnvG.SpscA.a64_spsc_envG_runner
#print axioms Kraken.Promising.SLR.EnvG.SpscA.a64_spsc_envG_runner_concrete
