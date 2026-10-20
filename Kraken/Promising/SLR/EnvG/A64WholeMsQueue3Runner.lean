/-
**`msqueue3.kl` for AArch64 from the runner's exact configuration**
`msqueue3_envG_runner`, `msqueue3_envG_whole` for
threads that carry the `.kl` runner's declarations (the typed header
`uint64_t head, tail; uint32_t d, n1, n2`: strict sized,
`Decls.StrictSized`), and its concrete instance
`msqueue3_envG_runner_concrete` (`runnerMatchesDQ3`: declarations and
initial memory included).

The proof is `A64WholeMsQueue3`'s with the D forms of
`EnvG/A64DeclsLink.lean` (`ThreadRuleRXF.ofSafelyEnvGFCAdjMD`,
`invGFCAdjMD_init`, `RelPureSpec.HoldsD`, `final_of_relPureSafelyFD`); the
start states are the verbatim `StartEQ3`/`StartDQ3` with declarations
(`A64Whole.WithDeclsD`). The old theorems are unchanged. Faults are not
covered (see `EnvG/A64DeclsBridge.lean`).
-/
import Kraken.Promising.SLR.EnvG.A64WholeMsQueue3Concrete
import Kraken.Promising.SLR.EnvG.A64DeclsRunner

namespace Kraken.Promising.SLR.EnvG.MsQueue

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)

/-! ## The rules and the start, with declarations -/

section Rules

variable [layout : _root_.Layout] [Executable.ValidLayout (layout msq3Image)]

omit [Executable.ValidLayout (layout msq3Image)] in
/-- The image has no `LDXP`/`STXP`. -/
theorem msq3Image_noPairs : Kraken.Executable.noPairs (layout msq3Image) = true := by
  rw [Layout.apply_noPairs]; decide

/-- **The whole-image enqueuer's rule with strict sized declarations
`ds`** (`enqRuleQ3` through `ofSafelyEnvGFCAdjMD`). -/
noncomputable def enqRuleQ3_decls {ds : Decls} (hsz : ds.StrictSized) (P : Params2) :
    ThreadRuleRXF (I := isa) Arch.armv8 (MB3 P) 0 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdjMD (post := postEQ3 P) hsz msq3Image_noPairs (maskOf_layout _ _)
    (planE2_valid P) msq3Image_rmwLive (phase1TreeF_maskKeep_range msq3Image_dirs)
    (fun _ ⟨_, h⟩ => h.elim And.left False.elim) (enqQ3_stuck _) (hB_EQ3 P)

/-- **The whole-image first dequeuer's rule with declarations.** -/
noncomputable def deqARuleQ3_decls {ds : Decls} (hsz : ds.StrictSized) (P : Params2) :
    ThreadRuleRXF (I := isa) Arch.armv8 (MB3 P) 1 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdjMD (post := postDAQ3 P) hsz msq3Image_noPairs (maskOf_layout _ _)
    (planD2_valid P) msq3Image_rmwLive (phase1TreeF_maskKeep_range msq3Image_dirs)
    (fun _ ⟨_, h⟩ => h.elim And.left False.elim) (deqAQ3_stuck _) (hB_DAQ3 P)

/-- **The whole-image second dequeuer's rule with declarations.** -/
noncomputable def deqBRuleQ3_decls {ds : Decls} (hsz : ds.StrictSized) (P : Params2) :
    ThreadRuleRXF (I := isa) Arch.armv8 (MB3 P) 2 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdjMD (post := postDBQ3 P) hsz msq3Image_noPairs (maskOf_layout _ _)
    (planD2_valid P) msq3Image_rmwLive (phase1TreeF_maskKeep_range msq3Image_dirs)
    (fun _ ⟨_, h⟩ => h.elim And.left False.elim) (deqBQ3_stuck _) (hB_DBQ3 P)

end Rules

section Start

variable [layout : _root_.Layout] [Executable.ValidLayout (layout msq3Image)] {ds : Decls}
  {s0 s1 s2 : isa.State} {initMem : List (Loc × Val)}

theorem invEQ3_init_decls (hsz : ds.StrictSized) {P : Params2} (hL : QLocs2 P)
    (hS : WithDeclsD ds (StartEQ3 P.t P.n1 P.n2) s0) :
    (enqRuleQ3_decls hsz P).Inv True (Config.init [s0, s1, s2] initMem)
      (tRes3 (Config.init [s0, s1, s2] initMem).mem P 0) (ghost2 P) := by
  obtain ⟨hds, hS⟩ := hS
  refine invGFCAdjMD_init (s := s0) rfl rfl (QA64MD.of_noDecls hds ⟨hS.exe, hS.decls, hS.endPc, ?_⟩)
  rw [show s0.noDecls.st = (s0.st.1, labQ3 "enq1") from Prod.ext rfl (hS.pc.trans labQ3_enq)]
  exact Safely.uncountA (enqQ3_envGCAdj P hL _ (_, 0)
    ⟨hS.x1, hS.d8, hS.d4, hS.x13, .inl ⟨rfl, hS.x12, start1_init3 hL _⟩⟩)

theorem invDAQ3_init_decls (hsz : ds.StrictSized) {P : Params2} (hL : QLocs2 P)
    (hS : WithDeclsD ds (StartDQ3 "deq1" "ddone1" P.h P.t) s1)
    (hi : InitV2 (Config.init [s0, s1, s2] initMem).mem P) :
    (deqARuleQ3_decls hsz P).Inv True (Config.init [s0, s1, s2] initMem)
      (tRes3 (Config.init [s0, s1, s2] initMem).mem P 1) (ghost2 P) := by
  obtain ⟨hds, hS⟩ := hS
  refine invGFCAdjMD_init (s := s1) rfl rfl (QA64MD.of_noDecls hds ⟨hS.exe, hS.decls, hS.endPc, ?_⟩)
  rw [show s1.noDecls.st = (s1.st.1, labQ3 "deq1a") from Prod.ext rfl (hS.pc.trans labQ3_deq1)]
  exact Safely.uncountA (deqAQ3_envGCAdj P hL _ (_, 0)
    ⟨hS.x0, hS.x1, hS.d8, hS.d4, .inl ⟨rfl, comDa3_init P _ hi⟩⟩)

theorem invDBQ3_init_decls (hsz : ds.StrictSized) {P : Params2} (hL : QLocs2 P)
    (hS : WithDeclsD ds (StartDQ3 "deq2" "ddone2" P.h P.t) s2)
    (hi : InitV2 (Config.init [s0, s1, s2] initMem).mem P) :
    (deqBRuleQ3_decls hsz P).Inv True (Config.init [s0, s1, s2] initMem)
      (tRes3 (Config.init [s0, s1, s2] initMem).mem P 2) (ghost2 P) := by
  obtain ⟨hds, hS⟩ := hS
  refine invGFCAdjMD_init (s := s2) rfl rfl (QA64MD.of_noDecls hds ⟨hS.exe, hS.decls, hS.endPc, ?_⟩)
  rw [show s2.noDecls.st = (s2.st.1, labQ3 "deq2a") from Prod.ext rfl (hS.pc.trans labQ3_deq2)]
  exact Safely.uncountA (deqBQ3_envGCAdj P hL _ (_, 0)
    ⟨hS.x0, hS.x1, hS.d8, hS.d4, .inl ⟨rfl, comDb3_init P _ hi⟩⟩)

end Start

/-- **The `NPSafeF` side with declarations.** -/
theorem msqueue3_whole_npSafeF_decls (l : _root_.Layout) [Executable.ValidLayout (l msq3Image)] {ds : Decls}
    (hsz : ds.StrictSized) {P : Params2} (hL : QLocs2 P) {s0 s1 s2 : isa.State} {initMem : List (Loc × Val)}
    (h0 : WithDeclsD ds (StartEQ3 (layout := l) P.t P.n1 P.n2) s0)
    (h1 : WithDeclsD ds (StartDQ3 (layout := l) "deq1" "ddone1" P.h P.t) s1)
    (h2 : WithDeclsD ds (StartDQ3 (layout := l) "deq2" "ddone2" P.h P.t) s2)
    (hi : InitV2 (Config.init [s0, s1, s2] initMem).mem P) :
    ∀ tid, tid < [s0, s1, s2].length → ∀ k j, NPSafeF (model isa) Arch.armv8 (MB3 P) tid k j True
      (Config.init [s0, s1, s2] initMem) (tRes3 (Config.init [s0, s1, s2] initMem).mem P tid) (ghost2 P) := by
  intro tid htid k j
  rcases tid with _ | _ | _ | i
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invEQ3_init_decls (layout := l) hsz hL h0)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invDAQ3_init_decls (layout := l) hsz hL h1 hi)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invDBQ3_init_decls (layout := l) hsz hL h2 hi)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- **The Michael–Scott queue with two competing dequeuers `msqueue3.kl` for
AArch64 under `Arch.armv8`, all three threads running the whole `.kl` image,
with the runner's declarations**: `msqueue3_envG_whole` for threads whose
declarations are strict sized (`ds.StrictSized`: the `.kl` runner's, from
the typed header) and which otherwise start as there (`StartEQ3`/`StartDQ3`
of the thread with its declarations dropped). -/
theorem msqueue3_envG_runner {fuel : Nat} (l : _root_.Layout) [Executable.ValidLayout (l msq3Image)]
    {ds : Decls} (hsz : ds.StrictSized) (h t d n1 n2 : BitVec 64)
    (hht : h ≠ t) (hhd : h ≠ d + 8) (hhn : h ≠ n1 + 8) (hhn2 : h ≠ n2 + 8) (htd : t ≠ d + 8)
    (htn : t ≠ n1 + 8) (htn2 : t ≠ n2 + 8) (hdn : d ≠ n1) (hdn2 : d ≠ n2) (hn12 : n1 ≠ n2) (hn1 : n1 ≠ 0)
    (hn2 : n2 ≠ 0) {s0 s1 s2 : isa.State} {initMem : List (Loc × Val)}
    (h0 : WithDeclsD ds (StartEQ3 (layout := l) t n1 n2) s0)
    (h1 : WithDeclsD ds (StartDQ3 (layout := l) "deq1" "ddone1" h t) s1)
    (h2 : WithDeclsD ds (StartDQ3 (layout := l) "deq2" "ddone2" h t) s2)
    (hi : InitV2 (Config.init [s0, s1, s2] initMem).mem ⟨⟨h, t, d, n1⟩, n2⟩)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1, s2] initMem) cfg)
    (hf : cfg.final = true) :
    ∃ th1 th2, cfg.threads[1]? = some th1 ∧ cfg.threads[2]? = some th2 ∧
      ((th1.st.st.1.regs.X10.toBitVec = 1 ∧ th2.st.st.1.regs.X10.toBitVec = 2) ∨
        (th1.st.st.1.regs.X10.toBitVec = 2 ∧ th2.st.st.1.regs.X10.toBitVec = 1)) := by
  have hL : QLocs2 ⟨⟨h, t, d, n1⟩, n2⟩ := ⟨⟨hht, hhd, hhn, htd, htn, hdn⟩, hhn2, htn2, hdn2, hn12, hn1, hn2⟩
  refine final_of_relPureSafelyFD Arch.armv8 fuel (B := MB3 ⟨⟨h, t, d, n1⟩, n2⟩) (Φ := MsQueue3Final)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_init3 hL _) (ghost2_pend _) (msq3PureSpecW l _)
    (fun _ => ds) (fun _ => hsz)
    (fun tid => by rcases tid with _ | _ | _ <;> exact msq3Image_noPairs (layout := l))
    (RelPureSpec.holdsD_init (ss := [s0, s1, s2]) (List.forall_mem_cons.2 ⟨h0.1,
      List.forall_mem_cons.2 ⟨h1.1, List.forall_mem_cons.2 ⟨h2.1, fun _ h => nomatch h⟩⟩⟩)
      (msq3PureSpecW_init l (fun v => ?_) (fun v => ?_) h0.2 h1.2 h2.2))
    (msqueue3_whole_npSafeF_decls l hsz hL h0 h1 h2 hi) hc hf fun rF' g' E' hle hsize hB => ?_
  · show Pred.Pure ((ghost2 ⟨⟨h, t, d, n1⟩, n2⟩).rel (Params.dat ⟨h, t, d, n1⟩)) v
    rw [ghost2_rel_ne (not_isW_dat _)]; exact Pred.emp_pure v
  · show Pred.Pure ((ghost2 ⟨⟨h, t, d, n1⟩, n2⟩).rel (Params2.dat2 ⟨⟨h, t, d, n1⟩, n2⟩)) v
    rw [ghost2_rel_ne (not_isW_dat2 _)]; exact Pred.emp_pure v
  exact msqueue3_final_of_hB hL hf E' hle hsize hB

/-! ## The runner's configuration -/

/-- The runner's declarations for the typed `msqueue3.kl`: `head`, `tail`
8-byte words, `d`, `n1`, `n2` 4-byte words (strict). -/
def msq3DeclsD : Decls :=
  { locs := [⟨0x1000, 8⟩, ⟨0x1200, 8⟩, ⟨0x1100, 4⟩, ⟨0x1300, 4⟩, ⟨0x1400, 4⟩], unsizedDefault := false }

theorem msq3DeclsD_sized : msq3DeclsD.StrictSized := ⟨rfl, by decide⟩

/-- The runner's initial memory for the typed `msqueue3.kl`: `head = tail =
d`, the data words `0` (the links at `n + 8` are undeclared, initially
`0`). -/
def msq3InitMemD : List (Loc × Val) :=
  [(⟨0x1000, 8⟩, 0x1100), (⟨0x1200, 8⟩, 0x1100), (⟨0x1100, 4⟩, 0), (⟨0x1300, 4⟩, 0), (⟨0x1400, 4⟩, 0)]

/-- The threads as the runner prepares them, declarations included. -/
def enqDQ3 : AArch64.State := { enqWQ3 with decls := msq3DeclsD }
def deqADQ3 : AArch64.State := { deqAWQ3 with decls := msq3DeclsD }
def deqBDQ3 : AArch64.State := { deqBWQ3 with decls := msq3DeclsD }

/-- The runner's configuration is `Config.init [enqDQ3, deqADQ3, deqBDQ3]
msq3InitMemD` in everything the theorem reads (declarations and initial
memory included). -/
def runnerMatchesDQ3 (src : String) : Bool := A64Whole.runnerIsD src [enqDQ3, deqADQ3, deqBDQ3] msq3InitMemD

/-- info: true -/
#guard_msgs in
#eval runnerMatchesDQ3 msqueue3KlW

/-- **`(1:X10 = 1 ∧ 2:X10 = 2) ∨ (1:X10 = 2 ∧ 2:X10 = 1)`** for
`msqueue3.kl` under `Arch.armv8`, from the runner's exact configuration (the
whole `code` block at `0x100000`, the typed header's declarations and
initial memory): concrete instance of `msqueue3_envG_runner`. -/
theorem msqueue3_envG_runner_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [enqDQ3, deqADQ3, deqBDQ3] msq3InitMemD) c)
    (hf : c.final = true) :
    ∃ th1 th2, c.threads[1]? = some th1 ∧ c.threads[2]? = some th2 ∧
      ((th1.st.st.1.regs.X10.toBitVec = 1 ∧ th2.st.st.1.regs.X10.toBitVec = 2) ∨
        (th1.st.st.1.regs.X10.toBitVec = 2 ∧ th2.st.st.1.regs.X10.toBitVec = 1)) :=
  msqueue3_envG_runner wLayoutQ3 msq3DeclsD_sized 0x1000 0x1200 0x1100 0x1300 0x1400 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (withDeclsD_of rfl enqWQ3_start) (withDeclsD_of rfl deqAWQ3_start)
    (withDeclsD_of rfl deqBWQ3_start)
    (by refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp only [Config.init] <;> decide) hc hf

end Kraken.Promising.SLR.EnvG.MsQueue

#print axioms Kraken.Promising.SLR.EnvG.MsQueue.msqueue3_envG_runner
#print axioms Kraken.Promising.SLR.EnvG.MsQueue.msqueue3_envG_runner_concrete
