/-
**`msqueue1.kl` for AArch64 from the runner's exact configuration**
`msqueue1_envG_runner`, `msqueue1_envG_whole` for
threads that carry the `.kl` runner's declarations (the typed header
`uint64_t head, tail; uint32_t d, n1, n2`: strict sized,
`Decls.StrictSized`), and its concrete instance
`msqueue1_envG_runner_concrete` (`runnerMatchesDQ1`: declarations and
initial memory included).

The proof is `A64WholeMsQueue1`'s with the D forms of
`EnvG/A64DeclsLink.lean`: `enqRuleQ1_decls`/`deqRuleQ1_decls`
(`ThreadRuleRXF.ofSafelyEnvGFCAdjMD`), `invGFCAdjMD_init`,
`RelPureSpec.HoldsD`, `final_of_relPureSafelyFD`. The start states are the
verbatim `StartEQ1`/`StartDQ1` with declarations (`A64Whole.WithDeclsD`).
The old theorems are unchanged. Faults are not covered (see
`EnvG/A64DeclsBridge.lean`); `enqRuleQ1_noFault`/`deqRuleQ1_noFault` stay at
`decls = {}`.
-/
import Kraken.Promising.SLR.EnvG.A64WholeMsQueue1Concrete
import Kraken.Promising.SLR.EnvG.A64DeclsRunner

namespace Kraken.Promising.SLR.EnvG.MsQueue

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)

/-! ## The rules and the start, with declarations -/

section Rules

variable [layout : _root_.Layout] [Executable.ValidLayout (layout msq1Image)]

omit [Executable.ValidLayout (layout msq1Image)] in
/-- The image has no `LDXP`/`STXP`. -/
theorem msq1Image_noPairs : Kraken.Executable.noPairs (layout msq1Image) = true := by
  rw [Layout.apply_noPairs]; decide

/-- **The whole-image enqueuer's rule with strict sized declarations
`ds`** (`enqRuleQ1` through `ofSafelyEnvGFCAdjMD`). -/
noncomputable def enqRuleQ1_decls {ds : Decls} (hsz : ds.StrictSized) (P : Params) :
    ThreadRuleRXF (I := isa) Arch.armv8 (MB P) 0 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdjMD (post := postEQ1 P) hsz msq1Image_noPairs (maskOf_layout _ _) (planE_valid P)
    msq1Image_rmwLive (phase1TreeF_maskKeep_range msq1Image_dirs) (fun _ ⟨_, h⟩ => h.elim And.left False.elim)
    (enqQ1_stuck _) (hB_EQ1 P)

/-- **The whole-image dequeuer's rule with strict sized declarations
`ds`.** -/
noncomputable def deqRuleQ1_decls {ds : Decls} (hsz : ds.StrictSized) (P : Params) :
    ThreadRuleRXF (I := isa) Arch.armv8 (MB P) 1 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdjMD (post := postDQ1 P) hsz msq1Image_noPairs (maskOf_layout _ _) (planD_valid P)
    msq1Image_rmwLive (phase1TreeF_maskKeep_range msq1Image_dirs) (fun _ ⟨_, h⟩ => h.elim And.left False.elim)
    (deqQ1_stuck _) (hB_DQ1 P)

end Rules

section Start

variable [layout : _root_.Layout] [Executable.ValidLayout (layout msq1Image)] {ds : Decls} {s0 s1 : isa.State}
  {initMem : List (Loc × Val)}

theorem invEQ1_init_decls (hsz : ds.StrictSized) {P : Params} (hL : QLocs P)
    (hS : WithDeclsD ds (StartEQ1 P.t P.n1) s0) :
    (enqRuleQ1_decls hsz P).Inv True (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem P 0)
      (ghost₀ P) := by
  obtain ⟨hds, hS⟩ := hS
  refine invGFCAdjMD_init (s := s0) rfl rfl (QA64MD.of_noDecls hds ⟨hS.exe, hS.decls, hS.endPc, ?_⟩)
  rw [show s0.noDecls.st = (s0.st.1, labQ1 "enq1") from Prod.ext rfl (hS.pc.trans labQ1_enq)]
  exact Safely.uncountA (enqQ1_envGCAdj P hL _ (_, 0) ⟨hS.x1, hS.d8, hS.d4, .inl ⟨rfl, hS.x12, e0_init P _⟩⟩)

theorem invDQ1_init_decls (hsz : ds.StrictSized) {P : Params} (hL : QLocs P)
    (hS : WithDeclsD ds (StartDQ1 P.h P.t) s1) (hi : InitV (Config.init [s0, s1] initMem).mem P) :
    (deqRuleQ1_decls hsz P).Inv True (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem P 1)
      (ghost₀ P) := by
  obtain ⟨hds, hS⟩ := hS
  refine invGFCAdjMD_init (s := s1) rfl rfl (QA64MD.of_noDecls hds ⟨hS.exe, hS.decls, hS.endPc, ?_⟩)
  rw [show s1.noDecls.st = (s1.st.1, labQ1 "deq1a") from Prod.ext rfl (hS.pc.trans labQ1_deq1)]
  exact Safely.uncountA (deqQ1_envGCAdj P hL _ (_, 0) ⟨hS.x0, hS.x1, hS.d8, hS.d4, .inl ⟨rfl, comD_init P _ hi⟩⟩)

end Start

/-- **The `NPSafeF` side with declarations.** -/
theorem msqueue1_whole_npSafeF_decls (l : _root_.Layout) [Executable.ValidLayout (l msq1Image)] {ds : Decls}
    (hsz : ds.StrictSized) {P : Params} (hL : QLocs P) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : WithDeclsD ds (StartEQ1 (layout := l) P.t P.n1) s0) (h1 : WithDeclsD ds (StartDQ1 (layout := l) P.h P.t) s1)
    (hi : InitV (Config.init [s0, s1] initMem).mem P) :
    ∀ tid, tid < [s0, s1].length → ∀ k j, NPSafeF (model isa) Arch.armv8 (MB P) tid k j True
      (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem P tid) (ghost₀ P) := by
  intro tid htid k j
  rcases tid with _ | _ | i
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invEQ1_init_decls (layout := l) hsz hL h0)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invDQ1_init_decls (layout := l) hsz hL h1 hi)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- **The one-node Michael–Scott queue `msqueue1.kl` for AArch64 under
`Arch.armv8`, both threads running the whole `.kl` image, with the runner's
declarations**: `msqueue1_envG_whole` for threads whose declarations are
strict sized (`ds.StrictSized`: the `.kl` runner's, from the typed header)
and which otherwise start as there (`StartEQ1`/`StartDQ1` of the thread
with its declarations dropped). -/
theorem msqueue1_envG_runner {fuel : Nat} (l : _root_.Layout) [Executable.ValidLayout (l msq1Image)]
    {ds : Decls} (hsz : ds.StrictSized) (h t d n1 : BitVec 64) (hht : h ≠ t) (hhd : h ≠ d + 8)
    (hhn : h ≠ n1 + 8) (htd : t ≠ d + 8) (htn : t ≠ n1 + 8) (hdn : d ≠ n1) {s0 s1 : isa.State}
    {initMem : List (Loc × Val)} (h0 : WithDeclsD ds (StartEQ1 (layout := l) t n1) s0)
    (h1 : WithDeclsD ds (StartDQ1 (layout := l) h t) s1)
    (hi : InitV (Config.init [s0, s1] initMem).mem ⟨h, t, d, n1⟩)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) :
    ∃ th1, cfg.threads[1]? = some th1 ∧ th1.st.st.1.regs.X10.toBitVec = 1 := by
  have hL : QLocs ⟨h, t, d, n1⟩ := ⟨hht, hhd, hhn, htd, htn, hdn⟩
  refine final_of_relPureSafelyFD Arch.armv8 fuel (B := MB ⟨h, t, d, n1⟩) (Φ := MsQueue1Final)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_init hL _) (ghost₀_pend _) (msq1PureSpecW l _)
    (fun _ => ds) (fun _ => hsz) (fun tid => by cases tid <;> exact msq1Image_noPairs (layout := l))
    (RelPureSpec.holdsD_init (ss := [s0, s1])
      (List.forall_mem_cons.2 ⟨h0.1, List.forall_mem_cons.2 ⟨h1.1, fun _ h => nomatch h⟩⟩) (msq1PureSpecW_init l (fun v => ?_) h0.2 h1.2))
    (msqueue1_whole_npSafeF_decls l hsz hL h0 h1 hi) hc hf fun rF' g' E' hle hsize hB => ?_
  · show Pred.Pure ((ghost₀ ⟨h, t, d, n1⟩).rel (Params.dat ⟨h, t, d, n1⟩)) v
    rw [ghost₀_rel_ne (not_isQ_dat _)]; exact Pred.emp_pure v
  exact msqueue1_final_of_hB hL hf E' hle hsize hB

/-! ## The runner's configuration -/

/-- The runner's declarations for the typed `msqueue1.kl`: `head`, `tail`
8-byte words, `d`, `n1`, `n2` 4-byte words (strict). -/
def msq1DeclsD : Decls :=
  { locs := [⟨0x1000, 8⟩, ⟨0x1200, 8⟩, ⟨0x1100, 4⟩, ⟨0x1300, 4⟩, ⟨0x1400, 4⟩], unsizedDefault := false }

theorem msq1DeclsD_sized : msq1DeclsD.StrictSized := ⟨rfl, by decide⟩

/-- The runner's initial memory for the typed `msqueue1.kl`: `head = tail =
d`, the data words `0` (the links at `n + 8` are undeclared, initially
`0`). -/
def msq1InitMemD : List (Loc × Val) :=
  [(⟨0x1000, 8⟩, 0x1100), (⟨0x1200, 8⟩, 0x1100), (⟨0x1100, 4⟩, 0), (⟨0x1300, 4⟩, 0), (⟨0x1400, 4⟩, 0)]

/-- The threads as the runner prepares them, declarations included. -/
def enqDQ1 : AArch64.State := { enqWQ1 with decls := msq1DeclsD }
def deqDQ1 : AArch64.State := { deqWQ1 with decls := msq1DeclsD }

/-- The runner's configuration is `Config.init [enqDQ1, deqDQ1]
msq1InitMemD` in everything the theorem reads (declarations and initial
memory included). -/
def runnerMatchesDQ1 (src : String) : Bool := A64Whole.runnerIsD src [enqDQ1, deqDQ1] msq1InitMemD

/-- info: true -/
#guard_msgs in
#eval runnerMatchesDQ1 msqueue1KlW

/-- **`1:X10 = 1`** for `msqueue1.kl` under `Arch.armv8`, from the runner's
exact configuration (the whole `code` block at `0x100000`, the typed
header's declarations and initial memory): concrete instance of
`msqueue1_envG_runner`. -/
theorem msqueue1_envG_runner_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [enqDQ1, deqDQ1] msq1InitMemD) c) (hf : c.final = true) :
    ∃ th1, c.threads[1]? = some th1 ∧ th1.st.st.1.regs.X10.toBitVec = 1 :=
  msqueue1_envG_runner wLayoutQ1 msq1DeclsD_sized 0x1000 0x1200 0x1100 0x1300 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (withDeclsD_of rfl enqWQ1_start) (withDeclsD_of rfl deqWQ1_start)
    (by refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Config.init] <;> decide) hc hf

end Kraken.Promising.SLR.EnvG.MsQueue

#print axioms Kraken.Promising.SLR.EnvG.MsQueue.msqueue1_envG_runner
#print axioms Kraken.Promising.SLR.EnvG.MsQueue.msqueue1_envG_runner_concrete
