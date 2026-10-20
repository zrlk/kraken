/-
Part 9: **`treiber2_arm.kl` for AArch64 from the
runner's exact configuration**, as `EnvG/A64WholeTreiber2Runner.lean` for
`treiber2.kl`: `treiber2_arm_envG_runner`, `treiber2_arm_envG_whole` for
threads that carry the `.kl` runner's declarations (the typed header
`uint64_t top; uint32_t n1, n2`: strict sized, `Decls.StrictSized`), and its
concrete instance `treiber2_arm_envG_runner_concrete` (`runnerMatchesDA`:
declarations and initial memory included).

The proof is `Treiber2ArmPublic`'s with the D forms of
`EnvG/A64DeclsLink.lean`: `wRuleA_decls` (`ThreadRuleRXF.ofSafelyEnvGFCAdjMD`,
unmasked), `invWA_init_decls` (`invGFCAdjMD_init`), `RelPureSpec.HoldsD`,
`final_of_relPureSafelyFD`. The runner's declarations and initial memory are
`treiber2.kl`'s (`Treiber2.treiber2DeclsD`, `Treiber2.treiber2InitMemD`: the
same typed header). Faults are not covered (see `EnvG/A64DeclsBridge.lean`);
`wRuleA_noFault` stays at `decls = {}`.
-/
import Kraken.Promising.SLR.EnvG.A64Treiber2ArmWhole
import Kraken.Promising.SLR.EnvG.A64WholeTreiber2Runner

namespace Kraken.Promising.SLR.EnvG.Treiber2Arm

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)
open Kraken.Promising.SLR.EnvG.Treiber2 (Params TLocs tPD tLocs_tPD thrRes tRes acq_pair_false x32_tPD
  Treiber2DFinal treiber2DeclsD treiber2DeclsD_sized treiber2InitMemD)

/-! ## The rule and the start, with declarations -/

section Rule

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiber2ArmWorker)]

omit [Executable.ValidLayout (layout treiber2ArmWorker)] in
/-- The worker has no `LDXP`/`STXP`. -/
theorem treiber2ArmWorker_noPairs : Kraken.Executable.noPairs (layout treiber2ArmWorker) = true := by
  rw [Layout.apply_noPairs]; decide

/-- **Thread `w`'s rule with strict sized declarations `ds`** (`wRuleA`
through `ofSafelyEnvGFCAdjMD`). -/
noncomputable def wRuleA_decls {ds : Decls} (hsz : ds.StrictSized) (P : Params) (w : Nat) (hw : w < 2) :
    ThreadRuleRXF (I := isa) Arch.armv8 (TB2A P) w :=
  ThreadRuleRXF.ofSafelyEnvGFCAdjMD (post := postWA P w) hsz treiber2ArmWorker_noPairs (MaskOf.refl _)
    planA_valid treiber2ArmWorker_rmwLive treiber2ArmWorker_phase1F postOf_end
    (not_instrStepEnv_of_end_labels _ 1) (hB_wA P hw)

end Rule

section Start

variable [layout : _root_.Layout] {s0 s1 : isa.State} {initMem : List (Loc × Val)}

/-- **Thread `w`'s initial invariant with declarations** (`invWA_init`). -/
theorem invWA_init_decls [Executable.ValidLayout (layout treiber2ArmWorker)] {ds : Decls} (hsz : ds.StrictSized)
    {P : Params} (hL : TLocs P) {w : Nat} (hw : w < 2) {d9 : BitVec 32}
    (hD : ∀ d : Val, BitVec.setWidth 32 d = d9 → P.D w d) {s : isa.State}
    (hs : [s0, s1][w]? = some s) (hS : WithDeclsD ds (StartWA P.t (P.n w) d9) s)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal P.top = 0) :
    (wRuleA_decls hsz P w hw).Inv True (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem P w)
      (ghost₀A P) := by
  letI : CodeEnv := ⟨layout treiber2ArmWorker⟩
  have htr : tRes (Config.init [s0, s1] initMem).mem P w = thrRes (Config.init [s0, s1] initMem).mem P w := by
    rcases w with _ | _ | w
    · rfl
    · rfl
    · omega
  rw [htr]
  obtain ⟨hds, hS⟩ := hS
  exact invGFCAdjMD_init hs rfl (QA64MD.of_noDecls hds
    (qa64CAdj_of_partialTripleEnv (st := s.noDecls) (workerA_envGCAdj P w hL hw d9 hD).uncount rfl
      hS.exe hS.decls hS.endPc hS.pc ⟨0, hS.x0, hS.x1, hS.d8, hS.d4, hS.x9, pu0A_init P hL hw _ hT0⟩))

end Start

/-- **The `NPSafeF` side with declarations**, one layout `l`. -/
theorem treiber2A_npSafeF_decls (l : _root_.Layout) [Executable.ValidLayout (l treiber2ArmWorker)] {ds : Decls}
    (hsz : ds.StrictSized) {t n0 n1 : BitVec 64} (hL : TLocs (tPD t n0 n1)) {s0 s1 : isa.State}
    {initMem : List (Loc × Val)} (h0 : WithDeclsD ds (StartWA (layout := l) t n0 1) s0)
    (h1 : WithDeclsD ds (StartWA (layout := l) t n1 2) s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0) :
    ∀ tid, tid < [s0, s1].length → ∀ k j, NPSafeF (model isa) Arch.armv8 (TB2A (tPD t n0 n1)) tid k j True
      (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem (tPD t n0 n1) tid)
      (ghost₀A (tPD t n0 n1)) := by
  intro tid htid k j
  rcases tid with _ | _ | i
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _
      (invWA_init_decls (layout := l) hsz hL (by decide) (fun _ h => h) rfl h0 hT0)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _
      (invWA_init_decls (layout := l) hsz hL (by decide) (fun _ h => h) rfl h1 hT0)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- **`treiber2_arm.kl` for AArch64, both threads running the whole `.kl`
image, with the runner's declarations**: `treiber2_arm_envG_whole` for
threads whose declarations are strict sized (`ds.StrictSized`: the `.kl`
runner's, from the typed header) and which otherwise start as there
(`StartWA` of the thread with its declarations dropped). -/
theorem treiber2_arm_envG_runner {fuel : Nat} (l : _root_.Layout) [Executable.ValidLayout (l treiber2ArmWorker)]
    {ds : Decls} (hsz : ds.StrictSized) (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8)
    (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : WithDeclsD ds (StartWA (layout := l) t n0 1) s0) (h1 : WithDeclsD ds (StartWA (layout := l) t n1 2) s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : Treiber2DFinal n0 n1 cfg := by
  have hL := tLocs_tPD ht0 ht1 hn hn0 hn1
  refine final_of_relPureSafelyFD Arch.armv8 fuel (B := TB2A (tPD t n0 n1)) (Φ := Treiber2DFinal n0 n1)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_initA hL _) (ghost₀A_pend _) (treiber2ArmPureSpec l l _)
    (fun _ => ds) (fun _ => hsz) (fun tid => by cases tid <;> exact treiber2ArmWorker_noPairs (layout := l))
    (RelPureSpec.holdsD_init (ss := [s0, s1])
      (List.forall_mem_cons.2 ⟨h0.1, List.forall_mem_cons.2 ⟨h1.1, fun _ h => nomatch h⟩⟩)
      (treiber2ArmPureSpec_init l l (fun v => Pred.emp_pure v) (fun v => Pred.emp_pure v)
        (fun v => Pred.emp_pure v) (fun v => Pred.emp_pure v) (fun v => Pred.emp_pure v) h0.2 h1.2))
    (treiber2A_npSafeF_decls l hsz hL h0 h1 hT0) hc hf fun rF' g' E' hle hsize hB => ?_
  have hi0 : (0 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hi1 : (1 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hall : ∀ k, k < cfg.threads.size → k = 0 ∨ k = 1 := by
    intro k hk; rw [hsize] at hk; simp at hk; omega
  have hall' : ∀ k, k < cfg.threads.size → k = 1 ∨ k = 0 := fun k hk => (hall k hk).symm
  have hno := Config.final_not_outstanding hf
  obtain ⟨w0, hw0, th, hth, hd0⟩ := hB 0 (Config.final_done hf hi0)
  obtain ⟨w1, hw1, th', hth', hd1⟩ := hB 1 (Config.final_done hf hi1)
  by_cases hww : w0 = w1
  · subst hww
    exact (acq_pair_false E' hi0 hi1 (by decide) hd0.1 hd1.1).elim
  rcases w0 with _ | _ | w0
  · rcases w1 with _ | _ | w1
    · exact absurd rfl hww
    · refine ⟨th, th', hth, hth', ?_⟩
      rcases final_values_dataA E' hL hno hi0 hi1 (by decide) hall hd0 hd1 with
        ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩
      · exact .inl ⟨ha, x32_tPD (by decide) hc, hb, x32_tPD (by decide) hd⟩
      · exact .inr ⟨ha, x32_tPD (by decide) hc, hb, x32_tPD (by decide) hd⟩
    · omega
  · rcases w1 with _ | _ | w1
    · refine ⟨th', th, hth', hth, ?_⟩
      rcases final_values_dataA E' hL hno hi1 hi0 (by decide) hall' hd1 hd0 with
        ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩
      · exact .inl ⟨ha, x32_tPD (by decide) hc, hb, x32_tPD (by decide) hd⟩
      · exact .inr ⟨ha, x32_tPD (by decide) hc, hb, x32_tPD (by decide) hd⟩
    · exact absurd rfl hww
    · omega
  · omega

/-! ## The runner's configuration -/

open Kraken.Promising.SLR.EnvG.ConcreteTreiber2 (topAddr n1Addr n2Addr)

/-- The threads as the runner prepares them, declarations included. -/
def wWorkerDA0 : AArch64.State := { wWorkerA0 with decls := treiber2DeclsD }
def wWorkerDA1 : AArch64.State := { wWorkerA1 with decls := treiber2DeclsD }

/-- The runner's configuration is `Config.init [wWorkerDA0, wWorkerDA1]
treiber2InitMemD` in everything the theorem reads (declarations and initial
memory included). -/
def runnerMatchesDA (src : String) : Bool := A64Whole.runnerIsD src [wWorkerDA0, wWorkerDA1] treiber2InitMemD

/-- info: true -/
#guard_msgs in
#eval runnerMatchesDA treiber2ArmKl

/-- **`(0:X10=n1 ∧ 0:X11=1 ∧ 1:X10=n2 ∧ 1:X11=2) ∨
(0:X10=n2 ∧ 0:X11=2 ∧ 1:X10=n1 ∧ 1:X11=1)`** for `treiber2_arm.kl` under
`Arch.armv8`, from the runner's exact configuration (the whole `code` block
at `0x100000`, the typed header's declarations and initial memory):
concrete instance of `treiber2_arm_envG_runner`. -/
theorem treiber2_arm_envG_runner_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [wWorkerDA0, wWorkerDA1] treiber2InitMemD) c)
    (hf : c.final = true) : Treiber2DFinal n1Addr n2Addr c :=
  treiber2_arm_envG_runner wLayoutA treiber2DeclsD_sized topAddr n1Addr n2Addr (by decide) (by decide)
    (by decide) (by decide) (by decide) (withDeclsD_of rfl wWorkerA0_start) (withDeclsD_of rfl wWorkerA1_start)
    (by simp only [Config.init]; decide) hc hf

end Kraken.Promising.SLR.EnvG.Treiber2Arm

#print axioms Kraken.Promising.SLR.EnvG.Treiber2Arm.treiber2_arm_envG_runner
#print axioms Kraken.Promising.SLR.EnvG.Treiber2Arm.treiber2_arm_envG_runner_concrete
