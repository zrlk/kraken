/-
**`treiber2.kl` for AArch64 from the runner's exact configuration**
`treiber2_envG_runner`, `treiber2_envG_whole` for
threads that carry the `.kl` runner's declarations (the typed header
`uint64_t top; uint32_t n1, n2`: strict sized, `Decls.StrictSized`), and its
concrete instance `treiber2_envG_runner_concrete` (`runnerMatchesD2`:
declarations and initial memory included).

The proof is `Treiber2DataPublic`'s with the D forms of
`EnvG/A64DeclsLink.lean`: `wRuleD_decls` (`ThreadRuleRXF.ofSafelyEnvGFCAdjMD`,
unmasked), `invWD_init_decls` (`invGFCAdjMD_init`), `RelPureSpec.HoldsD`,
`final_of_relPureSafelyFD`. The start states are the verbatim `StartWD`
with declarations (`A64Whole.WithDeclsD`). The old theorems are unchanged.
Faults are not covered (see `EnvG/A64DeclsBridge.lean`); `wRuleD_noFault`
stays at `decls = {}`.
-/
import Kraken.Promising.SLR.EnvG.A64WholeTreiber2
import Kraken.Promising.SLR.EnvG.A64DeclsRunner

namespace Kraken.Promising.SLR.EnvG.Treiber2

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)

/-! ## The rule and the start, with declarations -/

section Rule

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiber2DWorker)]

omit [Executable.ValidLayout (layout treiber2DWorker)] in
/-- The worker has no `LDXP`/`STXP`. -/
theorem treiber2DWorker_noPairs : Kraken.Executable.noPairs (layout treiber2DWorker) = true := by
  rw [Layout.apply_noPairs]; decide

/-- **Thread `w`'s rule with strict sized declarations `ds`** (`wRuleD`
through `ofSafelyEnvGFCAdjMD`). -/
noncomputable def wRuleD_decls {ds : Decls} (hsz : ds.StrictSized) (P : Params) (w : Nat) (hw : w < 2) :
    ThreadRuleRXF (I := isa) Arch.armv8 (TB2D P) w :=
  ThreadRuleRXF.ofSafelyEnvGFCAdjMD (post := postWD P w) hsz treiber2DWorker_noPairs (MaskOf.refl _)
    (plan_valid P w) treiber2DWorker_rmwLive treiber2DWorker_phase1F postOf_end
    (not_instrStepEnv_of_end_labels _ 1) (hB_wD P hw)

end Rule

section Start

variable [layout : _root_.Layout] {s0 s1 : isa.State} {initMem : List (Loc × Val)}

/-- **Thread `w`'s initial invariant with declarations** (`invWD_init`). -/
theorem invWD_init_decls [Executable.ValidLayout (layout treiber2DWorker)] {ds : Decls} (hsz : ds.StrictSized)
    {P : Params} (hL : TLocs P) {w : Nat} (hw : w < 2) {d9 : BitVec 32}
    (hD : ∀ d : Val, BitVec.setWidth 32 d = d9 → P.D w d) {s : isa.State}
    (hs : [s0, s1][w]? = some s) (hS : WithDeclsD ds (StartWD P.t (P.n w) d9) s)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal P.top = 0) :
    (wRuleD_decls hsz P w hw).Inv True (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem P w)
      (ghost₀ P) := by
  letI : CodeEnv := ⟨layout treiber2DWorker⟩
  have htr : tRes (Config.init [s0, s1] initMem).mem P w = thrRes (Config.init [s0, s1] initMem).mem P w := by
    rcases w with _ | _ | w
    · rfl
    · rfl
    · omega
  rw [htr]
  obtain ⟨hds, hS⟩ := hS
  exact invGFCAdjMD_init hs rfl (QA64MD.of_noDecls hds
    (qa64CAdj_of_partialTripleEnv (st := s.noDecls) (workerD_envGCAdj P w hL hw d9 hD).uncount rfl
      hS.exe hS.decls hS.endPc hS.pc ⟨0, hS.x0, hS.x1, hS.d8, hS.d4, hS.x9, pu0_init P hL hw _ hT0⟩))

end Start

/-- **The `NPSafeF` side with declarations**, one layout `l`. -/
theorem treiber2D_npSafeF_decls (l : _root_.Layout) [Executable.ValidLayout (l treiber2DWorker)] {ds : Decls}
    (hsz : ds.StrictSized) {t n0 n1 : BitVec 64} (hL : TLocs (tPD t n0 n1)) {s0 s1 : isa.State}
    {initMem : List (Loc × Val)} (h0 : WithDeclsD ds (StartWD (layout := l) t n0 1) s0)
    (h1 : WithDeclsD ds (StartWD (layout := l) t n1 2) s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0) :
    ∀ tid, tid < [s0, s1].length → ∀ k j, NPSafeF (model isa) Arch.armv8 (TB2D (tPD t n0 n1)) tid k j True
      (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem (tPD t n0 n1) tid)
      (ghost₀ (tPD t n0 n1)) := by
  intro tid htid k j
  rcases tid with _ | _ | i
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _
      (invWD_init_decls (layout := l) hsz hL (by decide) (fun _ h => h) rfl h0 hT0)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _
      (invWD_init_decls (layout := l) hsz hL (by decide) (fun _ h => h) rfl h1 hT0)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- **The two-thread Treiber stack `treiber2.kl` for AArch64, both threads
running the whole `.kl` image, with the runner's declarations**:
`treiber2_envG_whole` for threads whose declarations are strict sized
(`ds.StrictSized`: the `.kl` runner's, from the typed header) and which
otherwise start as there (`StartWD` of the thread with its declarations
dropped). -/
theorem treiber2_envG_runner {fuel : Nat} (l : _root_.Layout) [Executable.ValidLayout (l treiber2DWorker)]
    {ds : Decls} (hsz : ds.StrictSized) (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8)
    (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : WithDeclsD ds (StartWD (layout := l) t n0 1) s0) (h1 : WithDeclsD ds (StartWD (layout := l) t n1 2) s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : Treiber2DFinal n0 n1 cfg := by
  have hL := tLocs_tPD ht0 ht1 hn hn0 hn1
  refine final_of_relPureSafelyFD Arch.armv8 fuel (B := TB2D (tPD t n0 n1)) (Φ := Treiber2DFinal n0 n1)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_init hL _) (ghost₀_pend _) (treiber2DPureSpec l l _)
    (fun _ => ds) (fun _ => hsz) (fun tid => by cases tid <;> exact treiber2DWorker_noPairs (layout := l))
    (RelPureSpec.holdsD_init (ss := [s0, s1])
      (List.forall_mem_cons.2 ⟨h0.1, List.forall_mem_cons.2 ⟨h1.1, fun _ h => nomatch h⟩⟩)
      (treiber2DPureSpec_init l l (fun v => ?_) (fun v => ?_) (fun v => ?_) (fun v => ?_) h0.2 h1.2))
    (treiber2D_npSafeF_decls l hsz hL h0 h1 hT0) hc hf fun rF' g' E' hle hsize hB => ?_
  · show Pred.Pure ((ghost₀ (tPD t n0 n1)).rel ((tPD t n0 n1).dd 0)) v
    rw [ghost₀_rel_ne (Ne.symm (top_dd _ 0))]; exact Pred.emp_pure v
  · show Pred.Pure ((ghost₀ (tPD t n0 n1)).rel ((tPD t n0 n1).dd 1)) v
    rw [ghost₀_rel_ne (Ne.symm (top_dd _ 1))]; exact Pred.emp_pure v
  · show Pred.Pure ((ghost₀ (tPD t n0 n1)).rel ((tPD t n0 n1).nd 0)) v
    rw [ghost₀_rel_ne (Ne.symm (hL.top_nd' (by decide)))]; exact Pred.emp_pure v
  · show Pred.Pure ((ghost₀ (tPD t n0 n1)).rel ((tPD t n0 n1).nd 1)) v
    rw [ghost₀_rel_ne (Ne.symm (hL.top_nd' (by decide)))]; exact Pred.emp_pure v
  have hi0 : (0 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hi1 : (1 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hW := (ghost₀_gw (tPD t n0 n1)).mono hle
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
      rcases final_values_data E' hW hL hno hi0 hi1 hd0 hd1 with ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩
      · exact .inl ⟨ha, x32_tPD (by decide) hc, hb, x32_tPD (by decide) hd⟩
      · exact .inr ⟨ha, x32_tPD (by decide) hc, hb, x32_tPD (by decide) hd⟩
    · omega
  · rcases w1 with _ | _ | w1
    · refine ⟨th', th, hth', hth, ?_⟩
      rcases final_values_data E' hW hL hno hi1 hi0 hd1 hd0 with ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩
      · exact .inl ⟨ha, x32_tPD (by decide) hc, hb, x32_tPD (by decide) hd⟩
      · exact .inr ⟨ha, x32_tPD (by decide) hc, hb, x32_tPD (by decide) hd⟩
    · exact absurd rfl hww
    · omega
  · omega

/-! ## The runner's configuration -/

open Kraken.Promising.SLR.EnvG.ConcreteTreiber2 (topAddr n1Addr n2Addr)
open Kraken.Promising.SLR.EnvG.ConcreteTreiber2Data (treiber2Kl)

/-- The runner's declarations for the typed `treiber2.kl`: `top` an 8-byte
word, `n1`, `n2` 4-byte words (strict). -/
def treiber2DeclsD : Decls := { locs := [⟨topAddr, 8⟩, ⟨n1Addr, 4⟩, ⟨n2Addr, 4⟩], unsizedDefault := false }

theorem treiber2DeclsD_sized : treiber2DeclsD.StrictSized := ⟨rfl, by decide⟩

/-- The runner's initial memory for the typed `treiber2.kl`: the three
declared words `0` (the links at `n + 8` are undeclared, initially `0`). -/
def treiber2InitMemD : List (Loc × Val) := [(⟨topAddr, 8⟩, 0), (⟨n1Addr, 4⟩, 0), (⟨n2Addr, 4⟩, 0)]

/-- The threads as the runner prepares them, declarations included. -/
def wWorkerD0 : AArch64.State := { wWorker0 with decls := treiber2DeclsD }
def wWorkerD1 : AArch64.State := { wWorker1 with decls := treiber2DeclsD }

/-- The runner's configuration is `Config.init [wWorkerD0, wWorkerD1]
treiber2InitMemD` in everything the theorem reads (declarations and initial
memory included). -/
def runnerMatchesD2 (src : String) : Bool := A64Whole.runnerIsD src [wWorkerD0, wWorkerD1] treiber2InitMemD

/-- info: true -/
#guard_msgs in
#eval runnerMatchesD2 treiber2Kl

/-- **`(0:X10=n1 ∧ 0:X11=1 ∧ 1:X10=n2 ∧ 1:X11=2) ∨
(0:X10=n2 ∧ 0:X11=2 ∧ 1:X10=n1 ∧ 1:X11=1)`** for `treiber2.kl` under
`Arch.armv8`, from the runner's exact configuration (the whole `code` block
at `0x100000`, the typed header's declarations and initial memory):
concrete instance of `treiber2_envG_runner`. -/
theorem treiber2_envG_runner_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [wWorkerD0, wWorkerD1] treiber2InitMemD) c)
    (hf : c.final = true) : Treiber2DFinal n1Addr n2Addr c :=
  treiber2_envG_runner wLayout2D treiber2DeclsD_sized topAddr n1Addr n2Addr (by decide) (by decide) (by decide)
    (by decide) (by decide) (withDeclsD_of rfl wWorker0_start) (withDeclsD_of rfl wWorker1_start)
    (by simp only [Config.init]; decide) hc hf

end Kraken.Promising.SLR.EnvG.Treiber2

#print axioms Kraken.Promising.SLR.EnvG.Treiber2.treiber2_envG_runner
#print axioms Kraken.Promising.SLR.EnvG.Treiber2.treiber2_envG_runner_concrete
