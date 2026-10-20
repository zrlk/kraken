/-
**`treiber2_nodes.kl` for AArch64 from the runner's exact configuration**
`treiber2_nodes_envG_runner`,
`treiber2_nodes_envG_whole` for threads that carry the `.kl` runner's
declarations (the typed header `uint64_t top, n1, n2`: strict sized,
`Decls.StrictSized`), and its concrete instance
`treiber2_nodes_envG_runner_concrete` (`runnerMatchesDN`: declarations and
initial memory included).

The proof is `A64WholeTreiber2Nodes`'s with the D forms of
`EnvG/A64DeclsLink.lean`: `wRuleN_decls` (`ThreadRuleRXF.ofSafelyEnvGFCAdjMD`,
unmasked), `invWN_init_decls` (`invGFCAdjMD_init`), `RelPureSpec.HoldsD`,
`final_of_relPureSafelyFD`. The start states are the verbatim `StartWN` with
declarations (`A64Whole.WithDeclsD`). The old theorems are unchanged. Faults
are not covered (see `EnvG/A64DeclsBridge.lean`); `wRuleN_noFault` stays at
`decls = {}`.
-/
import Kraken.Promising.SLR.EnvG.A64WholeTreiber2Nodes
import Kraken.Promising.SLR.EnvG.A64DeclsRunner

namespace Kraken.Promising.SLR.EnvG.Treiber2

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)

/-! ## The rule and the start, with declarations -/

section Rule

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiber2NImage)]

omit [Executable.ValidLayout (layout treiber2NImage)] in
/-- The image has no `LDXP`/`STXP`. -/
theorem treiber2NImage_noPairs : Kraken.Executable.noPairs (layout treiber2NImage) = true := by
  rw [Layout.apply_noPairs]; decide

/-- **The whole-image thread `w`'s rule with strict sized declarations
`ds`** (`wRuleN` through `ofSafelyEnvGFCAdjMD`). -/
noncomputable def wRuleN_decls {ds : Decls} (hsz : ds.StrictSized) (P : Params) (w : Nat) (hw : w < 2) :
    ThreadRuleRXF (I := isa) Arch.armv8 (TB2 P) w :=
  ThreadRuleRXF.ofSafelyEnvGFCAdjMD (post := postWN P w) hsz treiber2NImage_noPairs (MaskOf.refl _)
    (plan_valid P w) treiber2NImage_rmwLive treiber2NImage_phase1F (postWN_end P w) (workerN_stuck _) (hB_wN P hw)

/-- **The whole-image thread `w`'s initial invariant with declarations**
(`invWN_init`). -/
theorem invWN_init_decls {ds : Decls} (hsz : ds.StrictSized) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    {P : Params} (hL : TLocs P) {w : Nat} (hw : w < 2) (hD : ∀ d, P.D w d) {s : isa.State}
    (hs : [s0, s1][w]? = some s) (hS : WithDeclsD ds (StartWN P.t (P.n w)) s)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal P.top = 0) :
    (wRuleN_decls hsz P w hw).Inv True (Config.init [s0, s1] initMem)
      (tRes (Config.init [s0, s1] initMem).mem P w) (ghost₀ P) := by
  have htr : tRes (Config.init [s0, s1] initMem).mem P w = thrRes (Config.init [s0, s1] initMem).mem P w := by
    rcases w with _ | _ | w
    · rfl
    · rfl
    · omega
  rw [htr]
  obtain ⟨hds, he, hds0, hpc, hend, hx0, hx1, hd8⟩ := hS
  refine invGFCAdjMD_init hs rfl (QA64MD.of_noDecls hds ⟨he, hds0, hend, ?_⟩)
  rw [show s.noDecls.st = (s.noDecls.st.1, labN "push") from Prod.ext rfl (hpc.trans labN_worker)]
  exact Safely.uncountA (workerN_envGCAdj P w hL hw _ (_, 0) ⟨hx0, hx1, hd8, .inl ⟨rfl, pu_init P hL hw hD _ hT0⟩⟩)

end Rule

/-- **The `NPSafeF` side with declarations**, whole image. -/
theorem treiber2N_npSafeF_decls (l : _root_.Layout) [Executable.ValidLayout (l treiber2NImage)] {ds : Decls}
    (hsz : ds.StrictSized) {t n0 n1 : BitVec 64} (hL : TLocs (tP2 t n0 n1)) {s0 s1 : isa.State}
    {initMem : List (Loc × Val)} (h0 : WithDeclsD ds (StartWN (layout := l) t n0) s0)
    (h1 : WithDeclsD ds (StartWN (layout := l) t n1) s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0) :
    ∀ tid, tid < [s0, s1].length → ∀ k j, NPSafeF (model isa) Arch.armv8 (TB2 (tP2 t n0 n1)) tid k j True
      (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem (tP2 t n0 n1) tid)
      (ghost₀ (tP2 t n0 n1)) := by
  intro tid htid k j
  rcases tid with _ | _ | i
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _
      (invWN_init_decls (layout := l) hsz hL (by decide) (fun _ => trivial) rfl h0 hT0)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _
      (invWN_init_decls (layout := l) hsz hL (by decide) (fun _ => trivial) rfl h1 hT0)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- **The two-thread Treiber stack `treiber2_nodes.kl` for AArch64, both
threads running the whole `.kl` image, with the runner's declarations**:
`treiber2_nodes_envG_whole` for threads whose declarations are strict sized
(`ds.StrictSized`: the `.kl` runner's, from the typed header) and which
otherwise start as there (`StartWN` of the thread with its declarations
dropped). -/
theorem treiber2_nodes_envG_runner {fuel : Nat} (l : _root_.Layout) [Executable.ValidLayout (l treiber2NImage)]
    {ds : Decls} (hsz : ds.StrictSized) (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8)
    (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : WithDeclsD ds (StartWN (layout := l) t n0) s0) (h1 : WithDeclsD ds (StartWN (layout := l) t n1) s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : Treiber2Final n0 n1 cfg := by
  have hL := tLocs_tP2 ht0 ht1 hn hn0 hn1
  refine final_of_relPureSafelyFD Arch.armv8 fuel (B := TB2 (tP2 t n0 n1)) (Φ := Treiber2Final n0 n1)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_init hL _) (ghost₀_pend _) (treiber2NPureSpecW l _)
    (fun _ => ds) (fun _ => hsz) (fun tid => by cases tid <;> exact treiber2NImage_noPairs (layout := l))
    (RelPureSpec.holdsD_init (ss := [s0, s1])
      (List.forall_mem_cons.2 ⟨h0.1, List.forall_mem_cons.2 ⟨h1.1, fun _ h => nomatch h⟩⟩)
      (treiber2NPureSpecW_init l (fun v => ?_) (fun v => ?_) h0.2 h1.2))
    (treiber2N_npSafeF_decls l hsz hL h0 h1 hT0) hc hf fun rF' g' E' hle hsize hB => ?_
  · show Pred.Pure ((ghost₀ (tP2 t n0 n1)).rel ((tP2 t n0 n1).nd 0)) v
    rw [ghost₀_rel_ne (Ne.symm (hL.top_nd' (by decide)))]; exact Pred.emp_pure v
  · show Pred.Pure ((ghost₀ (tP2 t n0 n1)).rel ((tP2 t n0 n1).nd 1)) v
    rw [ghost₀_rel_ne (Ne.symm (hL.top_nd' (by decide)))]; exact Pred.emp_pure v
  have hi0 : (0 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hi1 : (1 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hW := (ghost₀_gw (tP2 t n0 n1)).mono hle
  have hno := Config.final_not_outstanding hf
  obtain ⟨w0, hw0, th, hth, hd0⟩ := hB 0 (Config.final_done hf hi0)
  obtain ⟨w1, hw1, th', hth', hd1⟩ := hB 1 (Config.final_done hf hi1)
  by_cases hww : w0 = w1
  · subst hww
    exact (acq_pair_false E' hi0 hi1 (by decide) hd0.1 hd1.1).elim
  rcases w0 with _ | _ | w0
  · rcases w1 with _ | _ | w1
    · exact absurd rfl hww
    · exact ⟨th, th', hth, hth', final_values E' hW hL hno hi0 hi1 hd0 hd1⟩
    · omega
  · rcases w1 with _ | _ | w1
    · have := final_values E' hW hL hno hi1 hi0 hd1 hd0
      exact ⟨th', th, hth', hth, this⟩
    · exact absurd rfl hww
    · omega
  · omega

/-! ## The runner's configuration -/

open Kraken.Promising.SLR.EnvG.ConcreteTreiber2 (topAddr n1Addr n2Addr treiber2NodesKl)

/-- The runner's declarations for the typed `treiber2_nodes.kl`: `top`, `n1`,
`n2` 8-byte words (strict). -/
def treiber2NDeclsD : Decls := { locs := [⟨topAddr, 8⟩, ⟨n1Addr, 8⟩, ⟨n2Addr, 8⟩], unsizedDefault := false }

theorem treiber2NDeclsD_sized : treiber2NDeclsD.StrictSized := ⟨rfl, by decide⟩

/-- The runner's initial memory for the typed `treiber2_nodes.kl`: the three
declared words `0` (the links at `n + 8` are undeclared, initially `0`). -/
def treiber2NInitMemD : List (Loc × Val) := [(⟨topAddr, 8⟩, 0), (⟨n1Addr, 8⟩, 0), (⟨n2Addr, 8⟩, 0)]

/-- The threads as the runner prepares them, declarations included. -/
def wNWorkerD0 : AArch64.State := { wNWorker0 with decls := treiber2NDeclsD }
def wNWorkerD1 : AArch64.State := { wNWorker1 with decls := treiber2NDeclsD }

/-- The runner's configuration is `Config.init [wNWorkerD0, wNWorkerD1]
treiber2NInitMemD` in everything the theorem reads (declarations and initial
memory included). -/
def runnerMatchesDN (src : String) : Bool :=
  A64Whole.runnerIsD src [wNWorkerD0, wNWorkerD1] treiber2NInitMemD

/-- info: true -/
#guard_msgs in
#eval runnerMatchesDN treiber2NodesKl

/-- **`(0:X10=n1 ∧ 1:X10=n2) ∨ (0:X10=n2 ∧ 1:X10=n1)`** for
`treiber2_nodes.kl` under `Arch.armv8`, from the runner's exact
configuration (the whole `code` block at `0x100000`, the typed header's
declarations and initial memory): concrete instance of
`treiber2_nodes_envG_runner`. -/
theorem treiber2_nodes_envG_runner_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [wNWorkerD0, wNWorkerD1] treiber2NInitMemD) c)
    (hf : c.final = true) : Treiber2Final n1Addr n2Addr c :=
  treiber2_nodes_envG_runner wLayout2N treiber2NDeclsD_sized topAddr n1Addr n2Addr (by decide) (by decide)
    (by decide) (by decide) (by decide) (withDeclsD_of rfl wNWorker0_start) (withDeclsD_of rfl wNWorker1_start)
    (by simp only [Config.init]; decide) hc hf

end Kraken.Promising.SLR.EnvG.Treiber2

#print axioms Kraken.Promising.SLR.EnvG.Treiber2.treiber2_nodes_envG_runner
#print axioms Kraken.Promising.SLR.EnvG.Treiber2.treiber2_nodes_envG_runner_concrete
