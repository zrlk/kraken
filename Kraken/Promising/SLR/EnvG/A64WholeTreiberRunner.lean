/-
**`treiber_pp.kl` for AArch64 from the runner's exact configuration**
`treiber_pp_envG_runner`, `treiber_pp_envG_whole`
for threads that carry the `.kl` runner's declarations (the typed header
`uint64_t top; uint32_t n1`: strict sized, `Decls.StrictSized`), and its
concrete instance `treiber_pp_envG_runner_concrete` (`runnerMatchesWD`:
declarations and initial memory included).

The proof is `A64WholeTreiberPublic`'s with the D forms of
`EnvG/A64DeclsLink.lean`: `pushRuleWD`/`popRuleWD`
(`ThreadRuleRXF.ofSafelyEnvGFCMD`), `invPushWD_init`/`invPopWD_init`
(`invGFCMD_init`), `RelPureSpec.HoldsD`, `final_of_relPureSafelyFD`. The old
theorems are unchanged. Faults are not covered (see
`EnvG/A64DeclsBridge.lean`); `pushRuleW_noFault`/`popRuleW_noFault` stay at
`decls = {}`.
-/
import Kraken.Promising.SLR.EnvG.A64WholeTreiberConcrete
import Kraken.Promising.SLR.EnvG.A64DeclsLink
import Kraken.Promising.SLR.EnvG.A64DeclsRunner

namespace Kraken.Promising.SLR.EnvG.Treiber

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## The rules and the start, with declarations -/

section Rules

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiberImageA)]

omit [Executable.ValidLayout (layout treiberImageA)] in
/-- The image has no `LDXP`/`STXP`. -/
theorem treiberImageA_noPairs : Kraken.Executable.noPairs (layout treiberImageA) = true := by
  rw [Layout.apply_noPairs]; decide

/-- **The whole-image pusher's rule with strict sized declarations `ds`**
(`pushRuleW` through `ofSafelyEnvGFCMD`). -/
noncomputable def pushRuleWD {ds : Decls} (hsz : ds.StrictSized) (P : Params) (hL : TLocs P) (n : BitVec 64) :
    ThreadRuleRXF (I := isa) Arch.armv8 (TB P n) 0 :=
  ThreadRuleRXF.ofSafelyEnvGFCMD (post := postPushW P) hsz treiberImageA_noPairs treiberImageP_mask
    (pushPlan_valid hL) treiberImageA_rmwLive treiberImageP_phase1F (postPushW_end P) (pushP_stuck _) (hB_pushW P n)

/-- **The whole-image popper's rule with strict sized declarations `ds`.** -/
noncomputable def popRuleWD {ds : Decls} (hsz : ds.StrictSized) (P : Params) (hL : TLocs P) (n : BitVec 64) :
    ThreadRuleRXF (I := isa) Arch.armv8 (TB P n) 1 :=
  ThreadRuleRXF.ofSafelyEnvGFCMD (post := postPopW n) hsz treiberImageA_noPairs (MaskOf.refl _) (popPlan_valid hL)
    treiberImageA_rmwLive treiberImageA_phase1F (postPopW_end n) (popA_stuck _) (hB_popW P n)

end Rules

/-- **The pusher at its start with declarations `ds`** (`StartPushW` with
`decls = ds`). -/
structure StartPushWD [layout : _root_.Layout] (ds : Decls) (t n : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout treiberImageA
  decls : s.decls = ds
  pc : s.st.2 = labT "pusher"
  endPc : s.endPc = labT "pdone"
  x0 : s.st.1.regs.X0.toBitVec = t
  x1 : s.st.1.regs.X1.toBitVec = n
  x9 : s.st.1.regs.X9.toBitVec.setWidth 32 = 1
  dt : Mem.loadInt s.st.1.dmem t 8 = none
  dd : Mem.loadInt s.st.1.dmem n 4 = none
  dn : Mem.loadInt s.st.1.dmem (n + 8) 8 = none

/-- **The popper at its start with declarations `ds`** (`StartPopW` with
`decls = ds`). -/
structure StartPopWD [layout : _root_.Layout] (ds : Decls) (t : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout treiberImageA
  decls : s.decls = ds
  pc : s.st.2 = labT "popper"
  endPc : s.endPc = labT "qdone"
  x0 : s.st.1.regs.X0.toBitVec = t
  dt : Mem.loadInt s.st.1.dmem t 8 = none
  d4 : ∀ a, Mem.loadInt s.st.1.dmem a 4 = none

section Start

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiberImageA)] {ds : Decls} {t n : BitVec 64}
  {sP sQ : isa.State} {initMem : List (Loc × Val)}

/-- **The pusher's initial invariant with declarations** (`invPushW_init`). -/
theorem invPushWD_init (hsz : ds.StrictSized) (htn : t ≠ n + 8) (hP : StartPushWD ds t n sP) :
    (pushRuleWD hsz (tP t n) (tLocs_tP htn) n).Inv True (Config.init [sP, sQ] initMem)
      (tRes (Config.init [sP, sQ] initMem).mem (tP t n) 0) (ghost₀ (tP t n)) := by
  have hL := tLocs_tP htn
  obtain ⟨he, hds, hpc, hend, hx0, hx1, hx9, hdt, hdd, hdn⟩ := hP
  have hPu0 : Pu0 (tP t n) (σInit (Config.init [sP, sQ] initMem)
      (tRes (Config.init [sP, sQ] initMem).mem (tP t n) 0) (ghost₀ (tP t n))) := by
    refine ⟨ghost₀_gw _, ?_⟩
    have htd := hL.top_d; have htn' := hL.top_n; have hdn := hL.d_n
    simp only [σInit, tRes, ↓reduceIte, pushRes, Res.initOf, Perm.init, pushFrac]
    simp only [Ne.symm htd, Ne.symm htn', ↓reduceIte, true_or, or_true, true_and]
    refine ⟨by grind, fun p hp => by rw [hp.2]⟩
  refine invGFCMD_init (s := sP) rfl rfl ⟨he, hds, hend, ?_⟩
  rw [show sP.st = (sP.st.1, labT "pusher") from Prod.ext rfl hpc]
  exact Safely.uncountA (pusherW_envGC t n ⟨t, 1⟩ hL _ (_, 0) ⟨hx0, hx1, hdt, hdd, hdn, .inl ⟨rfl, hx9, hPu0⟩⟩)

/-- **The popper's initial invariant with declarations** (`invPopW_init`). -/
theorem invPopWD_init (hsz : ds.StrictSized) (htn : t ≠ n + 8) (hQ : StartPopWD ds t sQ)
    (hT0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨t, 8⟩ = 0) :
    (popRuleWD hsz (tP t n) (tLocs_tP htn) n).Inv True (Config.init [sP, sQ] initMem)
      (tRes (Config.init [sP, sQ] initMem).mem (tP t n) 1) (ghost₀ (tP t n)) := by
  have hL := tLocs_tP htn
  obtain ⟨he, hds, hpc, hend, hx0, hdt, hd4⟩ := hQ
  have hPp : Pp (tP t n) (σInit (Config.init [sP, sQ] initMem)
      (tRes (Config.init [sP, sQ] initMem).mem (tP t n) 1) (ghost₀ (tP t n))) := by
    refine ⟨ghost₀_gw _, ?_⟩
    have htt := hL.top_t
    simp only [σInit, tRes, popRes, Res.initOf, Perm.init, popFrac]
    simp [Ne.symm htt, Views.getFwd]
    exact ⟨by grind, hT0⟩
  refine invGFCMD_init (s := sQ) rfl rfl ⟨he, hds, hend, ?_⟩
  rw [show sQ.st = (sQ.st.1, labT "popper") from Prod.ext rfl hpc]
  exact Safely.uncountA (popperW_envGC t n ⟨t, 1⟩ hL _ (_, 0) ⟨hx0, hdt, hd4, .inl ⟨rfl, hPp⟩⟩)

end Start

/-- **The `NPSafeF` side with declarations.** -/
theorem treiber_whole_npSafeFD (l : _root_.Layout) [Executable.ValidLayout (l treiberImageA)] {ds : Decls}
    (hsz : ds.StrictSized) {t n : BitVec 64} (htn : t ≠ n + 8) {sP sQ : isa.State} {initMem : List (Loc × Val)}
    (hP : StartPushWD (layout := l) ds t n sP) (hQ : StartPopWD (layout := l) ds t sQ)
    (hT0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨t, 8⟩ = 0) :
    ∀ tid, tid < [sP, sQ].length → ∀ k j, NPSafeF (model isa) Arch.armv8 (TB (tP t n) n) tid k j True
      (Config.init [sP, sQ] initMem) (tRes (Config.init [sP, sQ] initMem).mem (tP t n) tid) (ghost₀ (tP t n)) := by
  intro tid htid k j
  rcases tid with _ | _ | i
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invPushWD_init (layout := l) hsz htn hP)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invPopWD_init (layout := l) hsz htn hQ hT0)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- **The purity specifications hold at the start states with
declarations** (`treiberPureSpecW_init`). -/
theorem treiberPureSpecW_initD (l : _root_.Layout) [Executable.ValidLayout (l treiberImageA)] {ds : Decls}
    {rel : Loc → Pred} {t n : BitVec 64} (hd : ∀ v : Val, Pred.Pure (rel ⟨n, 4⟩) v)
    (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v) {sP sQ : isa.State} (hP : StartPushWD (layout := l) ds t n sP)
    (hQ : StartPopWD (layout := l) ds t sQ) :
    ∀ tid s, [sP, sQ][tid]? = some s → (treiberPureSpecW l rel tid).HoldsD ds s
  | 0, s, hs => by
    cases hs
    obtain ⟨he, hds, hpc, hend, hx0, hx1, -, hdt, hdd, hdn⟩ := hP
    refine ⟨he, hend, hds, ?_⟩
    rw [show sP.st = (sP.st.1, labT (layout := l) "pusher") from Prod.ext rfl hpc]
    exact Safely.uncountA (pusherW_relPure (layout := l) rel t n hd hn _ ((), 0)
      ⟨hx0, hx1, hdt, hdd, hdn, .inl rfl⟩)
  | 1, s, hs => by
    cases hs
    obtain ⟨he, hds, hpc, hend, hx0, hdt, -⟩ := hQ
    refine ⟨he, hend, hds, ?_⟩
    rw [show sQ.st = (sQ.st.1, labT (layout := l) "popper") from Prod.ext rfl hpc]
    exact Safely.uncountA (popperW_relPure (layout := l) rel t _ ((), 0) ⟨hx0, hdt, .inl rfl⟩)
  | _ + 2, _, hs => by cases hs

/-- **The Treiber stack `treiber_pp.kl` for AArch64, both threads running
the whole `.kl` image, with the runner's declarations**:
`treiber_pp_envG_whole` for threads whose declarations are strict sized
(`ds.StrictSized`: the `.kl` runner's, from the typed header). -/
theorem treiber_pp_envG_runner {fuel : Nat} (l : _root_.Layout) [Executable.ValidLayout (l treiberImageA)]
    {ds : Decls} (hsz : ds.StrictSized) (t n : BitVec 64) (htn : t ≠ n + 8) {sP sQ : isa.State}
    {initMem : List (Loc × Val)} (hP : StartPushWD (layout := l) ds t n sP) (hQ : StartPopWD (layout := l) ds t sQ)
    (hT0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨t, 8⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [sP, sQ] initMem) cfg)
    (hf : cfg.final = true) :
    ∃ th, cfg.threads[1]? = some th ∧ th.st.st.1.regs.X10.toBitVec = n ∧ th.st.st.1.regs.X11.toBitVec = 1 := by
  have hL := tLocs_tP htn
  refine final_of_relPureSafelyFD Arch.armv8 fuel (B := TB (tP t n) n) (Φ := PopperFinal n)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_init hL _) (ghost₀_pend _) (treiberPureSpecW l _) (fun _ => ds)
    (fun _ => hsz) (fun tid => by cases tid <;> exact treiberImageA_noPairs (layout := l))
    (treiberPureSpecW_initD l (fun v => ?_) (fun v => ?_) hP hQ) (treiber_whole_npSafeFD l hsz htn hP hQ hT0) hc hf
    fun rF' g' E' _ hsize hB => ?_
  · show Pred.Pure ((ghost₀ (tP t n)).rel (tP t n).n1d) v
    rw [ghost₀_rel_ne (Ne.symm hL.top_d)]; exact Pred.emp_pure v
  · show Pred.Pure ((ghost₀ (tP t n)).rel (tP t n).n1n) v
    rw [ghost₀_rel_ne (Ne.symm hL.top_n)]; exact Pred.emp_pure v
  have h0 : (0 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have h1 : (1 : Nat) < cfg.threads.size := by rw [hsize]; simp
  rcases hB 1 (Config.final_done hf h1) with hfin | hq1
  · exact hfin
  rcases hB 0 (Config.final_done hf h0) with hfin | hq0
  · exact hfin
  have := E'.q_add_le_one h0 h1 (by decide) (tP t n).top
  exfalso
  grind

/-! ## The runner's configuration -/

open Kraken.Promising.SLR.EnvG.ConcreteTreiber

/-- The runner's declarations for the typed `treiber_pp.kl`: `top` an
8-byte word, `n1` a 4-byte word (strict). -/
def treiberDeclsD : Decls := { locs := [⟨topAddr, 8⟩, ⟨n1Addr, 4⟩], unsizedDefault := false }

theorem treiberDeclsD_sized : treiberDeclsD.StrictSized := ⟨rfl, by decide⟩

/-- The threads as the runner prepares them, declarations included. -/
def pusherWD0 : AArch64.State := { pusherW0 with decls := treiberDeclsD }
def popperWD1 : AArch64.State := { popperW1 with decls := treiberDeclsD }

/-- The runner's configuration is `Config.init [pusherWD0, popperWD1]
treiberInitMem` in everything the theorem reads (declarations and initial
memory included). -/
def runnerMatchesWD (src : String) : Bool := A64Whole.runnerIsD src [pusherWD0, popperWD1] treiberInitMem

/-- info: true -/
#guard_msgs in
#eval runnerMatchesWD treiberPpKl

section
attribute [local instance] wLayoutT

set_option maxRecDepth 8192 in
theorem pusherWD0_start : StartPushWD treiberDeclsD topAddr n1Addr pusherWD0 := by
  refine ⟨rfl, rfl, ?_, ?_, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · show (0x100000 : Int64) = labT "pusher"; rw [labT_at 0]; decide
  · show (0x100000 + 32 : Int64) = labT "pdone"; rw [labT_at 10]; decide
  all_goals simp [pusherWD0, pusherW0, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ, topAddr, n1Addr]

set_option maxRecDepth 8192 in
theorem popperWD1_start : StartPopWD treiberDeclsD topAddr popperWD1 := by
  refine ⟨rfl, rfl, ?_, ?_, by decide, ?_, fun a => ?_⟩
  · show (0x100000 + 36 : Int64) = labT "popper"; rw [labT_at 12]; decide
  · show (0x100000 + 76 : Int64) = labT "qdone"; rw [labT_at 23]; decide
  all_goals simp [popperWD1, popperW1, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ, topAddr]

end

/-- **`1:X10 = n1 ∧ 1:X11 = 1`** for `treiber_pp.kl` under `Arch.armv8`,
from the runner's exact configuration (the whole `code` block at `0x100000`,
the typed header's declarations and initial memory): concrete instance of
`treiber_pp_envG_runner`. -/
theorem treiber_pp_envG_runner_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [pusherWD0, popperWD1] treiberInitMem) c)
    (hf : c.final = true) :
    ∃ th, c.threads[1]? = some th ∧ th.st.st.1.regs.X10.toBitVec = n1Addr ∧ th.st.st.1.regs.X11.toBitVec = 1 :=
  treiber_pp_envG_runner wLayoutT treiberDeclsD_sized topAddr n1Addr (by decide) pusherWD0_start popperWD1_start
    (by simp only [Config.init]; decide) hc hf

end Kraken.Promising.SLR.EnvG.Treiber

#print axioms Kraken.Promising.SLR.EnvG.Treiber.treiber_pp_envG_runner
#print axioms Kraken.Promising.SLR.EnvG.Treiber.treiber_pp_envG_runner_concrete
