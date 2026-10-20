/-
Part 10: **the Treiber stack `treiber_pp.kl`, end to
end** (on the claim-conditional environment with failing release RMWs):
`treiber_pp_envG`, the `.kl`'s property `1:X10=n1 ∧ 1:X11=1` at every final
configuration reachable under `Arch.armv8`, for all layouts.

- **Parameters** (`tP`): `top = ⟨t, 8⟩`, `n1d = ⟨n, 4⟩`, `n1n = ⟨n + 8, 8⟩`,
  the ghost token `⟨t, 1⟩` (never accessed); `TLocs` from `t ≠ n + 8`
  (`tLocs_tP`).
- **Shared postcondition** (`TB`): the popper's final registers
  (`PopperFinal`) or more than half of `top`. The pusher keeps two thirds of
  `top` (`Pd`), the popper reaches `PopperFinal` under the clean flag; two
  threads with more than half of `top` contradict erasure
  (`Erase.q_add_le_one`).
- **Rules**: `ThreadRuleRXF.ofSafelyEnvGFC` from `pusher_envGC` /
  `popper_envGC` (`EnvG/TreiberVCGen.lean`), with `Phase1TreeF`; no-fault by
  `noFaultRuleF_ofSafelyEnvGFC_struct` (`DirsNoFault`), unconditional in the
  threads' promises.
- **Start**: `invGFC_init` at `σInit` with `tRes`/`ghost₀`
  (`EnvG/TreiberGhost.lean`), `QA64C` by `qa64C_of_partialTripleEnv`.
- **Assembly**: `final_of_relPureSafelyF` (`EnvG/A64RmwFailFinal.lean`;
  Theorem 1′ `theorem1FChain`), purity `treiberPureSpec_init`
  (`EnvG/TreiberRelPure.lean`), initial erasure `erase_init`.
-/
import Kraken.Promising.SLR.EnvG.TreiberVCGen
import Kraken.Promising.SLR.EnvG.TreiberRelPure
import Kraken.Promising.SLR.EnvG.A64RmwFailFinal

namespace Kraken.Promising.SLR.EnvG.Treiber

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG

/-! ## Parameters and the shared postcondition -/

/-- The parameters of `treiber_pp.kl` at `top = t`, `n1 = n`, with the ghost
token `⟨t, 1⟩`. -/
abbrev tP (t n : BitVec 64) : Params := tParams t n ⟨t, 1⟩

theorem tLocs_tP {t n : BitVec 64} (htn : t ≠ n + 8) : TLocs (tP t n) where
  top_d := by simp [tParams]
  top_n := by simp only [tParams, ne_eq, Loc.mk.injEq, and_true]; exact htn
  top_t := by simp [tParams]
  d_n := by simp [tParams]
  d_t := by simp [tParams]
  n_t := by simp [tParams]

/-- **The `.kl`'s property**: thread `1` has `X10 = n` and `X11 = 1`. -/
def PopperFinal (n : BitVec 64) (c : Config isa) : Prop :=
  ∃ th, c.threads[1]? = some th ∧ th.st.st.1.regs.X10.toBitVec = n ∧ th.st.st.1.regs.X11.toBitVec = 1

/-- **The shared postcondition**: the popper's result, or more than half of
`top` (the pusher's). -/
def TB (P : Params) (n : BitVec 64) (c : Config isa) (r : Res) (_ : Ghost) : Prop :=
  PopperFinal n c ∨ 1 / 2 < (r.wr P.top).q

/-! ## The rules -/

section Pusher

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiberPusher)]

/-- The pusher's postcondition: the end of its text and `Pd`. -/
abbrev postPush (P : Params) : MachineState × EStateA → Prop := postOf treiberPusher fun _ σ => ∃ _ : Nat, Pd P σ

omit [Executable.ValidLayout (layout treiberPusher)] in
/-- **`hB` for the pusher**: it keeps more than half of `top`. -/
theorem hB_push (P : Params) (n : BitVec 64) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postPush P (t.st.st, σ) → t.prom = [] → EnvRel 0 (pushPlan P) σ c t r g cl → cl → TB P n c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, -, hPd⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inr hPd.2
  · rw [hp] at hts; cases hts

/-- **The pusher's rule** (thread `0`). -/
noncomputable def pushRule (P : Params) (hL : TLocs P) (n : BitVec 64) : ThreadRuleRXF (I := isa) Arch.armv8 (TB P n) 0 :=
  ThreadRuleRXF.ofSafelyEnvGFC (post := postPush P) (pushPlan_valid hL) treiberPusher_rmwLive treiberPusher_phase1F
    postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_push P n)

/-- **The pusher's rule excludes faults** (unconditional in promises). -/
theorem pushRule_noFault (P : Params) (hL : TLocs P) (n : BitVec 64) : NoFaultRuleF (pushRule P hL n) :=
  noFaultRuleF_ofSafelyEnvGFC_struct _ _ _ _ _ _ treiberPusher_noFault

end Pusher

section Popper

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiberPopper)]

/-- The popper's postcondition: the end of its text and, under the clean
flag, its registers. -/
abbrev postPop (n : BitVec 64) : MachineState × EStateA → Prop :=
  postOf treiberPopper fun s σ => ∃ _ : Nat, σ.cl → s.regs.X10.toBitVec = n ∧ s.regs.X11.toBitVec = 1

omit [Executable.ValidLayout (layout treiberPopper)] in
/-- **`hB` for the popper**: its registers under the clean flag. -/
theorem hB_pop (P : Params) (n : BitVec 64) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postPop n (t.st.st, σ) → t.prom = [] → EnvRel 1 (popPlan P) σ c t r g cl → cl → TB P n c r g := by
  rintro c t r g cl σ hpost - hrel hcl
  obtain ⟨-, -, hq⟩ := hpost.resolve_right id
  obtain ⟨h10, h11⟩ := hq (hrel.cl hcl)
  exact .inl ⟨t, hrel.ht, h10, h11⟩

/-- **The popper's rule** (thread `1`). -/
noncomputable def popRule (P : Params) (hL : TLocs P) (n : BitVec 64) : ThreadRuleRXF (I := isa) Arch.armv8 (TB P n) 1 :=
  ThreadRuleRXF.ofSafelyEnvGFC (post := postPop n) (popPlan_valid hL) treiberPopper_rmwLive treiberPopper_phase1F
    postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_pop P n)

/-- **The popper's rule excludes faults** (unconditional in promises). -/
theorem popRule_noFault (P : Params) (hL : TLocs P) (n : BitVec 64) : NoFaultRuleF (popRule P hL n) :=
  noFaultRuleF_ofSafelyEnvGFC_struct _ _ _ _ _ _ treiberPopper_noFault

end Popper

/-! ## The start -/

section Start

variable [layout : _root_.Layout] {t n : BitVec 64} {sP sQ : isa.State} {initMem : List (Loc × Val)}

/-- **The pusher's initial invariant** (thread `0`). -/
theorem invPush_init [Executable.ValidLayout (layout treiberPusher)] (htn : t ≠ n + 8) (hP : StartPush t n sP) :
    (pushRule (tP t n) (tLocs_tP htn) n).Inv True (Config.init [sP, sQ] initMem)
      (tRes (Config.init [sP, sQ] initMem).mem (tP t n) 0) (ghost₀ (tP t n)) := by
  letI : CodeEnv := ⟨layout treiberPusher⟩
  have hL := tLocs_tP htn
  refine invGFC_init (s := sP) rfl rfl (qa64C_of_partialTripleEnv (pusher_envGC t n ⟨t, 1⟩ hL).uncount rfl hP.exe
    hP.decls hP.endPc hP.pc ⟨0, hP.x0, hP.x1, hP.dt, hP.dd, hP.dn, hP.x9, ghost₀_gw _, ?_⟩)
  have htd := hL.top_d; have htn' := hL.top_n; have hdn := hL.d_n
  simp only [σInit, tRes, ↓reduceIte, pushRes, Res.initOf, Perm.init, pushFrac]
  simp only [Ne.symm htd, Ne.symm htn', ↓reduceIte, true_or, or_true, true_and]
  refine ⟨by grind, fun p hp => by rw [hp.2]⟩

/-- **The popper's initial invariant** (thread `1`). -/
theorem invPop_init [Executable.ValidLayout (layout treiberPopper)] (htn : t ≠ n + 8) (hQ : StartPop t sQ)
    (hT0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨t, 8⟩ = 0) :
    (popRule (tP t n) (tLocs_tP htn) n).Inv True (Config.init [sP, sQ] initMem)
      (tRes (Config.init [sP, sQ] initMem).mem (tP t n) 1) (ghost₀ (tP t n)) := by
  letI : CodeEnv := ⟨layout treiberPopper⟩
  have hL := tLocs_tP htn
  refine invGFC_init (s := sQ) rfl rfl (qa64C_of_partialTripleEnv (popper_envGC t n ⟨t, 1⟩ hL).uncount rfl hQ.exe
    hQ.decls hQ.endPc hQ.pc ⟨0, hQ.x0, hQ.dt, hQ.d4, ghost₀_gw _, ?_⟩)
  have htt := hL.top_t
  simp only [σInit, tRes, popRes, Res.initOf, Perm.init, popFrac]
  simp [Ne.symm htt, Views.getFwd]
  exact ⟨by grind, hT0⟩

end Start

/-! ## `NPSafeF` and the theorem -/

/-- **The `NPSafeF` side of Theorem 1′ for `treiber_pp`**: both threads at the
initial configuration, through their rules. -/
theorem treiber_npSafeF (lP lQ : _root_.Layout) [Executable.ValidLayout (lP treiberPusher)]
    [Executable.ValidLayout (lQ treiberPopper)] {t n : BitVec 64} (htn : t ≠ n + 8) {sP sQ : isa.State}
    {initMem : List (Loc × Val)} (hP : StartPush (layout := lP) t n sP) (hQ : StartPop (layout := lQ) t sQ)
    (hT0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨t, 8⟩ = 0) :
    ∀ tid, tid < [sP, sQ].length → ∀ k j, NPSafeF (model isa) Arch.armv8 (TB (tP t n) n) tid k j True
      (Config.init [sP, sQ] initMem) (tRes (Config.init [sP, sQ] initMem).mem (tP t n) tid) (ghost₀ (tP t n)) := by
  intro tid htid k j
  rcases tid with _ | _ | i
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invPush_init (layout := lP) htn hP)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invPop_init (layout := lQ) htn hQ hT0)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- **The Treiber stack `treiber_pp.kl` for AArch64 under `Arch.armv8`, on
`EnvGC` with failing release RMWs**: for all layouts `lP` of the pusher and
`lQ` of the popper, all addresses `t` of `top` (8 bytes) and `n` of the node
(data word `[n]`, 4 bytes; link word `[n + 8]`, 8 bytes) with `t ≠ n + 8`: if
thread `0` starts the pusher with `x0 = t`, `x1 = n`, `w9 = 1` and thread `1`
the popper with `x0 = t` (`StartPush`, `StartPop`), and `top` is initially
`0`, then every final configuration reachable under `Arch.armv8` has the
popper's `X10 = n` and `X11 = 1` (the `.kl`'s `forall (1:X10=n1 /\ 1:X11=1)`).

The `.kl`'s threads share one code block; here they are split per thread
(`treiberPusher`, `treiberPopper`, each with its own layout). Only the
addresses' `Loc`s are distinguished (`t ≠ n + 8`): the model's mixed-size gap
as in `swpl_counter_envG`'s `hdisj`. -/
theorem treiber_pp_envG {fuel : Nat} (lP lQ : _root_.Layout) [Executable.ValidLayout (lP treiberPusher)]
    [Executable.ValidLayout (lQ treiberPopper)] (t n : BitVec 64) (htn : t ≠ n + 8) {sP sQ : isa.State}
    {initMem : List (Loc × Val)} (hP : StartPush (layout := lP) t n sP) (hQ : StartPop (layout := lQ) t sQ)
    (hT0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨t, 8⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [sP, sQ] initMem) cfg)
    (hf : cfg.final = true) :
    ∃ th, cfg.threads[1]? = some th ∧ th.st.st.1.regs.X10.toBitVec = n ∧ th.st.st.1.regs.X11.toBitVec = 1 := by
  have hL := tLocs_tP htn
  refine final_of_relPureSafelyF Arch.armv8 fuel (B := TB (tP t n) n) (Φ := PopperFinal n)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_init hL _) (ghost₀_pend _) (treiberPureSpec lP lQ _)
    (treiberPureSpec_init lP lQ (fun v => ?_) (fun v => ?_) hP hQ) (treiber_npSafeF lP lQ htn hP hQ hT0) hc hf
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

end Kraken.Promising.SLR.EnvG.Treiber
