/-
**Part 7: the x64 Treiber stack
`LockFree/X64/treiber_pp.kl`, end to end** (on the claim-conditional
environment with failing release RMWs): `x64_treiber_pp_envG`, the `.kl`'s
property `1:r10=n1 ∧ 1:r11=1` at every final configuration reachable under
`Arch.tso`, for all layouts. The x64 counterpart of the Treiber proof's
`EnvG/TreiberPublic.lean` (`treiber_pp_envG`).

- **Parameters** (`tPX`): `top = ⟨t, 8⟩`, `n1d = ⟨n, 4⟩`, `n1n = ⟨n + 8, 8⟩`,
  the ghost token `⟨t, 1⟩` (never accessed); `TLocs` from `t ≠ n + 8`
  (`tLocs_tPX`, from the neutral `tLocs_tParamsC`). The ghost, plans and erasure
  are the Treiber proof's ISA-neutral
  `EnvG/TreiberGhost.lean`, unchanged.
- **Shared postcondition** (`TBX`): the popper's final registers
  (`PopperFinalX`) or more than half of `top`, as in `TB`.
- **Rules**: `ThreadRuleRXF.ofSafelyEnvGFCX` (`EnvG/X64RmwFailGhost.lean`)
  from `pusherX_envGC` / `popperX_envGC` (`EnvG/X64TreiberVCGen.lean`), with
  `Phase1TreeFX`; the pusher's layout is `pushS t n`, the popper's `sAll`
  (its loads at `rax` are at a loaded address). No-fault by
  `noFaultRuleF_ofSafelyEnvGFCX_struct` (`DirsNoFault`), unconditional in the
  threads' promises.
- **Start**: `invGFCX_init` at `σInitX` with `tRes`/`ghost₀`, `QX64C` by
  `qx64C_of_partialTripleEnv`. The popper starts with a private memory that
  maps no byte (`StartPopX.dmem`), so `Split sAll` holds.
- **Assembly**: `CmpxPublic.final_of_relPureSafelyQX_tsoF'` (Theorem 1′ by
  `theorem1FChain`), the all-release specifications `treiberNoNTSpecX_init`
  (`EnvG/X64TreiberRelPure.lean`; vacuous on `Arch.tso`), initial erasure
  `erase_init`.
-/
import Kraken.Promising.SLR.EnvG.X64TreiberVCGen
import Kraken.Promising.SLR.EnvG.X64TreiberRelPure
import Kraken.Promising.SLR.EnvG.X64RmwFailGhost

namespace Kraken.Promising.X64.EnvG.TreiberX

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.EnvG.Treiber Kraken.Promising.SLR.EnvG.TreiberCommon

/-! ## Parameters and the shared postcondition -/

/-- The parameters of the x64 `treiber_pp.kl` at `top = t`, `n1 = n`, with
the ghost token `⟨t, 1⟩`. -/
abbrev tPX (t n : BitVec 64) : Params := tParamsX t n ⟨t, 1⟩

theorem tLocs_tPX {t n : BitVec 64} (htn : t ≠ n + 8) : TLocs (tPX t n) :=
  tLocs_tParamsC htn

/-- **The `.kl`'s property**: thread `1` has `r10 = n` and `r11d = 1`. -/
def PopperFinalX (n : BitVec 64) (c : Config isa) : Prop :=
  ∃ th, c.threads[1]? = some th ∧ th.st.st.1.regs.get64 .r10 = n ∧
    BitVec.setWidth 32 (th.st.st.1.regs.get64 .r11) = 1

/-- **The shared postcondition**: the popper's result, or more than half of
`top` (the pusher's). -/
def TBX (P : Params) (n : BitVec 64) (c : Config isa) (r : Res) (_ : Ghost) : Prop :=
  PopperFinalX n c ∨ 1 / 2 < (r.wr P.top).q

/-! ## The rules -/

section Pusher

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiberPusherX)]

/-- The pusher's postcondition: the end of its text and `Pd`. -/
abbrev postPushX (P : Params) : MachineState × EStateX → Prop :=
  postOfX treiberPusherX fun _ σ => ∃ _ : Nat, Pd P σ

omit [Executable.ValidLayout (layout treiberPusherX)] in
/-- **`hB` for the pusher**: it keeps more than half of `top`. -/
theorem hB_pushX (P : Params) (n : BitVec 64) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postPushX P (t.st.st, σ) → t.prom = [] → EnvRel 0 (pushPlan P) σ c t r g cl → cl → TBX P n c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, -, hPd⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inr hPd.2
  · rw [hp] at hts; cases hts

/-- **The x64 pusher's rule** (thread `0`, layout `pushS t n`). -/
noncomputable def pushRuleX (t n : BitVec 64) (hL : TLocs (tPX t n)) :
    ThreadRuleRXF (I := isa) Arch.tso (TBX (tPX t n) n) 0 :=
  ThreadRuleRXF.ofSafelyEnvGFCX (S := pushS t n) (post := postPushX (tPX t n)) (pushPlan_valid hL)
    (pushS_le16 t n) treiberPusherX_phase1FX postOfX_end (not_instrStepEnv_of_end_labels _ 1) (hB_pushX _ n)

/-- **The x64 pusher's rule excludes faults** (unconditional in promises). -/
theorem pushRuleX_noFault (t n : BitVec 64) (hL : TLocs (tPX t n)) : NoFaultRuleF (pushRuleX t n hL) :=
  noFaultRuleF_ofSafelyEnvGFCX_struct _ _ _ _ _ _ treiberPusherX_noFault

end Pusher

section Popper

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiberPopperX)]

/-- The popper's postcondition: the end of its text and, under the clean
flag, its registers. -/
abbrev postPopX (n : BitVec 64) : MachineState × EStateX → Prop :=
  postOfX treiberPopperX fun s σ => ∃ _ : Nat, PopPostX n s σ.cl

omit [Executable.ValidLayout (layout treiberPopperX)] in
/-- **`hB` for the popper**: its registers under the clean flag. -/
theorem hB_popX (P : Params) (n : BitVec 64) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postPopX n (t.st.st, σ) → t.prom = [] → EnvRel 1 (popPlan P) σ c t r g cl → cl → TBX P n c r g := by
  rintro c t r g cl σ hpost - hrel hcl
  obtain ⟨-, -, hq⟩ := hpost.resolve_right id
  obtain ⟨h10, h11⟩ := hq (hrel.cl hcl)
  exact .inl ⟨t, hrel.ht, h10, h11⟩

/-- **The x64 popper's rule** (thread `1`, layout `sAll`). -/
noncomputable def popRuleX (t n : BitVec 64) (hL : TLocs (tPX t n)) :
    ThreadRuleRXF (I := isa) Arch.tso (TBX (tPX t n) n) 1 :=
  ThreadRuleRXF.ofSafelyEnvGFCX (S := sAll) (post := postPopX n) (popPlan_valid hL) sAll_le16
    treiberPopperX_phase1FX postOfX_end (not_instrStepEnv_of_end_labels _ 1) (hB_popX _ n)

/-- **The x64 popper's rule excludes faults** (unconditional in promises). -/
theorem popRuleX_noFault (t n : BitVec 64) (hL : TLocs (tPX t n)) : NoFaultRuleF (popRuleX t n hL) :=
  noFaultRuleF_ofSafelyEnvGFCX_struct _ _ _ _ _ _ treiberPopperX_noFault

end Popper

/-! ## The start -/

section Start

variable [layout : _root_.Layout] {t n : BitVec 64} {sP sQ : isa.State} {initMem : List (Loc × Val)}

/-- **The x64 pusher's initial invariant** (thread `0`). -/
theorem invPushX_init [Executable.ValidLayout (layout treiberPusherX)] (htn : t ≠ n + 8) (hP : StartPushX t n sP) :
    (pushRuleX t n (tLocs_tPX htn)).Inv True (Config.init [sP, sQ] initMem)
      (tRes (Config.init [sP, sQ] initMem).mem (tPX t n) 0) (ghost₀ (tPX t n)) := by
  letI : CodeEnv := ⟨layout treiberPusherX⟩
  have hL := tLocs_tPX htn
  refine invGFCX_init (s := sP) rfl rfl (qx64C_of_partialTripleEnv (pusherX_envGC t n ⟨t, 1⟩ hL).uncount rfl
    hP.exe hP.decls hP.endPc hP.pc hP.split ⟨0, hP.frame, ghost₀_gw _, ?_⟩)
  have htd := hL.top_d; have htn' := hL.top_n; have hdn := hL.d_n
  simp only [σInitX, tRes, ↓reduceIte, pushRes, Res.initOf, Perm.init, pushFrac]
  simp only [Ne.symm htd, Ne.symm htn', ↓reduceIte, true_or, or_true, true_and]
  refine ⟨by grind, fun p hp => by rw [hp.2]⟩

/-- **The x64 popper's initial invariant** (thread `1`). -/
theorem invPopX_init [Executable.ValidLayout (layout treiberPopperX)] (htn : t ≠ n + 8) (hQ : StartPopX t sQ)
    (hT0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨t, 8⟩ = 0) :
    (popRuleX t n (tLocs_tPX htn)).Inv True (Config.init [sP, sQ] initMem)
      (tRes (Config.init [sP, sQ] initMem).mem (tPX t n) 1) (ghost₀ (tPX t n)) := by
  letI : CodeEnv := ⟨layout treiberPopperX⟩
  have hL := tLocs_tPX htn
  refine invGFCX_init (s := sQ) rfl rfl (qx64C_of_partialTripleEnv (popperX_envGC t n ⟨t, 1⟩ hL).uncount rfl
    hQ.exe hQ.decls hQ.endPc hQ.pc hQ.split ⟨0, hQ.frame, ghost₀_gw _, ?_⟩)
  have htt := hL.top_t
  simp only [σInitX, tRes, popRes, Res.initOf, Perm.init, popFrac]
  simp [Ne.symm htt, Views.getFwd]
  exact ⟨by grind, hT0⟩

end Start

/-! ## `NPSafeF` and the theorem -/

/-- **The `NPSafeF` side of Theorem 1′ for the x64 `treiber_pp`**: both
threads at the initial configuration, through their rules. -/
theorem treiberX_npSafeF (lP lQ : _root_.Layout) [Executable.ValidLayout (lP treiberPusherX)]
    [Executable.ValidLayout (lQ treiberPopperX)] {t n : BitVec 64} (htn : t ≠ n + 8) {sP sQ : isa.State}
    {initMem : List (Loc × Val)} (hP : StartPushX (layout := lP) t n sP) (hQ : StartPopX (layout := lQ) t sQ)
    (hT0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨t, 8⟩ = 0) :
    ∀ tid, tid < [sP, sQ].length → ∀ k j, NPSafeF (model isa) Arch.tso (TBX (tPX t n) n) tid k j True
      (Config.init [sP, sQ] initMem) (tRes (Config.init [sP, sQ] initMem).mem (tPX t n) tid) (ghost₀ (tPX t n)) := by
  intro tid htid k j
  rcases tid with _ | _ | i
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invPushX_init (layout := lP) htn hP)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invPopX_init (layout := lQ) htn hQ hT0)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- **The Treiber stack `LockFree/X64/treiber_pp.kl` for x64 under
`Arch.tso`, on `EnvGC` with failing release RMWs**: for all layouts `lP` of
the pusher and `lQ` of the popper, all addresses `t` of `top` (8 bytes) and
`n` of the node (data word `[n]`, 4 bytes; link word `[n + 8]`, 8 bytes) with
`t ≠ n + 8`: if thread `0` starts the pusher with `%rdi = t`, `%rbx = n`
and neither `top` nor the node's words in its private memory
(`StartPushX`), thread `1` starts the popper with `%rdi = t` and an empty
private memory (`StartPopX`), and `top` is initially `0`, then every final
configuration reachable under `Arch.tso` has the popper's `r10 = n` and
`r11d = 1` (the `.kl`'s `forall (1:r10=n1 /\ 1:r11=1)`).

The `.kl`'s threads share one code block; here they are split per thread
(`treiberPusherX`, `treiberPopperX`, each with its own layout). Only the
addresses' `Loc`s are distinguished (`t ≠ n + 8`): the model's mixed-size gap
as in `treiber_pp_envG`. The popper's empty private memory is the price of
its layout `sAll` (x64 environments check every access against the layout,
also outside the clean flag, and the popper's `rax`-relative loads are at a
loaded address). -/
theorem x64_treiber_pp_envG {fuel : Nat} (lP lQ : _root_.Layout) [Executable.ValidLayout (lP treiberPusherX)]
    [Executable.ValidLayout (lQ treiberPopperX)] (t n : BitVec 64) (htn : t ≠ n + 8) {sP sQ : isa.State}
    {initMem : List (Loc × Val)} (hP : StartPushX (layout := lP) t n sP) (hQ : StartPopX (layout := lQ) t sQ)
    (hT0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨t, 8⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [sP, sQ] initMem) cfg)
    (hf : cfg.final = true) :
    ∃ th, cfg.threads[1]? = some th ∧ th.st.st.1.regs.get64 .r10 = n ∧
      BitVec.setWidth 32 (th.st.st.1.regs.get64 .r11) = 1 := by
  have hL := tLocs_tPX htn
  refine CmpxPublic.final_of_relPureSafelyQX_tsoF' (B := TBX (tPX t n) n) (Φ := PopperFinalX n)
    (erase_init hL _) (ghost₀_pend _) (treiberNoNTSpecX lP lQ t n) (treiberNoNTSpecX_init lP lQ hP hQ)
    (treiberX_npSafeF lP lQ htn hP hQ hT0) hc hf fun rF' g' E' _ hsize hB => ?_
  have h0 : (0 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have h1 : (1 : Nat) < cfg.threads.size := by rw [hsize]; simp
  rcases hB 1 (Config.final_done hf h1) with hfin | hq1
  · exact hfin
  rcases hB 0 (Config.final_done hf h0) with hfin | hq0
  · exact hfin
  have := E'.q_add_le_one h0 h1 (by decide) (tPX t n).top
  exfalso
  grind

end Kraken.Promising.X64.EnvG.TreiberX

#print axioms Kraken.Promising.X64.EnvG.TreiberX.x64_treiber_pp_envG
#print axioms Kraken.Promising.X64.EnvG.TreiberX.pushRuleX_noFault
#print axioms Kraken.Promising.X64.EnvG.TreiberX.popRuleX_noFault
