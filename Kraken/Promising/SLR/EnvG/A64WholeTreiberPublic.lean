/-
**`treiber_pp.kl` whole image, part 2: the Treiber
stack with both threads running the whole `.kl` image** (under
`Arch.armv8`, on `EnvGC` with failing release RMWs). Additive:
`Treiber.treiber_pp_envG` (`EnvG/TreiberPublic.lean`) is unchanged.

**`treiber_pp_envG_whole`**: `treiber_pp_envG`'s conclusion (at every
reachable final configuration the popper has `X10 = n` and `X11 = 1`), with
both threads' executable the whole `code` block `treiberImageA` under one
layout, the pusher from `pusher` to `pdone`, the popper from `popper` to
`qdone` (as `Kraken.Litmus.AArch64.prepareProgram` sets them up). This
resolves `treiber_pp_envG`'s per-thread-image deviation.

- **Pusher**: `ThreadRuleRXF.ofSafelyEnvGFCM` (`EnvG/A64MaskLink.lean`) over
  the mask `treiberImageP` (the dead `NOP` behind `pdone:` and the popper's
  code masked): the shape `treiberImageP_phase1F` and the halt
  `pushP_stuck` of the mask, the static check and fault-freedom of the
  image.
- **Popper**: the same link at the trivial mask (`MaskOf.refl`): its exit
  `qdone` ends the image (`popA_stuck`).
- **Final argument, ghost and resources**: the Treiber proof's (`TB`, `PopperFinal`,
  `tRes`, `ghost₀`, `erase_init`, the start-resource computations of
  `invPush_init`/`invPop_init`, `treiber_pp_envG`'s final step); the purity
  runs are `pusherW_relPure`/`popperW_relPure` in the image.
-/
import Kraken.Promising.SLR.EnvG.A64WholeTreiberVCGen
import Kraken.Promising.SLR.EnvG.TreiberPublic
import Kraken.Promising.SLR.EnvG.A64MaskHelpers

namespace Kraken.Promising.SLR.EnvG.Treiber

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

set_option linter.unusedSimpArgs false

/-! ## The image's static facts -/

/-- Every cell of the image is phase-1 with failing release RMWs
(`dirs_phase1F`'s script, for every ambient executable). -/
theorem treiberImageA_dirsPhase1F : ∀ d ∈ treiberImageA, ∀ (e : _root_.Executable) z, DirPhase1F e d z := by
  dirs_phase1F_any treiberImageA

-- `label_dirPhase1F_any`, `byteArray_dirPhase1F_any` (`EnvG/A64MaskHelpers.lean`) under their
-- the whole-image AArch64 proofs names.
hoist_alias [Kraken.Promising.AArch64.EnvG.label_dirPhase1F_any ↦ Kraken.Promising.SLR.EnvG.Treiber.label_dirPhase1F,
  Kraken.Promising.AArch64.EnvG.byteArray_dirPhase1F_any ↦ Kraken.Promising.SLR.EnvG.Treiber.byteArray_dirPhase1F]

section Static

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiberImageA)]

omit [Executable.ValidLayout (layout treiberImageA)] in
theorem treiberImageA_rmwLive : (layout treiberImageA).rmwLive = true := by rw [Layout.apply_rmwLive]; decide

/-- The image is phase-1 with failing release RMWs (both roles' code). -/
theorem treiberImageA_phase1F : Phase1TreeF (layout treiberImageA) :=
  phase1TreeF_of_dirs (dirsPhase1F_layout treiberImageA_dirsPhase1F)

/-- The pusher's mask is phase-1 with failing release RMWs. -/
theorem treiberImageP_phase1F : Phase1TreeF (layout treiberImageP) :=
  haveI := treiberImageP_valid (layout := layout)
  phase1TreeF_of_dirs (dirsPhase1F_layout (mem_maskKeep_range (Φd := fun d => ∀ e z, DirPhase1F e d z)
    (fun d hd => treiberImageA_dirsPhase1F d (List.mem_of_mem_drop (List.mem_of_mem_take hd)))
    (fun l => label_dirPhase1F l) (byteArray_dirPhase1F _)))

omit [Executable.ValidLayout (layout treiberImageA)] in
theorem treiberImageA_noFault : DirsNoFault (layout treiberImageA) := by dirs_no_fault' treiberImageA

/-! ## The halts -/

set_option maxRecDepth 8192 in
/-- `pdone`'s address is the pusher's mask's cell `11` (the masked `NOP`). -/
theorem labT_pdone : labT "pdone" = (layout treiberImageP).addrOf 11 := by
  have hd : labT "pdone" = (layout treiberImageA).addrOf 10 :=
    Program.label_addrOf_drop treiberImageA_wf.nodup (by decide) (by decide)
  have h10 : (layout treiberImageA).2[10]? = some (Directive.label "pdone", Kraken.Layout.size Directive 10) := by
    simp [Layout.apply_snd, Layout.frag, treiberImageA]
  rw [addrOf_mask treiberImageP_mask, Executable.addrOf_succ _ h10,
    Executable.ValidLayout.label_size 10 "pdone" _ h10, hd]
  simp

/-- **No step of the pusher's mask at its exit label `pdone`** (the guarded
exit: the image has the `NOP` there). -/
theorem pushP_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labT "pdone" → ¬ (layout treiberImageP).instrStepEnv env x R := by
  haveI := treiberImageP_valid (layout := layout)
  rw [labT_pdone]
  exact not_instrStepEnv_of_byteArray (i := 11) (b := .mk #[]) env treiberImageP_11

set_option maxRecDepth 8192 in
/-- `qdone`'s address is the end of the image. -/
theorem labT_qdone : labT "qdone" = (layout treiberImageA).addrOf treiberImageA.length := by
  have hd : labT "qdone" = (layout treiberImageA).addrOf 23 :=
    Program.label_addrOf_drop treiberImageA_wf.nodup (by decide) (by decide)
  have h23 : (layout treiberImageA).2[23]? = some (Directive.label "qdone", Kraken.Layout.size Directive 23) := by
    simp [Layout.apply_snd, Layout.frag, treiberImageA]
  rw [show treiberImageA.length = 23 + 1 from rfl, Executable.addrOf_succ _ h23,
    Executable.ValidLayout.label_size 23 "qdone" _ h23, hd]
  simp

/-- **No step of the image at the popper's exit label `qdone`.** -/
theorem popA_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labT "qdone" → ¬ (layout treiberImageA).instrStepEnv env x R := by
  rw [labT_qdone]
  exact not_instrStepEnv_of_end_labels env 1

end Static

/-! ## The rules -/

section Rules

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiberImageA)]

/-- The whole-image pusher's postcondition: its exit label and `Pd` (the
counter projected away). -/
abbrev postPushW (P : Params) : MachineState × EStateA → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labT "pdone" ∧ Pd P x.2) ∨ False

omit [Executable.ValidLayout (layout treiberImageA)] in
theorem postPushW_end (P : Params) : ∀ y, postPushW P y → y.1.2 = labT "pdone" :=
  fun _ ⟨_, h⟩ => h.elim And.left False.elim

omit [Executable.ValidLayout (layout treiberImageA)] in
/-- **`hB` for the whole-image pusher** (`hB_push`'s proof). -/
theorem hB_pushW (P : Params) (n : BitVec 64) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postPushW P (t.st.st, σ) → t.prom = [] → EnvRel 0 (pushPlan P) σ c t r g cl → cl → TB P n c r g := by
  rintro c t r g cl σ ⟨_, hpost⟩ hp hrel -
  obtain ⟨-, hPd⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inr hPd.2
  · rw [hp] at hts; cases hts

/-- **The whole-image pusher's rule** (thread `0`, over its mask). -/
noncomputable def pushRuleW (P : Params) (hL : TLocs P) (n : BitVec 64) :
    ThreadRuleRXF (I := isa) Arch.armv8 (TB P n) 0 :=
  ThreadRuleRXF.ofSafelyEnvGFCM (post := postPushW P) treiberImageP_mask (pushPlan_valid hL)
    treiberImageA_rmwLive treiberImageP_phase1F (postPushW_end P) (pushP_stuck _) (hB_pushW P n)

/-- **The whole-image pusher's rule excludes faults** (unconditional in
promises). -/
theorem pushRuleW_noFault (P : Params) (hL : TLocs P) (n : BitVec 64) : NoFaultRuleF (pushRuleW P hL n) :=
  noFaultRuleF_ofSafelyEnvGFCM _ _ _ _ _ _ _ treiberImageA_noFault

/-- The whole-image popper's postcondition: its exit label and, under the
clean flag, its registers. -/
abbrev postPopW (n : BitVec 64) : MachineState × EStateA → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labT "qdone" ∧
    (x.2.cl → x.1.1.regs.X10.toBitVec = n ∧ x.1.1.regs.X11.toBitVec = 1)) ∨ False

omit [Executable.ValidLayout (layout treiberImageA)] in
theorem postPopW_end (n : BitVec 64) : ∀ y, postPopW n y → y.1.2 = labT "qdone" :=
  fun _ ⟨_, h⟩ => h.elim And.left False.elim

omit [Executable.ValidLayout (layout treiberImageA)] in
/-- **`hB` for the whole-image popper** (`hB_pop`'s proof). -/
theorem hB_popW (P : Params) (n : BitVec 64) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postPopW n (t.st.st, σ) → t.prom = [] → EnvRel 1 (popPlan P) σ c t r g cl → cl → TB P n c r g := by
  rintro c t r g cl σ ⟨_, hpost⟩ - hrel hcl
  obtain ⟨-, hq⟩ := hpost.resolve_right id
  obtain ⟨h10, h11⟩ := hq (hrel.cl hcl)
  exact .inl ⟨t, hrel.ht, h10, h11⟩

/-- **The whole-image popper's rule** (thread `1`, the image itself as its
mask). -/
noncomputable def popRuleW (P : Params) (hL : TLocs P) (n : BitVec 64) :
    ThreadRuleRXF (I := isa) Arch.armv8 (TB P n) 1 :=
  ThreadRuleRXF.ofSafelyEnvGFCM (post := postPopW n) (MaskOf.refl _) (popPlan_valid hL)
    treiberImageA_rmwLive treiberImageA_phase1F (postPopW_end n) (popA_stuck _) (hB_popW P n)

/-- **The whole-image popper's rule excludes faults.** -/
theorem popRuleW_noFault (P : Params) (hL : TLocs P) (n : BitVec 64) : NoFaultRuleF (popRuleW P hL n) :=
  noFaultRuleF_ofSafelyEnvGFCM _ _ _ _ _ _ _ treiberImageA_noFault

end Rules

/-! ## The start -/

/-- **The pusher at its start in the whole image**, as the runner sets it up
(`0:X0=top; 0:X1=n1; 0:X9=1`): the image, no declarations, pc at `pusher`,
end at `pdone`, `x0 = t`, `x1 = n`, `w9 = 1`, and no private copy of `top`
or of the node's words (`StartPush` with the image). -/
structure StartPushW [layout : _root_.Layout] (t n : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout treiberImageA
  decls : s.decls = {}
  pc : s.st.2 = labT "pusher"
  endPc : s.endPc = labT "pdone"
  x0 : s.st.1.regs.X0.toBitVec = t
  x1 : s.st.1.regs.X1.toBitVec = n
  x9 : s.st.1.regs.X9.toBitVec.setWidth 32 = 1
  dt : Mem.loadInt s.st.1.dmem t 8 = none
  dd : Mem.loadInt s.st.1.dmem n 4 = none
  dn : Mem.loadInt s.st.1.dmem (n + 8) 8 = none

/-- **The popper at its start in the whole image** (`1:X0=top`): pc at
`popper`, end at `qdone`, `x0 = t`, no private copy of `top` or of any
4-byte word (`StartPop` with the image). -/
structure StartPopW [layout : _root_.Layout] (t : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout treiberImageA
  decls : s.decls = {}
  pc : s.st.2 = labT "popper"
  endPc : s.endPc = labT "qdone"
  x0 : s.st.1.regs.X0.toBitVec = t
  dt : Mem.loadInt s.st.1.dmem t 8 = none
  d4 : ∀ a, Mem.loadInt s.st.1.dmem a 4 = none

section Start

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiberImageA)] {t n : BitVec 64}
  {sP sQ : isa.State} {initMem : List (Loc × Val)}

/-- **The whole-image pusher's initial invariant** (thread `0`;
`invPush_init`'s resource computation). -/
theorem invPushW_init (htn : t ≠ n + 8) (hP : StartPushW t n sP) :
    (pushRuleW (tP t n) (tLocs_tP htn) n).Inv True (Config.init [sP, sQ] initMem)
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
  refine invGFCM_init (s := sP) rfl rfl ⟨he, hds, hend, ?_⟩
  rw [show sP.st = (sP.st.1, labT "pusher") from Prod.ext rfl hpc]
  exact Safely.uncountA (pusherW_envGC t n ⟨t, 1⟩ hL _ (_, 0) ⟨hx0, hx1, hdt, hdd, hdn, .inl ⟨rfl, hx9, hPu0⟩⟩)

/-- **The whole-image popper's initial invariant** (thread `1`;
`invPop_init`'s resource computation). -/
theorem invPopW_init (htn : t ≠ n + 8) (hQ : StartPopW t sQ)
    (hT0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨t, 8⟩ = 0) :
    (popRuleW (tP t n) (tLocs_tP htn) n).Inv True (Config.init [sP, sQ] initMem)
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
  refine invGFCM_init (s := sQ) rfl rfl ⟨he, hds, hend, ?_⟩
  rw [show sQ.st = (sQ.st.1, labT "popper") from Prod.ext rfl hpc]
  exact Safely.uncountA (popperW_envGC t n ⟨t, 1⟩ hL _ (_, 0) ⟨hx0, hdt, hd4, .inl ⟨rfl, hPp⟩⟩)

end Start

/-! ## `NPSafeF` -/

/-- **The `NPSafeF` side, whole image.** -/
theorem treiber_whole_npSafeF (l : _root_.Layout) [Executable.ValidLayout (l treiberImageA)] {t n : BitVec 64}
    (htn : t ≠ n + 8) {sP sQ : isa.State} {initMem : List (Loc × Val)} (hP : StartPushW (layout := l) t n sP)
    (hQ : StartPopW (layout := l) t sQ) (hT0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨t, 8⟩ = 0) :
    ∀ tid, tid < [sP, sQ].length → ∀ k j, NPSafeF (model isa) Arch.armv8 (TB (tP t n) n) tid k j True
      (Config.init [sP, sQ] initMem) (tRes (Config.init [sP, sQ] initMem).mem (tP t n) tid) (ghost₀ (tP t n)) := by
  intro tid htid k j
  rcases tid with _ | _ | i
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invPushW_init (layout := l) htn hP)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invPopW_init (layout := l) htn hQ hT0)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-! ## Purity -/

/-- The threads' purity specifications in the whole image: the pusher's run
to `pdone` at thread `0`, the popper's to `qdone` elsewhere. -/
def treiberPureSpecW (l : _root_.Layout) [hv : Executable.ValidLayout (l treiberImageA)] (rel : Loc → Pred) :
    Nat → RelPureSpec Arch.armv8 rel
  | 0 => { e := l treiberImageA, valid := hv, endPc := labT (layout := l) "pdone",
           post := fun x => ∃ _ : Nat, (x.1.2 = labT (layout := l) "pdone" ∧ True) ∨ False,
           post_end := fun _ ⟨_, h⟩ => h.elim And.left False.elim }
  | _ + 1 => { e := l treiberImageA, valid := hv, endPc := labT (layout := l) "qdone",
               post := fun x => ∃ _ : Nat, (x.1.2 = labT (layout := l) "qdone" ∧ True) ∨ False,
               post_end := fun _ ⟨_, h⟩ => h.elim And.left False.elim }

/-- **The purity specifications hold at the start states**, for release
predicates pure at the node's words. -/
theorem treiberPureSpecW_init (l : _root_.Layout) [Executable.ValidLayout (l treiberImageA)] {rel : Loc → Pred}
    {t n : BitVec 64} (hd : ∀ v : Val, Pred.Pure (rel ⟨n, 4⟩) v) (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v)
    {sP sQ : isa.State} (hP : StartPushW (layout := l) t n sP) (hQ : StartPopW (layout := l) t sQ) :
    ∀ tid s, [sP, sQ][tid]? = some s → (treiberPureSpecW l rel tid).Holds s
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

/-! ## The theorem -/

/-- **The Treiber stack `treiber_pp.kl` for AArch64 under `Arch.armv8`, both
threads running the whole `.kl` image** (on `EnvGC` with failing release
RMWs; `forall (1:X10=n1 /\ 1:X11=1)`).

For a valid layout `l` of the `.kl`'s `code` block `treiberImageA`, all
addresses `t` of `top` (8 bytes) and `n` of the node (data word `[n]`,
4 bytes; link word `[n + 8]`, 8 bytes) with `t ≠ n + 8`: if thread `0` runs
the image from `pusher` to `pdone` with `x0 = t`, `x1 = n`, `w9 = 1` and
thread `1` from `popper` to `qdone` with `x0 = t`, each with no declarations
and no private copy of the shared words (`StartPushW`, `StartPopW`), and
`top` is initially `0`, then every final configuration reachable under
`Arch.armv8` has the popper's `X10 = n` and `X11 = 1`.

This is `treiber_pp_envG` with the runner's executable: its per-thread-image
deviation is resolved here (the dead `NOP` at `pdone`, which broke the halt,
and the popper's code, which is not the pusher's phase-1 obligation, are
handled by the pusher's mask: `EnvG/A64MaskLink.lean`). As there, only the
addresses' `Loc`s are distinguished (`t ≠ n + 8`), only final configurations
are constrained, faults are covered by `pushRuleW_noFault`/`popRuleW_noFault`,
and the threads have no declarations (the runner sets `decls` from the init
block). -/
theorem treiber_pp_envG_whole {fuel : Nat} (l : _root_.Layout) [Executable.ValidLayout (l treiberImageA)]
    (t n : BitVec 64) (htn : t ≠ n + 8) {sP sQ : isa.State} {initMem : List (Loc × Val)}
    (hP : StartPushW (layout := l) t n sP) (hQ : StartPopW (layout := l) t sQ)
    (hT0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨t, 8⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [sP, sQ] initMem) cfg)
    (hf : cfg.final = true) :
    ∃ th, cfg.threads[1]? = some th ∧ th.st.st.1.regs.X10.toBitVec = n ∧ th.st.st.1.regs.X11.toBitVec = 1 := by
  have hL := tLocs_tP htn
  refine final_of_relPureSafelyF Arch.armv8 fuel (B := TB (tP t n) n) (Φ := PopperFinal n)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_init hL _) (ghost₀_pend _) (treiberPureSpecW l _)
    (treiberPureSpecW_init l (fun v => ?_) (fun v => ?_) hP hQ) (treiber_whole_npSafeF l htn hP hQ hT0) hc hf
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

#print axioms Kraken.Promising.SLR.EnvG.Treiber.treiber_pp_envG_whole
#print axioms Kraken.Promising.SLR.EnvG.Treiber.pushRuleW_noFault
#print axioms Kraken.Promising.SLR.EnvG.Treiber.popRuleW_noFault
