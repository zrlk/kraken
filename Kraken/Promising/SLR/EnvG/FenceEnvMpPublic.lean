/-
**Message passing with a fence-released writer, on `EnvG`**: `mp_fence_envG`, the statement of `MpFence.mp_fence` (writer
`fwriterMp`: `str data; dmb ish; str flag`, both plain; impure flag
predicate), proved by the EnvG/vcgen route.

- **Rules**: both threads by `ThreadRuleRXG.ofSafelyEnvGHyb`
  (`EnvG/FenceEnvA64.lean`) through `npSafeP_hyb_of_safelyEnvG_S`, from the
  `vcgen` proofs on `EnvG` (`FenceEnvMp.fwriter_envG`, the existing
  `MpSmoke.mpReader_envGP`) and `ofSafelyEnvG`'s initial invariant
  (`invG_init`). The writer's fence-released flag store is prepaid by the
  generic prepay (`InvG.prepayHyb`); no per-program prepay, trees, or cells.
- **Purity**: `final_of_relPureFSafely` (`EnvG/FenceEnvPureA64.lean`) with
  one `RelPureFSpec` per thread (`FenceEnvMp.fwriter_relPureF`,
  `mpReader_relPureF` below).
- **Erasure, ghost, final argument**: the existing MP ones (`erase_mpInit`,
  `mpGhost`, `mp_final`), as in `mp_envG'` and `mp_fence`.
-/
import Kraken.Promising.SLR.EnvG.FenceEnvMp
import Kraken.Promising.SLR.EnvG.FenceEnvA64
import Kraken.Promising.SLR.EnvG.MpEnvGPublic2
import Kraken.Promising.SLR.MpFence

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Mp Kraken.Promising.SLR.MpTrees Kraken.Promising.SLR.FenceW
open Kraken.Promising.SLR.EnvG.MpSmoke Kraken.Promising.SLR.EnvG.MpLink Kraken.Promising.SLR.MpPublic

namespace Kraken.Promising.SLR.EnvG.FenceEnvMp

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The reader in the fence-aware purity environment -/

section Reader

variable [layout : _root_.Layout] [Executable.ValidLayout (layout mpReader)]

local instance mpReader.env : CodeEnv := ⟨layout mpReader⟩

/-- The reader's table: at `spin`, the flag address in `X0`, not in `dmem`. -/
abbrev readerTableF (f : BitVec 64) (rel : Loc → Pred) :
    Label → MachineData → (SharedEnv.counted (SharedEnv.relPureF Arch.armv8 rel)).State → Prop :=
  fun lb s _ => lb = "spin" → s.regs.X0.toBitVec = f ∧ Mem.loadInt s.dmem f 4 = none

/-- **The MP reader is fence-aware pure** (it writes nothing); counted,
partial. -/
theorem mpReader_relPureF (rel : Loc → Pred) (f : BitVec 64) :
    PartialTripleEnv (SharedEnv.counted (SharedEnv.relPureF Arch.armv8 rel))
      (fun s _ => s.regs.X0.toBitVec = f ∧ Mem.loadInt s.dmem f 4 = none)
      mpReader (fun _ _ => True) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (readerTableF f rel) (hP := by funext s g; simp [readerTableF])
  cfg_cases_env [mpReader]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨hT, rfl, rfl⟩ := ‹(_ → _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [forall_const] at hT
  case vc4 =>
    -- the back edge (`cbz` taken): the counter moved
    have hn := (‹(SharedEnv.counted _).step _ _ _ _›).2
    have hle := ‹SharedEnv.FenceMono.le _ _›
    simp only [fenceMono_le_counted] at hle
    refine Table.ofLabelsEnv_at ⟨by decide, fun _ => ⟨by simpa using hT.1, by simpa using hT.2⟩,
      .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg; simp at hn; omega
  all_goals simp_all [SharedEnv.counted_ok, SharedEnv.relPureFQ_ok_load]

end Reader

/-! ## The writer's rule data -/

section Writer

variable [layout : _root_.Layout] [Executable.ValidLayout (layout fwriterMp)]

omit [Executable.ValidLayout (layout fwriterMp)] in
theorem fwriter_rmwLive : (layout fwriterMp).rmwLive = true := by rw [Layout.apply_rmwLive]; decide

theorem fwriter_phase1 : Phase1Tree Arch.armv8 (layout fwriterMp) := phase1Tree_of_dirs (by dirs_phase1 fwriterMp)

/-- The writer's postcondition: the end of its text and `W3`. -/
abbrev postWF (P : Params) : MachineState × EStateA → Prop := postOf fwriterMp fun _ σ => W3 P σ

omit [Executable.ValidLayout (layout fwriterMp)] in
/-- **`hB` for the writer**: it keeps the token `W` (as `MpLink.hB_W`). -/
theorem hB_WF (P : Params) (tid rd : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postWF P (t.st.st, σ) → t.prom = [] → EnvRel tid (mpPlan P) σ c t r g cl → cl → MpPost P rd c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, hW⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inl hW.2
  · rw [hp] at hts; cases hts

/-- **The writer's initial invariant** (thread `0`), `ofSafelyEnvG`'s, from
`fwriter_envG`. -/
theorem invWF_init {f d : BitVec 64} {sW sR : isa.State} {initMem : List (Loc × Val)} (hfd : f ≠ d)
    (hW : MpFence.StartF f d sW) :
    InvG (I := isa) Arch.armv8 0 (mpPlan (ghostParams f d))
      (QA64 Arch.armv8 0 (mpPlan (ghostParams f d)) (layout fwriterMp) ((layout fwriterMp).addrOf fwriterMp.length)
        (postWF (ghostParams f d)))
      True (Config.init [sW, sR] initMem) (mpRes (Config.init [sW, sR] initMem).mem (ghostParams f d) 0)
      (mpGhost (ghostParams f d)) := by
  letI : CodeEnv := ⟨layout fwriterMp⟩
  have hL := ghostParams_mpLocs hfd
  refine invG_init (s := sW) rfl rfl (qa64_of_partialTripleEnv (fwriter_envG _ hL 0).partial rfl hW.exe
    hW.decls hW.endPc hW.pc ⟨hW.x0, hW.x1, hW.df, hW.dd, ⟨mpGhost_rel_Fl, fun v => ?_⟩, ?_⟩)
  · show Pred.Pure ((mpGhost _).rel _) v
    rw [mpGhost_rel_ne (Ne.symm hL.fl_dt)]; exact Pred.emp_pure v
  · simp only [σInit, Own0, mpRes, ↓reduceIte, writerRes, Res.initOf, Perm.init, writerFrac]
    exact ⟨by simp, fun p hp => by rw [hp.2], by simp, by simp <;> decide⟩

end Writer

/-! ## `NPSafeP` at the fence-aware guard, purity, and the theorem -/

variable (lW lR : _root_.Layout) [hw : Executable.ValidLayout (lW fwriterMp)]
  [hr : Executable.ValidLayout (lR mpReader)]

/-- **The `NPSafeP (GHyb g.rel) (K2Scope AllocIds)` side for the
fence-released MP on `EnvG`**: both threads through
`npSafeP_hyb_of_safelyEnvG_S` (the reader with the existing EnvG reader's
data, `MpLink.mpRuleR_envG`). -/
theorem mpF_envG_npSafe {f d : BitVec 64} (hfd : f ≠ d) {sW sR : isa.State} {initMem : List (Loc × Val)}
    (hW : MpFence.StartF (layout := lW) f d sW) (hR : StartR (layout := lR) f d sR) :
    ∀ tid, tid < [sW, sR].length → ∀ n m,
      NPSafeP (model isa) Arch.armv8 (MpPost (ghostParams f d) 1) tid (GHyb (mpGhost (ghostParams f d)).rel)
        (K2Scope (model isa) AllocIds) n m True (Config.init [sW, sR] initMem)
        (mpRes (Config.init [sW, sR] initMem).mem (ghostParams f d) tid) (mpGhost (ghostParams f d)) := by
  have hL := ghostParams_mpLocs hfd
  intro tid htid n m
  rcases tid with _ | _ | k
  · exact npSafeP_hyb_of_safelyEnvG_S (mpPlan_valid hL) (fwriter_rmwLive (layout := lW))
      (fwriter_phase1 (layout := lW)) (postOf_end (layout := lW))
      (not_instrStepEnv_of_end_labels (layout := lW) (p := fwriterMp) _ 1)
      (hB_WF (layout := lW) _ 0 1) n m (invWF_init (layout := lW) hfd hW)
  · exact npSafeP_hyb_of_safelyEnvG_S (mpPlan_valid hL) (mpReader_rmwLive (layout := lR))
      (mpReader_phase1 (layout := lR)) (postOf_end (layout := lR))
      (not_instrStepEnv_of_end_labels (layout := lR) (p := mpReader) _ 1)
      (hB_R (layout := lR) _ 1) n m (invR_envG_init (layout := lR) hfd hR)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- The fence-released MP threads' purity specifications: the writer
(layout `lW`) at thread `0`, the reader (layout `lR`) elsewhere. -/
def mpFPureSpec (rel : Loc → Pred) : Nat → RelPureFSpec Arch.armv8 rel
  | 0 => RelPureFSpec.ofProgram (layout := lW) fwriterMp fun _ _ => True
  | _ + 1 => RelPureFSpec.ofProgram (layout := lR) mpReader fun _ _ => ∃ _ : Nat, True

/-- **The purity specifications hold at the start states** (flag clear). -/
theorem mpFPureSpec_init {f d : BitVec 64} (hfd : f ≠ d) {sW sR : isa.State}
    (hW : MpFence.StartF (layout := lW) f d sW) (hR : StartR (layout := lR) f d sR) :
    ∀ tid s, [sW, sR][tid]? = some s → (mpFPureSpec lW lR (mpGhost (ghostParams f d)).rel tid).Holds s false
  | 0, s, hs => by
    cases hs
    obtain ⟨he, hds, hend, hpc, hx0, hx1, hdf, hdd⟩ := hW
    letI : CodeEnv := ⟨lW fwriterMp⟩
    refine RelPureFSpec.holds_of_partialTripleEnv (layout := lW)
      (fwriter_relPureF (layout := lW) _ f d fun v => ?_).partial rfl he hds hend hpc ⟨hx0, hx1, hdf, hdd⟩
    rw [show (⟨d, 4⟩ : Loc) = (ghostParams f d).Dt from rfl,
      mpGhost_rel_ne (Ne.symm (ghostParams_mpLocs hfd).fl_dt)]
    exact Pred.emp_pure v
  | 1, s, hs => by
    cases hs
    obtain ⟨he, hds, hend, hpc, hx0, -, hdf, -⟩ := hR
    letI : CodeEnv := ⟨lR mpReader⟩
    exact RelPureFSpec.holds_of_partialTripleEnv (layout := lR) (mpReader_relPureF (layout := lR) _ f).uncount rfl
      he hds hend hpc ⟨0, hx0, hdf⟩
  | _ + 2, _, hs => by cases hs

/-- **Message passing with a fence-released writer (`dmb ish; str`), proved
on `EnvG`**: the statement of `MpFence.mp_fence` (see there for coverage),
with both rules from `ThreadRuleRXG.ofSafelyEnvGHyb` and purity from
`final_of_relPureFSafely`. -/
theorem mp_fence_envG {fuel : Nat} (f d : BitVec 64) (hfd : f ≠ d)
    {sW sR : isa.State} {initMem : List (Loc × Val)}
    (hW : MpFence.StartF (layout := lW) f d sW) (hR : MpPublic.StartR (layout := lR) f d sR)
    (hF0 : (Config.init [sW, sR] initMem).mem.initVal ⟨f, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [sW, sR] initMem) cfg)
    (hf : cfg.final = true) :
    (∃ t, cfg.threads[1]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 1) ∧
      cfg.mem.finalVal ⟨d, 4⟩ = 1#128 :=
  final_of_relPureFSafely Arch.armv8 fuel (B := MpPost (ghostParams f d) 1)
    (Φ := fun c => (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 1) ∧
      c.mem.finalVal ⟨d, 4⟩ = 1#128)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_mpInit _ _ hF0) pend_mpGhost
    (mpFPureSpec lW lR _) (mpFPureSpec_init lW lR hfd hW hR) (mpF_envG_npSafe lW lR hfd hW hR) hc hf
    fun _ _ E' hle hsize hB => mp_final E' hf hsize (by rw [hle.rel]; exact mpGhost_rel_Fl) hB

/-- `mp_fence_envG` has exactly the statement of `MpFence.mp_fence`. -/
example : type_of% @mp_fence_envG = type_of% @MpFence.mp_fence := rfl

end Kraken.Promising.SLR.EnvG.FenceEnvMp

#print axioms Kraken.Promising.SLR.EnvG.FenceEnvMp.mp_fence_envG
