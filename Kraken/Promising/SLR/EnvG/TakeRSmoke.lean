/-
**Part 3: smoke tests of the link with taking
loads and release-kind RMWs** (`EnvG/TakeRLink.lean`,
`EnvG/TakeRA64Link.lean`).

1. **The new route subsumes the take route, end to end.** `takeMp_envGR` is
   `takeMp_envG` (same statement) with the writing reader linked
   by `npSafeP_of_safelyEnvGTR` instead of `npSafeP_of_safelyEnvGT`: its
   Plain phase-1 code is phase-1 with release-kind RMWs (`Phase1Tree.toR`) and
   its empty plan gives nothing away (`RelRmwGiveOk.of_gives_nil`). The
   reader's no-fault rule is `noFaultRule_ofSafelyEnvGTR_struct`.
2. **Code with both features passes the static checks.** `takeRelRmw` (an
   acquire spin that takes, then a release swap and a release fetch-add)
   satisfies `DirsPhase1R` (which the plain `Phase1Tree` rejects) and
   `rmwLive`; this is the code shape `ofSafelyEnvGTR` admits and neither
   `ofSafelyEnvGT` nor `ofSafelyEnvGR` does. This is a shape check only:
   release-only RMWs (`swpl`, `ldaddl`) cannot discharge `RmwOk`, and a plan
   that gives something away cannot discharge `RelRmwGiveOk` as stated
   (`KNOWN_GAPS.md`, release-RMW limit 2).
-/
import Kraken.Promising.SLR.EnvG.TakeRA64Link
import Kraken.Promising.SLR.EnvG.TakeMpPublic

namespace Kraken.Promising.SLR.EnvG.TakeMp

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Mp Kraken.Promising.SLR.MpTrees
open Kraken.Promising.SLR.EnvG.MpSmoke Kraken.Promising.SLR.EnvG.MpLink Kraken.Promising.SLR.MpPublic
open Kraken.Promising.SLR.EnvG.MpRelPure Kraken.Promising.SLR.EnvG.TakeSmoke

/-! ## 1. The writing reader through the combined link -/

/-- The empty plan gives nothing away. -/
theorem rdPlan_giveOk (rel : Loc → Pred) : RelRmwGiveOk isa rdPlan rel :=
  RelRmwGiveOk.of_gives_nil fun _ _ => rfl

section Reader

variable [layout : _root_.Layout] [Executable.ValidLayout (layout takeReader)]

/-- **The reader's no-fault rule through the combined link.** -/
theorem takeRuleR_noFaultR (P : Params) (tid : Nat) (rel₀ : Loc → Pred) :
    NoFaultRuleS (ThreadRuleRXGS.ofSafelyEnvGTR (e := layout takeReader) (post := postT P) (rel₀ := rel₀)
      rdPlan_valid takeReader_rmwLive takeReader_phase1.toR (rdPlan_giveOk rel₀) postOf_end
      (not_instrStepEnv_of_end_labels _ 1) (hB_T P tid)) :=
  noFaultRule_ofSafelyEnvGTR_struct _ _ _ _ _ _ _ takeReader_noFault

end Reader

section Start

variable [layout : _root_.Layout] {f d : BitVec 64} {sW sR : isa.State} {initMem : List (Loc × Val)}

/-- **The reader's initial invariant for the combined link** (`invT_init`
with `invGTR_init`). -/
theorem invTR_init [Executable.ValidLayout (layout takeReader)] (hfd : f ≠ d) (hR : StartT f d sR) :
    InvGR (I := isa) 1 rdPlan
      (QA64TR Arch.armv8 1 rdPlan (layout takeReader) ((layout takeReader).addrOf takeReader.length)
        (postT (ghostParams f d)) (mpGhost (ghostParams f d)).rel)
      True (Config.init [sW, sR] initMem)
      (mpRes (Config.init [sW, sR] initMem).mem (ghostParams f d) 1) (mpGhost (ghostParams f d)) := by
  letI : CodeEnv := ⟨layout takeReader⟩
  have hL := ghostParams_mpLocs hfd
  refine invGTR_init (s := sR) rfl rfl (qa64T_of_partialTripleEnv (takeReader_envGT _ 1).uncount rfl hR.exe
    hR.decls hR.endPc hR.pc ⟨0, hR.x0, hR.x1, hR.df, hR.dd, mpGhost_rel_Fl, fun v => ?_, ?_, 0, Nat.zero_lt_one,
      ?_, OkPred.flag⟩)
  · show Pred.Pure ((mpGhost _).rel _) v
    rw [mpGhost_rel_ne (Ne.symm hL.fl_dt)]; exact Pred.emp_pure v
  · simp [σInit, Views.getFwd]
  · simp [σInit, mpRes, readerRes]

omit layout in
/-- **The `NPSafeP` side for MP with a writing reader, the reader through the
combined link** (`takeMp_npSafe` with `npSafeP_of_safelyEnvGTR`). -/
theorem takeMp_npSafeR (lW lR : _root_.Layout) [Executable.ValidLayout (lW mpWriter)]
    [Executable.ValidLayout (lR takeReader)] (hfd : f ≠ d) (hW : StartW (layout := lW) f d sW)
    (hR : StartT (layout := lR) f d sR) :
    ∀ tid, tid < [sW, sR].length → ∀ n m, NPSafeP (model isa) Arch.armv8 (TPost (ghostParams f d) 1) tid G₀
      (K2Scope (model isa) AllocIds) n m True (Config.init [sW, sR] initMem)
      (mpRes (Config.init [sW, sR] initMem).mem (ghostParams f d) tid) (mpGhost (ghostParams f d)) := by
  intro tid htid n m
  rcases tid with _ | _ | k
  · exact NPSafe.toP (fun _ _ _ _ _ h => h) (fun _ _ _ h => K2₀.toScope _ h)
      (NPSafe.of_ruleRX (takeRuleW (layout := lW) _ (ghostParams_mpLocs hfd) 0 1) n m _ _ _ _
        (invW_envG_init (layout := lW) hfd hW))
  · exact npSafeP_of_safelyEnvGTR (e := lR takeReader) (post := postT (layout := lR) _) rdPlan_valid
      (takeReader_rmwLive (layout := lR)) (takeReader_phase1 (layout := lR)).toR (rdPlan_giveOk _) postOf_end
      (not_instrStepEnv_of_end_labels _ 1) (hB_T (layout := lR) _ 1) n m (invTR_init (layout := lR) hfd hR)
  · simp only [List.length_cons, List.length_nil] at htid; omega

end Start

/-- **`takeMp_envG` through the combined link** (same statement; the reader
is linked by `npSafeP_of_safelyEnvGTR`). -/
theorem takeMp_envGR {fuel : Nat} (lW lR : _root_.Layout) [Executable.ValidLayout (lW mpWriter)]
    [Executable.ValidLayout (lR takeReader)] (f d : BitVec 64) (hfd : f ≠ d) {sW sR : isa.State}
    {initMem : List (Loc × Val)} (hW : StartW (layout := lW) f d sW) (hR : StartT (layout := lR) f d sR)
    (hF0 : (Config.init [sW, sR] initMem).mem.initVal ⟨f, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [sW, sR] initMem) cfg)
    (hf : cfg.final = true) :
    (∃ t, cfg.threads[1]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 43) ∧
      cfg.mem.finalVal ⟨d, 4⟩ = 43#128 :=
  final_of_relPureSafelyS Arch.armv8 fuel (B := TPost (ghostParams f d) 1)
    (Φ := fun c => (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 43) ∧
      c.mem.finalVal ⟨d, 4⟩ = 43#128)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_mpInit _ _ hF0) pend_mpGhost
    (takePureSpec lW lR _) (takePureSpec_init lW lR hfd hW hR) (takeMp_npSafeR lW lR hfd hW hR) hc hf
    fun _ _ E' _ hsize hB => takeMp_final E' hf hsize hB

/-- Same statement as `takeMp_envG`. -/
example : @takeMp_envGR = @takeMp_envG := rfl

end Kraken.Promising.SLR.EnvG.TakeMp

/-! ## 2. Static checks on code with a taking load and release-kind RMWs -/

namespace Kraken.Promising.AArch64.EnvG.TakeRSmoke

open Kraken Kraken.Promising Kraken.Promising.SLR.EnvG
open Kraken.AArch64.Parser

/-- An acquire spin (which takes on `EnvGT`), then a release swap and a
release fetch-add. -/
def takeRelRmw : Program := parseAArch64("
spin:
    ldar w3, [x0]
    cbz w3, spin
    mov w5, #43
    swpl w5, w6, [x1]
    mov w4, #1
    ldaddl w4, w7, [x2]
")

example [layout : _root_.Layout] (A : Arch) : DirsPhase1R A (layout takeRelRmw) := by dirs_phase1R takeRelRmw

example [layout : _root_.Layout] : (layout takeRelRmw).rmwLive = true := by rw [Layout.apply_rmwLive]; decide

set_option linter.unusedVariables false in
/-- The plain shape check rejects it (release-kind RMWs). -/
example [layout : _root_.Layout] (A : Arch) : True := by
  fail_if_success have _h : DirsPhase1 A (layout takeRelRmw) := by dirs_phase1 takeRelRmw
  trivial

end Kraken.Promising.AArch64.EnvG.TakeRSmoke

#print axioms Kraken.Promising.SLR.EnvG.TakeMp.takeMp_envGR
#print axioms Kraken.Promising.SLR.EnvG.TakeMp.takeRuleR_noFaultR
