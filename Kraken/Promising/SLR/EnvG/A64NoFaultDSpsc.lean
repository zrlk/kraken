/-
**No fault at the runner's declarations for the AArch64 SPSC ring**
`spsc_queue.kl`.

Per role: the role text's **address run** in `SharedEnv.invTop S` over the
role's executable (the producer's mask, the consumer's image), by
`cfgEnv_partial_at` with a register-only table (`FrameP`/`FrameC`, and the
slot pointer `X7` one of the two slots `b`, `b ^^^ 8` inside the loops),
giving `AddrSafeA` at the role's start; the role's rule with the address run
(`ofSafelyEnvGTUMAD`, `EnvG/A64NoFaultD.lean`; same `B` as the existing
`…_decls` rules); its initial invariant at the runner's start; and the
rule's no-fault at `decls = ds` for declarations agreeing on the two slots,
`head` and `tail` (`…_runner_noFault`), with concrete instances at the
runner's declarations. The slot `b ^^^ 8` is undeclared at the runner
(`spscDeclsD`): it agrees with `{}` there all the same.
-/
import Kraken.Promising.SLR.EnvG.A64NoFaultD
import Kraken.Promising.SLR.EnvG.A64SpscWholeRunner

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP

namespace Kraken.Promising.SLR.EnvG.SpscA

open Kraken.Promising.AArch64.EnvG Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)

set_option mvcgen.warning false
set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

/-- The ring's layout: the two slots (4-byte words), `head` and `tail`
(8-byte words). -/
abbrev spscS (P : SP) : SharedEnv.Layout := [(P.b, 4), (P.b ^^^ 8, 4), (P.h, 8), (P.t, 8)]

/-! ## The role texts' address runs -/

section RunsAt

variable [CodeEnv]

/-- The producer's address table: the frame, and at `prod_loop` the slot
pointer is one of the two slots (`prodPureTable`). -/
abbrev prodAddrTable (P : SP) :
    Label → MachineData → (SharedEnv.counted (SharedEnv.invTop (spscS P))).State → Prop :=
  fun lb s _ => FrameP P s ∧ (lb = "prod_loop" → s.regs.X7.toBitVec = P.b ∨ s.regs.X7.toBitVec = P.b ^^^ 8)

/-- **The producer's address run in any ambient code** in which `spscProdA`
is `PlacedIn`. -/
theorem spscProdA_addr_at (P : SP) (hpl : Program.PlacedIn spscProdA) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt spscProdA l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, (prodAddrTable P) "prod" s g → Safely (cenv.instrStepEnv (SharedEnv.counted (SharedEnv.invTop (spscS P))))
      (fun x => (x.1.2 = endA ∧ True) ∨ False)
      ((s, (_root_.Executable.labels cenv).label "prod"), g) := by
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (SharedEnv.invTop (spscS P)))
    (Q := fun _ _ => True) (E := fun _ _ _ => False) (prodAddrTable P) ?_ (by rfl) (by decide) hpl hlast
  cfg_cases_env [spscProdA]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hx0, hx1, hx2, hdh, hdt, hdb, hdb1⟩, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [forall_const, true_implies] at hT
  all_goals try simp at hdb1
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok, and_true, true_and] at *
  all_goals try (simp [SharedEnv.inv, hx0, hx1, hx2, hdh, hdt, hdb, hdb1]; done)
  case vc1 =>
    refine ⟨?_, fun _ => .inl ?_⟩ <;> simp [FrameP, hx0, hx1, hx2, hdh, hdt, hdb, hdb1]
  case vc4 =>
    rename_i hcnt _
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨?_, fun _ => ?_⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    · simp [FrameP, hx0, hx1, hx2, hdh, hdt, hdb, hdb1]
    · simpa using hT
    · have := congrArg Prod.snd hg; simp [SharedAccess.tick] at hcnt; omega
  case vc6 =>
    rcases hT with h | h <;> simp [SharedEnv.inv, h]
  case vc8 =>
    rename_i hstr _
    rcases hT with h | h <;> simp [h, hx0, hx1, hx2, hdh, hdt, hdb, hdb1] at hstr <;> simp [hstr.1, hx2, hdt]
  case vc10 =>
    rename_i v σ1 r1 hc r2 dm σ2 r3 hc2 σ3 r4 r5 hc3 hcnt hstr hstl _
    rcases hT with h | h <;> simp [h, hx0, hx1, hx2, hdh, hdt, hdb, hdb1] at hstr hstl hc2 hc3 hcnt
    all_goals
      obtain ⟨rfl, hs2⟩ := hstr
      refine Table.ofLabelsEnv_at ⟨by decide, ⟨?_, fun _ => ?_⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      · simp [FrameP, hx0, hx1, hx2, hdh, hdt, hdb, hdb1]
      · simp [h, BitVec.xor_assoc]
      · have := congrArg Prod.snd hg; omega
  case vc11 =>
    rename_i v σ1 r1 hc r2 dm σ2 r3 hc2 σ3 r4 r5 hc3 hcnt hstr hstl _
    rcases hT with h | h <;> simp [h, hx0, hx1, hx2, hdh, hdt, hdb, hdb1] at hstr hstl hc2 hc3 hcnt
    all_goals
      obtain ⟨rfl, -⟩ := hstr
      refine Table.ofLabelsEnv_at ⟨by decide, ⟨?_, fun h => absurd h (by decide)⟩, .inl (by decide)⟩
      simp [FrameP, hx0, hx1, hx2, hdh, hdt, hdb, hdb1]

/-- The consumer's address table: the frame, and the slot pointer at the
three rounds (`b`, `b ^^^ 8`, `b`). -/
abbrev consAddrTable (P : SP) :
    Label → MachineData → (SharedEnv.counted (SharedEnv.invTop (spscS P))).State → Prop :=
  fun lb s _ => FrameC P s ∧ ((lb = "c1" ∨ lb = "c3") → s.regs.X7.toBitVec = P.b) ∧
    (lb = "c2" → s.regs.X7.toBitVec = P.b ^^^ 8)

/-- **The consumer's address run in any ambient code** in which `spscConsA`
is `PlacedIn`. -/
theorem spscConsA_addr_at (P : SP) (hpl : Program.PlacedIn spscConsA) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt spscConsA l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, (consAddrTable P) "cons" s g → Safely (cenv.instrStepEnv (SharedEnv.counted (SharedEnv.invTop (spscS P))))
      (fun x => (x.1.2 = endA ∧ True) ∨ False)
      ((s, (_root_.Executable.labels cenv).label "cons"), g) := by
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (SharedEnv.invTop (spscS P)))
    (Q := fun _ _ => True) (E := fun _ _ _ => False) (consAddrTable P) ?_ (by rfl) (by decide) hpl hlast
  cfg_cases_env [spscConsA]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hx0, hx1, hx2, hdh, hdt, hdb, hdb1⟩, hT1, hT2⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [forall_const, true_implies, true_or, or_true,
    false_or, or_false, false_implies, imp_false] at hT1 hT2
  all_goals try simp at hdb1
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok, and_true, true_and] at *
  all_goals try (simp [SharedEnv.inv, hx0, hx1, hx2, hdh, hdt, hdb, hdb1, hT1, hT2]; done)
  -- the spin loops' back edges: the counter moved
  case vc4 | vc4 | vc4 =>
    rename_i hcnt _
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [FrameC, hx0, hx1, hx2, hdh, hdt, hdb, hdb1],
      by simp_all, by simp_all⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    have := congrArg Prod.snd hg; simp [SharedAccess.tick] at hcnt; omega
  all_goals (try refine Table.ofLabelsEnv_at ⟨by decide, ?_, .inl (by decide)⟩)
  all_goals simp_all [FrameC, Reg64s.setXReg, BitVec.xor_assoc]

end RunsAt

/-! ## The roles' address runs at the image's labels -/

section Lay

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spscImageA)]

/-- **The producer's address run over its mask**, at the image's labels. -/
theorem spscProdW_addr (P : SP) :
    ∀ s g, prodAddrTable P "prod" s g →
      Safely ((layout spscImageP).instrStepEnv (SharedEnv.counted (SharedEnv.invTop (spscS P))))
        (fun x => (x.1.2 = labA "pdone" ∧ True) ∨ False) ((s, labA "prod"), g) := by
  intro s g hsg
  have h : Safely ((layout spscImageP).instrStepEnv (SharedEnv.counted (SharedEnv.invTop (spscS P))))
      (fun x => (x.1.2 = (_root_.Executable.labels (layout spscImageP)).label "pdone" ∧ True) ∨ False)
      ((s, (_root_.Executable.labels (layout spscImageP)).label "prod"), g) :=
    letI : CodeEnv := ⟨layout spscImageP⟩
    spscProdA_addr_at P prodP_placedIn (Program.last_of_check spscProdA_exit) s g hsg
  rw [labelsP_eq] at h
  exact h

/-- **The consumer's address run in the image.** -/
theorem spscConsW_addr (P : SP) :
    ∀ s g, consAddrTable P "cons" s g →
      Safely ((layout spscImageA).instrStepEnv (SharedEnv.counted (SharedEnv.invTop (spscS P))))
        (fun x => (x.1.2 = labA "cdone" ∧ True) ∨ False) ((s, labA "cons"), g) := by
  letI : CodeEnv := ⟨layout spscImageA⟩
  exact spscConsA_addr_at P consA_placedIn (Program.last_of_check spscConsA_exit)

end Lay

/-! ## The rules with the address run, and the start -/

section Rules

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spscImageA)] {ds : Decls}

/-- **The whole-image producer's rule with the address run** (thread `0`;
`prodW_npSafeP_decls`'s rule through `ofSafelyEnvGTUMAD`). -/
def prodRuleW_declsA (hsz : ds.StrictSized) (P : SP) (hL : SpscLocs P) :
    ThreadRuleRXGS (I := isa) G₀ Arch.armv8 (SpscPost P) 0 :=
  ThreadRuleRXGS.ofSafelyEnvGTUMAD (post := postPW P) (spscS P) hsz spscImageA_noPairs spscImageP_mask
    (prodPlan_valid hL) spscImageA_rmwLive spscImageP_phase1 (postPW_end P) (prodP_stuck _) (hB_PW P 0)

/-- **The whole-image consumer's rule with the address run** (thread `1`;
`consW_npSafeP_decls`'s rule through `ofSafelyEnvGTUMAD`). -/
def consRuleW_declsA (hsz : ds.StrictSized) (P : SP) (hL : SpscLocs P) :
    ThreadRuleRXGS (I := isa) G₀ Arch.armv8 (SpscPost P) 1 :=
  ThreadRuleRXGS.ofSafelyEnvGTUMAD (post := postCW) (spscS P) hsz spscImageA_noPairs (MaskOf.refl _)
    (consPlan_valid hL) spscImageA_rmwLive spscImageA_phase1 postCW_end (consA_stuck _) (hB_CW P)

variable {P : SP} {sP sC : isa.State} {initMem : List (Loc × Val)}

/-- **The producer's initial invariant with the address run.** -/
theorem prodW_init_declsA (hsz : ds.StrictSized) (hL : SpscLocs P) (hP : WithDeclsD ds (StartPW P) sP)
    (hH0 : (Config.init [sP, sC] initMem).mem.initVal P.H = 0) :
    (prodRuleW_declsA hsz P hL).Inv True (Config.init [sP, sC] initMem)
      (spscRes (Config.init [sP, sC] initMem).mem P 0) (spscGhost P) := by
  obtain ⟨hds, he, hds0, hpc, hend, hfr⟩ := hP
  refine invGTUMAD_init (s := sP) rfl rfl ⟨QA64MD.of_noDecls hds ⟨he, hds0, hend, ?_⟩, ?addr⟩
  case addr =>
    unfold AddrSafeA
    rw [show sP.st = (sP.st.1, labA "prod") from Prod.ext rfl hpc]
    exact (Safely.uncountA (spscProdW_addr P _ ((), 0) ⟨hfr, fun h => absurd h (by decide)⟩)).mono
      fun _ ⟨_, h⟩ => h.elim And.left False.elim
  rw [show sP.noDecls.st = (sP.noDecls.st.1, labA "prod") from Prod.ext rfl hpc]
  exact Safely.uncountA (spscProdW_envGTU P hL 0 _ (_, 0) ⟨hfr, PR_init hL hH0⟩)

/-- **The consumer's initial invariant with the address run.** -/
theorem consW_init_declsA (hsz : ds.StrictSized) (hL : SpscLocs P) (hC : WithDeclsD ds (StartCW P) sC)
    (hT0 : (Config.init [sP, sC] initMem).mem.initVal P.T = 0) :
    (consRuleW_declsA hsz P hL).Inv True (Config.init [sP, sC] initMem)
      (spscRes (Config.init [sP, sC] initMem).mem P 1) (spscGhost P) := by
  obtain ⟨hds, he, hds0, hpc, hend, hfr⟩ := hC
  refine invGTUMAD_init (s := sC) rfl rfl ⟨QA64MD.of_noDecls hds ⟨he, hds0, hend, ?_⟩, ?addr⟩
  case addr =>
    unfold AddrSafeA
    rw [show sC.st = (sC.st.1, labA "cons") from Prod.ext rfl hpc]
    exact (Safely.uncountA (spscConsW_addr P _ ((), 0)
      ⟨hfr, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩)).mono
      fun _ ⟨_, h⟩ => h.elim And.left False.elim
  rw [show sC.noDecls.st = (sC.noDecls.st.1, labA "cons") from Prod.ext rfl hpc]
  exact Safely.uncountA (spscConsW_envGTU P hL 1 _ (_, 0) ⟨hfr, CE_init hL hT0⟩)

/-- **No fault at the runner's declarations** for the whole-image producer's
rule: declarations agreeing on the two slots, `head` and `tail`. -/
theorem a64_spscP_envG_runner_noFault (hsz : ds.StrictSized) (P : SP) (hL : SpscLocs P)
    (hag : ds.AgreesOnA (spscS P)) : NoFaultRuleS (prodRuleW_declsA hsz P hL) :=
  noFaultRule_ofSafelyEnvGTUMAD_rootD _ _ _ _ _ _ _ _ _ spscImageA_noFault hag

/-- **No fault at the runner's declarations** for the whole-image consumer's
rule. -/
theorem a64_spscC_envG_runner_noFault (hsz : ds.StrictSized) (P : SP) (hL : SpscLocs P)
    (hag : ds.AgreesOnA (spscS P)) : NoFaultRuleS (consRuleW_declsA hsz P hL) :=
  noFaultRule_ofSafelyEnvGTUMAD_rootD _ _ _ _ _ _ _ _ _ spscImageA_noFault hag

end Rules

/-- The runner's declarations agree with `{}` on the two slots, `head` and
`tail` (the slot `buf ^^^ 8` undeclared). -/
theorem spscDeclsD_agreesA : spscDeclsD.AgreesOnA (spscS ⟨bufA, headA, tailA⟩) := by
  decls_agrees_on_a

/-- **No fault at the runner's declarations**, concrete: both roles' rules at
`wLayoutA` and `spscDeclsD`. -/
theorem a64_spsc_envG_runner_noFault_concrete :
    NoFaultRuleS (prodRuleW_declsA (layout := wLayoutA) spscDeclsD_sized _ spscLocsA) ∧
      NoFaultRuleS (consRuleW_declsA (layout := wLayoutA) spscDeclsD_sized _ spscLocsA) :=
  ⟨a64_spscP_envG_runner_noFault (layout := wLayoutA) _ _ _ spscDeclsD_agreesA,
    a64_spscC_envG_runner_noFault (layout := wLayoutA) _ _ _ spscDeclsD_agreesA⟩

end Kraken.Promising.SLR.EnvG.SpscA

#print axioms Kraken.Promising.SLR.EnvG.SpscA.prodW_init_declsA
#print axioms Kraken.Promising.SLR.EnvG.SpscA.consW_init_declsA
#print axioms Kraken.Promising.SLR.EnvG.SpscA.a64_spsc_envG_runner_noFault_concrete
