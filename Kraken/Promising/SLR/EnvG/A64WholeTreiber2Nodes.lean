/-
**`treiber2_nodes.kl` whole image: both threads run
the whole `.kl` image.** Additive: `Treiber2.treiber2_nodes_envG`
(`EnvG/Treiber2Public.lean`) is unchanged.

`treiber2_nodes_envG` runs `treiber2Worker`, the `code` block without its
leading `worker:` label, each thread with its own layout. The runner's
executable is the whole block `treiber2NImage = .label "worker" ::
treiber2Worker` (`treiber2NImage_eq`) under one layout, each thread from
`worker` to `done`. `done:` is the block's last cell, so no mask is needed:
the adjacency link `ThreadRuleRXF.ofSafelyEnvGFCAdj` (`EnvG/AdjSpikeA64.lean`)
takes any executable, and here it is the image.

- **Runs**: the Treiber node proof's scripts, tables and VCs (`worker_envGCAdj`,
  `treiber2Worker_relPure`; `workTable`, `workPureTable`; the VCs of
  `EnvG/Treiber2VC.lean`), unchanged; only the control-flow rule differs:
  `MachineWP.cfgEnv_partial_at` (`EnvG/A64MaskCfg.lean`) with
  `treiber2Worker` `PlacedIn` the image, from `push`, whose address is
  `worker`'s (`labN_worker`: the label cell has size `0`).
- **Final argument, ghost and resources**: the Treiber node proof's (`TB2`,
  `Treiber2Final`, `tP2`, `tRes`/`thrRes`, `ghost₀`, `pu_init`, `erase_init`,
  `acq_pair_false`, `final_values`).
- `treiber2_nodes_envG_whole`, and its runner instance
  `treiber2_nodes_envG_whole_concrete` with `codeMatchesWN`/`runnerMatchesWN`.
-/
import Kraken.Promising.SLR.EnvG.ConcreteTreiber2
import Kraken.Promising.SLR.EnvG.A64MaskCfg
import Kraken.Promising.SLR.EnvG.A64MaskLink
open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
namespace Kraken.Promising.SLR.EnvG.Treiber2
open Kraken.Promising.SLR.EnvG.Treiber (casOp64 initVal_eq)
set_option mvcgen.warning false
set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

/-! ## The image -/

/-- **The `code` block of `treiber2_nodes.kl`, verbatim**: the runner's
executable, shared by both threads (`P0: worker done; P1: worker done`). -/
def treiber2NImage : Program := parseAArch64("
worker:
push:
  LDAR X2,[X0]
  STR X2,[X1,#8]
  MOV X3,X2
  CASAL X3,X1,[X0]
  CMP X3,X2
  B.NE push
pop:
  LDAR X2,[X0]
  CBZ X2,done
  LDR X4,[X2,#8]
  MOV X3,X2
  CASAL X3,X4,[X0]
  CMP X3,X2
  B.NE pop
  MOV X10,X2
  B done
done:
")

/-- info: 19 -/
#guard_msgs in
#eval treiber2NImage.length

/-- The image is `treiber2Worker` behind the `worker:` label. -/
theorem treiber2NImage_eq : treiber2NImage = .label "worker" :: treiber2Worker := by decide

theorem treiber2NImage_wf : Program.WF treiber2NImage := by decide
theorem treiber2Worker_wf : Program.WF treiber2Worker := by decide
theorem treiber2Worker_eq : treiber2Worker = Directive.label "push" :: treiber2Worker.tail := by decide
theorem treiber2Worker_sub : Program.subBlocksOfE treiber2Worker treiber2NImage = true := by decide
theorem treiber2Worker_exit : Program.exitCheck treiber2Worker "done" = true := by decide

section Lay

variable [layout : _root_.Layout]

/-- A label's address in the image. -/
abbrev labN (x : Label) : Int64 := (_root_.Executable.labels (layout treiber2NImage)).label x

/-! ## The runs in the image -/

section Runs

variable [Executable.ValidLayout (layout treiber2NImage)]

local instance treiber2NImage.env : CodeEnv := ⟨layout treiber2NImage⟩

theorem workerN_placedIn : Program.PlacedIn treiber2Worker :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := treiber2NImage) treiber2NImage_wf rfl (by decide))
    treiber2Worker_sub

/-- The worker's run in the image, from `push` (`worker_envGCAdj`'s
script). -/
theorem workerN_envGCAdj (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) :
    ∀ s g, workTable P w "push" s g →
      Safely ((layout treiber2NImage).instrStepEnv (SharedEnv.counted (EW P w)))
        (fun x => (x.1.2 = labN "done" ∧ Dn P w x.1.1.regs.X10.toBitVec x.2.1) ∨ False)
        ((s, labN "push"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EW P w))
    (Q := fun s σ => Dn P w s.regs.X10.toBitVec σ.1) (E := fun _ _ _ => False) (workTable P w) ?_
    treiber2Worker_eq treiber2Worker_wf workerN_placedIn (Program.last_of_check treiber2Worker_exit) s g hsg
  cfg_cases_env [treiber2Worker]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hd8, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj, SharedEnv.counted_step,
    SharedEnv.counted_ok] at *
  all_goals try (simp [hx0, hx1, hd8]; done)
  case vc5 =>
    rename_i s σ0 v σ1 rng hnone hld _
    have hP := vc_push_load _ hT v σ1.1 hld.1
    simp [hx1]
    exact (vc_push_str hL hw _ hP _).1
  case vc7 =>
    rename_i s σ0 v σ1 rng dm σ2 σ3 hld hst hf _
    simp [hx1, hd8] at hst
    obtain ⟨hdm, -, -⟩ := hst
    subst hdm
    simp [hx0, hd8]
  case vc8 =>
    rename_i s σ0 v σ1 rng dm σ2 σ3 hld hst hf _
    have hP := vc_push_load _ hT v σ1.1 hld.1
    simp [hx1, hd8] at hst
    obtain ⟨hdm, hso, -⟩ := hst
    subst hdm
    have hP2 : Pu2 P w (BitVec.setWidth 128 (BitVec.setWidth 64 v)) σ2.1 := by
      rcases hso with h | h <;> exact (vc_push_str hL hw _ hP _).2 _ σ2.1 (by simpa [Params.nd] using h)
    have h := (vc_push_cas hL hw _ (hP2.fence hf.1) (BitVec.setWidth 64 v) (by simp)).1
    simp [hx0, hx1]
    simpa [casOp64, Params.top] using h
  case vc9 =>
    rename_i s σ0 v σ1 rng dm σ2 σ3 old σ4 σ5 hbr σ6 hld hst hf1 hcas hf2 hf3 _
    have hP := vc_push_load _ hT v σ1.1 hld.1
    simp [hx1, hd8] at hst
    obtain ⟨hdm, hso, htk⟩ := hst
    subst hdm
    have hP2 : Pu2 P w (BitVec.setWidth 128 (BitVec.setWidth 64 v)) σ2.1 := by
      rcases hso with h | h <;> exact (vc_push_str hL hw _ hP _).2 _ σ2.1 (by simpa [Params.nd] using h)
    have hc := (vc_push_cas hL hw _ (hP2.fence hf1.1) (BitVec.setWidth 64 v) (by simp)).2 old σ4.1
      (by simpa [hx0, hx1, casOp64, Params.top] using hcas.1)
    simp at hbr
    have hs2 : σ1.2 ≤ σ2.2 := by omega
    rcases hc with ⟨-, hPu⟩ | ⟨heq, -⟩
    · refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8],
        .inl ⟨rfl, Pu.fence (Pu.fence hPu.pu hf2.1) hf3.1⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg
      have h1 := hld.2; have h2 := hcas.2; have h3 := hf1.2; have h4 := hf2.2; have h5 := hf3.2
      simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
      omega
    · exact absurd (by rw [heq]; exact BitVec.sub_self _) hbr
  case vc10 =>
    rename_i s σ0 v σ1 rng dm σ2 σ3 old σ4 σ5 hbr σ6 hld hst hf1 hcas hf2 hf3 _
    have hP := vc_push_load _ hT v σ1.1 hld.1
    simp [hx1, hd8] at hst
    obtain ⟨hdm, hso, -⟩ := hst
    subst hdm
    have hP2 : Pu2 P w (BitVec.setWidth 128 (BitVec.setWidth 64 v)) σ2.1 := by
      rcases hso with h | h <;> exact (vc_push_str hL hw _ hP _).2 _ σ2.1 (by simpa [Params.nd] using h)
    have hc := (vc_push_cas hL hw _ (hP2.fence hf1.1) (BitVec.setWidth 64 v) (by simp)).2 old σ4.1
      (by simpa [hx0, hx1, casOp64, Params.top] using hcas.1)
    simp at hbr
    rcases hc with ⟨hne, -⟩ | ⟨-, hPo⟩
    · exact absurd (TreiberCommon.bv64_eq_of_sub_eq_zero hbr) hne
    · simp [hx0, hx1, hd8]
      exact Po.fence (Po.fence hPo hf2.1) hf3.1
  case vc4 =>
    rename_i s σ0 v σ1 hz σ2 hld hf _
    simp at hz
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8],
      .inr (.inr ⟨rfl, Dn.fence (vc_pop_cbz _ (vc_pop_ldar (xcl := false) _ hT v σ1.1 (by simpa [hx0, Params.top] using hld.1)) hz _) hf.1⟩)⟩, .inl (by decide)⟩
  case vc9 =>
    rename_i s σ0 v σ1 hnz σ2 rng v4 σ3 σ4 hld hf1 hld2 hf2 _
    simp [hd8] at hnz hld2
    have hP1 : Pl P w v σ2.1 := (vc_pop_ldar (xcl := false) _ hT v σ1.1 (by simpa [hx0, Params.top] using hld.1)).fence hf1.1
    obtain ⟨u, h, rfl⟩ := hld2
    have hP3 := vc_pop_ldr _ hP1 u σ3.1 h.1
    have h := (vc_pop_cas hw _ (hP3.fence hf2.1) hnz).1
    simp [hx0]
    simpa [casOp64, Params.top] using h
  case vc10 =>
    rename_i s σ0 v σ1 hnz σ2 rng v4 σ3 σ4 old σ5 σ6 hbr σ7 hld hf1 hld2 hf2 hcas hf3 hf4 _
    simp [hd8] at hnz hld2
    have hP1 : Pl P w v σ2.1 := (vc_pop_ldar (xcl := false) _ hT v σ1.1 (by simpa [hx0, Params.top] using hld.1)).fence hf1.1
    obtain ⟨u, h, rfl⟩ := hld2
    have hP3 := vc_pop_ldr _ hP1 u σ3.1 h.1
    have hc := (vc_pop_cas hw _ (hP3.fence hf2.1) hnz).2 old σ5.1 (by simpa [hx0, casOp64, Params.top] using hcas.1)
    simp at hbr
    rcases hc with ⟨-, hPo⟩ | ⟨heq, -⟩
    · refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8],
        .inr (.inl ⟨rfl, Po.fence (Po.fence hPo hf3.1) hf4.1⟩)⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg
      have h1 := hld.2; have h2 := hcas.2; have h3 := hf1.2; have h4 := hf2.2; have h5 := hf3.2
      have h6 := hf4.2
      simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
      omega
    · exact absurd (by rw [heq]; exact BitVec.sub_self _) hbr
  case vc11 =>
    rename_i s σ0 v σ1 hnz σ2 rng v4 σ3 σ4 old σ5 σ6 hbr σ7 σ8 σ9 hld hf1 hld2 hf2 hcas hf3 hf4 hf5 hf6 _
    simp [hd8] at hnz hld2
    have hP1 : Pl P w v σ2.1 := (vc_pop_ldar (xcl := false) _ hT v σ1.1 (by simpa [hx0, Params.top] using hld.1)).fence hf1.1
    obtain ⟨u, h, rfl⟩ := hld2
    have hP3 := vc_pop_ldr _ hP1 u σ3.1 h.1
    have hc := (vc_pop_cas hw _ (hP3.fence hf2.1) hnz).2 old σ5.1 (by simpa [hx0, casOp64, Params.top] using hcas.1)
    simp at hbr
    rcases hc with ⟨hne, -⟩ | ⟨-, hDn⟩
    · exact absurd (TreiberCommon.bv64_eq_of_sub_eq_zero hbr) hne
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8],
      .inr (.inr ⟨rfl, ?_⟩)⟩, .inl (by decide)⟩
    simp
    exact ((((hDn.fence hf3.1).fence hf4.1).fence hf5.1).fence hf6.1).dn
  case vc1 => exact hT
  all_goals done

/-- The worker's purity run in the image, from `push`
(`treiber2Worker_relPure`'s script). -/
theorem workerN_relPure (rel : Loc → Pred) (t n : BitVec 64) (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v) :
    ∀ s g, workPureTable t n rel "push" s g →
      Safely ((layout treiber2NImage).instrStepEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)))
        (fun x => (x.1.2 = labN "done" ∧ True) ∨ False) ((s, labN "push"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel))
    (Q := fun _ _ => True) (E := fun _ _ _ => False) (workPureTable t n rel) ?_ treiber2Worker_eq
    treiber2Worker_wf workerN_placedIn (Program.last_of_check treiber2Worker_exit) s g hsg
  cfg_cases_env [treiber2Worker]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hd8, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals have hn' : ∀ v : Val, Pred.Pure (rel ⟨n + 8#64, 8⟩) v := hn
  all_goals try (simp [hx0, hx1, hd8, SharedEnv.relPureQ, Arch.storeKind, hn',
    show Arch.armv8.plainStore = .plain from rfl]; done)
  case vc7 =>
    rename_i s σ0 v σ1 rng dm σ2 hld hst _
    simp [hx1, hd8] at hst
    obtain ⟨rfl, -⟩ := hst
    simp [hx0, hd8]
  case vc8 =>
    rename_i s σ0 v σ1 rng dm σ2 hld hst _
    simp [hx1, hd8] at hst
    obtain ⟨rfl, -⟩ := hst
    simp [hx0, hx1, SharedEnv.relPureQ]
    -- the `casal` is a release RMW: unconstrained
    exact fun h => (h (by decide)).elim
  case vc9 =>
    rename_i s σ0 v σ1 rng dm σ2 old σ3 hbr hld hst hcas _
    simp [hx1, hd8] at hst
    obtain ⟨rfl, hst2⟩ := hst
    have h12 : σ1.2 ≤ σ2.2 := by omega
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], .inl rfl⟩,
      .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    have h1 := hld.2; have h2 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
    omega
  case vc10 =>
    rename_i s σ0 v σ1 rng dm σ2 old σ3 hbr hld hst hcas _
    simp [hx1, hd8] at hst
    obtain ⟨rfl, -⟩ := hst
    simp [hx0, hx1, hd8]
  case vc4 =>
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], .inr (.inr rfl)⟩,
      .inl (by decide)⟩
  case vc9 =>
    simp [hx0, SharedEnv.relPureQ]
    -- the `casal` is a release RMW: unconstrained
    exact fun h => (h (by decide)).elim
  case vc10 =>
    rename_i s σ0 v σ1 hnz rng v4 σ2 old σ3 hbr hld hld2 hcas _
    simp [hd8] at hld2
    have h12 : σ1.2 ≤ σ2.2 := by
      obtain ⟨_, ⟨_, h⟩, _⟩ := hld2
      omega
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], .inr (.inl rfl)⟩,
      .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    have h1 := hld.2; have h2 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
    omega
  case vc11 =>
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], .inr (.inr rfl)⟩,
      .inl (by decide)⟩
  all_goals done

end Runs

/-! ## The image's static facts -/

section Static

variable [Executable.ValidLayout (layout treiber2NImage)]

omit [Executable.ValidLayout (layout treiber2NImage)] in
theorem treiber2NImage_rmwLive : (layout treiber2NImage).rmwLive = true := by rw [Layout.apply_rmwLive]; decide

theorem treiber2NImage_phase1F : Phase1TreeF (layout treiber2NImage) :=
  phase1TreeF_of_dirs (by dirs_phase1F treiber2NImage)

omit [Executable.ValidLayout (layout treiber2NImage)] in
theorem treiber2NImage_noFault : DirsNoFault (layout treiber2NImage) := by dirs_no_fault' treiber2NImage

set_option maxRecDepth 8192 in
/-- **The entry `worker` is `push`'s address** (the label cell has size
`0`). -/
theorem labN_worker : labN "worker" = labN "push" := by
  have h0 : labN "worker" = (layout treiber2NImage).addrOf 0 :=
    Program.label_addrOf_drop treiber2NImage_wf.nodup (by decide) (by decide)
  have h1 : labN "push" = (layout treiber2NImage).addrOf 1 :=
    Program.label_addrOf_drop treiber2NImage_wf.nodup (by decide) (by decide)
  have hc : (layout treiber2NImage).2[0]? = some (Directive.label "worker", Kraken.Layout.size Directive 0) := by
    simp [Layout.apply_snd, Layout.frag, treiber2NImage]
  rw [h1, Executable.addrOf_succ _ hc, Executable.ValidLayout.label_size 0 "worker" _ hc, h0]
  simp

set_option maxRecDepth 8192 in
/-- `done`'s address is the end of the image. -/
theorem labN_done : labN "done" = (layout treiber2NImage).addrOf treiber2NImage.length := by
  have hd : labN "done" = (layout treiber2NImage).addrOf 18 :=
    Program.label_addrOf_drop treiber2NImage_wf.nodup (by decide) (by decide)
  have h18 : (layout treiber2NImage).2[18]? = some (Directive.label "done", Kraken.Layout.size Directive 18) := by
    simp [Layout.apply_snd, Layout.frag, treiber2NImage]
  rw [show treiber2NImage.length = 18 + 1 from rfl, Executable.addrOf_succ _ h18,
    Executable.ValidLayout.label_size 18 "done" _ h18, hd]
  simp

/-- **No step of the image at the exit label `done`.** -/
theorem workerN_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labN "done" → ¬ (layout treiber2NImage).instrStepEnv env x R := by
  rw [labN_done]
  exact not_instrStepEnv_of_end_labels env 1

end Static

/-! ## The rule -/

section Rule

variable [Executable.ValidLayout (layout treiber2NImage)]

/-- The whole-image worker's postcondition: `done` and `Dn` (the counter
projected away). -/
abbrev postWN (P : Params) (w : Nat) : MachineState × EStateA → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labN "done" ∧ Dn P w x.1.1.regs.X10.toBitVec x.2) ∨ False

omit [Executable.ValidLayout (layout treiber2NImage)] in
theorem postWN_end (P : Params) (w : Nat) : ∀ y, postWN P w y → y.1.2 = labN "done" :=
  fun _ ⟨_, h⟩ => h.elim And.left False.elim

omit [Executable.ValidLayout (layout treiber2NImage)] in
/-- **`hB` for the whole-image thread `w`** (`hB_w`'s proof). -/
theorem hB_wN (P : Params) {w : Nat} (hw : w < 2) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postWN P w (t.st.st, σ) → t.prom = [] → EnvRel w (plan P w) σ c t r g cl → cl → TB2 P c r g := by
  rintro c t r g cl σ ⟨_, hpost⟩ hp hrel -
  obtain ⟨-, hcom, hd⟩ := hpost.resolve_right id
  have hpre : σ.snap.mem.Prefix c.mem := ⟨hrel.snap.init, hrel.snap.msgs⟩
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact ⟨w, hw, t, hrel.ht, hcom.2.2.1, by rw [initVal_eq hrel.snap.init]; exact hcom.2.2.2.1,
      hd.imp (DonePop.mono hpre) (DoneCbz.mono hpre)⟩
  · rw [hp] at hts; cases hts

/-- **The whole-image thread `w`'s rule** (adjacency link at the image). -/
noncomputable def wRuleN (P : Params) (w : Nat) (hw : w < 2) : ThreadRuleRXF (I := isa) Arch.armv8 (TB2 P) w :=
  ThreadRuleRXF.ofSafelyEnvGFCAdj (post := postWN P w) (plan_valid P w) treiber2NImage_rmwLive
    treiber2NImage_phase1F (postWN_end P w) (workerN_stuck _) (hB_wN P hw)

/-- **The whole-image thread `w`'s rule excludes faults** (unconditional in
promises). -/
theorem wRuleN_noFault (P : Params) (w : Nat) (hw : w < 2) : NoFaultRuleF (wRuleN P w hw) :=
  noFaultRuleF_ofSafelyEnvGFCAdj_struct _ _ _ _ _ _ treiber2NImage_noFault

end Rule

/-! ## The start -/

/-- **A worker at its start in the whole image** (`i:X0=top; i:X1=n(i+1)`),
as the runner sets it up: the image, no declarations, pc at `worker`, end at
`done`, `x0 = t`, `x1 = n`, no private copy of any 8-byte word (`StartW`
with the image). -/
structure StartWN [layout : _root_.Layout] (t n : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout treiber2NImage
  decls : s.decls = {}
  pc : s.st.2 = labN "worker"
  endPc : s.endPc = labN "done"
  x0 : s.st.1.regs.X0.toBitVec = t
  x1 : s.st.1.regs.X1.toBitVec = n
  d8 : ∀ a, Mem.loadInt s.st.1.dmem a 8 = none

section Start

variable [Executable.ValidLayout (layout treiber2NImage)] {s0 s1 : isa.State} {initMem : List (Loc × Val)}

/-- **The whole-image thread `w`'s initial invariant** (`invW_init`). -/
theorem invWN_init {P : Params} (hL : TLocs P) {w : Nat} (hw : w < 2) (hD : ∀ d, P.D w d) {s : isa.State}
    (hs : [s0, s1][w]? = some s) (hS : StartWN P.t (P.n w) s)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal P.top = 0) :
    (wRuleN P w hw).Inv True (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem P w)
      (ghost₀ P) := by
  have htr : tRes (Config.init [s0, s1] initMem).mem P w = thrRes (Config.init [s0, s1] initMem).mem P w := by
    rcases w with _ | _ | w
    · rfl
    · rfl
    · omega
  rw [htr]
  obtain ⟨he, hds, hpc, hend, hx0, hx1, hd8⟩ := hS
  refine invGFCAdj_init hs rfl ⟨he, hds, hend, ?_⟩
  rw [show s.st = (s.st.1, labN "push") from Prod.ext rfl (hpc.trans labN_worker)]
  exact Safely.uncountA (workerN_envGCAdj P w hL hw _ (_, 0) ⟨hx0, hx1, hd8, .inl ⟨rfl, pu_init P hL hw hD _ hT0⟩⟩)

end Start

end Lay

/-! ## `NPSafeF`, purity and the theorem -/

/-- **The `NPSafeF` side, whole image.** -/
theorem treiber2N_whole_npSafeF (l : _root_.Layout) [Executable.ValidLayout (l treiber2NImage)]
    {t n0 n1 : BitVec 64} (hL : TLocs (tP2 t n0 n1)) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartWN (layout := l) t n0 s0) (h1 : StartWN (layout := l) t n1 s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0) :
    ∀ tid, tid < [s0, s1].length → ∀ k j, NPSafeF (model isa) Arch.armv8 (TB2 (tP2 t n0 n1)) tid k j True
      (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem (tP2 t n0 n1) tid)
      (ghost₀ (tP2 t n0 n1)) := by
  intro tid htid k j
  rcases tid with _ | _ | i
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _
      (invWN_init (layout := l) hL (by decide) (fun _ => trivial) rfl h0 hT0)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _
      (invWN_init (layout := l) hL (by decide) (fun _ => trivial) rfl h1 hT0)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- The threads' purity specifications in the whole image: the run to
`done`. -/
def treiber2NPureSpecW (l : _root_.Layout) [hv : Executable.ValidLayout (l treiber2NImage)] (rel : Loc → Pred) :
    Nat → RelPureSpec Arch.armv8 rel :=
  fun _ => { e := l treiber2NImage, valid := hv, endPc := labN (layout := l) "done",
             post := fun x => ∃ _ : Nat, (x.1.2 = labN (layout := l) "done" ∧ True) ∨ False,
             post_end := fun _ ⟨_, h⟩ => h.elim And.left False.elim }

/-- **The purity specifications hold at the start states.** -/
theorem treiber2NPureSpecW_init (l : _root_.Layout) [Executable.ValidLayout (l treiber2NImage)]
    {rel : Loc → Pred} {t n0 n1 : BitVec 64}
    (hn0 : ∀ v : Val, Pred.Pure (rel ⟨n0 + 8, 8⟩) v) (hn1 : ∀ v : Val, Pred.Pure (rel ⟨n1 + 8, 8⟩) v)
    {s0 s1 : isa.State} (h0 : StartWN (layout := l) t n0 s0) (h1 : StartWN (layout := l) t n1 s1) :
    ∀ tid s, [s0, s1][tid]? = some s → (treiber2NPureSpecW l rel tid).Holds s
  | 0, s, hs => by
    cases hs
    obtain ⟨he, hds, hpc, hend, hx0, hx1, hd8⟩ := h0
    refine ⟨he, hend, hds, ?_⟩
    rw [show s0.st = (s0.st.1, labN (layout := l) "push") from Prod.ext rfl (hpc.trans (labN_worker (layout := l)))]
    exact Safely.uncountA (workerN_relPure (layout := l) rel t n0 hn0 _ ((), 0) ⟨hx0, hx1, hd8, .inl rfl⟩)
  | 1, s, hs => by
    cases hs
    obtain ⟨he, hds, hpc, hend, hx0, hx1, hd8⟩ := h1
    refine ⟨he, hend, hds, ?_⟩
    rw [show s1.st = (s1.st.1, labN (layout := l) "push") from Prod.ext rfl (hpc.trans (labN_worker (layout := l)))]
    exact Safely.uncountA (workerN_relPure (layout := l) rel t n1 hn1 _ ((), 0) ⟨hx0, hx1, hd8, .inl rfl⟩)
  | _ + 2, _, hs => by cases hs

/-- **The two-thread Treiber stack `treiber2_nodes.kl` for AArch64 under
`Arch.armv8`, both threads running the whole `.kl` image** (on `EnvGCAdj`):
for a valid layout `l` of the `.kl`'s `code` block `treiber2NImage`, all
addresses `t` of `top` (8 bytes) and `n0`, `n1` of the nodes (links
`[n0 + 8]`, `[n1 + 8]`, 8 bytes) with `t ≠ n0 + 8`, `t ≠ n1 + 8`, `n0 ≠ n1`,
`n0 ≠ 0`, `n1 ≠ 0`: if both threads run the image from `worker` to `done`,
thread `0` with `x0 = t`, `x1 = n0` and thread `1` with `x0 = t`, `x1 = n1`,
each with no declarations and no private copy of an 8-byte word
(`StartWN`), and `top` is initially `0`, then every final configuration
reachable under `Arch.armv8` has
`(0:X10 = n0 ∧ 1:X10 = n1) ∨ (0:X10 = n1 ∧ 1:X10 = n0)`.

This is `treiber2_nodes_envG` with the runner's executable (the `code` block
with its `worker:` label, one layout for both threads). As there, only the
addresses' `Loc`s are distinguished and only final configurations are
constrained; faults are covered by `wRuleN_noFault`; the threads have no
declarations (the runner sets `decls` from the init block). -/
theorem treiber2_nodes_envG_whole {fuel : Nat} (l : _root_.Layout) [Executable.ValidLayout (l treiber2NImage)]
    (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8) (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartWN (layout := l) t n0 s0) (h1 : StartWN (layout := l) t n1 s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : Treiber2Final n0 n1 cfg := by
  have hL := tLocs_tP2 ht0 ht1 hn hn0 hn1
  refine final_of_relPureSafelyF Arch.armv8 fuel (B := TB2 (tP2 t n0 n1)) (Φ := Treiber2Final n0 n1)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_init hL _) (ghost₀_pend _) (treiber2NPureSpecW l _)
    (treiber2NPureSpecW_init l (fun v => ?_) (fun v => ?_) h0 h1) (treiber2N_whole_npSafeF l hL h0 h1 hT0) hc hf
    fun rF' g' E' hle hsize hB => ?_
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

/-! ## The runner's instance -/

open Kraken.Promising.SLR.EnvG.ConcreteTreiber2 (topAddr n1Addr n2Addr treiber2NodesKl treiber2InitMem)

/-- The runner's layout of the image: text at `0x100000`, each directive
its `fakeSize`. -/
@[reducible] def wLayout2N : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize treiber2NImage

instance wValid2N : Executable.ValidLayout (wLayout2N treiber2NImage) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-- Thread `0` as the runner prepares it: `X0 = top`, `X1 = n1`, from
`worker` to `done`. -/
def wNWorker0 : AArch64.State where
  exe := wLayout2N treiber2NImage
  endPc := 0x100000 + 60
  st := ({ regs := { X0 := 0x1000, X1 := 0x1100 } }, 0x100000)

/-- Thread `1` as the runner prepares it: `X0 = top`, `X1 = n2`. -/
def wNWorker1 : AArch64.State where
  exe := wLayout2N treiber2NImage
  endPc := 0x100000 + 60
  st := ({ regs := { X0 := 0x1000, X1 := 0x1200 } }, 0x100000)

/-- The `code` block of the `.kl` parses to `treiber2NImage`. -/
def codeMatchesWN (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.AArch64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => prog == treiber2NImage
    | .error _ => false

/-- The runner's threads run `wNWorker0`'s and `wNWorker1`'s executable, pc,
end, registers and private memory. -/
def runnerMatchesWN (src : String) : Bool :=
  let same (t : Thread isa) (s : AArch64.State) : Bool :=
    t.st.exe == s.exe && t.st.endPc == s.endPc && t.st.st.2 == s.st.2 &&
      t.st.st.1.regs == s.st.1.regs && t.st.st.1.dmem.isEmpty
  match Kraken.Litmus.parseProgram src >>= Kraken.Litmus.AArch64.prepareProgram with
  | .error _ => false
  | .ok pr => match pr.config.threads.toList with
    | [t0, t1] => same t0 wNWorker0 && same t1 wNWorker1
    | _ => false

/-- info: (true, true) -/
#guard_msgs in
#eval (codeMatchesWN treiber2NodesKl, runnerMatchesWN treiber2NodesKl)

section
attribute [local instance] wLayout2N

set_option maxRecDepth 8192 in
theorem labN_at {x : Label} (i : Nat) (hd : treiber2NImage.drop i = Program.fromLabel treiber2NImage x := by decide)
    (hne : Program.fromLabel treiber2NImage x ≠ [] := by decide) : labN x = (wLayout2N treiber2NImage).addrOf i :=
  Program.label_addrOf_drop treiber2NImage_wf.nodup hd hne

set_option maxRecDepth 8192 in
theorem wNWorker0_start : StartWN topAddr n1Addr wNWorker0 := by
  refine ⟨rfl, rfl, ?_, ?_, by decide, by decide, fun a => ?_⟩
  · show (0x100000 : Int64) = labN "worker"; rw [labN_at 0]; decide
  · show (0x100000 + 60 : Int64) = labN "done"; rw [labN_at 18]; decide
  simp [wNWorker0, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

set_option maxRecDepth 8192 in
theorem wNWorker1_start : StartWN topAddr n2Addr wNWorker1 := by
  refine ⟨rfl, rfl, ?_, ?_, by decide, by decide, fun a => ?_⟩
  · show (0x100000 : Int64) = labN "worker"; rw [labN_at 0]; decide
  · show (0x100000 + 60 : Int64) = labN "done"; rw [labN_at 18]; decide
  simp [wNWorker1, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

end

/-- **`(0:X10=n1 ∧ 1:X10=n2) ∨ (0:X10=n2 ∧ 1:X10=n1)`** for
`treiber2_nodes.kl` under `Arch.armv8`, both threads running the runner's
executable (the whole `code` block at `0x100000`): concrete instance of
`treiber2_nodes_envG_whole`. -/
theorem treiber2_nodes_envG_whole_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [wNWorker0, wNWorker1] treiber2InitMem) c)
    (hf : c.final = true) : Treiber2Final n1Addr n2Addr c :=
  treiber2_nodes_envG_whole wLayout2N topAddr n1Addr n2Addr (by decide) (by decide) (by decide) (by decide)
    (by decide) wNWorker0_start wNWorker1_start (by simp only [Config.init]; decide) hc hf

end Kraken.Promising.SLR.EnvG.Treiber2

#print axioms Kraken.Promising.SLR.EnvG.Treiber2.treiber2_nodes_envG_whole
#print axioms Kraken.Promising.SLR.EnvG.Treiber2.treiber2_nodes_envG_whole_concrete
#print axioms Kraken.Promising.SLR.EnvG.Treiber2.wRuleN_noFault
