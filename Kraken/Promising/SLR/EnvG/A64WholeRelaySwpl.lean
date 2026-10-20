/-
**`mp_relay3_swpl.kl` with every thread running the
whole `.kl` image** (under `Arch.armv8`). Additive:
`Relay.mp_relay3_swpl_envG` (`EnvG/RelaySwplPublic.lean`) is unchanged.

**`mp_relay3_swpl_envG_whole`**: `mp_relay3_swpl_envG`'s conclusion (at
every reachable final configuration the reader's `W4` is `43` and the data
word's final value is `43`), with the three threads' executable the whole
`code` block `relaySwpl3Img` under one layout: the writer from `writer` to
`wdone`, the relay from `relay` to `rdone`, the reader from `reader` to
`ddone`.

- **All three roles are masked**: the image's `swpl` is not phase-1 for the
  writer's and the reader's `EnvG`/`EnvGT` rules, so each role runs over its
  own cells (`relaySwpl3ImgW`: `0 … 6`, `relaySwpl3ImgY`: `8 … 16`,
  `relaySwpl3ImgD`: `18 … 23`); the dead `NOP`s behind `wdone:`/`rdone:` are
  masked, `ddone` ends the image.
- **Writer**: `ThreadRuleRX.ofSafelyEnvGM` from `writerT3_envG_at`
  (`EnvG/A64WholeRelayVCGen.lean`: the `.kl`'s writer text is `mp_relay3`'s);
  into the take route by `NPSafe.toP`.
- **Relay**: `ThreadRuleRXGS.ofSafelyEnvGTRCM` (`EnvG/A64MaskTC.lean`) from
  `relaySwplY3_envGTC`, `relaySwpl_envGTC`'s script at the `.kl`'s labels
  (one more fence and the `b rdone`).
- **Reader**: `ThreadRuleRXGS.ofSafelyEnvGTM` from `readerT3_envGT_at`.
- **Ghost, resources, initial erasure and final argument**: the relay proof's
  (`relayParams`, `relayGhost`, `relayRes`, `erase_relayInit`, `YPost`,
  `relay_final`); the start-resource computations are those of
  `invYW_init`, `invYS_init` and `invD_init`.
- **Purity**: `writerT3_relPure_at`, `relaySwplY3_relPure` (new, the
  `swpl` relay's purity script at the `.kl`'s labels), `readerT3_relPure_at`
  at the unmasked image.
-/
import Kraken.Promising.SLR.EnvG.A64WholeRelayPublic
import Kraken.Promising.SLR.EnvG.RelaySwplPublic
import Kraken.Promising.SLR.EnvG.A64MaskTC
import Kraken.Promising.SLR.EnvG.A64MaskHelpers

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Mp Kraken.Promising.SLR.MpTrees
open Kraken.Promising.SLR.EnvG.MpSmoke Kraken.Promising.SLR.EnvG.MpLink Kraken.Promising.SLR.MpPublic
open Kraken.Promising.SLR.EnvG.MpRelPure Kraken.Promising.SLR.EnvG.TakeSmoke Kraken.Promising.SLR.EnvG.TakeMp

namespace Kraken.Promising.SLR.EnvG.Relay

set_option mvcgen.warning false
set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

/-! ## The image, the relay's text and the masks -/

/-- **The `code` block of `mp_relay3_swpl.kl`, verbatim**: the runner's
executable, shared by the three threads (`P0: writer wdone; P1: relay rdone;
P2: reader ddone`). -/
def relaySwpl3Img : Program := parseAArch64("
writer:
  MOV W2,#1
  STR W2,[X1]
  MOV W3,#1
  STLR W3,[X0]
  B wdone
wdone:
  NOP
relay:
  LDAR W3,[X0]
  CBZ W3,relay
  MOV W5,#43
  STR W5,[X1]
  MOV W6,#1
  SWPL W6,W7,[X2]
  B rdone
rdone:
  NOP
reader:
  LDAR W3,[X0]
  CBZ W3,reader
  LDR W4,[X1]
  B ddone
ddone:
")

/-- The `swpl` relay's role text (`relay` to `rdone:`). -/
def relaySwplT3 : Program := parseAArch64("
relay:
  LDAR W3,[X0]
  CBZ W3,relay
  MOV W5,#43
  STR W5,[X1]
  MOV W6,#1
  SWPL W6,W7,[X2]
  B rdone
rdone:
")

/-- The image is `mp_relay3`'s writer and reader texts around the `swpl`
relay's, with the dead `NOP`s behind `wdone:` and `rdone:`; outside the
relay's `swpl` it is `relay3Img`. -/
theorem relaySwpl3Img_eq :
    relaySwpl3Img.take 7 = writerT3 ∧ (relaySwpl3Img.drop 8).take 9 = relaySwplT3 ∧
      relaySwpl3Img.drop 18 = readerT3 ∧ relaySwpl3Img.length = 24 := by decide

/-- **The writer's mask**: cells `0 … 6` (`writer` to `wdone:`) kept. -/
abbrev relaySwpl3ImgW : Program := relaySwpl3Img.maskKeep (keepRange 0 7)
/-- **The relay's mask**: cells `8 … 16` (`relay` to `rdone:`) kept. -/
abbrev relaySwpl3ImgY : Program := relaySwpl3Img.maskKeep (keepRange 8 17)
/-- **The reader's mask**: cells `18 … 23` (`reader` to `ddone:`) kept. -/
abbrev relaySwpl3ImgD : Program := relaySwpl3Img.maskKeep (keepRange 18 24)

/-- Every cell of the relay's text is phase-1 with release-kind RMWs. -/
theorem relaySwplT3_dirsR : ∀ d ∈ relaySwplT3, ∀ (e : _root_.Executable) z, DirPhase1R Arch.armv8 e d z := by
  dirs_phase1R_any relaySwplT3

/-- **A range mask keeping only cells of `relay3Img` is phase-1** (`EnvG`
shape): the kept slice is `relay3Img`'s (`relay3Img_dirsPhase1`). -/
theorem phase1Tree_maskKeep_relay3 [layout : _root_.Layout] [Executable.ValidLayout (layout relaySwpl3Img)]
    {lo hi : Nat} (hs : (relaySwpl3Img.drop lo).take (hi - lo) = (relay3Img.drop lo).take (hi - lo)) :
    Phase1Tree Arch.armv8 (layout (relaySwpl3Img.maskKeep (keepRange lo hi))) :=
  haveI := ValidLayout.of_mask (maskOf_layout (layout := layout) (keepRange lo hi) relaySwpl3Img)
  phase1Tree_of_dirs (dirsPhase1_layout (mem_maskKeep_range (Φd := fun d => ∀ e z, DirPhase1 Arch.armv8 e d z)
    (fun d hd => relay3Img_dirsPhase1 d (List.mem_of_mem_drop (List.mem_of_mem_take (hs ▸ hd))))
    (fun l => label_dirPhase1Y l) (byteArray_dirPhase1Y _)))

section Lay

variable [layout : _root_.Layout]

/-- A label's address in the image. -/
abbrev labS3 (x : Label) : Int64 := (_root_.Executable.labels (layout relaySwpl3Img)).label x

theorem relaySwpl3Img_rmwLive : (layout relaySwpl3Img).rmwLive = true := by rw [Layout.apply_rmwLive]; decide

theorem relaySwpl3Img_noFault : DirsNoFault (layout relaySwpl3Img) := by dirs_no_fault' relaySwpl3Img

variable [Executable.ValidLayout (layout relaySwpl3Img)]

theorem relaySwpl3ImgW_phase1 : Phase1Tree Arch.armv8 (layout relaySwpl3ImgW) :=
  phase1Tree_maskKeep_relay3 (by decide)

theorem relaySwpl3ImgD_phase1 : Phase1Tree Arch.armv8 (layout relaySwpl3ImgD) :=
  phase1Tree_maskKeep_relay3 (by decide)

/-- The relay's mask is phase-1 with release-kind RMWs: its kept slice is
`relaySwplT3`. -/
theorem relaySwpl3ImgY_phase1R : Phase1TreeR Arch.armv8 (layout relaySwpl3ImgY) :=
  haveI := ValidLayout.of_mask (maskOf_layout (layout := layout) (keepRange 8 17) relaySwpl3Img)
  phase1TreeR_of_dirs (dirsPhase1R_layout (mem_maskKeep_range (Φd := fun d => ∀ e z, DirPhase1R Arch.armv8 e d z)
    (fun d hd => relaySwplT3_dirsR d (relaySwpl3Img_eq.2.1 ▸ hd))
    (fun l => label_dirPhase1R_any _ l) (byteArray_dirPhase1R_any _ _)))

set_option maxRecDepth 8192 in
/-- **No step of the writer's mask at `wdone`** (the masked `NOP`). -/
theorem writerS3_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labS3 "wdone" → ¬ (layout relaySwpl3ImgW).instrStepEnv env x R := by
  haveI := ValidLayout.of_mask (maskOf_layout (layout := layout) (keepRange 0 7) relaySwpl3Img)
  intro x R hx
  exact not_instrStepEnv_of_byteArray (q := relaySwpl3ImgW) (i := 7) (b := .mk #[]) env (by decide) x R
    (hx.trans (label_addrOf_succ_maskKeep (keepRange 0 7) (i := 6) (by decide) (by decide) (by decide) (by decide)))

set_option maxRecDepth 8192 in
/-- **No step of the relay's mask at `rdone`** (the masked `NOP`). -/
theorem relayS3_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labS3 "rdone" → ¬ (layout relaySwpl3ImgY).instrStepEnv env x R := by
  haveI := ValidLayout.of_mask (maskOf_layout (layout := layout) (keepRange 8 17) relaySwpl3Img)
  intro x R hx
  exact not_instrStepEnv_of_byteArray (q := relaySwpl3ImgY) (i := 17) (b := .mk #[]) env (by decide) x R
    (hx.trans (label_addrOf_succ_maskKeep (keepRange 8 17) (i := 16) (by decide) (by decide) (by decide) (by decide)))

set_option maxRecDepth 8192 in
/-- **No step of the reader's mask at `ddone`** (the end of the image). -/
theorem readerS3_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labS3 "ddone" → ¬ (layout relaySwpl3ImgD).instrStepEnv env x R := by
  haveI := ValidLayout.of_mask (maskOf_layout (layout := layout) (keepRange 18 24) relaySwpl3Img)
  intro x R hx
  have h := not_instrStepEnv_of_end_labels (p := relaySwpl3ImgD) env 1
  exact h x R
    (hx.trans ((label_addrOf_succ_maskKeep (keepRange 18 24) (i := 23) (by decide) (by decide) (by decide)
      (by decide)).trans rfl))

/-! ## The runs -/

/-- The writer's run over its mask, at the image's labels (`writerT3_envG_at`). -/
theorem writerS3_envG (P : Params) (hL : MpLocs P) (tid : Nat) :
    ∀ s g, writerTable3 P tid "writer" s g →
      Safely ((layout relaySwpl3ImgW).instrStepEnv (E P tid))
        (fun x => (x.1.2 = labS3 "wdone" ∧ W3 P x.2) ∨ False) ((s, labS3 "writer"), g) := by
  haveI := ValidLayout.of_mask (maskOf_layout (layout := layout) (keepRange 0 7) relaySwpl3Img)
  letI : CodeEnv := ⟨layout relaySwpl3ImgW⟩
  intro s g hsg
  exact Safely.atImageLabels (maskOf_layout _ _) (writerT3_envG_at P hL tid (Program.PlacedIn.of_placedE
    (Program.placed_of_layout (p := relaySwpl3ImgW) (by decide) rfl (by decide)) (by decide))
    (Program.last_of_check (lx := "wdone") (by decide)) s g hsg)

/-- The reader's run over its mask, at the image's labels (`readerT3_envGT_at`). -/
theorem readerS3_envGT (Q : Params) (tid : Nat) :
    ∀ s g, readerTable3 Q tid "reader" s g →
      Safely ((layout relaySwpl3ImgD).instrStepEnv (SharedEnv.counted (ET tid)))
        (fun x => (x.1.2 = labS3 "ddone" ∧
          (Own43 Q x.2.1.r ∧ (x.2.1.cl → x.1.1.regs.X4.toBitVec.setWidth 32 = 43))) ∨ False)
        ((s, labS3 "reader"), g) := by
  haveI := ValidLayout.of_mask (maskOf_layout (layout := layout) (keepRange 18 24) relaySwpl3Img)
  letI : CodeEnv := ⟨layout relaySwpl3ImgD⟩
  intro s g hsg
  exact Safely.atImageLabels (maskOf_layout _ _) (readerT3_envGT_at Q tid (Program.PlacedIn.of_placedE
    (Program.placed_of_layout (p := relaySwpl3ImgD) (by decide) rfl (by decide)) (by decide))
    (Program.last_of_check (lx := "ddone") (by decide)) s g hsg)

/-- The `swpl` relay's table at the `.kl`'s labels: `RK1` at `relay`, `RK4`
at `rdone` (`relaySwplTable`). -/
abbrev relaySwplTable3 (rp : RP) (tid : Nat) :
    Label → MachineData → (SharedEnv.counted (ERC rp tid)).State → Prop :=
  fun lb s σ => RFrame rp s ∧ ((lb = "relay" ∧ RK1 rp σ.1) ∨ (lb = "rdone" ∧ RK4 rp σ.1))

section RelayY

local instance relaySwpl3ImgY.env : CodeEnv := ⟨layout relaySwpl3ImgY⟩

theorem relaySwplY3_placedIn : Program.PlacedIn relaySwplT3 :=
  haveI := ValidLayout.of_mask (maskOf_layout (layout := layout) (keepRange 8 17) relaySwpl3Img)
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := relaySwpl3ImgY) (by decide) rfl (by decide)) (by decide)

/-- The `swpl` relay's run over its mask, at the mask's labels
(`relaySwpl_envGTC`'s script). -/
theorem relaySwplY3_envGTC' (rp : RP) (hL : MpLocs rp.Q) (tid : Nat) :
    ∀ s g, relaySwplTable3 rp tid "relay" s g →
      Safely (cenv.instrStepEnv (SharedEnv.counted (ERC rp tid)))
        (fun x => (x.1.2 = (_root_.Executable.labels cenv).label "rdone" ∧ RK4 rp x.2.1) ∨ False)
        ((s, (_root_.Executable.labels cenv).label "relay"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (ERC rp tid)) (Q := fun _ σ => RK4 rp σ.1)
    (E := fun _ _ _ => False) (relaySwplTable3 rp tid) ?_ (by rfl) (by decide) relaySwplY3_placedIn
    (Program.last_of_check (lx := "rdone") (by decide)) s g hsg
  cfg_cases_env [relaySwplT3]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hx0, hx1, hx2, hdf, hdd, hdg⟩, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals try (simp [hx0, hx1, hx2, hdf, hdd, hdg]; done)
  case vc4 =>
    -- the back edge (`cbz` taken): `RK1` again; the counter moved
    rename_i s σ0 b σ1 hst1 hcbz σ2 hf _
    simp only [fenceMono_le_counted, fenceMono_le_envGTC, SharedEnv.counted_step, envGTC_step_load] at hst1 hf
    simp [hx0] at hst1
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simp [hx2], by simp [hdf],
      by simp [hdd], by simp [hdg]⟩, .inl ⟨rfl, RK1.fence (((vc_r1c tid σ0.1 hT) _ σ1.1 hst1.1).1
        (by simpa using hcbz)) hf.1⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg; omega
  case vc6 =>
    rename_i v σ1 hst1 hcbz σ2 hf1 σ3 hf2 rng hdm _
    simp only [fenceMono_le_counted, fenceMono_le_envGTC, SharedEnv.counted_step, envGTC_step_load] at hst1 hf1 hf2
    simp [hx0] at hst1
    have hK2 : RK2 rp σ3.1 :=
      RK2.fence (RK2.fence (((vc_r1c tid _ hT) _ σ1.1 hst1.1).2 (by simpa using hcbz)) hf1.1) hf2.1
    simpa [hx1] using (vc_r2c hL tid σ3.1 hK2).1
  case vc8 =>
    rename_i v σ1 hst1 hcbz σ2 hf1 σ3 hf2 rng dm σ4 hd σ5 hf3 _
    simp [hx1, hdd] at hd
    simp [hd.1, hx2, hdg]
  case vc9 =>
    rename_i v σ1 hst1 hcbz σ2 hf1 σ3 hf2 rng dm σ4 hd σ5 hf3 _
    simp only [fenceMono_le_counted, fenceMono_le_envGTC, SharedEnv.counted_step, envGTC_step_load] at hst1 hf1 hf2 hf3
    simp [hx0] at hst1
    have hK2 : RK2 rp σ3.1 :=
      RK2.fence (RK2.fence (((vc_r1c tid _ hT) _ σ1.1 hst1.1).2 (by simpa using hcbz)) hf1.1) hf2.1
    simp [hx1, hdd] at hd
    have hK3 : RK3 rp σ4.1 := by
      rcases hd.2 with hst | hst <;> exact (vc_r2c hL tid σ3.1 hK2).2 _ σ4.1 (by simpa using hst)
    simpa [hx2, hd.1, hdg] using (vc_r3c hL tid σ5.1 (RK3.fence hK3 hf3.1) _ rmwOpBits_one).1
  case vc10 =>
    rename_i v σ1 hst1 hcbz σ2 hf1 σ3 hf2 rng dm σ4 hd σ5 hf3 b σ6 hst6 σ7 hf6 _
    simp only [fenceMono_le_counted, fenceMono_le_envGTC, SharedEnv.counted_step, envGTC_step_load] at hst1 hf1 hf2 hf3 hf6
    simp [hx0] at hst1
    have hK2 : RK2 rp σ3.1 :=
      RK2.fence (RK2.fence (((vc_r1c tid _ hT) _ σ1.1 hst1.1).2 (by simpa using hcbz)) hf1.1) hf2.1
    simp [hx1, hdd] at hd
    have hK3 : RK3 rp σ4.1 := by
      rcases hd.2 with hst | hst <;> exact (vc_r2c hL tid σ3.1 hK2).2 _ σ4.1 (by simpa using hst)
    simp [hx2] at hst6
    have h4 : RK4 rp σ6.1 := (vc_r3c hL tid σ5.1 (RK3.fence hK3 hf3.1) _ rmwOpBits_one).2 _ σ6.1 hst6.1
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simp [hx2], by simp [hd.1, hdf],
      by simp [hd.1, hdd], by simp [hd.1, hdg]⟩, .inr ⟨rfl, RK4.fence h4 hf6.1⟩⟩, .inl (by decide)⟩
  case vc1 => exact hT
  all_goals done

end RelayY

/-- **The `swpl` relay's run over its mask**, at the image's labels. -/
theorem relaySwplY3_envGTC (rp : RP) (hL : MpLocs rp.Q) (tid : Nat) :
    ∀ s g, relaySwplTable3 rp tid "relay" s g →
      Safely ((layout relaySwpl3ImgY).instrStepEnv (SharedEnv.counted (ERC rp tid)))
        (fun x => (x.1.2 = labS3 "rdone" ∧ RK4 rp x.2.1) ∨ False) ((s, labS3 "relay"), g) :=
  fun s g hsg => Safely.atImageLabels (maskOf_layout _ _) (relaySwplY3_envGTC' rp hL tid s g hsg)

/-! ## The purity runs, in the image -/

section ImageP

local instance relaySwpl3Img.env : CodeEnv := ⟨layout relaySwpl3Img⟩

theorem relaySwpl3Img_placed : Program.Placed relaySwpl3Img "writer" :=
  Program.placed_of_layout (by decide) rfl (by decide)

theorem relaySwplA3_placedIn : Program.PlacedIn relaySwplT3 :=
  Program.PlacedIn.of_placedE relaySwpl3Img_placed (by decide)

/-- The `swpl` relay's purity run in the image (`relaySwpl_relPure`'s
script): its only non-release write is to `⟨d, 4⟩`. -/
theorem relaySwplY3_relPure (rel : Loc → Pred) (f1 d f2 : BitVec 64) (hd : ∀ v, Pred.Pure (rel ⟨d, 4⟩) v) :
    ∀ s g, relayPureTable3 f1 d f2 rel "relay" s g →
      Safely ((layout relaySwpl3Img).instrStepEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)))
        (fun x => (x.1.2 = labS3 "rdone" ∧ True) ∨ False) ((s, labS3 "relay"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel))
    (Q := fun _ _ => True) (E := fun _ _ _ => False) (relayPureTable3 f1 d f2 rel) ?_ (by rfl) (by decide)
    relaySwplA3_placedIn (Program.last_of_check (lx := "rdone") (by decide))
    s g hsg
  cfg_cases_env [relaySwplT3]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨hT, rfl, rfl⟩ := ‹(_ → _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [forall_const] at hT
  case vc4 =>
    -- the back edge (`cbz` taken): the counter moved
    have hn := (‹(SharedEnv.counted _).step _ _ _ _›).2
    refine Table.ofLabelsEnv_at ⟨by decide, fun _ => ⟨by simpa using hT.1, by simpa using hT.2.1,
      by simpa using hT.2.2.1, by simpa using hT.2.2.2.1, by simpa using hT.2.2.2.2.1, by simpa using hT.2.2.2.2.2⟩,
      .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg; simp at hn
  case vc9 =>
    -- the swap is a release RMW (`swpl`): unconstrained
    exact fun h => (h (by decide)).elim
  case vc10 => exact Table.ofLabelsEnv_at ⟨by decide, fun h => absurd h (by decide), .inl (by decide)⟩
  all_goals simp_all [Arch.storeKind, show Arch.armv8.plainStore = .plain from rfl]

end ImageP

end Lay

/-! ## The rules -/

section Rules

variable [layout : _root_.Layout] [Executable.ValidLayout (layout relaySwpl3Img)]

/-- The whole-image writer's postcondition: its exit label and `W3`. -/
abbrev postWS3 (rp : RP) : MachineState × EStateA → Prop :=
  fun x => (x.1.2 = labS3 "wdone" ∧ W3 rp.P x.2) ∨ False

omit [Executable.ValidLayout (layout relaySwpl3Img)] in
theorem postWS3_end (rp : RP) : ∀ y, postWS3 rp y → y.1.2 = labS3 "wdone" :=
  fun _ h => h.elim And.left False.elim

omit [Executable.ValidLayout (layout relaySwpl3Img)] in
/-- **`hB` for the whole-image writer** (`hB_YW`'s proof): it keeps the token
`W`. -/
theorem hB_WS3 (rp : RP) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postWS3 rp (t.st.st, σ) → t.prom = [] → EnvRel tid (mpPlan rp.P) σ c t r g cl → cl → YPost rp c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, hW⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inl hW.2
  · rw [hp] at hts; cases hts

/-- **The whole-image writer's rule** (`EnvG`, over its mask). -/
def relayRuleWS3 (rp : RP) (hL : MpLocs rp.P) (tid : Nat) : ThreadRuleRX (I := isa) Arch.armv8 (YPost rp) tid :=
  ThreadRuleRX.ofSafelyEnvGM (post := postWS3 rp) (maskOf_layout _ _) (mpPlan_valid hL) relaySwpl3Img_rmwLive
    relaySwpl3ImgW_phase1 (postWS3_end rp) (writerS3_stuck _) (hB_WS3 rp tid)

/-- **The whole-image writer's rule excludes faults.** -/
theorem relayRuleWS3_noFault (rp : RP) (hL : MpLocs rp.P) (tid : Nat) : NoFaultRule (relayRuleWS3 rp hL tid) :=
  noFaultRule_ofSafelyEnvGM _ _ _ _ _ _ _ relaySwpl3Img_noFault

/-- The whole-image relay's postcondition: its exit label and `RK4` (the
counter projected away). -/
abbrev postYS3 (rp : RP) : MachineState × EStateA → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labS3 "rdone" ∧ RK4 rp x.2) ∨ False

omit [Executable.ValidLayout (layout relaySwpl3Img)] in
theorem postYS3_end (rp : RP) : ∀ y, postYS3 rp y → y.1.2 = labS3 "rdone" :=
  fun _ ⟨_, h⟩ => h.elim And.left False.elim

omit [Executable.ValidLayout (layout relaySwpl3Img)] in
/-- **`hB` for the whole-image relay** (`hB_Y`'s proof): it keeps the token
`W2`. -/
theorem hB_YS3 (rp : RP) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postYS3 rp (t.st.st, σ) → t.prom = [] → EnvRel tid (mpPlan rp.Q) σ c t r g cl → cl → YPost rp c r g := by
  rintro c t r g cl σ ⟨_, hpost⟩ hp hrel -
  obtain ⟨-, hW⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inr (.inl hW)
  · rw [hp] at hts; cases hts

/-- **The whole-image `swpl` relay's rule** (`EnvGTC`, over its mask). -/
def relayRuleYS3 (rp : RP) (hL : MpLocs rp.Q) (tid : Nat) : ThreadRuleRXGS (I := isa) G₀ Arch.armv8 (YPost rp) tid :=
  ThreadRuleRXGS.ofSafelyEnvGTRCM (post := postYS3 rp) (maskOf_layout _ _) (mpPlan_valid hL) relaySwpl3Img_rmwLive
    relaySwpl3ImgY_phase1R (postYS3_end rp) (relayS3_stuck _) (hB_YS3 rp tid)

/-- **The whole-image relay's rule excludes faults.** -/
theorem relayRuleYS3_noFault (rp : RP) (hL : MpLocs rp.Q) (tid : Nat) : NoFaultRuleS (relayRuleYS3 rp hL tid) :=
  noFaultRule_ofSafelyEnvGTRCM _ _ _ _ _ _ _ relaySwpl3Img_noFault

/-- The whole-image reader's postcondition: its exit label, `Own43`, and
`W4 = 43` under the clean flag (the counter projected away). -/
abbrev postDS3 (rp : RP) : MachineState × EStateA → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labS3 "ddone" ∧
    (Own43 rp.Q x.2.r ∧ (x.2.cl → x.1.1.regs.X4.toBitVec.setWidth 32 = 43))) ∨ False

omit [Executable.ValidLayout (layout relaySwpl3Img)] in
theorem postDS3_end (rp : RP) : ∀ y, postDS3 rp y → y.1.2 = labS3 "ddone" :=
  fun _ ⟨_, h⟩ => h.elim And.left False.elim

omit [Executable.ValidLayout (layout relaySwpl3Img)] in
/-- **`hB` for the whole-image reader** (thread `2`; `hB_D`'s proof). -/
theorem hB_DS3 (rp : RP) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postDS3 rp (t.st.st, σ) → t.prom = [] → EnvRel 2 rdPlan σ c t r g cl → cl → YPost rp c r g := by
  rintro c t r g cl σ ⟨_, hpost⟩ hp hrel hcl
  obtain ⟨-, hown, hx4⟩ := hpost.resolve_right id
  obtain rfl : r = σ.r := by
    rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
    · rfl
    · rw [hp] at hts; cases hts
  exact .inr (.inr ⟨⟨t, hrel.ht, hx4 (hrel.cl hcl)⟩, hown⟩)

/-- **The whole-image reader's rule** (`EnvGT`, thread `2`, over its mask). -/
def relayRuleDS3 (rp : RP) : ThreadRuleRXGS (I := isa) G₀ Arch.armv8 (YPost rp) 2 :=
  ThreadRuleRXGS.ofSafelyEnvGTM (post := postDS3 rp) (maskOf_layout _ _) rdPlan_valid relaySwpl3Img_rmwLive
    relaySwpl3ImgD_phase1 (postDS3_end rp) (readerS3_stuck _) (hB_DS3 rp)

/-- **The whole-image reader's rule excludes faults.** -/
theorem relayRuleDS3_noFault (rp : RP) : NoFaultRuleS (relayRuleDS3 rp) :=
  noFaultRule_ofSafelyEnvGTM _ _ _ _ _ _ _ relaySwpl3Img_noFault

end Rules

/-! ## The start -/

/-- **The writer at its start in the whole image**, as the runner sets it up
(`0:X0=f1; 0:X1=d`): the image, no declarations, pc at `writer`, end at
`wdone`, neither word in `dmem`. -/
structure StartWS3 [layout : _root_.Layout] (f1 d : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout relaySwpl3Img
  decls : s.decls = {}
  pc : s.st.2 = labS3 "writer"
  endPc : s.endPc = labS3 "wdone"
  x0 : s.st.1.regs.X0.toBitVec = f1
  x1 : s.st.1.regs.X1.toBitVec = d
  df : Mem.loadInt s.st.1.dmem f1 4 = none
  dd : Mem.loadInt s.st.1.dmem d 4 = none

/-- **The relay at its start in the whole image** (`1:X0=f1; 1:X1=d;
1:X2=f2`): pc at `relay`, end at `rdone`, none of the three words in
`dmem`. -/
structure StartYS3 [layout : _root_.Layout] (f1 f2 d : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout relaySwpl3Img
  decls : s.decls = {}
  pc : s.st.2 = labS3 "relay"
  endPc : s.endPc = labS3 "rdone"
  x0 : s.st.1.regs.X0.toBitVec = f1
  x1 : s.st.1.regs.X1.toBitVec = d
  x2 : s.st.1.regs.X2.toBitVec = f2
  df1 : Mem.loadInt s.st.1.dmem f1 4 = none
  dd : Mem.loadInt s.st.1.dmem d 4 = none
  df2 : Mem.loadInt s.st.1.dmem f2 4 = none

/-- **The reader at its start in the whole image** (`2:X0=f2; 2:X1=d`): pc
at `reader`, end at `ddone`, neither word in `dmem`. -/
structure StartDS3 [layout : _root_.Layout] (f2 d : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout relaySwpl3Img
  decls : s.decls = {}
  pc : s.st.2 = labS3 "reader"
  endPc : s.endPc = labS3 "ddone"
  x0 : s.st.1.regs.X0.toBitVec = f2
  x1 : s.st.1.regs.X1.toBitVec = d
  df : Mem.loadInt s.st.1.dmem f2 4 = none
  dd : Mem.loadInt s.st.1.dmem d 4 = none

section Inv

variable [layout : _root_.Layout] [Executable.ValidLayout (layout relaySwpl3Img)] {f1 f2 d : BitVec 64}
  {sW sY sR : isa.State} {initMem : List (Loc × Val)}

/-- **The whole-image writer's initial invariant** (thread `0`;
`invYW_init`'s resource computation). -/
theorem invWS3_init (hL : RelayLocs f1 f2 d) (hW : StartWS3 f1 d sW) :
    (relayRuleWS3 (relayParams f1 f2 d) hL.P 0).Inv True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) 0) (relayGhost (relayParams f1 f2 d)) := by
  refine invGM_init (s := sW) rfl rfl ⟨hW.exe, hW.decls, hW.endPc, ?_⟩
  rw [show sW.st = (sW.st.1, labS3 "writer") from Prod.ext rfl hW.pc]
  refine writerS3_envG _ hL.P 0 _ _ ⟨⟨hW.x0, hW.x1, hW.df, hW.dd⟩,
    .inl ⟨rfl, ⟨relayGhost_rel_F1 _, relayGhost_rel_Dt hL⟩, ?_⟩⟩
  simp only [σInit, Own0, relayRes, ↓reduceIte, writerRes, Res.initOf, Perm.init, writerFrac]
  exact ⟨by simp, fun p hp => by rw [hp.2], by simp, by simp <;> decide⟩

/-- **The whole-image relay's initial invariant** (thread `1`; `invY_init`'s
resource computation). -/
theorem invYS3_init (hL : RelayLocs f1 f2 d) (hY : StartYS3 f1 f2 d sY) :
    (relayRuleYS3 (relayParams f1 f2 d) hL.Q 1).Inv True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) 1) (relayGhost (relayParams f1 f2 d)) := by
  refine invGTRCM_init (s := sY) rfl rfl ⟨hY.exe, hY.decls, hY.endPc, ?_⟩
  rw [show sY.st = (sY.st.1, labS3 "relay") from Prod.ext rfl hY.pc]
  refine Safely.uncountA (relaySwplY3_envGTC _ hL.Q 1 _ (_, 0) ⟨⟨hY.x0, hY.x1, hY.x2, hY.df1, hY.dd, hY.df2⟩,
    .inl ⟨rfl, ⟨relayGhost_rel_F1 _, relayGhost_rel_Dt hL, ?_, 0, by show 0 < 2; decide, ?_, OkPred.flag⟩,
      relayGhost_rel_F2 hL.q_ne, ?_, ?_⟩⟩)
  · simp [σInit, Views.getFwd]
  · simp [σInit, relayRes, relayThreadRes]
  · simp [σInit, relayRes, relayThreadRes, Res.initOf, Perm.init, yFrac]; grind
  · simp [σInit, relayRes, relayThreadRes, Res.initOf, Perm.init, yFrac]

/-- **The whole-image reader's initial invariant** (thread `2`;
`invD_init`'s resource computation). -/
theorem invDS3_init (hL : RelayLocs f1 f2 d) (hR : StartDS3 f2 d sR) :
    (relayRuleDS3 (relayParams f1 f2 d)).Inv True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) 2) (relayGhost (relayParams f1 f2 d)) := by
  refine invGTM_init (s := sR) rfl rfl ⟨hR.exe, hR.decls, hR.endPc, ?_⟩
  rw [show sR.st = (sR.st.1, labS3 "reader") from Prod.ext rfl hR.pc]
  refine Safely.uncountA (readerS3_envGT (relayParams f1 f2 d).Q 2 _ (σInit (Config.init [sW, sY, sR] initMem)
    (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) 2) (relayGhost (relayParams f1 f2 d)), 0)
    ⟨hR.x0, hR.x1, hR.df, hR.dd,
    .inl ⟨rfl, relayGhost_rel_F2 hL.q_ne, ?_, 1, by show 1 < 2; decide, ?_, OkPred43.flag⟩⟩)
  · simp [σInit, Views.getFwd]
  · simp [σInit, relayRes, readerThreadRes]

end Inv

/-! ## `NPSafeP`, purity and the theorem -/

/-- **The `NPSafeP` side, whole image**: the writer through its
`ThreadRuleRX` (`NPSafe.toP`), the relay and the reader through the take
route. -/
theorem relaySwpl3_whole_npSafe (l : _root_.Layout) [Executable.ValidLayout (l relaySwpl3Img)] {f1 f2 d : BitVec 64}
    (hL : RelayLocs f1 f2 d) {sW sY sR : isa.State} {initMem : List (Loc × Val)}
    (hW : StartWS3 (layout := l) f1 d sW) (hY : StartYS3 (layout := l) f1 f2 d sY)
    (hR : StartDS3 (layout := l) f2 d sR) :
    ∀ tid, tid < [sW, sY, sR].length → ∀ n m, NPSafeP (model isa) Arch.armv8 (YPost (relayParams f1 f2 d)) tid G₀
      (K2Scope (model isa) AllocIds) n m True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) tid)
      (relayGhost (relayParams f1 f2 d)) := by
  intro tid htid n m
  match tid, htid with
  | 0, _ =>
    exact NPSafe.toP (fun _ _ _ _ _ h => h) (fun _ _ _ h => K2₀.toScope _ h)
      (NPSafe.of_ruleRX (relayRuleWS3 (layout := l) _ hL.P 0) n m _ _ _ _ (invWS3_init (layout := l) hL hW))
  | 1, _ => exact NPSafeP.of_ruleRXGS (relayRuleYS3 (layout := l) _ hL.Q 1) n m _ _ _ _ (invYS3_init (layout := l) hL hY)
  | 2, _ => exact NPSafeP.of_ruleRXGS (relayRuleDS3 (layout := l) _) n m _ _ _ _ (invDS3_init (layout := l) hL hR)
  | _ + 3, h => simp only [List.length_cons, List.length_nil] at h; omega

/-- The threads' purity specifications in the whole image: the writer's run
to `wdone` at thread `0`, the relay's to `rdone` at thread `1`, the reader's
to `ddone` elsewhere. -/
def relaySwpl3PureSpecW (l : _root_.Layout) [hv : Executable.ValidLayout (l relaySwpl3Img)] (rel : Loc → Pred) :
    Nat → RelPureSpec Arch.armv8 rel
  | 0 => { e := l relaySwpl3Img, valid := hv, endPc := labS3 (layout := l) "wdone",
           post := fun x => (x.1.2 = labS3 (layout := l) "wdone" ∧ True) ∨ False,
           post_end := fun _ h => h.elim And.left False.elim }
  | 1 => { e := l relaySwpl3Img, valid := hv, endPc := labS3 (layout := l) "rdone",
           post := fun x => ∃ _ : Nat, (x.1.2 = labS3 (layout := l) "rdone" ∧ True) ∨ False,
           post_end := fun _ ⟨_, h⟩ => h.elim And.left False.elim }
  | _ + 2 => { e := l relaySwpl3Img, valid := hv, endPc := labS3 (layout := l) "ddone",
               post := fun x => ∃ _ : Nat, (x.1.2 = labS3 (layout := l) "ddone" ∧ True) ∨ False,
               post_end := fun _ ⟨_, h⟩ => h.elim And.left False.elim }

/-- **The purity specifications hold at the start states.** -/
theorem relaySwpl3PureSpecW_init (l : _root_.Layout) [Executable.ValidLayout (l relaySwpl3Img)] {f1 f2 d : BitVec 64}
    (hL : RelayLocs f1 f2 d) {sW sY sR : isa.State} (hW : StartWS3 (layout := l) f1 d sW)
    (hY : StartYS3 (layout := l) f1 f2 d sY) (hR : StartDS3 (layout := l) f2 d sR) :
    ∀ tid s, [sW, sY, sR][tid]? = some s →
      (relaySwpl3PureSpecW l (relayGhost (relayParams f1 f2 d)).rel tid).Holds s
  | 0, s, hs => by
    cases hs
    refine ⟨hW.exe, hW.endPc, hW.decls, ?_⟩
    rw [show sW.st = (sW.st.1, labS3 (layout := l) "writer") from Prod.ext rfl hW.pc]
    letI : CodeEnv := ⟨l relaySwpl3Img⟩
    exact writerT3_relPure_at _ f1 d (relayGhost_rel_Dt hL)
      (Program.PlacedIn.of_placedE (relaySwpl3Img_placed (layout := l)) (by decide))
      (Program.last_of_check (lx := "wdone") (by decide)) _ () fun _ => ⟨hW.x0, hW.x1, hW.df, hW.dd⟩
  | 1, s, hs => by
    cases hs
    refine ⟨hY.exe, hY.endPc, hY.decls, ?_⟩
    rw [show sY.st = (sY.st.1, labS3 (layout := l) "relay") from Prod.ext rfl hY.pc]
    exact Safely.uncountA (relaySwplY3_relPure (layout := l) _ f1 d f2 (relayGhost_rel_Dt hL) _ ((), 0)
      fun _ => ⟨hY.x0, hY.x1, hY.x2, hY.df1, hY.dd, hY.df2⟩)
  | 2, s, hs => by
    cases hs
    refine ⟨hR.exe, hR.endPc, hR.decls, ?_⟩
    rw [show sR.st = (sR.st.1, labS3 (layout := l) "reader") from Prod.ext rfl hR.pc]
    letI : CodeEnv := ⟨l relaySwpl3Img⟩
    exact Safely.uncountA (readerT3_relPure_at _ f2
      (Program.PlacedIn.of_placedE (relaySwpl3Img_placed (layout := l)) (by decide))
      (Program.last_of_check (lx := "ddone") (by decide)) _ ((), 0) fun _ => ⟨hR.x0, hR.df⟩)
  | _ + 3, _, hs => by cases hs

/-- **A three-thread ownership relay through a release-only swap
`mp_relay3_swpl.kl` for AArch64 under `Arch.armv8`, every thread running the
whole `.kl` image**
(`forall (2:X4=43 /\ [d]=43)`).

For a valid layout `l` of the `.kl`'s `code` block `relaySwpl3Img` and distinct
addresses `f1`, `f2`, `d` (`RelayLocs`): if thread `0` runs the image from
`writer` to `wdone` with `x0 = f1`, `x1 = d`, thread `1` from `relay` to
`rdone` with `x0 = f1`, `x1 = d`, `x2 = f2`, thread `2` from `reader` to
`ddone` with `x0 = f2`, `x1 = d`, each with no declarations and none of its
words in its private memory (`StartWS3`, `StartYS3`, `StartDS3`), and both flags
are initially `0`, then every final configuration reachable under
`Arch.armv8` has the reader's `W4 = 43` and `[d] = 43`.

This is `mp_relay3_swpl_envG` with the runner's executable: every role runs
over its own mask (the dead `NOP`s behind `wdone:` and `rdone:` masked, and
the relay's `swpl` outside the writer's and the reader's phase-1 code;
`EnvG/A64MaskLink.lean`, `EnvG/A64MaskTC.lean`). As there, only final configurations are
constrained, faults are covered by `relayRuleWS3_noFault`,
`relayRuleYS3_noFault` and `relayRuleDS3_noFault`, and the threads have no
declarations (the runner sets `decls` from the init block). -/
theorem mp_relay3_swpl_envG_whole {fuel : Nat} (l : _root_.Layout) [Executable.ValidLayout (l relaySwpl3Img)]
    (f1 f2 d : BitVec 64) (hL : RelayLocs f1 f2 d) {sW sY sR : isa.State} {initMem : List (Loc × Val)}
    (hW : StartWS3 (layout := l) f1 d sW) (hY : StartYS3 (layout := l) f1 f2 d sY)
    (hR : StartDS3 (layout := l) f2 d sR)
    (hF1 : (Config.init [sW, sY, sR] initMem).mem.initVal ⟨f1, 4⟩ = 0)
    (hF2 : (Config.init [sW, sY, sR] initMem).mem.initVal ⟨f2, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [sW, sY, sR] initMem) cfg)
    (hf : cfg.final = true) :
    (∃ t, cfg.threads[2]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 43) ∧
      cfg.mem.finalVal ⟨d, 4⟩ = 43#128 :=
  final_of_relPureSafelyS Arch.armv8 fuel (B := YPost (relayParams f1 f2 d))
    (Φ := fun c => (∃ t, c.threads[2]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 43) ∧
      c.mem.finalVal ⟨d, 4⟩ = 43#128)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_relayInit hL _ hF1 hF2) initGhost_pend
    (relaySwpl3PureSpecW l _) (relaySwpl3PureSpecW_init l hL hW hY hR) (relaySwpl3_whole_npSafe l hL hW hY hR) hc hf
    fun _ _ E' _ hsize hB => relay_final E' hf hsize hB

end Kraken.Promising.SLR.EnvG.Relay

#print axioms Kraken.Promising.SLR.EnvG.Relay.mp_relay3_swpl_envG_whole
#print axioms Kraken.Promising.SLR.EnvG.Relay.relayRuleWS3_noFault
#print axioms Kraken.Promising.SLR.EnvG.Relay.relayRuleYS3_noFault
#print axioms Kraken.Promising.SLR.EnvG.Relay.relayRuleDS3_noFault
