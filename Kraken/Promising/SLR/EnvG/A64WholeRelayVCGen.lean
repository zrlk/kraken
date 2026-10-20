/-
**`mp_relay3.kl` whole image, part 1: the three
roles by `vcgen` in the whole `.kl` image.** Additive:
`Relay.mp_relay3_envG` (`EnvG/RelayPublic.lean`) is unchanged.

`mp_relay3_envG` runs MP's `mpWriter`, `relay` and MP's `mpReader`, each
with its own layout. The runner's executable is the whole `code` block
`relay3Img` under one layout, thread `0` from `writer` to `wdone`, thread
`1` from `relay` to `rdone`, thread `2` from `reader` to `ddone`
(`Kraken.Litmus.AArch64.prepareProgram`). The `.kl`'s role texts differ from
the per-thread texts in their labels and the `b <exit>` before each exit, so
the role texts here are the image's own slices (`writerT3`, `relayT3`,
`readerT3`, `relay3Img_eq`); the device is the AArch64 mask proofs'
(`EnvG/A64SpscWholeVCGen.lean`):

- **the writer runs over its mask** `relay3ImgW` (cells `0 … 6` kept:
  `writer` to `wdone:`; the dead `NOP`, the relay and the reader are data
  cells); **the relay over its mask** `relay3ImgY` (cells `8 … 16` kept:
  `relay` to `rdone:`); **the reader over the image itself** (`ddone` is the
  block's last cell).
- **The tables and VCs are the relay proof's and MP's** (`relayTable`,
  `readerTableD`, `vc_w1`/`vc_w2`, `vc_r1`/`vc_r2`/`vc_r3`, `vc_d1`/`vc_d2`)
  at the `.kl`'s labels; the scripts are `mpWriter_envG`'s, `relay_envGT`'s
  and `reader_envGT`'s, run by `MachineWP.cfgEnv_partial_at`
  (`EnvG/A64MaskCfg.lean`) with the role text `PlacedIn` the mask or image.
- `writerW3_envG`, `relayY3_envGT` (over the masks), `readerD3_envGT`: the
  runs; `writer3_relPure`, `relay3_relPure`, `reader3_relPure`: the purity
  runs in `relPure`, at the unmasked image.
- The writer's and the reader's scripts are stated once over any
  `[CodeEnv]` in which their text is `PlacedIn` (`writerT3_envG_at`,
  `readerT3_envGT_at`, `writerT3_relPure_at`,
  `readerT3_relPure_at`); the runs above are these at the masks and the
  image, and `mp_relay3_swpl.kl`'s whole image (whose writer and reader
  texts are these) reuses them.
-/
import Kraken.Promising.SLR.EnvG.RelayVCGen
import Kraken.Promising.SLR.EnvG.RelayRelPure
import Kraken.Promising.SLR.EnvG.MpSmokeVCGen
import Kraken.Promising.SLR.EnvG.MpRelPure
import Kraken.Promising.SLR.EnvG.A64MaskLink
import Kraken.Promising.SLR.EnvG.A64MaskCfg
open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Mp Kraken.Promising.SLR.MpTrees
open Kraken.Promising.SLR.EnvG.TakeSmoke Kraken.Promising.SLR.EnvG.TakeMp Kraken.Promising.SLR.EnvG.MpSmoke
namespace Kraken.Promising.SLR.EnvG.Relay
set_option mvcgen.warning false
set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

/-! ## The image, the role texts and the masks -/

/-- **The `code` block of `mp_relay3.kl`, verbatim**: the runner's
executable, shared by the three threads (`P0: writer wdone; P1: relay rdone;
P2: reader ddone`). -/
def relay3Img : Program := parseAArch64("
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
  STLR W6,[X2]
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

/-- info: 24 -/
#guard_msgs in
#eval relay3Img.length

/-- The writer's role text (`writer` to `wdone:`). -/
def writerT3 : Program := parseAArch64("
writer:
  MOV W2,#1
  STR W2,[X1]
  MOV W3,#1
  STLR W3,[X0]
  B wdone
wdone:
")

/-- The relay's role text (`relay` to `rdone:`). -/
def relayT3 : Program := parseAArch64("
relay:
  LDAR W3,[X0]
  CBZ W3,relay
  MOV W5,#43
  STR W5,[X1]
  MOV W6,#1
  STLR W6,[X2]
  B rdone
rdone:
")

/-- The reader's role text (`reader` to `ddone:`). -/
def readerT3 : Program := parseAArch64("
reader:
  LDAR W3,[X0]
  CBZ W3,reader
  LDR W4,[X1]
  B ddone
ddone:
")

/-- The image is the three role texts, with the dead `NOP`s behind `wdone:`
and `rdone:`. -/
theorem relay3Img_eq :
    relay3Img.take 7 = writerT3 ∧ (relay3Img.drop 8).take 9 = relayT3 ∧ relay3Img.drop 18 = readerT3 := by decide

/-- **The writer's mask**: cells `0 … 6` kept. -/
def relay3ImgW : Program := relay3Img.maskKeep (keepRange 0 7)
/-- **The relay's mask**: cells `8 … 16` kept. -/
def relay3ImgY : Program := relay3Img.maskKeep (keepRange 8 17)

theorem relay3Img_wf : Program.WF relay3Img := by decide
theorem relay3ImgW_wf : Program.WF relay3ImgW := by decide
theorem relay3ImgY_wf : Program.WF relay3ImgY := by decide
theorem writerT3_wf : Program.WF writerT3 := by decide
theorem relayT3_wf : Program.WF relayT3 := by decide
theorem readerT3_wf : Program.WF readerT3 := by decide
theorem writerT3_eq : writerT3 = Directive.label "writer" :: writerT3.tail := by decide
theorem relayT3_eq : relayT3 = Directive.label "relay" :: relayT3.tail := by decide
theorem readerT3_eq : readerT3 = Directive.label "reader" :: readerT3.tail := by decide
theorem writerT3_subW : Program.subBlocksOfE writerT3 relay3ImgW = true := by decide
theorem relayT3_subY : Program.subBlocksOfE relayT3 relay3ImgY = true := by decide
theorem writerT3_sub : Program.subBlocksOfE writerT3 relay3Img = true := by decide
theorem relayT3_sub : Program.subBlocksOfE relayT3 relay3Img = true := by decide
theorem readerT3_sub : Program.subBlocksOfE readerT3 relay3Img = true := by decide
theorem writerT3_exit : Program.exitCheck writerT3 "wdone" = true := by decide
theorem relayT3_exit : Program.exitCheck relayT3 "rdone" = true := by decide
theorem readerT3_exit : Program.exitCheck readerT3 "ddone" = true := by decide

/-- The writer's mask's cell behind `wdone:` (the `NOP`'s) is data. -/
theorem relay3ImgW_7 : relay3ImgW[7]? = some (.byteArray (.mk #[])) := by decide
/-- The relay's mask's cell behind `rdone:` (the `NOP`'s) is data. -/
theorem relay3ImgY_17 : relay3ImgY[17]? = some (.byteArray (.mk #[])) := by decide

/-! ## The writer's and the reader's runs in any ambient code

Stated once over any `[CodeEnv]` in which the role text is `PlacedIn`, from
its entry label to the end address `endA` of its last block (the scripts;
`MachineWP.cfgEnv_partial_at`): the writer's run over its mask and the
reader's run in the image below are these at `relay3ImgW`/`relay3Img`, and
the `swpl` relay's whole image (`EnvG/A64WholeRelaySwpl.lean`) uses them at
its own image. -/

section RunsAt

/-- The writer's frame: the flag and data addresses in `X0`/`X1`, neither in
`dmem`. -/
abbrev WFrame (P : Params) (s : MachineData) : Prop :=
  s.regs.X0.toBitVec = P.f ∧ s.regs.X1.toBitVec = P.d ∧ Mem.loadInt s.dmem P.f 4 = none ∧
    Mem.loadInt s.dmem P.d 4 = none

/-- The writer's table: `W1` at `writer`, `W3` at `wdone`. -/
abbrev writerTable3 (P : Params) (tid : Nat) : Label → MachineData → (E P tid).State → Prop :=
  fun lb s σ => WFrame P s ∧ ((lb = "writer" ∧ W1 P σ) ∨ (lb = "wdone" ∧ W3 P σ))

/-- The reader's table at the `.kl`'s labels: `DK1` at `reader`; at `ddone`,
`Own43` and, under the clean flag, `W4 = 43` (`readerTableD`). -/
abbrev readerTable3 (Q : Params) (tid : Nat) :
    Label → MachineData → (SharedEnv.counted (ET tid)).State → Prop :=
  fun lb s σ => s.regs.X0.toBitVec = Q.f ∧ s.regs.X1.toBitVec = Q.d ∧ Mem.loadInt s.dmem Q.f 4 = none ∧
    Mem.loadInt s.dmem Q.d 4 = none ∧
    ((lb = "reader" ∧ DK1 Q σ.1) ∨ (lb = "ddone" ∧ Own43 Q σ.1.r ∧ (σ.1.cl → s.regs.X4.toBitVec.setWidth 32 = 43)))

/-- The writer's purity table: at `writer`, both addresses in `X0`/`X1`,
neither in `dmem`. -/
abbrev writerPureTable3 (f d : BitVec 64) (rel : Loc → Pred) :
    Label → MachineData → (SharedEnv.relPure Arch.armv8 rel).State → Prop :=
  fun lb s _ => lb = "writer" → s.regs.X0.toBitVec = f ∧ s.regs.X1.toBitVec = d ∧ Mem.loadInt s.dmem f 4 = none ∧
    Mem.loadInt s.dmem d 4 = none

/-- The reader's purity table: at `reader`, the flag address in `X0`, not in
`dmem` (`readerTable`). -/
abbrev readerPureTable3 (f : BitVec 64) (rel : Loc → Pred) :
    Label → MachineData → (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)).State → Prop :=
  fun lb s _ => lb = "reader" → s.regs.X0.toBitVec = f ∧ Mem.loadInt s.dmem f 4 = none

variable [CodeEnv]

/-- **The writer's run in any ambient code** in which `writerT3` is
`PlacedIn` (`mpWriter_envG`'s VCs). -/
theorem writerT3_envG_at (P : Params) (hL : MpLocs P) (tid : Nat) (hpl : Program.PlacedIn writerT3) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt writerT3 l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, writerTable3 P tid "writer" s g →
      Safely (cenv.instrStepEnv (E P tid)) (fun x => (x.1.2 = endA ∧ W3 P x.2) ∨ False) ((s, (_root_.Executable.labels cenv).label "writer"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := E P tid) (Q := fun _ σ => W3 P σ) (E := fun _ _ _ => False)
    (writerTable3 P tid) ?_ writerT3_eq writerT3_wf hpl hlast s g hsg
  cfg_cases_env [writerT3]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hx0, hx1, hdf, hdd⟩, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMono_le_envG] at *
  all_goals try (simp [hx0, hx1, hdf, hdd]; done)
  case vc2 =>
    rename_i σ1 hf1 rng _ _
    simpa [hx1] using (vc_w1 hL tid σ1 (W1.fence hT hf1)).1
  case vc4 =>
    rename_i σ1 hf1 rng dm σ2 hd σ3 hf2 _
    simp [hx1, hdd] at hd
    simp [hx0, hd.1, hdf]
  case vc5 =>
    rename_i σ1 hf1 rng dm σ2 hd σ3 hf2 _
    simp [hx0, hx1, hdd] at hd ⊢
    have hW2 : W2 P σ2 := by
      rcases hd.2 with hst | hst <;> exact (vc_w1 hL tid σ1 (W1.fence hT hf1)).2 _ σ2 hst
    exact (vc_w2 hL tid σ3 (W2.fence hW2 hf2)).1
  case vc6 =>
    rename_i σ1 hf1 rng dm σ2 hd σ3 hf2 b σ4 hst4 σ5 hf4 _
    simp [hx0, hx1, hdd] at hd hst4
    have hW2 : W2 P σ2 := by
      rcases hd.2 with hst | hst <;> exact (vc_w1 hL tid σ1 (W1.fence hT hf1)).2 _ σ2 hst
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simp [hd.1, hdf], by simp [hd.1, hdd]⟩,
      .inr ⟨rfl, W3.fence ((vc_w2 hL tid σ3 (W2.fence hW2 hf2)).2 _ σ4 hst4) hf4⟩⟩, .inl (by decide)⟩
  case vc1 => exact hT

/-- **The reader's run in any ambient code** in which `readerT3` is
`PlacedIn` (`reader_envGT`'s script). -/
theorem readerT3_envGT_at (Q : Params) (tid : Nat) (hpl : Program.PlacedIn readerT3) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt readerT3 l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, readerTable3 Q tid "reader" s g →
      Safely (cenv.instrStepEnv (SharedEnv.counted (ET tid)))
        (fun x => (x.1.2 = endA ∧
          (Own43 Q x.2.1.r ∧ (x.2.1.cl → x.1.1.regs.X4.toBitVec.setWidth 32 = 43))) ∨ False)
        ((s, (_root_.Executable.labels cenv).label "reader"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (ET tid))
    (Q := fun s σ => Own43 Q σ.1.r ∧ (σ.1.cl → s.regs.X4.toBitVec.setWidth 32 = 43)) (E := fun _ _ _ => False)
    (readerTable3 Q tid) ?_ readerT3_eq readerT3_wf hpl hlast s g hsg
  cfg_cases_env [readerT3]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hdf, hdd, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals try (simp [hx0, hx1, hdf, hdd]; done)
  case vc4 =>
    -- the back edge (`cbz` taken): `DK1` again; the counter moved
    rename_i s σ0 b σ1 hst1 hcbz σ2 hf _
    simp only [fenceMono_le_counted, fenceMono_le_envGT, SharedEnv.counted_step, envGT_step_load] at hst1 hf
    simp [hx0] at hst1
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hdf], by simp [hdd],
      .inl ⟨rfl, DK1.fence (((vc_d1 tid σ0.1 hT) _ σ1.1 hst1.1).1 (by simpa using hcbz)) hf.1⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg; omega
  case vc7 =>
    -- `cbz` not taken, then the data load
    rename_i v σ1 hst1 hcbz σ2 hf1 rng w σ3 hld σ4 hf4 _
    simp only [fenceMono_le_counted, fenceMono_le_envGT, SharedEnv.counted_step, envGT_step_load] at hst1 hf1 hf4
    simp [hx0] at hst1
    have hK2 : DK2 Q σ2.1 := DK2.fence (((vc_d1 tid _ hT) _ σ1.1 hst1.1).2 (by simpa using hcbz)) hf1.1
    simp [hx1, hdd] at hld
    obtain ⟨v, ⟨hst3, -⟩, rfl⟩ := hld
    have h3 := vc_d2 tid σ2.1 hK2 v σ3.1 (by simpa using hst3)
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hdf], by simp [hdd],
      .inr ⟨rfl, hf4.1.r ▸ h3.1, fun hcl => ?_⟩⟩, .inl (by decide)⟩
    rw [h3.2 (hf4.1.cl ▸ hcl)]
    simp
  case vc1 => exact hT
  all_goals done

/-- **The writer's purity run in any ambient code** in which `writerT3` is
`PlacedIn` (`mpWriter_relPure`'s script). -/
theorem writerT3_relPure_at (rel : Loc → Pred) (f d : BitVec 64) (hd : ∀ v, Pred.Pure (rel ⟨d, 4⟩) v)
    (hpl : Program.PlacedIn writerT3) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt writerT3 l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, writerPureTable3 f d rel "writer" s g →
      Safely (cenv.instrStepEnv (SharedEnv.relPure Arch.armv8 rel))
        (fun x => (x.1.2 = endA ∧ True) ∨ False) ((s, (_root_.Executable.labels cenv).label "writer"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.relPure Arch.armv8 rel) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (writerPureTable3 f d rel) ?_ writerT3_eq writerT3_wf hpl
    hlast s g hsg
  cfg_cases_env [writerT3]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨hT, rfl, rfl⟩ := ‹(_ → _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [forall_const] at hT
  case vc6 => exact Table.ofLabelsEnv_at ⟨by decide, fun h => absurd h (by decide), .inl (by decide)⟩
  all_goals simp_all [Arch.storeKind, show Arch.armv8.plainStore = .plain from rfl]

/-- **The reader's purity run in any ambient code** in which `readerT3` is
`PlacedIn` (`mpReader_relPure`'s script). -/
theorem readerT3_relPure_at (rel : Loc → Pred) (f : BitVec 64) (hpl : Program.PlacedIn readerT3) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt readerT3 l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, readerPureTable3 f rel "reader" s g →
      Safely (cenv.instrStepEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)))
        (fun x => (x.1.2 = endA ∧ True) ∨ False) ((s, (_root_.Executable.labels cenv).label "reader"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel))
    (Q := fun _ _ => True) (E := fun _ _ _ => False) (readerPureTable3 f rel) ?_ readerT3_eq readerT3_wf
    hpl hlast s g hsg
  cfg_cases_env [readerT3]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨hT, rfl, rfl⟩ := ‹(_ → _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [forall_const] at hT
  case vc4 =>
    -- the back edge (`cbz` taken): the counter moved
    have hn := (‹(SharedEnv.counted _).step _ _ _ _›).2
    refine Table.ofLabelsEnv_at ⟨by decide, fun _ => ⟨by simpa using hT.1, by simpa using hT.2⟩,
      .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg; simp at hn
  case vc7 => exact Table.ofLabelsEnv_at ⟨by decide, fun h => absurd h (by decide), .inl (by decide)⟩
  all_goals simp_all

end RunsAt

section Lay

variable [layout : _root_.Layout]

/-- A label's address in the image. -/
abbrev labY3 (x : Label) : Int64 := (_root_.Executable.labels (layout relay3Img)).label x

theorem relay3ImgW_mask : MaskOf (layout relay3Img) (layout relay3ImgW) := maskOf_layout _ _
theorem relay3ImgY_mask : MaskOf (layout relay3Img) (layout relay3ImgY) := maskOf_layout _ _

theorem relay3ImgW_valid [Executable.ValidLayout (layout relay3Img)] :
    Executable.ValidLayout (layout relay3ImgW) :=
  ValidLayout.of_mask relay3ImgW_mask

theorem relay3ImgY_valid [Executable.ValidLayout (layout relay3Img)] :
    Executable.ValidLayout (layout relay3ImgY) :=
  ValidLayout.of_mask relay3ImgY_mask

/-! ## The writer over its mask -/

section WriterW

variable [Executable.ValidLayout (layout relay3Img)]

local instance relay3ImgW.env : CodeEnv := ⟨layout relay3ImgW⟩

theorem writerW3_placedIn : Program.PlacedIn writerT3 :=
  haveI := relay3ImgW_valid (layout := layout)
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := relay3ImgW) relay3ImgW_wf rfl (by decide))
    writerT3_subW

/-- The writer's run over its mask, at the mask's labels (`mpWriter_envG`'s
VCs). -/
theorem writerW3_envG' (P : Params) (hL : MpLocs P) (tid : Nat) :
    ∀ s g, writerTable3 P tid "writer" s g →
      Safely (cenv.instrStepEnv (E P tid))
        (fun x => (x.1.2 = (_root_.Executable.labels cenv).label "wdone" ∧ W3 P x.2) ∨ False)
        ((s, (_root_.Executable.labels cenv).label "writer"), g) := by
  exact writerT3_envG_at P hL tid writerW3_placedIn (Program.last_of_check writerT3_exit)

end WriterW

/-! ## The relay over its mask -/

section RelayY

variable [Executable.ValidLayout (layout relay3Img)]

local instance relay3ImgY.env : CodeEnv := ⟨layout relay3ImgY⟩

theorem relayY3_placedIn : Program.PlacedIn relayT3 :=
  haveI := relay3ImgY_valid (layout := layout)
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := relay3ImgY) relay3ImgY_wf rfl (by decide))
    relayT3_subY

/-- The relay's table at the `.kl`'s labels: `RK1` at `relay`, `RK4` at
`rdone` (`relayTable`). -/
abbrev relayTable3 (rp : RP) (tid : Nat) :
    Label → MachineData → (SharedEnv.counted (ER rp tid)).State → Prop :=
  fun lb s σ => RFrame rp s ∧ ((lb = "relay" ∧ RK1 rp σ.1) ∨ (lb = "rdone" ∧ RK4 rp σ.1))

/-- The relay's run over its mask, at the mask's labels (`relay_envGT`'s
script). -/
theorem relayY3_envGT' (rp : RP) (hL : MpLocs rp.Q) (tid : Nat) :
    ∀ s g, relayTable3 rp tid "relay" s g →
      Safely (cenv.instrStepEnv (SharedEnv.counted (ER rp tid)))
        (fun x => (x.1.2 = (_root_.Executable.labels cenv).label "rdone" ∧ RK4 rp x.2.1) ∨ False)
        ((s, (_root_.Executable.labels cenv).label "relay"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (ER rp tid)) (Q := fun _ σ => RK4 rp σ.1)
    (E := fun _ _ _ => False) (relayTable3 rp tid) ?_ relayT3_eq relayT3_wf relayY3_placedIn
    (Program.last_of_check relayT3_exit) s g hsg
  cfg_cases_env [relayT3]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hx0, hx1, hx2, hdf, hdd, hdg⟩, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals try (simp [hx0, hx1, hx2, hdf, hdd, hdg]; done)
  case vc4 =>
    -- the back edge (`cbz` taken): `RK1` again; the counter moved
    rename_i s σ0 b σ1 hst1 hcbz σ2 hf _
    simp only [fenceMono_le_counted, fenceMono_le_envGT, SharedEnv.counted_step, envGT_step_load] at hst1 hf
    simp [hx0] at hst1
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simp [hx2], by simp [hdf],
      by simp [hdd], by simp [hdg]⟩, .inl ⟨rfl, RK1.fence (((vc_r1 tid σ0.1 hT) _ σ1.1 hst1.1).1
        (by simpa using hcbz)) hf.1⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg; omega
  case vc6 =>
    rename_i v σ1 hst1 hcbz σ2 hf1 σ3 hf2 rng hdm _
    simp only [fenceMono_le_counted, fenceMono_le_envGT, SharedEnv.counted_step, envGT_step_load] at hst1 hf1 hf2
    simp [hx0] at hst1
    have hK2 : RK2 rp σ3.1 :=
      RK2.fence (RK2.fence (((vc_r1 tid _ hT) _ σ1.1 hst1.1).2 (by simpa using hcbz)) hf1.1) hf2.1
    simpa [hx1] using (vc_r2 hL tid σ3.1 hK2).1
  case vc8 =>
    rename_i v σ1 hst1 hcbz σ2 hf1 σ3 hf2 rng dm σ4 hd σ5 hf3 _
    simp [hx1, hdd] at hd
    simp [hd.1, hx2, hdg]
  case vc9 =>
    rename_i v σ1 hst1 hcbz σ2 hf1 σ3 hf2 rng dm σ4 hd σ5 hf3 _
    simp only [fenceMono_le_counted, fenceMono_le_envGT, SharedEnv.counted_step, envGT_step_load] at hst1 hf1 hf2 hf3
    simp [hx0] at hst1
    have hK2 : RK2 rp σ3.1 :=
      RK2.fence (RK2.fence (((vc_r1 tid _ hT) _ σ1.1 hst1.1).2 (by simpa using hcbz)) hf1.1) hf2.1
    simp [hx1, hdd] at hd
    have hK3 : RK3 rp σ4.1 := by
      rcases hd.2 with hst | hst <;> exact (vc_r2 hL tid σ3.1 hK2).2 _ σ4.1 (by simpa using hst)
    simpa [hx2, hd.1, hdg] using (vc_r3 hL tid σ5.1 (RK3.fence hK3 hf3.1)).1
  case vc10 =>
    rename_i v σ1 hst1 hcbz σ2 hf1 σ3 hf2 rng dm σ4 hd σ5 hf3 b σ6 hst6 σ7 hf6 _
    simp only [fenceMono_le_counted, fenceMono_le_envGT, SharedEnv.counted_step, envGT_step_load] at hst1 hf1 hf2 hf3 hf6
    simp [hx0] at hst1
    have hK2 : RK2 rp σ3.1 :=
      RK2.fence (RK2.fence (((vc_r1 tid _ hT) _ σ1.1 hst1.1).2 (by simpa using hcbz)) hf1.1) hf2.1
    simp [hx1, hdd] at hd
    have hK3 : RK3 rp σ4.1 := by
      rcases hd.2 with hst | hst <;> exact (vc_r2 hL tid σ3.1 hK2).2 _ σ4.1 (by simpa using hst)
    simp [hx2] at hst6
    have h4 : RK4 rp σ6.1 := (vc_r3 hL tid σ5.1 (RK3.fence hK3 hf3.1)).2 _ σ6.1 (by simpa using hst6.1)
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simp [hx2], by simp [hd.1, hdf],
      by simp [hd.1, hdd], by simp [hd.1, hdg]⟩, .inr ⟨rfl, RK4.fence h4 hf6.1⟩⟩, .inl (by decide)⟩
  case vc1 => exact hT
  all_goals done

end RelayY

/-! ## The reader and the purity runs over the image -/

section ImageD

variable [Executable.ValidLayout (layout relay3Img)]

local instance relay3Img.env : CodeEnv := ⟨layout relay3Img⟩

theorem readerD3_placedIn : Program.PlacedIn readerT3 :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := relay3Img) relay3Img_wf rfl (by decide))
    readerT3_sub

theorem writerA3_placedIn : Program.PlacedIn writerT3 :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := relay3Img) relay3Img_wf rfl (by decide))
    writerT3_sub

theorem relayA3_placedIn : Program.PlacedIn relayT3 :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := relay3Img) relay3Img_wf rfl (by decide))
    relayT3_sub

/-- The reader's run in the image (`reader_envGT`'s script). -/
theorem readerD3_envGT (Q : Params) (tid : Nat) :
    ∀ s g, readerTable3 Q tid "reader" s g →
      Safely ((layout relay3Img).instrStepEnv (SharedEnv.counted (ET tid)))
        (fun x => (x.1.2 = labY3 "ddone" ∧
          (Own43 Q x.2.1.r ∧ (x.2.1.cl → x.1.1.regs.X4.toBitVec.setWidth 32 = 43))) ∨ False)
        ((s, labY3 "reader"), g) := by
  exact readerT3_envGT_at Q tid readerD3_placedIn (Program.last_of_check readerT3_exit)

/-- The writer's purity run in the image (`mpWriter_relPure`'s script): its
only non-release write is to `⟨d, 4⟩`. -/
theorem writer3_relPure (rel : Loc → Pred) (f d : BitVec 64) (hd : ∀ v, Pred.Pure (rel ⟨d, 4⟩) v) :
    ∀ s g, writerPureTable3 f d rel "writer" s g →
      Safely ((layout relay3Img).instrStepEnv (SharedEnv.relPure Arch.armv8 rel))
        (fun x => (x.1.2 = labY3 "wdone" ∧ True) ∨ False) ((s, labY3 "writer"), g) := by
  exact writerT3_relPure_at rel f d hd writerA3_placedIn (Program.last_of_check writerT3_exit)

/-- The relay's purity table: at `relay`, the three addresses in `X0`/`X1`/
`X2`, none in `dmem` (`relayPureTable`). -/
abbrev relayPureTable3 (f1 d f2 : BitVec 64) (rel : Loc → Pred) :
    Label → MachineData → (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)).State → Prop :=
  fun lb s _ => lb = "relay" → s.regs.X0.toBitVec = f1 ∧ s.regs.X1.toBitVec = d ∧ s.regs.X2.toBitVec = f2 ∧
    Mem.loadInt s.dmem f1 4 = none ∧ Mem.loadInt s.dmem d 4 = none ∧ Mem.loadInt s.dmem f2 4 = none

/-- The relay's purity run in the image (`relay_relPure`'s script). -/
theorem relay3_relPure (rel : Loc → Pred) (f1 d f2 : BitVec 64) (hd : ∀ v, Pred.Pure (rel ⟨d, 4⟩) v) :
    ∀ s g, relayPureTable3 f1 d f2 rel "relay" s g →
      Safely ((layout relay3Img).instrStepEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)))
        (fun x => (x.1.2 = labY3 "rdone" ∧ True) ∨ False) ((s, labY3 "relay"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel))
    (Q := fun _ _ => True) (E := fun _ _ _ => False) (relayPureTable3 f1 d f2 rel) ?_ relayT3_eq relayT3_wf
    relayA3_placedIn (Program.last_of_check relayT3_exit) s g hsg
  cfg_cases_env [relayT3]
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
  case vc10 => exact Table.ofLabelsEnv_at ⟨by decide, fun h => absurd h (by decide), .inl (by decide)⟩
  all_goals simp_all [Arch.storeKind, show Arch.armv8.plainStore = .plain from rfl]

/-- The reader's purity run in the image (`mpReader_relPure`'s script): it
writes nothing. -/
theorem reader3_relPure (rel : Loc → Pred) (f : BitVec 64) :
    ∀ s g, readerPureTable3 f rel "reader" s g →
      Safely ((layout relay3Img).instrStepEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)))
        (fun x => (x.1.2 = labY3 "ddone" ∧ True) ∨ False) ((s, labY3 "reader"), g) := by
  exact readerT3_relPure_at rel f readerD3_placedIn (Program.last_of_check readerT3_exit)

end ImageD

/-- **The writer's run over its mask**, at the image's labels. -/
theorem writerW3_envG [Executable.ValidLayout (layout relay3Img)] (P : Params) (hL : MpLocs P) (tid : Nat) :
    ∀ s g, writerTable3 P tid "writer" s g →
      Safely ((layout relay3ImgW).instrStepEnv (E P tid))
        (fun x => (x.1.2 = labY3 "wdone" ∧ W3 P x.2) ∨ False) ((s, labY3 "writer"), g) := by
  intro s g hsg
  have h : Safely ((layout relay3ImgW).instrStepEnv (E P tid))
      (fun x => (x.1.2 = (_root_.Executable.labels (layout relay3ImgW)).label "wdone" ∧ W3 P x.2) ∨ False)
      ((s, (_root_.Executable.labels (layout relay3ImgW)).label "writer"), g) :=
    writerW3_envG' (layout := layout) P hL tid s g hsg
  rw [labels_mask relay3ImgW_mask] at h
  exact h

/-- **The relay's run over its mask**, at the image's labels. -/
theorem relayY3_envGT [Executable.ValidLayout (layout relay3Img)] (rp : RP) (hL : MpLocs rp.Q) (tid : Nat) :
    ∀ s g, relayTable3 rp tid "relay" s g →
      Safely ((layout relay3ImgY).instrStepEnv (SharedEnv.counted (ER rp tid)))
        (fun x => (x.1.2 = labY3 "rdone" ∧ RK4 rp x.2.1) ∨ False) ((s, labY3 "relay"), g) := by
  intro s g hsg
  have h : Safely ((layout relay3ImgY).instrStepEnv (SharedEnv.counted (ER rp tid)))
      (fun x => (x.1.2 = (_root_.Executable.labels (layout relay3ImgY)).label "rdone" ∧ RK4 rp x.2.1) ∨ False)
      ((s, (_root_.Executable.labels (layout relay3ImgY)).label "relay"), g) :=
    relayY3_envGT' (layout := layout) rp hL tid s g hsg
  rw [labels_mask relay3ImgY_mask] at h
  exact h

end Lay

end Kraken.Promising.SLR.EnvG.Relay

#print axioms Kraken.Promising.SLR.EnvG.Relay.writerW3_envG
#print axioms Kraken.Promising.SLR.EnvG.Relay.relayY3_envGT
#print axioms Kraken.Promising.SLR.EnvG.Relay.readerD3_envGT
#print axioms Kraken.Promising.SLR.EnvG.Relay.writer3_relPure
#print axioms Kraken.Promising.SLR.EnvG.Relay.relay3_relPure
#print axioms Kraken.Promising.SLR.EnvG.Relay.reader3_relPure
