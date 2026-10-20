/-
**The two threads of `mp_incl.kl`, verbatim, over masked images**
. Each thread's run is over a **mask** of the x64 absolute-address proofs'
image `mpInclImageV` (`EnvG/X64MpInclAbsVCGen.lean`; `Program.maskKeep`,
`EnvG/X64MaskCore.lean`), which keeps the thread's own cells:

- the writer's mask `mpInclImageW` keeps `writer:` … `wdone:` (cells
  `0 … 4`): `wdone`'s `nop` and the reader are data cells, so the mask
  halts at `wdone` and its code is `EnvGLR`-shaped (`LRTreeX`);
- the reader's mask `mpInclImageR` keeps `reader:` … `rdone:` (cells
  `6 … 12`): the writer's `incl` (two accesses, not phase-1) is a data cell,
  so the mask's code is phase-1 (`Phase1TreeX`).

The writer's run is on **`EnvGLRV`** (`EWV`, VCs `vc_w1V`,
`vc_incLoadV`, `vc_incStoreV` of `EnvG/LRValMpInc.lean`, unchanged), so it
ends with `W3V` (`FlFin` under `cl`): the flag's final write, which the
`[f]=1` conjunct needs. The reader's run is the x64 absolute-address proofs' `readerV_envG` script
over the reader's mask.

- `writerW_envG`, `writerW_stuck`, `mpInclImageW_lr`;
- `readerR_envG`, `readerR_stuck`, `mpInclImageR_phase1`;
- `mpInclImageV_noFaultCode`.
-/
import Kraken.Promising.SLR.EnvG.X64MpInclAbsVCGen
import Kraken.Promising.SLR.EnvG.LRValMpInc
import Kraken.Promising.SLR.EnvG.X64MaskLinkMore
import Kraken.Promising.SLR.EnvG.X64ImageNoFault

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Mp
open Kraken.Promising.X64.EnvG.MpSmoke Kraken.Promising.X64.EnvG.MpInc Kraken.Promising.X64.EnvG.MpIncV
open Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.MpInclAbs

set_option mvcgen.warning false
set_option experimental.vcgen true
-- The shape scripts are copies of the `dirs_lrX`/`dirs_phase1X` macros, whose simp sets
-- are generic.
set_option linter.unusedSimpArgs false

/-! ## The masks -/

/-- **The writer's mask of the image**: the cells `0 … 4` (`writer:` to
`wdone:`) kept, every later non-label cell a data cell. -/
def mpInclImageW : Program := mpInclImageV.maskKeep (keepRange 0 5)

/-- **The reader's mask of the image**: the cells `6 … 12` (`reader:` to
`rdone:`) kept, every other non-label cell a data cell. -/
def mpInclImageR : Program := mpInclImageV.maskKeep (keepRange 6 13)

theorem mpInclImageW_wf : Program.WF mpInclImageW := by decide

theorem mpInclImageR_wf : Program.WF mpInclImageR := by decide

theorem writerFragW_sub : Program.subBlocksOfE writerFragV mpInclImageW = true := by decide

theorem readerFragR_sub : Program.subBlocksOfE readerFragV mpInclImageR = true := by decide

/-- The writer's mask's cell at `wdone`'s `nop` is a data cell. -/
theorem mpInclImageW_5 : mpInclImageW[5]? = some (.byteArray (.mk #[])) := by decide

/-- The reader's mask's cell after `rdone` is a data cell. -/
theorem mpInclImageR_13 : mpInclImageR[13]? = some (.byteArray (.mk #[])) := by decide

variable [layout : _root_.Layout]

theorem mpInclImageW_mask : MaskOf (layout mpInclImageV) (layout mpInclImageW) := maskOf_layout _ _

theorem mpInclImageR_mask : MaskOf (layout mpInclImageV) (layout mpInclImageR) := maskOf_layout _ _

/-- A label's address in the writer's mask. -/
abbrev labW (x : Label) : Int64 := (_root_.Executable.labels (layout mpInclImageW)).label x

/-- A label's address in the reader's mask. -/
abbrev labR (x : Label) : Int64 := (_root_.Executable.labels (layout mpInclImageR)).label x

theorem labW_eq (x : Label) : labW x = labM x := by
  show (_root_.Executable.labels (layout mpInclImageW)).label x =
    (_root_.Executable.labels (layout mpInclImageV)).label x
  rw [labels_mask mpInclImageW_mask]

theorem labR_eq (x : Label) : labR x = labM x := by
  show (_root_.Executable.labels (layout mpInclImageR)).label x =
    (_root_.Executable.labels (layout mpInclImageV)).label x
  rw [labels_mask mpInclImageR_mask]

variable [Executable.ValidLayout (layout mpInclImageV)]

theorem mpInclImageW_valid : Executable.ValidLayout (layout mpInclImageW) := ValidLayout.of_mask mpInclImageW_mask

theorem mpInclImageR_valid : Executable.ValidLayout (layout mpInclImageR) := ValidLayout.of_mask mpInclImageR_mask

/-! ## The writer over its mask, on `EnvGLRV` -/

omit layout [Executable.ValidLayout (layout mpInclImageV)] in
theorem W3V.fence {P : Params} {σ σ' : EStateX} (h : W3V P σ) (hf : FenceLe σ σ') : W3V P σ' :=
  ⟨W3I.fence h.1 hf, by unfold FlFin; rw [hf.cl, hf.r]; exact h.2⟩

section Writer

local instance mpInclImageW.env : CodeEnv := ⟨layout mpInclImageW⟩

theorem writerFragW_placedIn : Program.PlacedIn writerFragV :=
  haveI := mpInclImageW_valid (layout := layout)
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := mpInclImageW) mpInclImageW_wf rfl (by decide))
    writerFragW_sub

omit [Executable.ValidLayout (layout mpInclImageV)] in
theorem writerFragW_last : ∀ l blk, Program.blockAt writerFragV l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = labW "wdone" :=
  Program.after_last_of (by decide)

/-- The writer's table on `EnvGLRV`: `W1V` at `writer`, `W3V` at `wdone`. -/
abbrev writerTableW (P : Params) (tid : Nat) : Label → MachineData → (EWV P tid).State → Prop :=
  fun lb s σ => FrameRX P s ∧ ((lb = "writer" ∧ W1V P σ) ∨ (lb = "wdone" ∧ W3V P σ))

/-- The writer's run over its mask, at the mask's labels (`writerV_envG`'s
script with the value-restricted link's VCs). -/
theorem writerW_envG' (P : Params) (hL : MpLocs P) (tid : Nat) :
    ∀ s g, FrameRX P s ∧ W1V P g →
      Safely (cenv.instrStepEnv (EWV P tid))
        (fun x => (x.1.2 = labW "wdone" ∧ W3V P x.2) ∨ False) ((s, labW "writer"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := EWV P tid) (Q := fun _ σ => W3V P σ)
    (E := fun _ _ _ => False) (writerTableW P tid) ?_ rfl (by decide) writerFragW_placedIn
    writerFragW_last s g (by simpa [writerTableW] using hsg)
  cfg_cases_env [writerFragV]
  all_goals intro s₀ g₀
  all_goals vcgen [inc32_shared_spec]
  all_goals obtain ⟨⟨⟨hx0, hx1, hdf, hdd⟩, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [Reg64s.get64] at hx0 hx1
  case vc1 => simp [hx1, hdd]
  case vc2 => exact (vc_w1V hL tid _ hT (by simp [hx1]) (by decide)).1
  case vc3 => simp [hx0, hdf]
  case vc4 => exact ⟨trivial, by simp [SharedEnv.AccessIn, hx0]⟩
  case vc5 =>
    rename_i b σ1 hst v σ2 hld _
    have hW2 := (vc_w1V hL tid _ hT (by simp [hx1]) (by decide)).2 b σ1 hst
    have hW2' := vc_incLoadV hL tid σ1 hW2 (by simp [hx0]) v σ2 hld
    refine ⟨(vc_incStoreV hL tid σ2 v hW2' (by simp [hx0])).1, fun _ g'' hs' st => ?_⟩
    have hW3 := (vc_incStoreV hL tid σ2 v hW2' (by simp [hx0])).2 _ g'' hs'
    vcgen
    rename_i σ3 hf
    simp only [fenceMonoX_le_within, fenceMonoX_le_envGLRV] at hf
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simpa using hdf,
      by simpa using hdd⟩, .inr ⟨rfl, W3V.fence hW3 hf⟩⟩, .inl (by decide)⟩
  case vc1 => exact hT

end Writer

/-- **The verbatim x64 MP `incl` writer on `EnvGLRVX`, over its mask**
(partial), at the image's labels: from `W1V` at `writer`, every run that
reaches `wdone` has `W3V`. -/
theorem writerW_envG (P : Params) (hL : MpLocs P) (tid : Nat) :
    ∀ s g, FrameRX P s ∧ W1V P g →
      Safely ((layout mpInclImageW).instrStepEnv (EWV P tid))
        (fun x => (x.1.2 = labM "wdone" ∧ W3V P x.2) ∨ False) ((s, labM "writer"), g) := by
  intro s g h
  have := writerW_envG' P hL tid s g h
  simp only [labW_eq] at this
  exact this

omit [Executable.ValidLayout (layout mpInclImageV)] in
/-- `wdone`'s address is the writer's mask's cell `5`. -/
theorem labM_wdone [Executable.ValidLayout (layout mpInclImageV)] :
    labM "wdone" = (layout mpInclImageW).addrOf 5 := by
  have hd : labM "wdone" = (layout mpInclImageV).addrOf 4 :=
    Program.label_addrOf_drop mpInclImageV_wf.nodup (by decide) (by decide)
  have h4 : (layout mpInclImageV).2[4]? = some (Directive.label "wdone", Kraken.Layout.size Directive 4) := by
    simp [Layout.apply_snd, Layout.frag, mpInclImageV, mpInclCodeV, mpInclDataV]
  rw [addrOf_mask mpInclImageW_mask, Executable.addrOf_succ _ h4,
    Executable.ValidLayout.label_size 4 "wdone" _ h4, hd]
  simp

/-- **No step of the writer's mask at the exit label `wdone`.** -/
theorem writerW_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labM "wdone" → ¬ (layout mpInclImageW).instrStepEnv env x R := by
  haveI := mpInclImageW_valid (layout := layout)
  rw [labM_wdone]
  exact not_instrStepEnv_of_byteArray (i := 5) (b := .mk #[]) env mpInclImageW_5

omit layout [Executable.ValidLayout (layout mpInclImageV)] in
/-- The writer's cells are `EnvGLR`-shaped (`cells_lrX`, `dirs_lrX`'s per-cell script). -/
theorem writerFragV_dirsLRX : ∀ d ∈ writerFragV, ∀ (e : _root_.Executable) z, DirLRX Arch.tso e d z := by
  intro d hd e z s pc
  cells_lrX writerFragV hd

/-- **The writer's mask is `EnvGLR`-shaped** (its kept cells are the
writer's). -/
theorem mpInclImageW_lr : LRTreeX Arch.tso (layout mpInclImageW) := by
  haveI := mpInclImageW_valid (layout := layout)
  refine lrTreeX_of_dirs (dirsLRX_layout (mem_maskKeep_range
    (Φd := fun d => ∀ (e : _root_.Executable) z, DirLRX Arch.tso e d z) ?_ ?_ ?_))
  · rw [show (mpInclImageV.drop 0).take (5 - 0) = writerFragV by decide]
    exact writerFragV_dirsLRX
  · intro l e z s pc
    refine Or.inl ?_
    simp [_root_.Directive.interp, Kraken.Promising.X64.toEv, Phase1Shape, DetAccess, SingleAccessS, AccessFree]
  · intro e z s pc
    refine Or.inl ?_
    simp [_root_.Directive.interp, Kraken.Promising.X64.toEv, Phase1Shape, DetAccess, SingleAccessS, AccessFree]

/-! ## The reader over its mask -/

section Reader

local instance mpInclImageR.env : CodeEnv := ⟨layout mpInclImageR⟩

theorem readerFragR_placedIn : Program.PlacedIn readerFragV :=
  haveI := mpInclImageR_valid (layout := layout)
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := mpInclImageR) mpInclImageR_wf rfl (by decide))
    readerFragR_sub

omit [Executable.ValidLayout (layout mpInclImageV)] in
theorem readerFragR_last : ∀ l blk, Program.blockAt readerFragV l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = labR "rdone" :=
  Program.after_last_of (by decide)

/-- The reader's run over its mask, at the mask's labels (`readerV_envG`'s
script). -/
theorem readerR_envG' (P : Params) (tid : Nat) :
    ∀ s g, FrameRX P s ∧ R1I P g.1 →
      Safely (cenv.instrStepEnv (SharedEnv.counted (E P tid)))
        (fun x => (x.1.2 = labR "rdone" ∧ (R4I P x.2.1 ∧ (x.2.1.cl → (x.1.1.regs.get64 .rbx).setWidth 32 = 42)))
          ∨ False) ((s, labR "reader"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (E P tid))
    (Q := fun s σ => R4I P σ.1 ∧ (σ.1.cl → (s.regs.get64 .rbx).setWidth 32 = 42))
    (E := fun _ _ _ => False) (readerTableV P tid) ?_ rfl (by decide) readerFragR_placedIn
    readerFragR_last s g (by simpa [readerTableV] using hsg)
  cfg_cases_env [readerFragV]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hx0, hx1, hdf, hdd⟩, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [Reg64s.get64] at hx0 hx1
  all_goals simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envG] at *
  case vc1 => simp [hx0] <;> trivial
  case vc2 =>
    rename_i x σ1 hld σ2 hz σ3 hf1 hf2 _
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hx0, hdf] at hm
    · have hR := vc_r1I_step tid _ hT (by simp [hx0]) v σ1.1 hst.1
      have hn := hst.2
      refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simpa using hdf,
        by simpa using hdd⟩, .inl ⟨rfl, R1I.fence (R1I.fence hR.1 hf1.1) hf2.1⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg
      simp [SharedAccess.tick] at hn
      omega
  case vc3 => simp [hx1] <;> trivial
  case vc4 =>
    rename_i x σ1 hld σ2 hz σ3 y σ4 hld2 σ5 hf1 hf2 hf3 _
    simp at hz
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hx0, hdf] at hm
    have hR3 : R3I P σ3.1 :=
      R3I.fence (R3I.fence ((vc_r1I_step tid _ hT (by simp [hx0]) v σ1.1 hst.1).2 hz) hf1.1) hf2.1
    rcases hld2 with ⟨w, hm, -, -⟩ | ⟨-, w, hst2, rfl⟩
    · simp [hx1, hdd] at hm
    have h4 := vc_r3I_step tid σ3.1 hR3 (by simp [hx1]) w σ4.1 hst2.1
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simpa using hdf,
      by simpa using hdd⟩, .inr ⟨rfl, R4I.fence h4.1 hf3.1, fun hcl => ?_⟩⟩, .inl (by decide)⟩
    obtain rfl := h4.2 (hf3.1.cl ▸ hcl)
    simp [dataVal]
  case vc1 => exact hT

end Reader

/-- **The verbatim x64 MP reader on `EnvG`, over its mask** (counted,
partial), at the image's labels. -/
theorem readerR_envG (P : Params) (tid : Nat) :
    ∀ s g, FrameRX P s ∧ R1I P g.1 →
      Safely ((layout mpInclImageR).instrStepEnv (SharedEnv.counted (E P tid)))
        (fun x => (x.1.2 = labM "rdone" ∧ (R4I P x.2.1 ∧ (x.2.1.cl → (x.1.1.regs.get64 .rbx).setWidth 32 = 42)))
          ∨ False) ((s, labM "reader"), g) := by
  intro s g h
  have := readerR_envG' P tid s g h
  simp only [labR_eq] at this
  exact this

omit [Executable.ValidLayout (layout mpInclImageV)] in
/-- `rdone`'s address is the reader's mask's cell `13`. -/
theorem labM_rdone [Executable.ValidLayout (layout mpInclImageV)] :
    labM "rdone" = (layout mpInclImageR).addrOf 13 := by
  have hd : labM "rdone" = (layout mpInclImageV).addrOf 12 :=
    Program.label_addrOf_drop mpInclImageV_wf.nodup (by decide) (by decide)
  have h12 : (layout mpInclImageV).2[12]? = some (Directive.label "rdone", Kraken.Layout.size Directive 12) := by
    simp [Layout.apply_snd, Layout.frag, mpInclImageV, mpInclCodeV, mpInclDataV]
  rw [addrOf_mask mpInclImageR_mask, Executable.addrOf_succ _ h12,
    Executable.ValidLayout.label_size 12 "rdone" _ h12, hd]
  simp

/-- **No step of the reader's mask at the exit label `rdone`.** -/
theorem readerR_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labM "rdone" → ¬ (layout mpInclImageR).instrStepEnv env x R := by
  haveI := mpInclImageR_valid (layout := layout)
  rw [labM_rdone]
  exact not_instrStepEnv_of_byteArray (i := 13) (b := .mk #[]) env mpInclImageR_13

omit layout [Executable.ValidLayout (layout mpInclImageV)] in
/-- The reader's cells are phase-1 (`dirs_phase1X`'s script; the conditional jump's
`if` by `prop_ite`, as the x64 absolute-address mask proofs' `popperX_dirsPhase1FX`). -/
theorem readerFragV_dirsPhase1X : ∀ d ∈ readerFragV, ∀ (e : _root_.Executable) z, DirPhase1X Arch.tso e d z := by
  intro d hd e z s pc
  simp only [readerFragV, List.mem_cons, List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  cells_phase1X

/-- **The reader's mask is phase-1** (its kept cells are the reader's; the
writer's `incl` is masked). -/
theorem mpInclImageR_phase1 : Phase1TreeX Arch.tso (layout mpInclImageR) := by
  haveI := mpInclImageR_valid (layout := layout)
  refine phase1TreeX_of_dirs (dirsPhase1X_layout (mem_maskKeep_range
    (Φd := fun d => ∀ (e : _root_.Executable) z, DirPhase1X Arch.tso e d z) ?_ ?_ ?_))
  · rw [show (mpInclImageV.drop 6).take (13 - 6) = readerFragV by decide]
    exact readerFragV_dirsPhase1X
  · intro l e z s pc
    simp [_root_.Directive.interp, Kraken.Promising.X64.toEv, Phase1Shape, DetAccess, SingleAccessS, AccessFree]
  · intro e z s pc
    simp [_root_.Directive.interp, Kraken.Promising.X64.toEv, Phase1Shape, DetAccess, SingleAccessS, AccessFree]

omit [Executable.ValidLayout (layout mpInclImageV)] in
/-- The image's non-data cells are fault-free. -/
theorem mpInclImageV_noFaultCode : DirsNoFaultCode (layout mpInclImageV) := by
  dirs_no_fault_code mpInclImageV mpInclCodeV mpInclDataV

end Kraken.Promising.X64.EnvG.MpInclAbs

#print axioms Kraken.Promising.X64.EnvG.MpInclAbs.writerW_envG
#print axioms Kraken.Promising.X64.EnvG.MpInclAbs.readerR_envG
#print axioms Kraken.Promising.X64.EnvG.MpInclAbs.mpInclImageW_lr
#print axioms Kraken.Promising.X64.EnvG.MpInclAbs.mpInclImageR_phase1
