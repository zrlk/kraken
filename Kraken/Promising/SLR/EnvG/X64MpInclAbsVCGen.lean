/-
**x64 MP with an unlocked `incl` release, the `.kl` code verbatim, on `EnvG`
by `vcgen`**: the `code` block of
`Kraken/Examples/LockFree/X64/mp_incl.kl` as written (`mpInclCodeV`: the
writer, `wdone: nop`, the reader, `rdone:`), run by both threads in its image
`mpInclImageV` (the code, then the `.kl` runner's data trailer
`mpInclDataV`). The x64 `incl` MP proof's theorem proves the per-thread texts
`mpIncWriterX` (no labels, no `jmp wdone`) and `mpReaderX` (labels
`spin`/`done_r`, no `jmp rdone`); this file proves the threads as the runner
runs them: thread `0` from the entry label `writer` to the exit label
`wdone`, thread `1` from `reader` to `rdone`.

The VCs are the x64 `incl` MP proof's and the x64 MP proof's, unchanged (`EnvG/X64MpIncVCGen.lean`,
`EnvG/X64MpVCGen.lean`). Placement: `cfgEnv_partial_at`
(`Kraken/EnvCfgAbs.lean`) at the fragments `writerFragV` (the `writer` block
and an empty exit block `wdone:`; the image's `wdone` block, `nop`, is never
run) and `readerFragV` (the image's tail), whose blocks are the image's
(`Program.subBlocksOfE`, by `decide`).

- `writerV_envG`: the writer's run in `EnvGLRX` (`MpInc.EW`);
- `readerV_envG`: the reader's run in the counted `EnvGX` (`MpSmoke.E`);
- `writerV_noNT`, `readerV_noNT`: the runs in the all-release environment.
-/
import Kraken.Promising.SLR.EnvG.X64MpIncVCGen
import Kraken.Promising.SLR.EnvG.X64MpIncRelPure
import Kraken.EnvVCGenAbs
import Kraken.EnvCfgAbs
import Kraken.Promising.SLR.EnvG.LRX64VCGen

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Mp
open Kraken.Promising.X64.EnvG.MpSmoke Kraken.Promising.X64.EnvG.MpInc
open Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.MpInclAbs

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The program and its image -/

/-- **The `code` block of `mp_incl.kl`, verbatim.** -/
def mpInclCodeV : Program := parse("
writer:
  movl $42,(%rsi)
  incl (%rdi)
  jmp wdone
wdone:
  nop
reader:
  movl (%rdi),%eax
  cmpl $0,%eax
  je reader
  movl (%rsi),%ebx
  jmp rdone
rdone:
")

/-- The `.kl` runner's data trailer of `mp_incl.kl`: each symbol a label
behind a padding cell, in the order of first mention (`d`, `f`). -/
def mpInclDataV : Program := [.byteArray (.mk #[]), .label "d", .byteArray (.mk #[]), .label "f"]

/-- The image: the code, then the data trailer. -/
def mpInclImageV : Program := mpInclCodeV ++ mpInclDataV

/-- The writer's fragment of the image: the `writer` block, then the exit
label `wdone` (an empty last block). -/
def writerFragV : Program := parse("
writer:
  movl $42,(%rsi)
  incl (%rdi)
  jmp wdone
wdone:
")

/-- The reader's fragment of the image: from `reader` to the exit label
`rdone`. -/
def readerFragV : Program := parse("
reader:
  movl (%rdi),%eax
  cmpl $0,%eax
  je reader
  movl (%rsi),%ebx
  jmp rdone
rdone:
")

/-- info: 13 -/
#guard_msgs in
#eval mpInclCodeV.length

theorem mpInclImageV_wf : Program.WF mpInclImageV := by decide

theorem writerFragV_sub : Program.subBlocksOfE writerFragV mpInclImageV = true := by decide

theorem readerFragV_sub : Program.subBlocksOfE readerFragV mpInclImageV = true := by decide

/-! ## The symbols -/

variable [layout : _root_.Layout]

/-- A label's address in the image. -/
abbrev labM (x : Label) : Int64 := (_root_.Executable.labels (layout mpInclImageV)).label x

/-- A symbol's address in the image. -/
abbrev symM (x : Label) : BitVec 64 := (labM x).toBitVec

variable [Executable.ValidLayout (layout mpInclImageV)]

local instance mpInclImageV.env : CodeEnv := ⟨layout mpInclImageV⟩

theorem writerFragV_placedIn : Program.PlacedIn writerFragV :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := mpInclImageV) mpInclImageV_wf rfl (by decide))
    writerFragV_sub

theorem readerFragV_placedIn : Program.PlacedIn readerFragV :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := mpInclImageV) mpInclImageV_wf rfl (by decide))
    readerFragV_sub

omit [Executable.ValidLayout (layout mpInclImageV)] in
theorem writerFragV_last : ∀ l blk, Program.blockAt writerFragV l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = labM "wdone" :=
  Program.after_last_of (by decide)

omit [Executable.ValidLayout (layout mpInclImageV)] in
theorem readerFragV_last : ∀ l blk, Program.blockAt readerFragV l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = labM "rdone" :=
  Program.after_last_of (by decide)

/-! ## The writer -/

/-- The writer's table: `W1I` at `writer`, `W3I` at `wdone`. -/
abbrev writerTableV (P : Params) (tid : Nat) : Label → MachineData → (EW P tid).State → Prop :=
  fun lb s σ => FrameRX P s ∧ ((lb = "writer" ∧ W1I P σ) ∨ (lb = "wdone" ∧ W3I P σ))

/-- **The verbatim x64 MP `incl` writer on `EnvGLRX`** (partial): from `W1I`
at the entry label, every run that reaches the exit label has `W3I`. -/
theorem writerV_envG (P : Params) (hL : MpLocs P) (tid : Nat) :
    ∀ s g, FrameRX P s ∧ W1I P g →
      Safely (cenv.instrStepEnv (EW P tid))
        (fun x => (x.1.2 = labM "wdone" ∧ W3I P x.2) ∨ False) ((s, labM "writer"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := EW P tid) (Q := fun _ σ => W3I P σ)
    (E := fun _ _ _ => False) (writerTableV P tid) ?_ rfl (by decide) writerFragV_placedIn
    writerFragV_last s g (by simpa [writerTableV] using hsg)
  cfg_cases_env [writerFragV]
  all_goals intro s₀ g₀
  all_goals vcgen [inc32_shared_spec]
  all_goals obtain ⟨⟨⟨hx0, hx1, hdf, hdd⟩, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [Reg64s.get64] at hx0 hx1
  case vc1 => simp [hx1, hdd]
  case vc2 => exact vc_w1I_ok hL tid _ hT (by simp [hx1]) (by decide)
  case vc3 => simp [hx0, hdf]
  case vc4 => exact ⟨trivial, by simp [SharedEnv.AccessIn, hx0]⟩
  case vc5 =>
    rename_i b σ1 hst v σ2 hld _
    have hW2 := vc_w1I_step hL tid _ hT (by simp [hx1]) (by decide) b σ1 hst
    have hW2' := vc_incLoad_at tid σ1 hW2 (by simp [hx0]) v σ2 hld
    refine ⟨(vc_incStore_at hL tid σ2 hW2' (by simp [hx0]) _).1, fun _ g'' hs' st => ?_⟩
    have hW3 := (vc_incStore_at hL tid σ2 hW2' (by simp [hx0]) _).2 _ g'' hs'
    vcgen
    rename_i σ3 hf
    simp only [fenceMonoX_le_within, fenceMonoX_le_envGLR] at hf
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simpa using hdf,
      by simpa using hdd⟩, .inr ⟨rfl, W3I.fence hW3 hf⟩⟩, .inl (by decide)⟩
  case vc1 => exact hT

/-! ## The reader -/

omit layout [Executable.ValidLayout (layout mpInclImageV)] in
theorem R4I.fence {P : Params} {σ σ' : EStateX} (h : R4I P σ) (hf : FenceLe σ σ') : R4I P σ' := by
  unfold R4I WorldRI at *; rw [hf.g, hf.r, hf.snap]; exact h

/-- The reader's table: `R1I` at `reader`; at `rdone`, `R4I` and, under the
clean flag, `ebx = 42`. -/
abbrev readerTableV (P : Params) (tid : Nat) :
    Label → MachineData → (SharedEnv.counted (E P tid)).State → Prop :=
  fun lb s σ => FrameRX P s ∧
    ((lb = "reader" ∧ R1I P σ.1) ∨
      (lb = "rdone" ∧ R4I P σ.1 ∧ (σ.1.cl → (s.regs.get64 .rbx).setWidth 32 = 42)))

/-- **The verbatim x64 MP reader on `EnvG`** (counted, partial): from `R1I`
at the entry label, every run that reaches the exit label has `R4I` and,
under the clean flag, `ebx = 42`. -/
theorem readerV_envG (P : Params) (tid : Nat) :
    ∀ s g, FrameRX P s ∧ R1I P g.1 →
      Safely (cenv.instrStepEnv (SharedEnv.counted (E P tid)))
        (fun x => (x.1.2 = labM "rdone" ∧ (R4I P x.2.1 ∧ (x.2.1.cl → (x.1.1.regs.get64 .rbx).setWidth 32 = 42)))
          ∨ False) ((s, labM "reader"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (E P tid))
    (Q := fun s σ => R4I P σ.1 ∧ (σ.1.cl → (s.regs.get64 .rbx).setWidth 32 = 42))
    (E := fun _ _ _ => False) (readerTableV P tid) ?_ rfl (by decide) readerFragV_placedIn
    readerFragV_last s g (by simpa [readerTableV] using hsg)
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

/-! ## Only release writes -/

open Kraken.Promising.X64.EnvG.MpRelPure

/-- The frame of either thread: `%rdi = f`, `%rsi = d`, neither word in
`dmem`. -/
abbrev FrameM (f d : BitVec 64) (s : MachineData) : Prop :=
  s.regs.get64 .rdi = f ∧ s.regs.get64 .rsi = d ∧ Mem.loadInt s.dmem f 4 = none ∧ Mem.loadInt s.dmem d 4 = none

/-- **The verbatim writer makes only release writes** (partial). -/
theorem writerV_noNT (f d : BitVec 64) :
    ∀ s g, FrameM f d s →
      Safely (cenv.instrStepEnv (EnvR f d)) (fun x => (x.1.2 = labM "wdone" ∧ True) ∨ False)
        ((s, labM "writer"), g) := by
  intro s g hs
  refine MachineWP.cfgEnv_partial_at (env := EnvR f d) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (fun lb s _ => lb = "writer" → FrameM f d s) ?_ rfl (by decide)
    writerFragV_placedIn writerFragV_last s g (fun _ => hs)
  cfg_cases_env [writerFragV]
  all_goals intro s₀ g₀
  all_goals vcgen [inc32_shared_spec]
  all_goals obtain ⟨hT, rfl, rfl⟩ := ‹(_ → _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [forall_const] at hT
  all_goals obtain ⟨hx0, hx1, hdf, hdd⟩ := hT
  all_goals simp only [Reg64s.get64] at hx0 hx1
  case vc5 =>
    refine ⟨?_, fun _ _ _ st => ?_⟩
    · simp_all
      exact fun h => h rfl
    · vcgen
      exact Table.ofLabelsEnv_at ⟨by decide, fun h => absurd h (by decide), .inl (by decide)⟩
  all_goals simp_all
  all_goals first | exact fun h => h rfl | trivial

/-- **The verbatim reader makes only release writes** (counted, partial). -/
theorem readerV_noNT (f d : BitVec 64) :
    ∀ s g, FrameM f d s →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EnvR f d))) (fun x => (x.1.2 = labM "rdone" ∧ True) ∨ False)
        ((s, labM "reader"), g) := by
  intro s g hs
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EnvR f d)) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (fun lb s _ => lb = "reader" → FrameM f d s) ?_ rfl (by decide)
    readerFragV_placedIn readerFragV_last s g (fun _ => hs)
  cfg_cases_env [readerFragV]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨hT, rfl, rfl⟩ := ‹(_ → _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [forall_const] at hT
  all_goals obtain ⟨hx0, hx1, hdf, hdd⟩ := hT
  all_goals simp only [Reg64s.get64] at hx0 hx1
  case vc2 =>
    rename_i x σ1 hld hz _
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hx0, hdf] at hm
    · refine Table.ofLabelsEnv_at ⟨by decide, fun _ => ⟨by simp [hx0], by simp [hx1], by simpa using hdf,
        by simpa using hdd⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      have hn := hst.2
      subst hg
      simp [SharedAccess.tick] at hn
  case vc4 => exact Table.ofLabelsEnv_at ⟨by decide, fun h => absurd h (by decide), .inl (by decide)⟩
  all_goals simp_all
  all_goals trivial

end Kraken.Promising.X64.EnvG.MpInclAbs
