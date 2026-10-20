/-
**Whole image, part 1: the threads of
`spsc_queue.kl` by `vcgen` in the whole `.kl` image.**

`a64_spsc_envG` (`EnvG/A64SpscPublic.lean`) runs each thread over its own
part of the `code` block (per-thread image). Here both threads run the
runner's executable: the whole block `spscImageA`
(`= spscProdA ++ spscNop ++ spscConsA`, `spscImageA_eq`), laid out by one
layout, each thread from its entry label to its exit label
(`Kraken.Litmus.AArch64.prepareProgram`).

- **The producer runs over its mask** `spscImageP` (`EnvG/A64MaskCore.lean`:
  cells `0 … 17` kept, the dead `NOP` behind `pdone:` and the consumer's
  code data cells), so its halt at `pdone` is read off the mask (the
  guarded exit, `prodP_stuck` in `EnvG/A64SpscWholePublic.lean`).
- **The consumer runs over the image itself**: its exit label `cdone` is the
  block's last cell, so nothing follows it, and every cell of the image is
  phase-1.
- **The scripts and VCs are the AArch64 SPSC proof's** (`EnvG/A64SpscVCGen.lean`,
  `EnvG/A64SpscRelPure.lean`, the VCs of `EnvG/A64SpscVCP.lean`,
  `EnvG/A64SpscVCC.lean`, the tables `prodTable`, `consTable`,
  `prodPureTable`), unchanged; only the control-flow rule differs:
  `MachineWP.cfgEnv_partial_at` (`EnvG/A64MaskCfg.lean`) with the thread's
  text `PlacedIn` the ambient code (`Program.PlacedIn.of_placedE`) and its
  exit by `Program.last_of_check`, instead of `cfgEnv_partial` in the
  thread's own layout. The scripts are not repeated here:
  each run is the AArch64 SPSC proof's `…_at` theorem (stated once over any ambient code
  in which the text is `PlacedIn`, `EnvG/A64MaskRunAt.lean`) at the image
  (or the mask).
- `spscProdW_envGTU`, `spscConsW_envGTU`: the runs in the counted `EnvGTU`;
  `spscProdW_relPure`, `spscConsW_relPure`: the purity runs in the counted
  `relPure` at the unmasked image.
-/
import Kraken.Promising.SLR.EnvG.A64SpscRelPure
import Kraken.Promising.SLR.EnvG.A64MaskLink
import Kraken.Promising.SLR.EnvG.A64MaskCfg
open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
namespace Kraken.Promising.SLR.EnvG.SpscA
set_option mvcgen.warning false
set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

/-! ## The image and the producer's mask -/

/-- **The `code` block of `spsc_queue.kl`, verbatim**: the runner's
executable, shared by both threads (`P0: prod pdone; P1: cons cdone`). -/
def spscImageA : Program := parseAArch64("
prod:
  MOV W3,#1
  MOV X4,#0
  MOV X7,X0
prod_loop:
  LDAR X5,[X1]
  SUB X6,X4,X5
  CMP X6,#2
  B.EQ prod_loop
  STR W3,[X7]
  EOR X7,X7,#8
  ADD X4,X4,#1
  STLR X4,[X2]
  ADD W3,W3,#1
  CMP W3,#4
  B.NE prod_loop
  B pdone
pdone:
  NOP
cons:
  MOV X4,#0
  MOV X7,X0
c1:
  LDAR X5,[X2]
  CMP X5,X4
  B.EQ c1
  LDR W10,[X7]
  EOR X7,X7,#8
  ADD X4,X4,#1
  STLR X4,[X1]
c2:
  LDAR X5,[X2]
  CMP X5,X4
  B.EQ c2
  LDR W11,[X7]
  EOR X7,X7,#8
  ADD X4,X4,#1
  STLR X4,[X1]
c3:
  LDAR X5,[X2]
  CMP X5,X4
  B.EQ c3
  LDR W12,[X7]
  EOR X7,X7,#8
  ADD X4,X4,#1
  STLR X4,[X1]
  B cdone
cdone:
")

/-- info: 48 -/
#guard_msgs in
#eval spscImageA.length

/-- The image is the per-thread parts of `a64_spsc_envG` in a row. -/
theorem spscImageA_eq : spscImageA = spscProdA ++ spscNop ++ spscConsA := by decide

/-- **The producer's mask**: cells `0 … 17` (`prod` to `pdone:`) kept; the
dead `NOP` and the consumer's code are data cells (labels kept). -/
def spscImageP : Program := spscImageA.maskKeep (keepRange 0 18)

theorem spscImageA_wf : Program.WF spscImageA := by decide
theorem spscImageP_wf : Program.WF spscImageP := by decide
theorem spscProdA_wf : Program.WF spscProdA := by decide
theorem spscConsA_wf : Program.WF spscConsA := by decide
theorem spscProdA_eq : spscProdA = Directive.label "prod" :: spscProdA.tail := by decide
theorem spscConsA_eq : spscConsA = Directive.label "cons" :: spscConsA.tail := by decide
theorem spscProdA_subP : Program.subBlocksOfE spscProdA spscImageP = true := by decide
theorem spscProdA_sub : Program.subBlocksOfE spscProdA spscImageA = true := by decide
theorem spscConsA_sub : Program.subBlocksOfE spscConsA spscImageA = true := by decide
theorem spscProdA_exit : Program.exitCheck spscProdA "pdone" = true := by decide
theorem spscConsA_exit : Program.exitCheck spscConsA "cdone" = true := by decide

/-- The producer's mask's cell behind `pdone:` (the `NOP`'s) is data. -/
theorem spscImageP_18 : spscImageP[18]? = some (.byteArray (.mk #[])) := by decide

variable [layout : _root_.Layout]

/-- A label's address in the image. -/
abbrev labA (x : Label) : Int64 := (_root_.Executable.labels (layout spscImageA)).label x

theorem spscImageP_mask : MaskOf (layout spscImageA) (layout spscImageP) := maskOf_layout _ _

theorem labelsP_eq : _root_.Executable.labels (layout spscImageP) = _root_.Executable.labels (layout spscImageA) :=
  labels_mask spscImageP_mask

theorem spscImageP_valid [Executable.ValidLayout (layout spscImageA)] :
    Executable.ValidLayout (layout spscImageP) :=
  ValidLayout.of_mask spscImageP_mask

/-! ## The producer over its mask -/

section Prod

variable [Executable.ValidLayout (layout spscImageA)]

local instance spscImageP.env : CodeEnv := ⟨layout spscImageP⟩

theorem prodP_placedIn : Program.PlacedIn spscProdA :=
  haveI := spscImageP_valid (layout := layout)
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := spscImageP) spscImageP_wf rfl (by decide))
    spscProdA_subP

/-- The producer's run over its mask, at the mask's labels
(`spscProdA_envGTU`'s script). -/
theorem spscProdW_envGTU' (P : SP) (hL : SpscLocs P) (tid : Nat) :
    ∀ s g, FrameP P s ∧ PR P 1 g.1 →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EP P tid)))
        (fun x => (x.1.2 = (_root_.Executable.labels cenv).label "pdone" ∧ (x.2.1.r.wr P.T).q = 1) ∨ False)
        ((s, (_root_.Executable.labels cenv).label "prod"), g) := by
  intro s g hsg
  exact spscProdA_envGTU_at P hL tid prodP_placedIn (Program.last_of_check spscProdA_exit) s g
    (by simpa [prodTable] using hsg)

end Prod

/-! ## The consumer over the image -/

section Cons

variable [Executable.ValidLayout (layout spscImageA)]

local instance spscImageA.env : CodeEnv := ⟨layout spscImageA⟩

theorem consA_placedIn : Program.PlacedIn spscConsA :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := spscImageA) spscImageA_wf rfl (by decide))
    spscConsA_sub

theorem prodA_placedIn : Program.PlacedIn spscProdA :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := spscImageA) spscImageA_wf rfl (by decide))
    spscProdA_sub

/-- The consumer's run in the image (`spscConsA_envGTU`'s script). -/
theorem spscConsW_envGTU (P : SP) (hL : SpscLocs P) (tid : Nat) :
    ∀ s g, FrameC P s ∧ CE P 1 g.1 →
      Safely ((layout spscImageA).instrStepEnv (SharedEnv.counted (EC P tid)))
        (fun x => (x.1.2 = labA "cdone" ∧ (x.2.1.cl → x.1.1.regs.X10.toBitVec.setWidth 32 = 1 ∧
          x.1.1.regs.X11.toBitVec.setWidth 32 = 2 ∧ x.1.1.regs.X12.toBitVec.setWidth 32 = 3)) ∨ False)
        ((s, labA "cons"), g) := by
  intro s g hsg
  exact spscConsA_envGTU_at P hL tid consA_placedIn (Program.last_of_check spscConsA_exit) s g
    (by simpa [consTable] using hsg)

/-- The producer's purity run in the image (`spscProdA_relPure`'s script). -/
theorem spscProdW_relPure (P : SP) (rel : Loc → Pred) (h0 : ∀ v, Pred.Pure (rel P.B0) v)
    (h1 : ∀ v, Pred.Pure (rel P.B1) v) :
    ∀ s g, FrameP P s →
      Safely ((layout spscImageA).instrStepEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)))
        (fun x => (x.1.2 = labA "pdone" ∧ True) ∨ False) ((s, labA "prod"), g) := by
  intro s g hsg
  exact spscProdA_relPure_at P rel h0 h1 prodA_placedIn (Program.last_of_check spscProdA_exit) s g
    (by simpa [prodPureTable] using hsg)

/-- The consumer's purity run in the image (`spscConsA_relPure`'s script). -/
theorem spscConsW_relPure (P : SP) (rel : Loc → Pred) :
    ∀ s g, FrameC P s →
      Safely ((layout spscImageA).instrStepEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)))
        (fun x => (x.1.2 = labA "cdone" ∧ True) ∨ False) ((s, labA "cons"), g) := by
  intro s g hsg
  exact spscConsA_relPure_at P rel consA_placedIn (Program.last_of_check spscConsA_exit) s g hsg

end Cons

/-- **The producer's run over its mask**, at the image's labels. -/
theorem spscProdW_envGTU [Executable.ValidLayout (layout spscImageA)] (P : SP) (hL : SpscLocs P) (tid : Nat) :
    ∀ s g, FrameP P s ∧ PR P 1 g.1 →
      Safely ((layout spscImageP).instrStepEnv (SharedEnv.counted (EP P tid)))
        (fun x => (x.1.2 = labA "pdone" ∧ (x.2.1.r.wr P.T).q = 1) ∨ False) ((s, labA "prod"), g) := by
  intro s g hsg
  have h : Safely ((layout spscImageP).instrStepEnv (SharedEnv.counted (EP P tid)))
      (fun x => (x.1.2 = (_root_.Executable.labels (layout spscImageP)).label "pdone" ∧ (x.2.1.r.wr P.T).q = 1) ∨ False)
      ((s, (_root_.Executable.labels (layout spscImageP)).label "prod"), g) :=
    spscProdW_envGTU' P hL tid s g hsg
  rw [labelsP_eq] at h
  exact h

end Kraken.Promising.SLR.EnvG.SpscA

#print axioms Kraken.Promising.SLR.EnvG.SpscA.spscProdW_envGTU
#print axioms Kraken.Promising.SLR.EnvG.SpscA.spscConsW_envGTU
#print axioms Kraken.Promising.SLR.EnvG.SpscA.spscProdW_relPure
#print axioms Kraken.Promising.SLR.EnvG.SpscA.spscConsW_relPure
