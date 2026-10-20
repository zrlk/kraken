/-
**`treiber_pp.kl` whole image, part 1: the threads
by `vcgen` in the whole `.kl` image.**

`Treiber.treiber_pp_envG` (`EnvG/TreiberPublic.lean`) runs each thread over
its own part of the `code` block (per-thread image, each with its own
layout). Here both threads run the runner's executable: the whole block
`treiberImageA` (`treiberPusher`, the dead `NOP` behind `pdone:`, then
`treiberPopper`: `treiberImageA_eq`), laid out by one layout, each thread
from its entry label to its exit label
(`Kraken.Litmus.AArch64.prepareProgram`). The device is the AArch64 mask proofs'
(`EnvG/A64SpscWholeVCGen.lean`):

- **the pusher runs over its mask** `treiberImageP` (cells `0 … 10` kept:
  `pusher` to `pdone:`; the `NOP` and the popper's code are data cells), so
  its halt at `pdone` is read off the mask;
- **the popper runs over the image itself**: its exit label `qdone` is the
  block's last cell.
- **The scripts, tables and VCs are the Treiber proof's** (`pusher_envGC`,
  `popper_envGC`, `treiberPusher_relPure`, `treiberPopper_relPure`; the
  tables `pushTable`, `popTable`, `pushPureTable`, `popPureTable`; the VCs of
  `EnvG/TreiberVC.lean`), unchanged; only the control-flow rule differs:
  `MachineWP.cfgEnv_partial_at` (`EnvG/A64MaskCfg.lean`) with the thread's
  text `PlacedIn` the image (or the mask), instead of `cfgEnv_partial` in the
  thread's own layout. (The runs are not re-elaborated here; they
  are the `_at` runs `pusher_envGC_at`, `popper_envGC_at`,
  `treiberPusher_relPure_at` and `treiberPopper_relPure_at` of
  `EnvG/TreiberVCGen.lean` and `EnvG/TreiberRelPure.lean`, instantiated at
  the image and the mask.)
- `pusherW_envGC` (over the mask), `popperW_envGC`: the runs in the counted
  `EnvGC`; `pusherW_relPure`, `popperW_relPure`: the purity runs in the
  counted `relPure`, at the unmasked image.
-/
import Kraken.Promising.SLR.EnvG.TreiberVCGen
import Kraken.Promising.SLR.EnvG.TreiberRelPure
import Kraken.Promising.SLR.EnvG.A64MaskLink
import Kraken.Promising.SLR.EnvG.A64MaskCfg
open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
namespace Kraken.Promising.SLR.EnvG.Treiber
set_option mvcgen.warning false
set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

/-! ## The image and the pusher's mask -/

/-- **The `code` block of `treiber_pp.kl`, verbatim**: the runner's
executable, shared by both threads (`P0: pusher pdone; P1: popper qdone`). -/
def treiberImageA : Program := parseAArch64("
pusher:
  STR W9,[X1]
push:
  LDAR X2,[X0]
  STR X2,[X1,#8]
  MOV X3,X2
  CASAL X3,X1,[X0]
  CMP X3,X2
  B.NE push
  B pdone
pdone:
  NOP
popper:
  LDAR X2,[X0]
  CBZ X2,popper
  LDR X4,[X2,#8]
  MOV X3,X2
  CASAL X3,X4,[X0]
  CMP X3,X2
  B.NE popper
  MOV X10,X2
  LDR W11,[X2]
  B qdone
qdone:
")

/-- info: 24 -/
#guard_msgs in
#eval treiberImageA.length

/-- The image is the per-thread parts of `treiber_pp_envG` around the `NOP`. -/
theorem treiberImageA_eq :
    treiberImageA.take 11 = treiberPusher ∧ treiberImageA.drop 12 = treiberPopper := by decide

/-- **The pusher's mask**: cells `0 … 10` (`pusher` to `pdone:`) kept; the
dead `NOP` and the popper's code are data cells (labels kept). -/
def treiberImageP : Program := treiberImageA.maskKeep (keepRange 0 11)

theorem treiberImageA_wf : Program.WF treiberImageA := by decide
theorem treiberImageP_wf : Program.WF treiberImageP := by decide
theorem treiberPusher_wf : Program.WF treiberPusher := by decide
theorem treiberPopper_wf : Program.WF treiberPopper := by decide
theorem treiberPusher_eq : treiberPusher = Directive.label "pusher" :: treiberPusher.tail := by decide
theorem treiberPopper_eq : treiberPopper = Directive.label "popper" :: treiberPopper.tail := by decide
theorem treiberPusher_subP : Program.subBlocksOfE treiberPusher treiberImageP = true := by decide
theorem treiberPusher_sub : Program.subBlocksOfE treiberPusher treiberImageA = true := by decide
theorem treiberPopper_sub : Program.subBlocksOfE treiberPopper treiberImageA = true := by decide
theorem treiberPusher_exit : Program.exitCheck treiberPusher "pdone" = true := by decide
theorem treiberPopper_exit : Program.exitCheck treiberPopper "qdone" = true := by decide

/-- The pusher's mask's cell behind `pdone:` (the `NOP`'s) is data. -/
theorem treiberImageP_11 : treiberImageP[11]? = some (.byteArray (.mk #[])) := by decide

variable [layout : _root_.Layout]

/-- A label's address in the image. -/
abbrev labT (x : Label) : Int64 := (_root_.Executable.labels (layout treiberImageA)).label x

theorem treiberImageP_mask : MaskOf (layout treiberImageA) (layout treiberImageP) := maskOf_layout _ _

theorem labelsTP_eq :
    _root_.Executable.labels (layout treiberImageP) = _root_.Executable.labels (layout treiberImageA) :=
  labels_mask treiberImageP_mask

theorem treiberImageP_valid [Executable.ValidLayout (layout treiberImageA)] :
    Executable.ValidLayout (layout treiberImageP) :=
  ValidLayout.of_mask treiberImageP_mask

/-! ## The pusher over its mask -/

section PushW

variable [Executable.ValidLayout (layout treiberImageA)]

local instance treiberImageP.env : CodeEnv := ⟨layout treiberImageP⟩

theorem pushP_placedIn : Program.PlacedIn treiberPusher :=
  haveI := treiberImageP_valid (layout := layout)
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := treiberImageP) treiberImageP_wf rfl (by decide))
    treiberPusher_subP

/-- The pusher's run over its mask, at the mask's labels (`pusher_envGC_at`
at the mask). -/
theorem pusherW_envGC' (t n : BitVec 64) (tok : Loc) (hL : TLocs (tParams t n tok)) :
    ∀ s g, pushTable t n tok "pusher" s g →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EP (tParams t n tok))))
        (fun x => (x.1.2 = (_root_.Executable.labels cenv).label "pdone" ∧ Pd (tParams t n tok) x.2.1) ∨ False)
        ((s, (_root_.Executable.labels cenv).label "pusher"), g) :=
  pusher_envGC_at t n tok hL pushP_placedIn (Program.last_of_check treiberPusher_exit)

end PushW

/-! ## The popper and the purity runs over the image -/

section ImageW

variable [Executable.ValidLayout (layout treiberImageA)]

local instance treiberImageA.env : CodeEnv := ⟨layout treiberImageA⟩

theorem popA_placedIn : Program.PlacedIn treiberPopper :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := treiberImageA) treiberImageA_wf rfl (by decide))
    treiberPopper_sub

theorem pushA_placedIn : Program.PlacedIn treiberPusher :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := treiberImageA) treiberImageA_wf rfl (by decide))
    treiberPusher_sub

/-- The popper's run in the image (`popper_envGC_at` at the image). -/
theorem popperW_envGC (t n : BitVec 64) (tok : Loc) (hL : TLocs (tParams t n tok)) :
    ∀ s g, popTable t n tok "popper" s g →
      Safely ((layout treiberImageA).instrStepEnv (SharedEnv.counted (EQ (tParams t n tok))))
        (fun x => (x.1.2 = labT "qdone" ∧ (x.2.1.cl → x.1.1.regs.X10.toBitVec = n ∧ x.1.1.regs.X11.toBitVec = 1))
          ∨ False)
        ((s, labT "popper"), g) :=
  popper_envGC_at t n tok hL popA_placedIn (Program.last_of_check treiberPopper_exit)

/-- The pusher's purity run in the image (`treiberPusher_relPure_at` at the
image). -/
theorem pusherW_relPure (rel : Loc → Pred) (t n : BitVec 64)
    (hd : ∀ v : Val, Pred.Pure (rel ⟨n, 4⟩) v) (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v) :
    ∀ s g, pushPureTable t n rel "pusher" s g →
      Safely ((layout treiberImageA).instrStepEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)))
        (fun x => (x.1.2 = labT "pdone" ∧ True) ∨ False) ((s, labT "pusher"), g) :=
  treiberPusher_relPure_at rel t n hd hn pushA_placedIn (Program.last_of_check treiberPusher_exit)

/-- The popper's purity run in the image (`treiberPopper_relPure_at` at the
image). -/
theorem popperW_relPure (rel : Loc → Pred) (t : BitVec 64) :
    ∀ s g, popPureTable t rel "popper" s g →
      Safely ((layout treiberImageA).instrStepEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)))
        (fun x => (x.1.2 = labT "qdone" ∧ True) ∨ False) ((s, labT "popper"), g) :=
  treiberPopper_relPure_at rel t popA_placedIn (Program.last_of_check treiberPopper_exit)

end ImageW

/-- **The pusher's run over its mask**, at the image's labels. -/
theorem pusherW_envGC [Executable.ValidLayout (layout treiberImageA)] (t n : BitVec 64) (tok : Loc)
    (hL : TLocs (tParams t n tok)) :
    ∀ s g, pushTable t n tok "pusher" s g →
      Safely ((layout treiberImageP).instrStepEnv (SharedEnv.counted (EP (tParams t n tok))))
        (fun x => (x.1.2 = labT "pdone" ∧ Pd (tParams t n tok) x.2.1) ∨ False) ((s, labT "pusher"), g) := by
  intro s g hsg
  have h : Safely ((layout treiberImageP).instrStepEnv (SharedEnv.counted (EP (tParams t n tok))))
      (fun x => (x.1.2 = (_root_.Executable.labels (layout treiberImageP)).label "pdone" ∧
        Pd (tParams t n tok) x.2.1) ∨ False)
      ((s, (_root_.Executable.labels (layout treiberImageP)).label "pusher"), g) :=
    pusherW_envGC' t n tok hL s g hsg
  rw [labelsTP_eq] at h
  exact h

end Kraken.Promising.SLR.EnvG.Treiber

#print axioms Kraken.Promising.SLR.EnvG.Treiber.pusherW_envGC
#print axioms Kraken.Promising.SLR.EnvG.Treiber.popperW_envGC
#print axioms Kraken.Promising.SLR.EnvG.Treiber.pusherW_relPure
#print axioms Kraken.Promising.SLR.EnvG.Treiber.popperW_relPure
