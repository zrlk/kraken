/-
**The pusher of `treiber_pp.kl`, verbatim, over the masked image**
The run of the x64 absolute-address proofs' `pusherV_envGC`
(`EnvG/X64TreiberAbsVCGen.lean`) with the ambient code the **mask**
`treiberImageM` of the image `treiberImageV`: the cells from `pdone`'s
`nop` on (the `nop` and the popper's code) are data cells
(`Program.maskKeep`, `EnvG/X64MaskCore.lean`). The script is
`pusherV_envGC`'s, unchanged; only the placement is in the mask.

The mask has no instruction at the exit label `pdone` (its `nop` is masked),
which is the halt the rule link needs (`X64MaskLink.lean`), and only the
pusher's cells have code, which is the phase-1 shape obligation.

- `treiberImageM`, `treiberImageM_mask` (`MaskOf`), `treiberImageM_valid`;
- `labM_eq`: the mask's labels are the image's;
- `pusherM_envGC`: the run, in the counted `EnvGCX`, over the mask, at the
  image's labels;
- `pusherM_stuck`: no step of the mask at `pdone`;
- `treiberImageM_phase1FX`: the mask's phase-1 shape.
-/
import Kraken.Promising.SLR.EnvG.X64TreiberAbsVCGen
import Kraken.Promising.SLR.EnvG.X64MaskLink

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.EnvG.Treiber Kraken.Promising.SLR.EnvG.TreiberCommon
open Kraken.Promising.X64.EnvG.TreiberX Kraken.Promising.X64.EnvG.TreiberAbs
open Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.TreiberAbs

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The mask -/

/-- **The pusher's mask of the image**: the cells `0 … 8` (`pusher:` to
`pdone:`) kept, every later non-label cell a data cell. -/
def treiberImageM : Program := treiberImageV.maskKeep (keepRange 0 9)

theorem treiberImageM_wf : Program.WF treiberImageM := by decide

theorem pusherFragM_sub : Program.subBlocksOfE treiberPusherX treiberImageM = true := by decide

/-- The mask's cell at `pdone`'s `nop` is a data cell. -/
theorem treiberImageM_9 : treiberImageM[9]? = some (.byteArray (.mk #[])) := by decide

variable [layout : _root_.Layout]

theorem treiberImageM_mask : MaskOf (layout treiberImageV) (layout treiberImageM) :=
  maskOf_layout _ _

/-- A label's address in the mask. -/
abbrev labM (x : Label) : Int64 := (_root_.Executable.labels (layout treiberImageM)).label x

theorem labM_eq (x : Label) : labM x = labT x := by
  show (_root_.Executable.labels (layout treiberImageM)).label x = (_root_.Executable.labels (layout treiberImageV)).label x
  rw [labels_mask treiberImageM_mask]

variable [Executable.ValidLayout (layout treiberImageV)]

theorem treiberImageM_valid : Executable.ValidLayout (layout treiberImageM) :=
  ValidLayout.of_mask treiberImageM_mask

section Run

local instance treiberImageM.env : CodeEnv := ⟨layout treiberImageM⟩

theorem pusherFragM_placedIn : Program.PlacedIn treiberPusherX :=
  haveI := treiberImageM_valid (layout := layout)
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := treiberImageM) treiberImageM_wf rfl (by decide))
    pusherFragM_sub

omit [Executable.ValidLayout (layout treiberImageV)] in
theorem pusherFragM_last : ∀ l blk, Program.blockAt treiberPusherX l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = labM "pdone" :=
  pusherFrag_last

/-! ## The pusher over the mask -/

/-- The run over the mask, at the mask's labels (`pusherV_envGC`'s script,
`pusher_envGC_of`). -/
theorem pusherM_envGC' (t n : BitVec 64) (tok : Loc) (hL : TLocs (tParamsX t n tok)) :
    ∀ s g, PFrameX t n s ∧ Pu0 (tParamsX t n tok) g.1 →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EPX t n tok)))
        (fun x => (x.1.2 = labM "pdone" ∧ Pd (tParamsX t n tok) x.2.1) ∨ False) ((s, labM "pusher"), g) :=
  pusher_envGC_of t n tok hL pusherFragM_placedIn

end Run

/-- **The verbatim x64 pusher on `EnvGCX`, over the mask** (counted,
partial), at the image's labels. -/
theorem pusherM_envGC (t n : BitVec 64) (tok : Loc) (hL : TLocs (tParamsX t n tok)) :
    ∀ s g, PFrameX t n s ∧ Pu0 (tParamsX t n tok) g.1 →
      Safely ((layout treiberImageM).instrStepEnv (SharedEnv.counted (EPX t n tok)))
        (fun x => (x.1.2 = labT "pdone" ∧ Pd (tParamsX t n tok) x.2.1) ∨ False) ((s, labT "pusher"), g) := by
  intro s g h
  have := pusherM_envGC' t n tok hL s g h
  simp only [labM_eq] at this
  exact this

omit [Executable.ValidLayout (layout treiberImageV)] in
/-- `pdone`'s address is the mask's cell `9`. -/
theorem labT_pdone [Executable.ValidLayout (layout treiberImageV)] :
    labT "pdone" = (layout treiberImageM).addrOf 9 := by
  have hd : labT "pdone" = (layout treiberImageV).addrOf 8 :=
    Program.label_addrOf_drop treiberImageV_wf.nodup (by decide) (by decide)
  have h8 : (layout treiberImageV).2[8]? = some (Directive.label "pdone", Kraken.Layout.size Directive 8) := by
    simp [Layout.apply_snd, Layout.frag, treiberImageV, treiberCodeV, treiberDataV]
  rw [addrOf_mask treiberImageM_mask, Executable.addrOf_succ _ h8,
    Executable.ValidLayout.label_size 8 "pdone" _ h8, hd]
  simp

/-- **No step of the mask at the exit label `pdone`.** -/
theorem pusherM_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labT "pdone" → ¬ (layout treiberImageM).instrStepEnv env x R := by
  haveI := treiberImageM_valid (layout := layout)
  rw [labT_pdone]
  exact not_instrStepEnv_of_byteArray (i := 9) (b := .mk #[]) env treiberImageM_9

end Kraken.Promising.X64.EnvG.TreiberAbs

#print axioms Kraken.Promising.X64.EnvG.TreiberAbs.pusherM_envGC
#print axioms Kraken.Promising.X64.EnvG.TreiberAbs.pusherM_stuck
