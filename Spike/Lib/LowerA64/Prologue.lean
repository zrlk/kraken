/-
**The stack-limit prologue lands at a lowered body's node** (AArch64),
symbolic in the frame.

`prologue_body_seg`: `prologue_seg_ofW` (the stack check against the
thread's limit, the frame's setup saving the caller's `x29`/`x30`) for a
function without parameters, from the function's label to `bodyN` at the
body's entry: the saved pair is the entry's `x29`/`x30` (`FrJ`), and the
source's node invariant holds of any cells (a body whose environment places
no word in a cell, as `main`'s `[(arg, unit, [])]`), the source control
reached locally from the ghost `c0`.
-/
import Spike.Lib.LowerA64.Node
import Spike.Lib.A64CodeSegs

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64 (CodeAt)
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.Form (opdVal NodeJ SEnv sevalAt lookupS WordPl WordsRep WordRep SRep)
open Spike.Lib.LowerNode

set_option linter.unusedSimpArgs false

/-- The body's offsets claim no more than the prologue's exit offsets. -/
theorem oF_le_oFr (cx : FnCtx) (hF : (Int64.ofInt cx.frame).toInt = cx.frame) :
    SO.le (oF cx) (oFr (Int64.ofInt cx.frame)) = true := by
  simp [SO.le, oF, oFr, hF]

/-- The saved pair after the frame's setup. -/
theorem frJ_frSlot (σ : AS) : FrJ σ.regs.X29.toBitVec σ.regs.X30.toBitVec (frSlot σ) := by
  constructor <;> simp [frSlot, upd_apply]

section Pro

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive} {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {W : Frag isaLSE2} {K : State → State → Prop}

/-- **A parameterless function's prologue is one segment** in any valid
layout of a program with `prologueIn` at the frame `cx.frame`: from the
function's label (`sp` at 0) to the body's node at its entry, the ghosts
`fp`/`ra` the entry's `x29`/`x30`. -/
theorem prologue_body_seg {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hp : Lays exe prog) (hend : endPc = endOf exe prog) {fn sc entry : Label} {lim : Int64} {L : Label}
    (hin : prologueIn prog fn sc entry (Int64.ofInt cx.frame) lim L [] = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} {fp ra : BitVec 64} {c0 : Ctl} {t : Expr} {s : SEnv}
    (hW : ProW W K exe endPc R F ms ((_root_.Executable.labels exe).label fn) (Int64.ofInt cx.frame) lim L [] J)
    (hedge : ∀ σ c, J σ c →
      (ms.rt (tcbA σ.regs lim).toNat ∧ ms.mp ⟨tcbA σ.regs lim, 8⟩ false ∧
        (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs lim) 8 = none) ∧
        ∀ v : Val, ms.G ⟨tcbA σ.regs lim, 8⟩ v →
          (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (Int64.ofInt cx.frame).toBitVec).toNat) ∧
      σ.regs.X29.toBitVec = fp ∧ σ.regs.X30.toBitVec = ra ∧ (∀ sl, NJ p lbl (rsOf cx) t s sl c) ∧
      LocalRun p c0 c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label fn, ⟨0, []⟩, J⟩)
      (At exe endPc R F (bodyN p lbl cx fp ra c0 ((_root_.Executable.labels exe).label entry) t s)) := by
  have hge := frame_ge16 hf
  have hF64 : (Int64.ofInt cx.frame).toInt = cx.frame := toInt_ofInt_small (by omega) (by omega)
  refine prologue_seg_ofW hp hend hin (by rw [hF64]; omega) (by rw [hF64]; omega) hF hR hal
    (by rw [hF64]; exact hlo) hhi (by simp) rfl (oF_le_oFr cx hF64) hW fun σ c hJ => ?_
  obtain ⟨⟨hrt, hmp, hld, hG⟩, h29, h30, hN, hc0⟩ := hedge σ c hJ
  refine ⟨hrt, hmp, hld, fun v hv => ⟨hG v hv, fun σ' _ hsl => ⟨hN _, ?_, hc0⟩⟩⟩
  simp only [stSlots] at hsl
  rw [hsl, ← h29, ← h30]
  exact frJ_frSlot σ

end Pro

end Spike.Lib.LowerA64
