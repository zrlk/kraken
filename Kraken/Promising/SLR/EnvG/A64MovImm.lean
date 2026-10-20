/-
Per-directive facts for AArch64 `MOVZ` and `MOVK`, generic in the immediate:
their trees are phase-1 (`DirPhase1F`) and fault-free (`DirNoFault`).

`dirs_phase1F` and `dirs_no_fault'` unfold each directive of a text; for a
16-bit immediate shifted by 32 or 48 that unfolding exceeds the kernel's
recursion depth. These lemmas discharge such directives without unfolding the
immediate: in a per-directive check, try `movz_phase1F`/`movk_phase1F`
(`movz_noFault`/`movk_noFault`) before the generic `simp`.
-/
import Kraken.Promising.SLR.EnvG.A64RmwFail
import Kraken.Promising.EnvLinkTermAArch64

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR.EnvG

/-- `MOVZ`'s tree is phase-1 (no access), for every immediate and shift. -/
theorem movz_phase1F {w : RegWidth} (dst : RegOrZr w) (imm : ConstExpr) (sh : MovShift w)
    (e : _root_.Executable) (z : Nat) : DirPhase1F e (.instr ⟨w, .MOVZ dst imm sh⟩) z := by
  intro s pc
  simp [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp, toEv, Phase1ShapeF,
    DetAccess, SingleAccessS2, _root_.MachineData.setRegOrZr]
  all_goals (repeat' (first | split | simp [toEv, Phase1ShapeF, DetAccess, SingleAccessS2, AccessFree]))

/-- `MOVK`'s tree is phase-1 (no access), for every immediate and shift. -/
theorem movk_phase1F {w : RegWidth} (dst : RegOrZr w) (imm : ConstExpr) (sh : MovShift w)
    (e : _root_.Executable) (z : Nat) : DirPhase1F e (.instr ⟨w, .MOVK dst imm sh⟩) z := by
  intro s pc
  simp [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp, toEv, Phase1ShapeF,
    DetAccess, SingleAccessS2, _root_.MachineData.setRegOrZr]
  all_goals (repeat' (first | split | simp [toEv, Phase1ShapeF, DetAccess, SingleAccessS2, AccessFree]))

/-- `MOVZ`'s tree has no fault leaf, for every immediate and shift. -/
theorem movz_noFault {w : RegWidth} (dst : RegOrZr w) (imm : ConstExpr) (sh : MovShift w)
    (e : _root_.Executable) (z : Nat) : DirNoFault e (.instr ⟨w, .MOVZ dst imm sh⟩) z := by
  intro s pc
  simp [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp, toEv, EvTree.NoFault,
    _root_.MachineData.setRegOrZr]
  all_goals (repeat' (first | split | simp [toEv, EvTree.NoFault]))

/-- `MOVK`'s tree has no fault leaf, for every immediate and shift. -/
theorem movk_noFault {w : RegWidth} (dst : RegOrZr w) (imm : ConstExpr) (sh : MovShift w)
    (e : _root_.Executable) (z : Nat) : DirNoFault e (.instr ⟨w, .MOVK dst imm sh⟩) z := by
  intro s pc
  simp [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp, toEv, EvTree.NoFault,
    _root_.MachineData.setRegOrZr]
  all_goals (repeat' (first | split | simp [toEv, EvTree.NoFault]))

end Kraken.Promising.AArch64.EnvG
