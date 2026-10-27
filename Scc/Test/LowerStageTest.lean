import Scc.Cert.LowerStage
import Spike.Lib.Ret0Src

/-!
# Tests of the lowering's two kernel steps (`Scc/Cert/LowerStage.lean`)

At `ret0.w`'s source (`Spike.Lib.Ret0Src.ret0Src`) on both ISAs: the depth
limit `frames1` and the lowering `ir1` hold as kernel checks, and
`lowerIR_of_stages` gives `lowerIR`'s IR and setup flag from them, the same
value the one-step check computes.
-/

namespace Scc.Test.LowerStage

open Scc.Cert.LowerStage

/-- The configurations of both ISAs. -/
def cfgX64 : Scc.Config := { arch := .x64, host := .linux, gc := .none }
def cfgA64 : Scc.Config := { arch := .arm, host := .linux, gc := .none }

/-- `ret0`'s depth limit, by evaluation (untrusted; the theorems check it). -/
def frX64 : Nat := (frames1 cfgX64 Spike.Lib.Ret0Src.ret0Src).get!
def frA64 : Nat := (frames1 cfgA64 Spike.Lib.Ret0Src.ret0Src).get!

#guard (frames1 cfgX64 Spike.Lib.Ret0Src.ret0Src).isSome
#guard (frames1 cfgA64 Spike.Lib.Ret0Src.ret0Src).isSome

/-- The two stages at `ret0`, each a kernel check. -/
theorem framesX64 : frames1 cfgX64 Spike.Lib.Ret0Src.ret0Src = some frX64 := by decide +kernel
theorem framesA64 : frames1 cfgA64 Spike.Lib.Ret0Src.ret0Src = some frA64 := by decide +kernel

/-- **The glue at `ret0`** (x64): `lowerIR`'s IR and setup flag from the
stages. -/
theorem lowerIR_ret0_x64 :
    (match Scc.Lower.lowerIR cfgX64 Spike.Lib.Ret0Src.ret0Src with
      | .ok l => some (l.ir, l.checked.entry.arg == .setupTid)
      | .error _ => none) = ir1 cfgX64 Spike.Lib.Ret0Src.ret0Src := by
  cases h : ir1 cfgX64 Spike.Lib.Ret0Src.ret0Src with
  | none =>
    have : (ir1 cfgX64 Spike.Lib.Ret0Src.ret0Src).isSome = true := by decide +kernel
    simp [h] at this
  | some r => exact lowerIR_of_stages framesX64 h

/-- **The glue at `ret0`** (AArch64). -/
theorem lowerIR_ret0_a64 :
    (match Scc.Lower.lowerIR cfgA64 Spike.Lib.Ret0Src.ret0Src with
      | .ok l => some (l.ir, l.checked.entry.arg == .setupTid)
      | .error _ => none) = ir1 cfgA64 Spike.Lib.Ret0Src.ret0Src := by
  cases h : ir1 cfgA64 Spike.Lib.Ret0Src.ret0Src with
  | none =>
    have : (ir1 cfgA64 Spike.Lib.Ret0Src.ret0Src).isSome = true := by decide +kernel
    simp [h] at this
  | some r => exact lowerIR_of_stages framesA64 h

-- `ret0` has no setup block, and the depth limit is positive.
#guard ((ir1 cfgX64 Spike.Lib.Ret0Src.ret0Src).map (·.2)) == some false
#guard 0 < frX64 && 0 < frA64

/-- info: 'Scc.Test.LowerStage.lowerIR_ret0_x64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lowerIR_ret0_x64

end Scc.Test.LowerStage
