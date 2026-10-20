/-
Part 14: **concrete instance of
`Treiber2.treiber2_envG`** (non-vacuity of its start hypotheses), as
`EnvG/ConcreteTreiber2.lean` for `treiber2.kl`: the data worker at
`0x100000` (thread `0`) and `0x200000` (thread `1`), `top` at `0x1000`, the
nodes `n1` at `0x1100` and `n2` at `0x1200`; thread `i` starts with
`X0 = top`, `X1 = n(i+1)`, `X9 = i + 1`. No `native_decide`. `codeMatches`:
the `.kl`'s `code` block parses to the `worker` label, then
`treiber2DWorker`.
-/
import Kraken.Promising.SLR.EnvG.Treiber2DataPublic
import Kraken.Promising.SLR.EnvG.ConcreteTreiber2

namespace Kraken.Promising.SLR.EnvG.ConcreteTreiber2Data

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.EnvG.Treiber2
open Kraken.Promising.SLR.EnvG.ConcreteTreiber2 (topAddr n1Addr n2Addr)

/-! ## The layouts -/

/-- Thread `0`'s layout: text at `0x100000`, each directive its `fakeSize`. -/
@[reducible] def layout0 : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize treiber2DWorker

/-- Thread `1`'s layout: text at `0x200000`, each directive its `fakeSize`. -/
@[reducible] def layout1 : _root_.Layout := Kraken.Layout.ofSize 0x200000 Directive.fakeSize treiber2DWorker

instance valid0 : Executable.ValidLayout (layout0 treiber2DWorker) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

instance valid1 : Executable.ValidLayout (layout1 treiber2DWorker) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-! ## The initial configuration -/

/-- Thread `0`'s initial state: `X0 = top`, `X1 = n1`, `X9 = 1`, at
`worker`, halting at `done`; no declarations, empty private memory. -/
def worker0 : AArch64.State where
  exe := layout0 treiber2DWorker
  endPc := 0x100000 + 68
  st := ({ regs := { X0 := 0x1000, X1 := 0x1100, X9 := 1 } }, 0x100000)

/-- Thread `1`'s initial state: `X0 = top`, `X1 = n2`, `X9 = 2`. -/
def worker1 : AArch64.State where
  exe := layout1 treiber2DWorker
  endPc := 0x200000 + 68
  st := ({ regs := { X0 := 0x1000, X1 := 0x1200, X9 := 2 } }, 0x200000)

/-- The initial memory: `top = 0`, the nodes' data words and links `0`. -/
def treiber2InitMem : List (Loc × Val) :=
  [(⟨topAddr, 8⟩, 0), (⟨n1Addr, 4⟩, 0), (⟨n1Addr + 8, 8⟩, 0), (⟨n2Addr, 4⟩, 0), (⟨n2Addr + 8, 8⟩, 0)]

section
attribute [local instance] layout0

theorem worker0_start : StartWD topAddr n1Addr 1 worker0 := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, by decide, fun a => ?_, fun a => ?_⟩ <;>
    simp [worker0, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

end

section
attribute [local instance] layout1

theorem worker1_start : StartWD topAddr n2Addr 2 worker1 := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, by decide, fun a => ?_, fun a => ?_⟩ <;>
    simp [worker1, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

end

/-! ## The `.kl` file runs these threads -/

/-- The `.kl` source. -/
def treiber2Kl : String := include_str "../../../Examples/LockFree/AArch64/treiber2.kl"

/-- The `code` block of the `.kl` parses to the `worker` label, then
`treiber2DWorker` without its own `worker` label. -/
def codeMatches (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.AArch64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => prog == treiber2DWorker
    | .error _ => false

/-- info: true -/
#guard_msgs in
#eval codeMatches treiber2Kl

/-! ## The instance -/

/-- **`(0:X10=n1 ∧ 0:X11=1 ∧ 1:X10=n2 ∧ 1:X11=2) ∨
(0:X10=n2 ∧ 0:X11=2 ∧ 1:X10=n1 ∧ 1:X11=1)`** for `treiber2.kl` under
`Arch.armv8`, concrete instance of `treiber2_envG`. -/
theorem treiber2_envG_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [worker0, worker1] treiber2InitMem) c)
    (hf : c.final = true) : Treiber2DFinal n1Addr n2Addr c :=
  treiber2_envG layout0 layout1 topAddr n1Addr n2Addr (by decide) (by decide) (by decide) (by decide)
    (by decide) worker0_start worker1_start (by simp only [Config.init]; decide) hc hf

end Kraken.Promising.SLR.EnvG.ConcreteTreiber2Data

#print axioms Kraken.Promising.SLR.EnvG.ConcreteTreiber2Data.treiber2_envG_concrete
