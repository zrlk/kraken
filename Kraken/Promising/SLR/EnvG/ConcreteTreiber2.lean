/-
Part 9: **concrete instance of
`Treiber2.treiber2_nodes_envG`** (non-vacuity of its start hypotheses). The
worker laid out at `0x100000` for thread `0` and at `0x200000` for thread
`1` (each directive its `fakeSize`, as the `.kl` runner lays out text), `top`
at `0x1000` (8 bytes, initially `0`), the nodes `n1` at `0x1100` and `n2` at
`0x1200`; thread `i` starts the worker with `X0 = top`, `X1 = n(i+1)`. Every
hypothesis is discharged by `decide`, `rfl` or `simp` (no `native_decide`).
`codeMatches`: the `.kl`'s `code` block parses to the `worker` label, then
`treiber2Worker`.
-/
import Kraken.Promising.SLR.EnvG.Treiber2Public
import Kraken.AArch64.WP.LayoutOfSize
import Kraken.Litmus.AArch64

namespace Kraken.Promising.SLR.EnvG.ConcreteTreiber2

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.EnvG.Treiber2

/-! ## The layouts -/

/-- Thread `0`'s layout: text at `0x100000`, each directive its `fakeSize`. -/
@[reducible] def layout0 : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize treiber2Worker

/-- Thread `1`'s layout: text at `0x200000`, each directive its `fakeSize`. -/
@[reducible] def layout1 : _root_.Layout := Kraken.Layout.ofSize 0x200000 Directive.fakeSize treiber2Worker

instance valid0 : Executable.ValidLayout (layout0 treiber2Worker) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

instance valid1 : Executable.ValidLayout (layout1 treiber2Worker) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-! ## The parameters and the initial configuration -/

/-- `top`'s address. -/
def topAddr : BitVec 64 := 0x1000
/-- The first node's address (`n1` of the `.kl`, thread `0`'s). -/
def n1Addr : BitVec 64 := 0x1100
/-- The second node's address (`n2` of the `.kl`, thread `1`'s). -/
def n2Addr : BitVec 64 := 0x1200

/-- Thread `0`'s initial state: `X0 = top`, `X1 = n1`, at `push`, halting at
`done` (the end of its text); no declarations, empty private memory. -/
def worker0 : AArch64.State where
  exe := layout0 treiber2Worker
  endPc := 0x100000 + 60
  st := ({ regs := { X0 := 0x1000, X1 := 0x1100 } }, 0x100000)

/-- Thread `1`'s initial state: `X0 = top`, `X1 = n2`. -/
def worker1 : AArch64.State where
  exe := layout1 treiber2Worker
  endPc := 0x200000 + 60
  st := ({ regs := { X0 := 0x1000, X1 := 0x1200 } }, 0x200000)

/-- The initial memory: `top = 0`, the nodes' links `0`. -/
def treiber2InitMem : List (Loc × Val) := [(⟨topAddr, 8⟩, 0), (⟨n1Addr + 8, 8⟩, 0), (⟨n2Addr + 8, 8⟩, 0)]

section
attribute [local instance] layout0

theorem worker0_start : StartW topAddr n1Addr worker0 := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, fun a => ?_⟩
  simp [worker0, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

end

section
attribute [local instance] layout1

theorem worker1_start : StartW topAddr n2Addr worker1 := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, fun a => ?_⟩
  simp [worker1, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

end

/-! ## The `.kl` file runs these threads -/

/-- The `.kl` source. -/
def treiber2NodesKl : String := include_str "../../../Examples/LockFree/AArch64/treiber2_nodes.kl"

/-- The `code` block of the `.kl` parses to the `worker` label, then
`treiber2Worker`. -/
def codeMatches (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.AArch64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => prog.drop 1 == treiber2Worker && prog.length == treiber2Worker.length + 1
    | .error _ => false

/-- info: true -/
#guard_msgs in
#eval codeMatches treiber2NodesKl

/-! ## The instance -/

/-- **`(0:X10 = n1 ∧ 1:X10 = n2) ∨ (0:X10 = n2 ∧ 1:X10 = n1)`** for
`treiber2_nodes.kl` under `Arch.armv8`, concrete instance of
`treiber2_nodes_envG`. -/
theorem treiber2_nodes_envG_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [worker0, worker1] treiber2InitMem) c)
    (hf : c.final = true) :
    ∃ th0 th1, c.threads[0]? = some th0 ∧ c.threads[1]? = some th1 ∧
      ((th0.st.st.1.regs.X10.toBitVec = n1Addr ∧ th1.st.st.1.regs.X10.toBitVec = n2Addr) ∨
        (th0.st.st.1.regs.X10.toBitVec = n2Addr ∧ th1.st.st.1.regs.X10.toBitVec = n1Addr)) :=
  treiber2_nodes_envG layout0 layout1 topAddr n1Addr n2Addr (by decide) (by decide) (by decide) (by decide)
    (by decide) worker0_start worker1_start (by simp only [Config.init]; decide) hc hf

end Kraken.Promising.SLR.EnvG.ConcreteTreiber2

#print axioms Kraken.Promising.SLR.EnvG.ConcreteTreiber2.treiber2_nodes_envG_concrete
