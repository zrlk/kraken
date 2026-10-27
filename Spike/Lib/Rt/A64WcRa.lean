/-
**A return-address slot's value** (AArch64): the cell at offset `-8` of a
region holds the return address `pc` (the 64-bit cell read as a signed
integer, its bits the address). A function's write tail (a predicate on
states closed under the certification steps, `Spike/Lib/TailDt.lean`) runs
on through the function's `ret`, so it must know where the `ret` goes; the
callee's facts at its entry give it as this cell's value in the callee's
region.

- `WcRa R pc m`: `Mem.loadInt m.dmem (R.addr (-8)) 8` is some `j` with
  `Int64.ofBitVec (BitVec.ofInt 64 j) = pc`.
-/
import Spike.Lib.Region
import Kraken.AArch64.Semantics

namespace Spike.Lib.A64.Rt

open Kraken

/-- The cell at offset `-8` of `R` holds the return address `pc`. -/
def WcRa (R : Region) (pc : Int64) (m : MachineData) : Prop :=
  ∃ j, Mem.loadInt m.dmem (R.addr (-8)) 8 = some j ∧ Int64.ofBitVec (BitVec.ofInt 64 j) = pc

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.A64.Rt.WcRa' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms WcRa

end Spike.Lib.A64.Rt
