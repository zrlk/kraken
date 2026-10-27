/-
**A return-address slot's value** (x86-64): the cell at offset `0` of a
region holds the return address `pc` (the 64-bit cell read as a signed
integer, its bits the address). A function's write tail (a predicate on
states closed under the certification steps, `Spike/Lib/TailDt.lean`) runs
on through the function's `ret`, so it must know where the `ret` goes; the
callee's facts at its entry give it as this cell's value in the callee's
region. The twin of `Spike.Lib.Rt.A64WcRa`; on x86-64 `call` pushes the
return address at the callee's offset `0` (its CFA minus 8), not `-8`.

- `WcRa R pc m`: `Mem.loadInt m.dmem (R.addr 0) 8` is some `j` with
  `Int64.ofBitVec (BitVec.ofInt 64 j) = pc`.
- `WcFp R fp m`: the saved frame pointer's cell, offset `-8`, holds `fp`
  (`popq %rbp` before the `ret` restores it, and the caller's code after the
  return addresses its frame by it).
-/
import Spike.Lib.Region
import Kraken.X64.Semantics

namespace Spike.Lib.X64.Rt

open Kraken

/-- The cell at offset `0` of `R` holds the return address `pc`. -/
def WcRa (R : Region) (pc : Int64) (m : MachineData) : Prop :=
  ∃ j, Mem.loadInt m.dmem (R.addr 0) 8 = some j ∧ Int64.ofBitVec (BitVec.ofInt 64 j) = pc

/-- The cell at offset `-8` of `R` holds the saved frame pointer `fp`. -/
def WcFp (R : Region) (fp : BitVec 64) (m : MachineData) : Prop :=
  ∃ j, Mem.loadInt m.dmem (R.addr (-8)) 8 = some j ∧ BitVec.ofInt 64 j = fp

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.X64.Rt.WcRa' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms WcRa

/--
info: 'Spike.Lib.X64.Rt.WcFp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms WcFp

end Spike.Lib.X64.Rt
