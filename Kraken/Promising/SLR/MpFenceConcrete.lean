/-
`MpFence.mp_fence` at a concrete instance (as `SLR/MpConcrete.lean` for
`mp_public`): the fence-released writer `fwriterMp` laid out at `0x100000`,
the MP reader at `0x200000`, the flag at `0x1000`, the data at `0x1100`, both
initially `0`; every hypothesis discharged. The explorer on the same initial
configuration finds only the final `(W4, data) = (1, 1)`.
-/
import Kraken.Promising.SLR.MpFence
import Kraken.Promising.SLR.MpConcrete

namespace Kraken.Promising.SLR.MpFenceConcrete

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.MpTrees
open Kraken.Promising.SLR.Mp
open Kraken.Promising.SLR.FenceW
open Kraken.Promising.SLR.MpFence
open Kraken.Promising.SLR.MpConcrete (rLayout flagAddr dataAddr Pmp initMemMp reader0)

/-- The writer's layout: text at `0x100000`, each directive its `fakeSize`. -/
@[reducible] def fLayout : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize fwriterMp

theorem fLayout_cells : ((fLayout fwriterMp).2.map (·.2)) = [4, 4, 4, 4, 4, 0] := by decide

instance fValid : Executable.ValidLayout (fLayout fwriterMp) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-- The writer's initial state: `X0 = flag`, `X1 = data`, at `0x100000`,
halting at the end of its text (`0x100000 + 20`). -/
def fwriter0 : State where
  exe := fLayout fwriterMp
  endPc := 0x100000 + 20
  st := ({ regs := { X0 := 0x1000, X1 := 0x1100 } }, 0x100000)

section
attribute [local instance] fLayout

theorem fwriter0_start : StartF flagAddr dataAddr fwriter0 := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, ?_, ?_⟩ <;>
    simp [fwriter0, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ, flagAddr, dataAddr]

end

/-- **Message passing with a fence-released writer**, concrete instance:
every reachable final configuration has the reader's `W4` at `1` and the data
word at `1`. -/
theorem mp_fence_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [fwriter0, reader0] initMemMp) c) (hf : c.final = true) :
    (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 1) ∧
      c.mem.finalVal Pmp.Dt = 1#128 :=
  mp_fence fLayout rLayout flagAddr dataAddr (by decide) fwriter0_start MpPublic.reader0_start (by decide) hc hf

/-- The explorer on the theorem's initial configuration: the final
`(W4 of the reader, data)` pairs. -/
def exploreFinalsF : List (Nat × Nat) × Bool :=
  let r := explore Arch.armv8 (Config.init [fwriter0, reader0] initMemMp : Config isa)
    (fun c => ((c.threads[1]?.map fun t => (BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec).toNat).getD 0,
      (c.mem.finalVal Pmp.Dt).toNat)) { fuel := 64 }
  (r.finals, r.boundHit || !r.faults.isEmpty)

/-- info: ([(1, 1)], false) -/
#guard_msgs in
#eval exploreFinalsF

end Kraken.Promising.SLR.MpFenceConcrete

#print axioms Kraken.Promising.SLR.MpFenceConcrete.mp_fence_concrete
