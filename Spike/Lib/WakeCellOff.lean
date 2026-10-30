/-
**A cell in a layout region other than the stack pool is never private**
(AArch64): along every run the private memory of thread `tid` maps exactly
its initial stack and the stack ranges it holds (`Kernel.OwnDom`), the
initial stack is clear of the layout's regions (`Entry.clear`) and the held
ranges lie in the stack pool; so an 8-byte cell of a region disjoint from
the pool (the heap, `.data`, the pinned region) is clear of the pool and
unmapped in every thread's private memory. wake.w's flag cell is one.

- `cell_off`: the cell clear of the pool and unmapped in the thread's
  private memory.
-/
import Scc.Sem.OwnDom
import Spike.Lib.Rt.A64Layout

namespace Spike.Lib.WakeCellOff

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel

/-- **A cell of a region disjoint from the pool is off every thread's private
memory**: under `OwnDom` at the entry's initial stack, at a configuration
whose pool is the layout's, the cell's 8 bytes in a region `Rc` of the
layout disjoint from the pool. -/
theorem cell_off {E : Entry} {Λ : Scc.Sem.Layout} {P : State → Prop} {c : Config isaLSE2 × KState}
    (hD : OwnDom abi (initDom E) P c) (hpool : c.2.pool = Λ.stackPool) (hE : E.clear Λ = true)
    {Rc : Range} (hRc : Rc ∈ Λ.regions) (hdisj : Rc.Disjoint Λ.stackPool) {cA : Nat}
    (hc : Rc.lo ≤ cA ∧ cA + 8 ≤ Rc.lo + Rc.size) (hfit : cA + 8 ≤ 2 ^ 64) {tid : Nat} {th : Thread isaLSE2}
    (hth : c.1.threads[tid]? = some th) :
    Mem.loadInt th.st.st.1.dmem (BitVec.ofNat 64 cA) 8 = none ∧
      Spike.Lib.A64.Rt.Clear Λ.stackPool (BitVec.ofNat 64 cA) := by
  have hEs := (Entry.clear_disjoint hE).2 Rc hRc
  have hcA : (BitVec.ofNat 64 cA).toNat = cA := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold Range.Disjoint at hEs hdisj
  refine ⟨?_, ?_⟩
  · have hni : BitVec.ofNat 64 cA ∉ th.st.st.1.dmem := by
      intro hm
      have hm' : BitVec.ofNat 64 cA ∈ abi.dmem th.st := hm
      rcases (hD.dom tid th hth _).mp hm' with ⟨-, hs⟩ | ⟨r, hr, hrc⟩
      · unfold Range.contains at hs; rw [hcA] at hs; omega
      · obtain ⟨-, hsub, -⟩ := hD.held_ok _ hr
        rw [hpool] at hsub
        simp only [Range.contains, Range.Sub, hcA] at hrc hsub; omega
    have hne : Std.ExtHashMap.get? th.st.st.1.dmem (BitVec.ofNat 64 cA + BitVec.ofNat 64 0) = none := by
      simpa [Std.ExtHashMap.get?_eq_getElem?] using hni
    unfold Mem.loadInt Mem.loadBytes
    rw [show List.range 8 = 0 :: List.range' 1 7 from rfl, List.map_cons, hne]
    simp [List.allSome]
  · unfold Spike.Lib.A64.Rt.Clear; rw [hcA]; omega

/-- info: 'Spike.Lib.WakeCellOff.cell_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeCellOff.cell_off

end Spike.Lib.WakeCellOff
