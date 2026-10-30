/-
**No word at a stack range's first address** (AArch64): the word-level
counterpart of `Unowned` (no byte of the range in the private memory).
A take site's caller needs only this to refute that the range is already
owned (`HeldOk2`'s held list, via `WakePz.pz_not_stackM`). Unlike `Unowned`, it
is a fact of the machine data's word loads, so frame stability keeps it.

- `Pz r m`: the 8-byte load at `r.lo` fails in `m.dmem`.
- `pz_of_unowned`: `Unowned r` gives `Pz r` (a nonempty range).
- `owned_not_pz`: an owned range holding an aligned word has a word at
  `r.lo`, so it is not `Pz`.
-/
import Spike.Lib.A64OwnedMono

namespace Spike.Lib.A64Consumer

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64

/-- **No word at the range's first address.** -/
def Pz (r : Range) (m : MachineData) : Prop := Mem.loadInt m.dmem (BitVec.ofNat 64 r.lo) 8 = none

/-- **`Unowned r` gives `Pz r`**: `r`'s first byte is not in `dmem`. -/
theorem pz_of_unowned {r : Range} {s : State} (hr : 0 < r.size) (h : Unowned r s) : Pz r s.st.1 := by
  have h0 : s.st.1.dmem[BitVec.ofNat 64 r.lo]? = none :=
    Std.ExtHashMap.getElem?_eq_none (h r.lo ⟨Nat.le_refl _, by omega⟩)
  simp [Pz, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ_eq_map, h0]

/-- **An owned range holding an aligned word is not `Pz`.** -/
theorem owned_not_pz {Λ : Scc.Sem.Layout} {r : Range} {s : State} (ho : Owned Λ r s) (hz : Pz r s.st.1)
    (hal : r.lo % 8 = 0) (hsz : 8 ≤ r.size) : False := by
  have h := ho.2 r.lo hal ⟨Nat.le_refl _, by omega⟩ ⟨by omega, by omega⟩
  simp only [privLoad, Option.isSome_map] at h
  rw [show Mem.loadInt s.st.1.dmem (BitVec.ofNat 64 r.lo) 8 = none from hz] at h
  cases h

end Spike.Lib.A64Consumer

/-- info: 'Spike.Lib.A64Consumer.pz_of_unowned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64Consumer.pz_of_unowned

/-- info: 'Spike.Lib.A64Consumer.owned_not_pz' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64Consumer.owned_not_pz
