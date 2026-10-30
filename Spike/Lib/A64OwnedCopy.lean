/-
**Ownership across a take** (AArch64): the state after the take of a range
`r` (`abi.skip (abi.setDmem s (Kernel.copyRange pm (abi.dmem s) r))`, as
`TakePathS.site` and `HeldPathS.held` name it) maps exactly `r`'s bytes
beside the private memory's (`OwnDom.mem_copyRange`).

- `dom_take`: the domain after the take.
- `owned_take_self`: the taken range is owned after it (in the pool).
- `owned_take_keep`: a range owned before stays owned.
- `unowned_take_keep`: a range unmapped before and off `r` stays unmapped.
- `heldOk2_take0`, `heldOk2_take1`: the two takes of `HeldOk2` from these.
-/
import Spike.Lib.A64HeldOk2

namespace Spike.Lib.A64Consumer

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64

/-- **The state after the take** of `r` from pool image `pm`. -/
abbrev afterTake (s : State) (pm : _root_.Mem 64) (r : Range) : State :=
  abi.skip (abi.setDmem s (Kernel.copyRange pm (abi.dmem s) r))

/-- **The domain after the take**: `r`'s addresses and the private memory's. -/
theorem dom_take (s : State) (pm : _root_.Mem 64) (r : Range) (a : BitVec 64) :
    a ∈ (afterTake s pm r).st.1.dmem ↔ a ∈ Kernel.addrs r ∨ a ∈ s.st.1.dmem := by
  show a ∈ Kernel.copyRange pm s.st.1.dmem r ↔ _
  exact Kernel.mem_copyRange _ _ _ _

/-- An 8-byte private load succeeds iff its eight bytes are mapped. -/
theorem privLoad_isSome_iff (s : State) (a : BitVec 64) :
    (privLoad s a).isSome = true ↔ ∀ i, i < 8 → a + BitVec.ofNat 64 i ∈ s.st.1.dmem := by
  simp [privLoad, Mem.loadInt, Option.isSome_map, Mem.loadBytes, List.allSome_isSome_iff]

/-- **The taken range is owned after the take**, given it in the pool. -/
theorem owned_take_self {Λ : Scc.Sem.Layout} {r : Range} (hsub : r.Sub Λ.stackPool) (s : State)
    (pm : _root_.Mem 64) : Owned Λ r (afterTake s pm r) := by
  refine ⟨hsub, fun a _ ha ha7 => ?_⟩
  rw [privLoad_isSome_iff]
  intro i hi
  rw [dom_take]
  left
  unfold Kernel.addrs
  unfold Range.contains at ha ha7
  refine List.mem_map.mpr ⟨a + i - r.lo, List.mem_range.mpr (by omega), ?_⟩
  rw [show r.lo + (a + i - r.lo) = a + i by omega, BitVec.ofNat_add]

/-- **A range owned before the take stays owned.** -/
theorem owned_take_keep {Λ : Scc.Sem.Layout} {r0 : Range} {s : State} (h : Owned Λ r0 s)
    (pm : _root_.Mem 64) (r : Range) : Owned Λ r0 (afterTake s pm r) := by
  refine ⟨h.1, fun a h8 ha ha7 => ?_⟩
  have := h.2 a h8 ha ha7
  rw [privLoad_isSome_iff] at this ⊢
  exact fun i hi => (dom_take s pm r _).mpr (.inr (this i hi))

/-- **A range unmapped before the take and off the taken range stays
unmapped**, neither range wrapping. -/
theorem unowned_take_keep {r1 r : Range} {s : State} (h : Unowned r1 s) (hd : r1.Disjoint r)
    (h1 : r1.lo + r1.size ≤ 2 ^ 64) (hr : r.lo + r.size ≤ 2 ^ 64) (pm : _root_.Mem 64) :
    Unowned r1 (afterTake s pm r) := by
  intro a ha
  rw [dom_take, not_or]
  refine ⟨fun hm => ?_, h a ha⟩
  rw [Kernel.mem_addrs_iff hr] at hm
  unfold Range.contains at ha hm
  unfold Range.Disjoint at hd
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hm
  omega

/-- **`HeldOk2`'s first take** of `r0`, from none held: `r0` owned after
it, `r1` unmapped (off `r0`). -/
theorem heldOk2_take0 {Λ : Scc.Sem.Layout} {r0 r1 : Range} {s : State} (h : HeldOk2 Λ r0 r1 s [])
    (hsub : r0.Sub Λ.stackPool) (hd : r1.Disjoint r0) (h1 : r1.lo + r1.size ≤ 2 ^ 64)
    (h0 : r0.lo + r0.size ≤ 2 ^ 64) (pm : _root_.Mem 64) :
    HeldOk2 Λ r0 r1 (afterTake s pm r0) [(0, r0)] := by
  rcases h with ⟨-, -, hu1⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact HeldOk2.take0 (owned_take_self hsub s pm) (unowned_take_keep hu1 hd h1 h0 pm)
  · cases h
  · cases h

/-- **`HeldOk2`'s second take** of `r1`, from `r0` held: both owned
after it. -/
theorem heldOk2_take1 {Λ : Scc.Sem.Layout} {r0 r1 : Range} {s : State} (h : HeldOk2 Λ r0 r1 s [(0, r0)])
    (hsub : r1.Sub Λ.stackPool) (pm : _root_.Mem 64) :
    HeldOk2 Λ r0 r1 (afterTake s pm r1) [(0, r1), (0, r0)] := by
  rcases h with ⟨h, -⟩ | ⟨-, ho0, -⟩ | ⟨h, -⟩
  · cases h
  · exact HeldOk2.take1 (owned_take_keep ho0 pm r1) (owned_take_self hsub s pm)
  · cases h

/-- info: 'Spike.Lib.A64Consumer.heldOk2_take0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64Consumer.heldOk2_take0

/-- info: 'Spike.Lib.A64Consumer.heldOk2_take1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64Consumer.heldOk2_take1

end Spike.Lib.A64Consumer
