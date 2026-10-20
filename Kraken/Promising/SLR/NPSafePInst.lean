/-
**Prototype.** Option (S) against `K2OK`, for the
SLR model.

Option (S) restricts `NPSafe`'s K2 to resources whose
acquire ids were all allocated before the step (`AllocIds g₁ ρ`). Condition
(3), K2's only consumer, feeds K2 only resources `rF i` of existing threads
of an erased configuration (`K2OK`); `Erase.acqIds` says every id held by the
total resource, hence by `rF i`, is allocated. So the restricted frame
satisfies `K2OK` (`k2OK_allocIds`), and the generic chain (Theorem 1′ for
`NPSafeP G K` under `GuardOK G`, `K2OK K`) applies to it.

Nothing imports this file.
-/
import Kraken.Promising.SLR.NPSafeP
import Kraken.Promising.SLR.Rmw

namespace Kraken.Promising.SLR

variable {I : ISA}

/-- Every acquire id `ρ` holds is allocated in `g` (option (S)'s scope). -/
def AllocIds (g : Ghost) (ρ : Res) : Prop := ∀ x ι, 1 ≤ ρ.acq x ι → ι < g.acqTab.length

/-- A thread of an erased configuration holds only allocated acquire ids. -/
theorem Erase.allocIds_thread {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I}
    (E : Erase rF g T c) {i : Nat} (hi : i < c.threads.size) : AllocIds g (rF i) := by
  intro x ι h
  obtain ⟨rest, hrest⟩ := threadsRes_split rF hi
  refine E.acqIds x ι ?_
  show 1 ≤ ((threadsRes rF c.threads.size).op g.slotsRes).acq x ι
  rw [hrest rF fun _ _ => rfl]
  show 1 ≤ (rF i).acq x ι + rest.acq x ι + g.slotsRes.acq x ι
  omega

/-- **Option (S)'s frame satisfies `K2OK`.** -/
theorem k2OK_allocIds : K2OK (model I) (K2Scope (model I) AllocIds) :=
  fun rF _ _ _ _ i _ E hi hK b hb x h => hK b hb (rF i) (Erase.allocIds_thread E hi) x h

/-- Every existing rule proof gives option (S)'s `NPSafeP` (K2 is only
weakened). -/
theorem NPSafe.toAllocIds {A : Arch} {B : Config I → Res → Ghost → Prop} {tid n m : Nat} {cl : Prop}
    {c : Config I} {r : Res} {g : Ghost} (h : NPSafe (model I) A B tid n m cl c r g) :
    NPSafeP (model I) A B tid G₀ (K2Scope (model I) AllocIds) n m cl c r g :=
  NPSafe.toP (fun _ _ _ _ _ h => h) (fun _ _ _ h => K2₀.toScope _ h) h

#print axioms k2OK_allocIds
#print axioms NPSafe.toAllocIds

end Kraken.Promising.SLR
