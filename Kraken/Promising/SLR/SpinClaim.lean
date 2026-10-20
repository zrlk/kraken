/-
What an RMW on the spinlock's lock word acquires (ISA-neutral; shared by the
AArch64 `swpa` and the x64 `xchgl` cells).

An RMW reading the message `(x, tr)` claims its update slots
(`claimedSlots`, `SLR/Rmw.lean`). From erasure:

- `Erase.claimedSlots_nil`: a message not in release mode has no slots;
- `Erase.claimedSlot`: an unclaimed release-mode message has, for every
  update id `ι` of `x`, a slot with id `ι` among the claimed ones, satisfying
  `acqPred ι` at the message's value and timestamp, and the claimed
  resources split off that slot's;
- `Erase.valid_claim`: the thread's resource together with the claimed
  slots is valid (both are parts of the erasure's total);
- `SpinCommon.World.lock_claim`: for the spinlock (`World`), reading `0`
  from an unclaimed message, the claimed resources contain a part
  satisfying `Good` (at the message's timestamp) or `Bad`; reading a
  non-release message at `0` is impossible (`lockPred` is not pure at `0`).
-/
import Kraken.Promising.SLR.SpinCommon

namespace Kraken.Promising.SLR

variable {I : ISA}

section Claim

variable {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I}

/-- The slots split into the claimed ones (of `(x, tr)`) and the rest. -/
theorem slotsRes_claimed (g : Ghost) (x : Loc) (tr : Time) :
    g.slotsRes = (Res.prod ((claimedSlots g x tr).map (·.res))).op
      (Res.prod ((g.u.filter fun s => !updSlot g (x, tr) s).map (·.res))) := by
  unfold Ghost.slotsRes claimedSlots
  rw [← Res.prod_append, ← List.map_append]
  exact Res.prod_perm ((List.filter_append_perm _ _).map _).symm

/-- A message not in release mode has no slots, so an RMW reading it claims
none. -/
theorem Erase.claimedSlots_nil (E : Erase rF g T c) {x : Loc} {tr : Time} (h : (x, tr) ∉ g.relMsgs) :
    claimedSlots g x tr = [] := by
  unfold claimedSlots
  refine List.filter_eq_nil_iff.mpr fun s hs hu => ?_
  simp only [updSlot, decide_eq_true_eq] at hu
  exact h ((E.slotsDom (x, tr) s.id).mp ⟨s, hs, hu.1, rfl⟩).1

/-- **The update slot of an unclaimed release message**: for an update id `ι`
of `x`, the claimed slots of `(x, tr)` contain one with id `ι`, satisfying
`acqPred ι` at the message, and the claimed resources split off its
resource. -/
theorem Erase.claimedSlot (E : Erase rF g T c) {x : Loc} {tr : Time} {v : Val} {ι : PredId}
    (hrel : (x, tr) ∈ g.relMsgs) (hun : ¬ g.Claimed (x, tr)) (hι : ι ∈ g.upd x)
    (hrd : c.mem.read? x tr = some v) :
    ∃ s : Slot, ∃ R : Res, s.id = ι ∧ (g.acqPred ι).P v c.mem tr s.res ∧
      Res.prod ((claimedSlots g x tr).map (·.res)) = s.res.op R := by
  obtain ⟨s, hs, hk, hid⟩ := (E.slotsDom (x, tr) ι).mpr ⟨hrel, .inr ⟨hι, hun⟩⟩
  have hmem : s ∈ claimedSlots g x tr := by
    unfold claimedSlots
    refine List.mem_filter.mpr ⟨hs, ?_⟩
    simp only [updSlot, decide_eq_true_eq]
    exact ⟨hk, hid ▸ hι⟩
  obtain ⟨as, bs, hab⟩ := List.append_of_mem hmem
  refine ⟨s, Res.prod ((as ++ bs).map (·.res)), hid, ?_, ?_⟩
  · have := E.slotsPred s hs v (by rw [hk]; exact hrd)
    rw [hk, hid] at this
    exact this
  · rw [hab, Res.prod_perm (List.perm_middle.map _)]
    rfl

/-- The thread's resource with the claimed slots is valid: both are parts of
the erasure's total. -/
theorem Erase.valid_claim {tid : Nat} {r : Res} (E : Erase (setRes rF tid r) g T c)
    (htid : tid < c.threads.size) (x : Loc) (tr : Time) :
    (r.op (Res.prod ((claimedSlots g x tr).map (·.res)))).valid := by
  have hv := E.valid
  obtain ⟨rest, hrest⟩ := threadsRes_split rF htid
  unfold total at hv
  rw [hrest (setRes rF tid r) (fun i hi => by simp [setRes, hi]), setRes_self, slotsRes_claimed g x tr] at hv
  rw [Res.op_assoc, Res.op_left_comm rest, ← Res.op_assoc] at hv
  exact Res.valid_op_left hv

end Claim

namespace SpinCommon

open Spinlock

/-- `lockPred` is not pure at the unlocked value `0`: the empty resource holds
no part of the counter. -/
theorem lockPred_not_pure_zero {P : Sys} : ¬ Pred.Pure P.φ 0 := by
  intro h
  have := h ({ init := [], msgs := #[] } : Memory) 0 rfl
  rcases this with ⟨_, _, _, ⟨hC, _⟩, _⟩ | ⟨_, _, hC, _⟩ <;>
    simp [Res.unit, Perm.unit] at hC

/-- **What an RMW reading `0` from the lock acquires**: the claimed slots of
the (unclaimed) message read contain a part `R` satisfying `Good` at the
message's timestamp or `Bad`. -/
theorem World.lock_claim {P : Sys} {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I}
    (hW : World P g) (E : Erase rF g T c) {tr : Time} (hrd : c.mem.read? P.Lk tr = some 0)
    (hun : ¬ g.Claimed (P.Lk, tr)) :
    ∃ R R' : Res, Res.prod ((claimedSlots g P.Lk tr).map (·.res)) = R.op R' ∧
      (Good P.N P.C P.K P.F tr R ∨ Bad P.N P.Lk P.C P.K P.F R) := by
  obtain ⟨hL, -, ι, hι, -, hφ⟩ := hW
  by_cases hrel : (P.Lk, tr) ∈ g.relMsgs
  · obtain ⟨s, R', -, hP, hprod⟩ := E.claimedSlot hrel hun hι hrd
    rw [hφ] at hP
    exact ⟨s.res, R', hprod, hP rfl⟩
  · have := E.pure P.Lk tr 0 hrd hrel
    rw [hL] at this
    exact absurd this lockPred_not_pure_zero

end SpinCommon

end Kraken.Promising.SLR
