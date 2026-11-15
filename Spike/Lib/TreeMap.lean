/-
**Tree predicates under a map of the leaves** (ISA-neutral; for the
post-pass transfer, which relabels every leaf of an instruction's tree):
the predicates the node obligations ask of an instruction's tree hold of the
mapped tree when they hold of the tree, the leaf predicates read through
the map.

- `touches_map`: `Kernel.Touches` reads only the events;
- `writeTree_map`: `WriteTree` likewise;
- `ownTree_map`: `OwnTree` with the owned words read through the map;
- `leaves_and_allInv`: `Leaves Q` and `AllInv … P` give `AllInv … (P ∧ Q)`.
-/
import Spike.Lib.RestTail
import Spike.Lib.Consumer1

namespace Spike.Lib.TreeMap

open Kraken.Promising
open Spike.Lib.RestTail (Leaves)

variable {σ τ : Type}

/-- `Touches` reads only the events: it holds of a mapped tree iff of the tree. -/
theorem touches_map (f : σ → τ) {p : Loc → Bool → Prop} :
    ∀ t : EvTree σ, Scc.Sem.Kernel.Touches p (t.map f) ↔ Scc.Sem.Kernel.Touches p t
  | .done _ => ⟨nofun, nofun⟩
  | .fault _ => ⟨nofun, nofun⟩
  | .choose _ k => ⟨fun h => by cases h with | choose i h => exact .choose i ((touches_map f (k i)).1 h),
      fun h => by cases h with | choose i h => exact .choose i ((touches_map f (k i)).2 h)⟩
  | .load _ _ _ ret => ⟨fun h => by
        cases h with
        | load h => exact .load h
        | loadRet v h => exact .loadRet v ((touches_map f (ret v)).1 h),
      fun h => by
        cases h with
        | load h => exact .load h
        | loadRet v h => exact .loadRet v ((touches_map f (ret v)).2 h)⟩
  | .store _ _ _ _ ret => ⟨fun h => by
        cases h with
        | store h => exact .store h
        | storeRet b h => exact .storeRet b ((touches_map f (ret b)).1 h),
      fun h => by
        cases h with
        | store h => exact .store h
        | storeRet b h => exact .storeRet b ((touches_map f (ret b)).2 h)⟩
  | .rmw _ _ _ _ ret => ⟨fun h => by
        cases h with
        | rmw h => exact .rmw h
        | rmwRet v h => exact .rmwRet v ((touches_map f (ret v)).1 h),
      fun h => by
        cases h with
        | rmw h => exact .rmw h
        | rmwRet v h => exact .rmwRet v ((touches_map f (ret v)).2 h)⟩
  | .fence _ ret => ⟨fun h => by cases h with | fence h => exact .fence ((touches_map f (ret ())).1 h),
      fun h => by cases h with | fence h => exact .fence ((touches_map f (ret ())).2 h)⟩

/-- `WriteTree` reads only the events. -/
theorem writeTree_map (f : σ → τ) {G : Loc → Val → Prop} :
    ∀ t : EvTree σ, Scc.Sem.WriteTree G (t.map f) ↔ Scc.Sem.WriteTree G t
  | .done _ => Iff.rfl
  | .fault _ => Iff.rfl
  | .choose _ k => forall_congr' fun i => writeTree_map f (k i)
  | .load _ _ _ ret => forall_congr' fun v => writeTree_map f (ret v)
  | .store _ _ _ _ ret => and_congr_right fun _ => forall_congr' fun b => writeTree_map f (ret b)
  | .rmw _ _ _ _ ret => and_congr_right fun _ => forall_congr' fun v => writeTree_map f (ret v)
  | .fence _ ret => forall_congr' fun u => writeTree_map f (ret u)

/-- **`OwnTree` of a mapped tree**: the owned words of the mapped leaves are
those of the leaves (`hown`). -/
theorem ownTree_map (f : σ → τ) {own : τ → List (Loc × Val)} {own' : σ → List (Loc × Val)}
    (hown : ∀ s, own (f s) = own' s) {ow : List (Loc × Val)} {t : EvTree σ}
    (h : Spike.Lib.Consumer1.OwnTree own' ow t) : Spike.Lib.Consumer1.OwnTree own ow (t.map f) := by
  rcases h with ⟨ha, hw⟩ | ⟨h0, kr, L, V, s', rfl, hb, ho⟩ | ⟨kr, L, V, s', rfl, hb, ho⟩ |
      ⟨k, nr, L, op, g, rfl, hb, hv, ho⟩
  · refine .inl ⟨(EvTree.allInv_map _ f _ t).2 (ha.mono fun s hs => by rw [hown]; exact hs), ?_⟩
    exact (writeTree_map f t).2 hw
  · exact .inr (.inl ⟨h0, kr, L, V, f s', rfl, hb, by rw [hown]; exact ho⟩)
  · exact .inr (.inr (.inl ⟨kr, L, V, f s', rfl, hb, by rw [hown]; exact ho⟩))
  · exact .inr (.inr (.inr ⟨k, nr, L, op, f ∘ g, rfl, hb, hv, fun v hv' => by
      simp only [Function.comp, hown]; exact ho v hv'⟩))

/-- `Leaves Q` and `AllInv G P` give `AllInv G (P ∧ Q)`. -/
theorem leaves_and_allInv {G : Loc → Val → Prop} {P Q : σ → Prop} :
    ∀ {t : EvTree σ}, Leaves Q t → t.AllInv G P → t.AllInv G (fun s => P s ∧ Q s)
  | .done _, hq, hp => ⟨hp, hq⟩
  | .fault _, _, _ => trivial
  | .choose _ _, hq, hp => fun i => leaves_and_allInv (hq i) (hp i)
  | .load _ _ _ _, hq, hp => fun v hg => leaves_and_allInv (hq v) (hp v hg)
  | .store _ _ _ _ _, hq, hp => ⟨hp.1, fun b hb => leaves_and_allInv (hq b) (hp.2 b hb)⟩
  | .rmw _ _ _ _ _, hq, hp => fun v hg => ⟨(hp v hg).1, leaves_and_allInv (hq v) (hp v hg).2⟩
  | .fence _ _, hq, hp => fun u => leaves_and_allInv (hq u) (hp u)

/-- Every leaf of a mapped tree is a mapped leaf. -/
theorem leaves_map (f : σ → τ) {Q : τ → Prop} :
    ∀ t : EvTree σ, Leaves Q (t.map f) ↔ Leaves (fun s => Q (f s)) t
  | .done _ => Iff.rfl
  | .fault _ => Iff.rfl
  | .choose _ k => forall_congr' fun i => leaves_map f (k i)
  | .load _ _ _ ret => forall_congr' fun v => leaves_map f (ret v)
  | .store _ _ _ _ ret => forall_congr' fun b => leaves_map f (ret b)
  | .rmw _ _ _ _ ret => forall_congr' fun v => leaves_map f (ret v)
  | .fence _ ret => forall_congr' fun u => leaves_map f (ret u)

/-- Every leaf of a tree has a property every state has. -/
theorem leaves_true {Q : σ → Prop} (hQ : ∀ s, Q s) : ∀ t : EvTree σ, Leaves Q t
  | .done s => hQ s
  | .fault _ => trivial
  | .choose _ k => fun i => leaves_true hQ (k i)
  | .load _ _ _ ret => fun v => leaves_true hQ (ret v)
  | .store _ _ _ _ ret => fun b => leaves_true hQ (ret b)
  | .rmw _ _ _ _ ret => fun v => leaves_true hQ (ret v)
  | .fence _ ret => fun u => leaves_true hQ (ret u)

end Spike.Lib.TreeMap

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.TreeMap.ownTree_map' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.TreeMap.ownTree_map
