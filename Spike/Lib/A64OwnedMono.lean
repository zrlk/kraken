/-
**Ownership of a stack range only moves at a transfer** (AArch64): whether
a range is owned (`A64Consumer.Owned`) or unmapped (`Unowned`) reads the
private memory's domain only, and off the transfer sites no step changes
that domain (`Kernel.OwnDom`'s step rule, `Scc.Cert.DomA64.domHyps`): an
instruction's every leaf keeps it (`DomHyps.exec`), a system call's
resumptions keep the private memory (`DomHyps.ret`, `DomHyps.setTp`).

- `privLoad_isSome_of_dom`, `owned_of_dom`, `unowned_of_dom`: equal domains
  give equal `Owned` and `Unowned`.
- `allInv_of_leaf`: a predicate of every leaf of a tree is its `AllInv`.
- `owned_mono` (instruction) and `owned_sys` (system call): `Owned` and
  `Unowned` are kept, in both directions, off the transfer sites; held
  ranges are not released or taken before the clone, so the domain never
  shrinks there.
-/
import Spike.Lib.A64Consumer
import Scc.Cert.Rt.DomA64

namespace Spike.Lib.A64Consumer

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64

/-- **The range is unmapped** in the thread state `s`: no byte of `rS` is in
the private memory (before its take). -/
def Unowned (rS : Range) (s : State) : Prop :=
  ∀ a, rS.contains a → BitVec.ofNat 64 a ∉ s.st.1.dmem

/-- **An 8-byte private load succeeds by the domain alone.** -/
theorem privLoad_isSome_of_dom {s s' : State} (hd : ∀ a, a ∈ s'.st.1.dmem ↔ a ∈ s.st.1.dmem)
    (a : BitVec 64) : (privLoad s' a).isSome = (privLoad s a).isSome := by
  have key : ∀ (m : _root_.Mem 64), (Mem.loadInt m a 8).isSome = true ↔
      ∀ i, i < 8 → a + BitVec.ofNat 64 i ∈ m := by
    intro m
    simp [Mem.loadInt, Option.isSome_map, Mem.loadBytes, List.allSome_isSome_iff]
  apply Bool.eq_iff_iff.mpr
  simp only [privLoad, Option.isSome_map]
  rw [key, key]
  exact forall_congr' fun i => imp_congr_right fun _ => hd _

/-- **`Owned` by the domain alone.** -/
theorem owned_of_dom {Λ : Scc.Sem.Layout} {rS : Range} {s s' : State}
    (hd : ∀ a, a ∈ s'.st.1.dmem ↔ a ∈ s.st.1.dmem) : Owned Λ rS s' ↔ Owned Λ rS s := by
  simp only [Owned, privLoad_isSome_of_dom hd]

/-- **`Unowned` by the domain alone.** -/
theorem unowned_of_dom {rS : Range} {s s' : State}
    (hd : ∀ a, a ∈ s'.st.1.dmem ↔ a ∈ s.st.1.dmem) : Unowned rS s' ↔ Unowned rS s := by
  simp only [Unowned, hd]

/-- **A predicate of every leaf** is the tree's `AllInv` (trivial `G`). -/
theorem allInv_of_leaf {σ : Type} {Q : σ → Prop} :
    ∀ t : EvTree σ, (∀ s, TreeLeaf t s → Q s) → t.AllInv (fun _ _ => True) Q
  | .done s, h => h s rfl
  | .fault _, _ => trivial
  | .choose _ k, h => fun i => allInv_of_leaf (k i) fun s hs => h s ⟨i, hs⟩
  | .load _ _ _ ret, h => fun v _ => allInv_of_leaf (ret v) fun s hs => h s ⟨v, hs⟩
  | .store _ _ _ _ ret, h => ⟨trivial, fun b _ => allInv_of_leaf (ret b) fun s hs => h s ⟨b, hs⟩⟩
  | .rmw _ _ _ _ ret, h => fun old _ => ⟨fun _ _ => trivial, allInv_of_leaf (ret old) fun s hs => h s ⟨old, hs⟩⟩
  | .fence _ ret, h => fun u => allInv_of_leaf (ret u) fun s hs => h s ⟨u, hs⟩

/-- **Off a transfer, an instruction keeps ownership** of any range, both
ways (`OwnDom`'s instruction rule, `DomHyps.exec`). -/
theorem owned_mono {Λ : Scc.Sem.Layout} {rS : Range} {s : State} (hs : WideSt s) {tree : EvTree State}
    (h : isaLSE2.exec s = some tree) :
    tree.AllInv (fun _ _ => True) (fun s' => (Owned Λ rS s' ↔ Owned Λ rS s) ∧ (Unowned rS s' ↔ Unowned rS s)) :=
  allInv_of_leaf tree fun _ hl =>
    have hd := (Scc.Cert.DomA64.domHyps.exec _ _ _ hs h hl).2
    ⟨owned_of_dom hd, unowned_of_dom hd⟩

/-- **A system call's resumptions keep ownership** of any range, both ways
(`DomHyps.ret`, `DomHyps.setTp`: the private memory unchanged). -/
theorem owned_sys {Λ : Scc.Sem.Layout} {rS : Range} {s : State} {call : Kernel.Call} {s' : State}
    (h : s' ∈ Kernel.certSuccs abi s call) :
    (Owned Λ rS s' ↔ Owned Λ rS s) ∧ (Unowned rS s' ↔ Unowned rS s) := by
  have hd : s'.st.1.dmem = s.st.1.dmem := by
    unfold Kernel.certSuccs at h
    split at h
    · cases h with
      | head => rfl
      | tail _ h => cases h
    · obtain ⟨_, -, rfl⟩ := List.mem_map.mp h; rfl
  have hd' : ∀ a, a ∈ s'.st.1.dmem ↔ a ∈ s.st.1.dmem := fun a => by rw [hd]
  exact ⟨owned_of_dom hd', unowned_of_dom hd'⟩

/-- info: 'Spike.Lib.A64Consumer.owned_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64Consumer.owned_mono

/-- info: 'Spike.Lib.A64Consumer.owned_sys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64Consumer.owned_sys

end Spike.Lib.A64Consumer
