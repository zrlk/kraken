/-
**Kernel-evaluable private-memory lookups**: the
replacements `#reach_clone` substitutes for `Mem.loadBytes`/`Mem.loadInt`.

A lookup in a `Mem w` (an `ExtHashMap`) is stuck in the kernel (the bucket
index is a `USize`). In an empty map every lookup of at least one byte
misses, and emptiness is the stored size, which the kernel does evaluate;
so `reachLoadBytes`/`reachLoadInt` answer `none` there without hashing and
defer to the originals elsewhere. `reachLoadBytes_eq`/`reachLoadInt_eq`: they
are the originals.

Also here, shared by the ISAs: `reachWithAddr`, `Executable.withAddresses`
by structural recursion (the original's well-founded recursion has a
decreasing proof the kernel cannot reduce).
-/
import Kraken.Mem
import Kraken.Layout

namespace Kraken.Promising.Reach

/-- `Mem.loadBytes`, answering an empty map without a lookup. -/
def reachLoadBytes {w : Nat} (m : Mem w) (a : BitVec w) (n : Nat) : Option (List UInt8) :=
  if m.isEmpty && n != 0 then none else Mem.loadBytes m a n

/-- `Mem.loadInt`, answering an empty map without a lookup. -/
def reachLoadInt {w : Nat} (m : Mem w) (a : BitVec w) (n : Nat) : Option Int :=
  if m.isEmpty && n != 0 then none else Mem.loadInt m a n

theorem reach_loadBytes_empty {w : Nat} (m : Mem w) (a : BitVec w) (n : Nat)
    (hm : m.isEmpty = true) (hn : n ≠ 0) : Mem.loadBytes m a n = none := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hm' : m = ∅ := Std.ExtHashMap.isEmpty_iff.mp hm
  subst hm'
  simp [Mem.loadBytes, List.allSome, List.range_succ_eq_map]

theorem reachLoadBytes_eq : @reachLoadBytes = @Mem.loadBytes := by
  funext w m a n
  unfold reachLoadBytes
  split
  · rename_i h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact (reach_loadBytes_empty m a n h.1 h.2).symm
  · rfl

theorem reachLoadInt_eq : @reachLoadInt = @Mem.loadInt := by
  funext w m a n
  unfold reachLoadInt
  split
  · rename_i h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp [Mem.loadInt, reach_loadBytes_empty m a n h.1 h.2]
  · rfl

/-- `Executable.withAddresses` by structural recursion. -/
def reachWithAddr {D : Type} (a : Int64) : List (D × Nat) → List (Int64 × D × Nat)
  | [] => []
  | (d, n) :: ds => (a, d, n) :: reachWithAddr (a + .ofNat n) ds

theorem reachWithAddr_eq {D : Type} : ∀ (a : Int64) (ds : List (D × Nat)),
    reachWithAddr a ds = Kraken.Executable.withAddresses (a, ds)
  | a, [] => by simp [reachWithAddr, Kraken.Executable.withAddresses]
  | a, (d, n) :: ds => by
    rw [reachWithAddr, reachWithAddr_eq (a + .ofNat n) ds, Kraken.Executable.withAddresses]

theorem reachWithAddr_eq' {D : Type} (e : Kraken.Executable D) :
    reachWithAddr e.1 e.2 = e.withAddresses := reachWithAddr_eq e.1 e.2

end Kraken.Promising.Reach

#print axioms Kraken.Promising.Reach.reachLoadBytes_eq
#print axioms Kraken.Promising.Reach.reachLoadInt_eq
