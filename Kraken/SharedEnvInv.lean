/-
The invariant environment (design note `Kraken/Promising/EnvWP.md`,
"Invariant environment").

`SharedEnv.inv S G` is the environment of a thread that knows only a
per-location invariant `G` about the shared locations `S`: every shared read
(any ordering) may return any value satisfying `G`, every shared write (any
ordering) must satisfy `G`, an `rmw` reads any value satisfying `G` and must
map it to one satisfying `G` when it writes, and fences are no-ops. The state
is trivial. Non-shared accesses never reach the environment (they are `dmem`
accesses).

Kang et al.'s write invariant (`Kraken.Promising.write_invariant`) is what
makes this environment sound for every thread of the full Promising machine,
promises included: `Kraken/Promising/InvLink*.lean` link a `TripleEnv`/
`cfgEnv` proof in `inv S G` to `MemInv G` at every reachable configuration.

ISA-free: the values are those of the interface (`BitVec 128` payloads with
a byte count), the locations the Promising machine's footprints `⟨addr, n⟩`,
which is how both ISA adapters build an access with no declarations.
-/
import Kraken.SharedEnv
import Kraken.Promising.Basic

namespace Kraken.SharedEnv

open Kraken.Promising (Loc Val)

/-- **The invariant environment.** `S` lists the shared locations (address,
width in bytes); `G` is the invariant of their values. An access must be
exactly a location of `S`; reads return any value satisfying `G`; writes and
`rmw` writes must satisfy `G` (an `rmw`'s `op` is checked on every old value
satisfying `G`; a failed compare writes nothing). A store succeeds, except
that an exclusive one may also fail. Fences are permitted and do nothing. -/
def inv (S : Layout) (G : Loc → Val → Prop) : SharedEnv where
  State := Unit
  ok a _ := match a with
    | .load _ _ addr n => (addr, n) ∈ S
    | .store _ _ addr n v => (addr, n) ∈ S ∧ G ⟨addr, n⟩ v
    | .rmw _ addr n op => (addr, n) ∈ S ∧ ∀ old, G ⟨addr, n⟩ old → ∀ v, op old = some v → G ⟨addr, n⟩ v
    | .fence _ => True
  step a _ r _ := match a, r with
    | .load _ _ addr n, v => G ⟨addr, n⟩ v
    | .store _ xcl _ _ _, b => b = true ∨ xcl = true
    | .rmw _ addr n _, old => G ⟨addr, n⟩ old
    | .fence _, _ => True

variable {S : Layout} {G : Loc → Val → Prop}

theorem inv_fencesSkip (S : Layout) (G : Loc → Val → Prop) : (inv S G).FencesSkip :=
  fun _ _ => ⟨trivial, fun _ _ => rfl⟩

instance (S : Layout) (G : Loc → Val → Prop) : (inv S G).Skips := ⟨inv_fencesSkip S G⟩

@[simp] theorem inv_ok_load {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {g : (inv S G).State} :
    (inv S G).ok (.load k xcl addr n) g ↔ (addr, n) ∈ S := Iff.rfl

@[simp] theorem inv_ok_store {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : BitVec 128}
    {g : (inv S G).State} : (inv S G).ok (.store k xcl addr n v) g ↔ (addr, n) ∈ S ∧ G ⟨addr, n⟩ v := Iff.rfl

@[simp] theorem inv_ok_rmw {k : RmwKind} {addr : BitVec 64} {n : Nat}
    {op : BitVec 128 → Option (BitVec 128)} {g : (inv S G).State} :
    (inv S G).ok (.rmw k addr n op) g ↔
      (addr, n) ∈ S ∧ ∀ old, G ⟨addr, n⟩ old → ∀ v, op old = some v → G ⟨addr, n⟩ v := Iff.rfl

@[simp] theorem inv_ok_fence {k : FenceKind} {g : (inv S G).State} : (inv S G).ok (.fence k) g ↔ True := Iff.rfl

@[simp] theorem inv_step_load {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {g g' : (inv S G).State}
    {v : BitVec 128} : (inv S G).step (.load k xcl addr n) g v g' ↔ G ⟨addr, n⟩ v := Iff.rfl

@[simp] theorem inv_step_store {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat}
    {v : BitVec 128} {g g' : (inv S G).State} {b : Bool} :
    (inv S G).step (.store k xcl addr n v) g b g' ↔ (b = true ∨ xcl = true) := Iff.rfl

@[simp] theorem inv_step_rmw {k : RmwKind} {addr : BitVec 64} {n : Nat}
    {op : BitVec 128 → Option (BitVec 128)} {g g' : (inv S G).State} {old : BitVec 128} :
    (inv S G).step (.rmw k addr n op) g old g' ↔ G ⟨addr, n⟩ old := Iff.rfl

@[simp] theorem inv_step_fence {k : FenceKind} {g g' : (inv S G).State} {u : Unit} :
    (inv S G).step (.fence k) g u g' ↔ True := Iff.rfl

end Kraken.SharedEnv
