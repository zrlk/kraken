/-
A ghost access counter for any environment (design note
`Kraken/Promising/EnvWP.md` §8).

`SharedEnv.counted env` is `env` with a natural number next to its state that
every access (load, store, read-modify-write) increments and fences leave
alone. It changes nothing the thread can observe: `ok` and `step` are `env`'s
on the first component. Its use is the zero-step guard of the
partial-correctness control-flow rule (`MachineWP.cfgEnv_partial`): a back
edge must leave the block's entry state, and after an access the counter has
moved even when nothing else did (an AArch64 store-exclusive that failed).
Each ISA's `EnvCfg` projects `Safely` judgments in `counted env` back to
`env` (`MachineWP.PartialTripleEnv.uncount`).
-/
import Kraken.SharedEnv

namespace Kraken

/-- The ghost increment of an access: one per load, store or
read-modify-write, none per fence. -/
def SharedAccess.tick : SharedAccess → Nat
  | .fence _ => 0
  | _ => 1

end Kraken

namespace Kraken.SharedEnv

/-- `env` with a ghost access counter. -/
def counted (env : SharedEnv) : SharedEnv where
  State := env.State × Nat
  ok a g := env.ok a g.1
  step a g r g' := env.step a g.1 r g'.1 ∧ g'.2 = g.2 + SharedAccess.tick a

@[simp] theorem counted_ok (env : SharedEnv) (a : SharedAccess) (g : (counted env).State) :
    (counted env).ok a g ↔ env.ok a g.1 := Iff.rfl

@[simp] theorem counted_step (env : SharedEnv) (a : SharedAccess) (g : (counted env).State)
    (r : a.Ret) (g' : (counted env).State) :
    (counted env).step a g r g' ↔ env.step a g.1 r g'.1 ∧ g'.2 = g.2 + SharedAccess.tick a :=
  Iff.rfl

@[simp] theorem tick_load (k : LoadKind) (xcl : Bool) (addr : BitVec 64) (n : Nat) :
    SharedAccess.tick (.load k xcl addr n) = 1 := rfl

@[simp] theorem tick_store (k : StoreKind) (xcl : Bool) (addr : BitVec 64) (n : Nat) (v : BitVec 128) :
    SharedAccess.tick (.store k xcl addr n v) = 1 := rfl

@[simp] theorem tick_rmw (k : RmwKind) (addr : BitVec 64) (n : Nat)
    (op : BitVec 128 → Option (BitVec 128)) : SharedAccess.tick (.rmw k addr n op) = 1 := rfl

@[simp] theorem tick_fence (k : FenceKind) : SharedAccess.tick (.fence k) = 0 := rfl

theorem counted_fencesSkip {env : SharedEnv} (h : env.FencesSkip) : (counted env).FencesSkip :=
  fun k g => ⟨(h k g.1).1, fun g' ⟨hs, hn⟩ => Prod.ext ((h k g.1).2 g'.1 hs) hn⟩

instance (env : SharedEnv) [env.Skips] : (counted env).Skips :=
  ⟨counted_fencesSkip Skips.fencesSkip⟩

end Kraken.SharedEnv
