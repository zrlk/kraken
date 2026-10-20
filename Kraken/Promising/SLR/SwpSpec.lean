/-
The resource specification of the spinlock counter (ISA-neutral): the lock's
release/update predicate `lockPred` and its parts, for the SWP spinlock
worker of both ISAs (AArch64 `swpWorker`, x64 `spinlock2`).

Locations: the lock `Lk`, the counter `C`, and per thread `j < N` two ghost
token locations, `K j` (the *incremented* token) and `F j` (the *fresh*
token), which no instruction accesses.

Initially thread `j` holds `1/2` of `K j`, all of `F j`, and `1/N` of `Lk`;
the pool (the slot of the initial lock message) holds all of `C` and the
other half of every `K j`. A thread that increments takes the pool's half of
`K j` (it now holds `K j` fully: `Post`) and leaves `F j` in the pool, so the
pool's set `S` of incremented threads is witnessed by `F` (validity: a thread
still holding `F j` has not incremented, `S j = false`).

`lockPred` at the unlocked value `0` (the low word, `setWidth 32`, which is
what both workers test) is `Good ∨ Bad`:

- `Good`: the pool, with the counter's maximal write `(k, ts)` at value
  `k = |S|`, at or below the release message (`ts ≤ V`);
- `Bad`: the pool (without the counter relation) and a positive share of
  `Lk`. A thread whose step starts without full erasure (`NPSafe`'s clean
  flag false) may have read a foreign promise of the counter; it releases
  `Bad`, paying with its lock share (its postcondition is not asked of it).
  A clean thread that acquired `Bad` forwards `Bad` with the received share.
  At a final configuration every thread holds `1/N` of `Lk`, so no slot holds
  a share (`Spinlock.adequacy`, `PoolSpec`'s first disjunct).

At any value with a non-zero low word `lockPred` holds of every resource
(the locked value `1` is written by relaxed RMWs: `Pred.Pure`).
-/
import Kraken.Promising.SLR.Adequacy

namespace Kraken.Promising.SLR

namespace Spinlock

/-- The token pool with incremented set `S`: the full counter permission;
for every `j < N`, half of `K j` if `j` has not incremented, all of `F j` if
it has. -/
def Pool (N : Nat) (C : Loc) (K F : Nat → Loc) (S : Nat → Bool) (r : Res) : Prop :=
  (r.wr C).q = 1 ∧ ∀ j < N, (S j = false → 1 / 2 ≤ (r.wr (K j)).q) ∧ (S j = true → 1 ≤ (r.wr (F j)).q)

/-- The good unlocked state: the pool, the counter's write set has its
maximal element `(k, ts)` at `k = |S|`, at or below the release message `V`
(`≤`: the initial lock message has `V = 0`, the counter's initial write `ts = 0`). -/
def Good (N : Nat) (C : Loc) (K F : Nat → Loc) (V : View) (r : Res) : Prop :=
  ∃ (k : Nat) (S : Nat → Bool) (ts : Time), Pool N C K F S r ∧ (r.wr C).X (BitVec.ofNat 128 k, ts) ∧
    (∀ p, (r.wr C).X p → p.2 ≤ ts) ∧ k = ((List.range N).filter S).length ∧ ts ≤ V

/-- The bad unlocked state: the pool, without the counter relation, and a
positive share of the lock. -/
def Bad (N : Nat) (Lk C : Loc) (K F : Nat → Loc) (r : Res) : Prop :=
  0 < (r.wr Lk).q ∧ ∃ S, Pool N C K F S r

/-- **The lock's release and update predicate.** The unlocked test is on the
low word (`setWidth 32 v = 0`): the workers compare only the 32-bit value
they swapped or loaded, so a message whose low word is `0` must carry the
pool whatever its upper bits. -/
def lockPred (N : Nat) (Lk C : Loc) (K F : Nat → Loc) : Pred where
  P v _ V r := BitVec.setWidth 32 v = 0 → Good N C K F V r ∨ Bad N Lk C K F r
  mono _ _ _ _ _ _ h := h

/-- `lockPred` is pure at a non-zero low word (the locking writes are
relaxed). -/
theorem lockPred_pure {N : Nat} {Lk C : Loc} {K F : Nat → Loc} {v : Val} (hv : BitVec.setWidth 32 v ≠ 0) :
    Pred.Pure (lockPred N Lk C K F) v :=
  fun _ _ h => absurd h hv

/-- `lockPred` meets `adequacy`'s `PoolSpec`. -/
theorem poolSpec_lockPred {N : Nat} {Lk C : Loc} {K F : Nat → Loc} :
    PoolSpec N Lk C K (lockPred N Lk C K F) := by
  intro m V r h
  rcases h (by decide) with ⟨k, S, ts, ⟨hC, hS⟩, hX, hmax, hk, -⟩ | ⟨hL, -⟩
  · refine .inr ⟨k, S, ts, hC, hX, hmax, hk, fun j hj hSj => ?_⟩
    have := (hS j hj).1 hSj
    grind
  · exact .inl hL

end Spinlock

end Kraken.Promising.SLR
