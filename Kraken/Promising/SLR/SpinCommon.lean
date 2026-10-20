/-
The ISA-neutral resource phases of the spinlock-counter workers (AArch64
`swpWorker`, `SLR/SwpInv.lean`; x64 `spinWorker`, `SLR/X64SpinInv.lean`),
over the resource specification of `SLR/SwpSpec.lean`.

The definitions mention no instruction syntax, so both the AArch64 and the
x64 invariants can import this file (the two syntax modules cannot be
imported together). They are stated over `Sys`: the number of threads, the
lock and counter words, and the ghost token locations.

- `Fresh`: before taking the lock;
- `Holding S`: the lock is taken, with the pool for `S` existing in;
- `CounterMax`/`CounterGood`: the counter's maximal write, and the counter
  relation `k = |S|`;
- `HoldMode`: the clean-mode facts while holding (counter relation below the
  read view, or a received surplus of the lock);
- `LockWritesIn`: every own write of the lock is in memory;
- `World`: the ghost facts (lock predicate, pure counter predicate, an update
  id for the lock), stable under `Ghost.Le` (`World.mono`).
-/
import Kraken.Promising.SLR.SwpSpec

namespace Kraken.Promising.SLR.SpinCommon

open Kraken Kraken.Promising
open Kraken.Promising.SLR.Spinlock

/-- The locations of a spinlock-counter instance: `N` threads, the lock and
counter words, and the ghost token locations. -/
structure Sys where
  N : Nat
  Lk : Loc
  C : Loc
  K : Nat → Loc
  F : Nat → Loc

/-- The lock's predicate. -/
abbrev Sys.φ (P : Sys) : Pred := lockPred P.N P.Lk P.C P.K P.F

/-- Before taking the lock. -/
def Fresh (P : Sys) (tid : Nat) (r : Res) : Prop :=
  1 / 2 ≤ (r.wr (P.K tid)).q ∧ 1 ≤ (r.wr (P.F tid)).q ∧ 1 / P.N ≤ (r.wr P.Lk).q

/-- Holding the lock with the pool for `S` merged into the thread's
resource. -/
def Holding (P : Sys) (tid : Nat) (S : Nat → Bool) (r : Res) : Prop :=
  (r.wr P.C).q = 1 ∧ S tid = false ∧ tid < P.N ∧ 1 ≤ (r.wr (P.K tid)).q ∧ 1 ≤ (r.wr (P.F tid)).q ∧
    0 < (r.wr P.Lk).q ∧
    ∀ j < P.N, j ≠ tid → (S j = false → 1 / 2 ≤ (r.wr (P.K j)).q) ∧ (S j = true → 1 ≤ (r.wr (P.F j)).q)

/-- The counter's maximal write: `(v, ts)` is in the write set of `C` and
every write in it is at or below `ts`. -/
def CounterMax (P : Sys) (v : Val) (ts : Time) (r : Res) : Prop :=
  (r.wr P.C).X (v, ts) ∧ ∀ p, (r.wr P.C).X p → p.2 ≤ ts

/-- The counter relation while holding: the maximal write of `C` is `(k, ts)`
with `k = |S|`. -/
def CounterGood (P : Sys) (S : Nat → Bool) (k : Nat) (ts : Time) (r : Res) : Prop :=
  CounterMax P (BitVec.ofNat 128 k) ts r ∧ k = ((List.range P.N).filter S).length

/-- The clean-mode lock facts while holding: at least the own share, and
either the counter relation (with the counter's maximal write below the
view `vr`) or a received surplus of the lock (`Bad` was acquired). -/
def HoldMode (P : Sys) (S : Nat → Bool) (k : Nat) (vr : View) (r : Res) : Prop :=
  1 / P.N ≤ (r.wr P.Lk).q ∧ ((∃ ts, CounterGood P S k ts r ∧ ts ≤ vr) ∨ 1 / P.N < (r.wr P.Lk).q)

/-- Every own write of the lock is in memory. -/
def LockWritesIn (P : Sys) (r : Res) (m : Memory) : Prop := ∀ p, (r.wr P.Lk).X p → p.2 ≤ m.last

/-- The world facts: the lock's release predicate is `φ` and it has an update
id with predicate `φ`; the counter's release predicate is pure. -/
def World (P : Sys) (g : Ghost) : Prop :=
  g.rel P.Lk = P.φ ∧ (∀ v, Pred.Pure (g.rel P.C) v) ∧
    ∃ ι, ι ∈ g.upd P.Lk ∧ ι < g.acqTab.length ∧ g.acqPred ι = P.φ

/-- `World` in a larger world. -/
theorem World.mono {P : Sys} {g g₁ : Ghost} (h : World P g) (hle : g.Le g₁) : World P g₁ := by
  obtain ⟨hL, hC, ι, hι, hlt, hφ⟩ := h
  refine ⟨by rw [hle.rel]; exact hL, fun v => by rw [hle.rel]; exact hC v, ι, (hle.upd P.Lk).subset hι,
    Nat.lt_of_lt_of_le hlt (hle.acqTab.length_le), ?_⟩
  rw [← hφ]
  exact Ghost.acqPred_of_prefix hle.acqTab hlt

/-- `HoldMode` with a larger view. -/
theorem HoldMode.mono {P : Sys} {S : Nat → Bool} {k : Nat} {vr vr' : View} {r : Res}
    (h : HoldMode P S k vr r) (hv : vr ≤ vr') : HoldMode P S k vr' r :=
  ⟨h.1, h.2.imp (fun ⟨ts, hg, hts⟩ => ⟨ts, hg, Nat.le_trans hts hv⟩) id⟩

end Kraken.Promising.SLR.SpinCommon
