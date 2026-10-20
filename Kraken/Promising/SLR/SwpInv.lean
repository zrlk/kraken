/-
The per-thread invariant of the SWP spinlock worker (AArch64 `swpWorker`)
for `ThreadRuleR` (`SLR/NPSafeInvR.lean`), with the resource specification
of `SLR/SwpSpec.lean`.

`Inv cl c r g` (thread `tid`, parameters `P`): thread `tid` of `c` runs the
laid-out worker with `X0 = l`, `X1 = c` (`Frame`), sits at one of the cells
(or at the end), and its resource `r` is in the phase of that cell:

- `Fresh` (before the lock is taken: positions 1, 3, 6, 7, 8, and 4 when the
  swap read a non-zero value): half of `K tid`, all of `F tid`, at least
  `1/N` of `Lk`;
- `Holding S` (the lock is taken, positions 4 after reading `0`, 10–13): the
  pool for `S` (minus nothing: all of `C`, `F tid`, `K tid` whole since
  `S tid = false`), a positive share of `Lk`; with flag `cl`, at least `1/N`
  of `Lk` and either the counter relation (`CounterGood`: the maximal write
  of `C` is at `|S|`, below the thread's read view, then, after the load, the
  value in `X5`; after the store, the thread's own write) or a received
  surplus of `Lk` (`> 1/N`, the acquired slot was `Bad`);
- `Done`-ward (position 14 and the end): all of `K tid`, at least `1/N` of
  `Lk` under `cl`, and the unlock in the write set of `Lk` (`Post`).

Every own write of `Lk` is in memory (`LockWritesIn`), so the unlock (a fresh
message, or a promise prepaid at position 13 above them) follows them all. Before the lock is taken, the lock's forwarding item is an
own `swpa` write of `1` in memory, and back at the swap a later write of the
lock is below `coh` (`LkMem`), so the swap's acquire read is not forwarded.

This file states the invariant; the obligations (`env`, `done`, `wp` per
cell, `prepay` at position 13) are proved from the cell rules of
`SLR/SwpCells.lean` (shapes: `SLR/RuleShapes.lean`).
-/
import Kraken.Promising.SLR.SwpSpec
import Kraken.Promising.SLR.SpinCommon
import Kraken.Promising.SLR.SwpTrees

namespace Kraken.Promising.SLR.SwpInv

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.AArch64.Examples.InvEnv
open Kraken.Promising.SLR.Spinlock

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout swpWorker)]

/-- The parameters of a spinlock-counter instance: `N` threads, the lock and
counter addresses, and the ghost token locations. -/
structure Params where
  N : Nat
  l : BitVec 64
  c : BitVec 64
  K : Nat → Loc
  F : Nat → Loc

namespace Params

/-- The lock word. -/
abbrev Lk (P : Params) : Loc := ⟨P.l, 4⟩

/-- The counter word. -/
abbrev C (P : Params) : Loc := ⟨P.c, 4⟩

/-- The lock's predicate for these parameters. -/
abbrev φ (P : Params) : Pred := lockPred P.N P.Lk P.C P.K P.F

/-- The ISA-neutral locations of these parameters (`SpinCommon.Sys`): the
phases below agree with `SpinCommon`'s at `P.sys` by unfolding, so the
ISA-neutral helpers (`SLR/SpinAcquire.lean`) apply. -/
abbrev sys (P : Params) : SpinCommon.Sys := ⟨P.N, P.Lk, P.C, P.K, P.F⟩

end Params

/-- The thread-state facts every cell shares: the laid-out worker, no
declarations, the end address, `X0 = l`, `X1 = c`, both words outside the
private data memory, and `W3 = 1` after the first instruction. -/
structure Frame (P : Params) (st : State) : Prop where
  exe : st.exe = layout swpWorker
  decls : st.decls = {}
  endPc : st.endPc = (layout swpWorker).addrOf 16
  x0 : st.st.1.regs.X0.toBitVec = P.l
  x1 : st.st.1.regs.X1.toBitVec = P.c
  dl : Mem.loadInt st.st.1.dmem P.l 4 = none
  dc : Mem.loadInt st.st.1.dmem P.c 4 = none
  /-- `W3 = 1` once past `mov w3, #1` (position 1, which shares its address
  with the start label). -/
  x3 : st.st.2 = (layout swpWorker).addrOf 1 ∨ BitVec.setWidth 32 st.st.1.regs.X3.toBitVec = 1

/-- The thread is at position `i`. -/
def AtPos (st : State) (i : Nat) : Prop := st.st.2 = (layout swpWorker).addrOf i

/-- Before taking the lock. -/
def Fresh (P : Params) (tid : Nat) (r : Res) : Prop :=
  1 / 2 ≤ (r.wr (P.K tid)).q ∧ 1 ≤ (r.wr (P.F tid)).q ∧ 1 / P.N ≤ (r.wr P.Lk).q

/-- Holding the lock with the pool for `S` merged into the thread's
resource. -/
def Holding (P : Params) (tid : Nat) (S : Nat → Bool) (r : Res) : Prop :=
  (r.wr P.C).q = 1 ∧ S tid = false ∧ tid < P.N ∧ 1 ≤ (r.wr (P.K tid)).q ∧ 1 ≤ (r.wr (P.F tid)).q ∧
    0 < (r.wr P.Lk).q ∧
    ∀ j < P.N, j ≠ tid → (S j = false → 1 / 2 ≤ (r.wr (P.K j)).q) ∧ (S j = true → 1 ≤ (r.wr (P.F j)).q)

/-- The counter's maximal write: `(v, ts)` is in the write set of `C` and
every write in it is at or below `ts`. -/
def CounterMax (P : Params) (v : Val) (ts : Time) (r : Res) : Prop :=
  (r.wr P.C).X (v, ts) ∧ ∀ p, (r.wr P.C).X p → p.2 ≤ ts

/-- The counter relation while holding: the maximal write of `C` is `(k, ts)`
with `k = |S|` (the value the thread will see). -/
def CounterGood (P : Params) (S : Nat → Bool) (k : Nat) (ts : Time) (r : Res) : Prop :=
  CounterMax P (BitVec.ofNat 128 k) ts r ∧ k = ((List.range P.N).filter S).length

/-- The clean-mode lock facts while holding: at least the own share, and
either the counter relation (with the counter's maximal write below the
thread's read view `vr`) or a received surplus of the lock (`Bad` was
acquired), which the release forwards. -/
def HoldMode (P : Params) (S : Nat → Bool) (k : Nat) (vr : View) (r : Res) : Prop :=
  1 / P.N ≤ (r.wr P.Lk).q ∧ ((∃ ts, CounterGood P S k ts r ∧ ts ≤ vr) ∨ 1 / P.N < (r.wr P.Lk).q)

/-- Every own write of the lock is in memory. -/
def LockWritesIn (P : Params) (r : Res) (m : Memory) : Prop := ∀ p, (r.wr P.Lk).X p → p.2 ≤ m.last

/-- After prepaying the unlock (`prepay` at position 13): the pool is in the
slots of the pending unlock promise, the thread keeps all of `K tid` and a
positive share of `Lk` (which the pending fulfilment's write needs), and
`Post` under the clean flag. -/
def Prepaid (P : Params) (tid : Nat) (cl : Prop) (r : Res) : Prop :=
  (r.wr P.C).q = 0 ∧ 1 ≤ (r.wr (P.K tid)).q ∧ 0 < (r.wr P.Lk).q ∧ (cl → Post P.N P.Lk P.K r)

/-- Before taking the lock, the thread's forwarding item for the lock (if
any, an own `swpa` write) is at or below `coh` of the lock. -/
def LkFwd (P : Params) (vs : Views) : Prop := ∀ f, vs.getFwd P.Lk = some f → f.time ≤ vs.getCoh P.Lk

/-- The memory side of the forwarding item for the lock before taking it: the
item (if any) is an own `swpa` write of `1`, and at the swap (position 3) and
on the way back to it (positions 1, 8, and 7 after reading a zero low word) a
later write of the lock is at or below `coh`. So the swap does not read at the
item's timestamp, and its acquire read is not forwarded (an acquire read may
take the forwarding view of an own exclusive write: herd's `aob` orders only
the exclusive pair's read before it). -/
def LkMem (P : Params) (i : Nat) (x2 : BitVec 32) (vs : Views) (m : Memory) : Prop :=
  ∀ f, vs.getFwd P.Lk = some f →
    (i ∈ [1, 3, 4, 6, 7, 8] → ∃ w, m.get? f.time = some w ∧ w.loc = P.Lk ∧ w.val = 1#128) ∧
    (i = 1 ∨ i = 3 ∨ i = 8 ∨ (i = 7 ∧ x2 = 0) → m.writeIn P.Lk f.time (vs.getCoh P.Lk) = true)

/-- The phase of the resource at each position (`x2`/`x5`: the low words of
`X2`/`X5`; `vs`: the thread's views). The counter's maximal write is below
the read view before the load (`vrNew`, which the load's bound takes), below
`coh C` after it (which the store's bound takes), and below `vwOld` after the
store (which the release's bound takes). At position 13 the unlock may
have been prepaid (`Prepaid`). Before the lock is taken, the lock's
forwarding item is at or below `coh` (`LkFwd`). -/
def Phase (P : Params) (tid : Nat) (cl : Prop) (i : Nat) (x2 x5 : BitVec 32) (vs : Views) (r : Res) : Prop :=
  match i with
  | 1 | 3 | 6 | 7 | 8 => Fresh P tid r ∧ LkFwd P vs
  | 4 => if x2 = 0 then ∃ S k, Holding P tid S r ∧ (cl → HoldMode P S k vs.vrNew r) else Fresh P tid r ∧ LkFwd P vs
  | 10 => ∃ S k, Holding P tid S r ∧ (cl → HoldMode P S k vs.vrNew r)
  | 11 => ∃ S k, Holding P tid S r ∧ (cl → 1 / P.N ≤ (r.wr P.Lk).q ∧
      ((∃ ts, CounterGood P S k ts r ∧ ts ≤ vs.getCoh P.C ∧ x5 = BitVec.ofNat 32 k) ∨ 1 / P.N < (r.wr P.Lk).q))
  | 12 => ∃ S k, Holding P tid S r ∧ (cl → 1 / P.N ≤ (r.wr P.Lk).q ∧
      ((∃ ts, CounterGood P S k ts r ∧ ts ≤ vs.getCoh P.C ∧ x5 = BitVec.ofNat 32 (k + 1)) ∨
        1 / P.N < (r.wr P.Lk).q))
  | 13 => (∃ S k, Holding P tid S r ∧ (cl → 1 / P.N ≤ (r.wr P.Lk).q ∧
      ((∃ ts, CounterMax P (BitVec.ofNat 128 (k + 1)) ts r ∧ k = ((List.range P.N).filter S).length ∧
        ts ≤ vs.vwOld) ∨ 1 / P.N < (r.wr P.Lk).q))) ∨ Prepaid P tid cl r
  | 14 | 16 => 1 ≤ (r.wr (P.K tid)).q ∧ (cl → Post P.N P.Lk P.K r)
  | _ => False

/-- The world facts: the lock's release predicate is `φ` and it has an update
id with predicate `φ`; the counter's release predicate is pure. Stable under
`Ghost.Le`. -/
def World (P : Params) (g : Ghost) : Prop :=
  g.rel P.Lk = P.φ ∧ (∀ v, Pred.Pure (g.rel P.C) v) ∧
    ∃ ι, ι ∈ g.upd P.Lk ∧ ι < g.acqTab.length ∧ g.acqPred ι = P.φ

/-- A prepaid state at position 13 (no counter permission) has the unlock
promise outstanding. -/
def PrepaidProm (P : Params) (tid : Nat) (i : Nat) (t : Thread isa) (m : Memory) (r : Res) : Prop :=
  i = 13 → (r.wr P.C).q = 0 → ∃ ts ∈ t.prom, m.get? ts = some ⟨P.Lk, 0, tid⟩

/-- **The invariant of thread `tid`** at clean flag `cl` (stable under the
environment: `SwpRule.inv_env`). -/
def Inv (P : Params) (tid : Nat) (cl : Prop) (c : Config isa) (r : Res) (g : Ghost) : Prop :=
  World P g ∧ ∃ t, c.threads[tid]? = some t ∧ Frame P t.st ∧ LockWritesIn P r c.mem ∧
    ∃ i, AtPos t.st i ∧
      Phase P tid cl i (BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec)
        (BitVec.setWidth 32 t.st.st.1.regs.X5.toBitVec) t.views r ∧
      PrepaidProm P tid i t c.mem r ∧ LkMem P i (BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec) t.views c.mem

/-- Every pending mark is a message of the memory (`Erase.pend` gives it
after every step; it survives the environment's memory growth). -/
def PendIn (g : Ghost) (m : Memory) : Prop := ∀ ts ∈ g.pend, ts ≤ m.last

/-- An own pending promise is the prepaid unlock: the thread is at position
13 and has given the pool away, and it is the only own pending promise. -/
def OwnPend (P : Params) (tid : Nat) (c : Config isa) (r : Res) (g : Ghost) : Prop :=
  ∀ t, c.threads[tid]? = some t → ∀ ts ∈ t.prom, ts ∈ g.pend → AtPos t.st 13 ∧ (r.wr P.C).q = 0 ∧
    ∀ ts' ∈ t.prom, ts' ∈ g.pend → ts' = ts

/-- **The instance invariant** of `ThreadRuleRX` (`SLR/ThreadRuleX.lean`):
`Inv` and the pending-mark facts, which are not stable under arbitrary
ghost growth but are transported from the `NPSafe` instance to the
extension by the own-pending transport (`SwpRule`). -/
def InvX (P : Params) (tid : Nat) (cl : Prop) (c : Config isa) (r : Res) (g : Ghost) : Prop :=
  Inv P tid cl c r g ∧ PendIn g c.mem ∧ OwnPend P tid c r g

end Kraken.Promising.SLR.SwpInv
