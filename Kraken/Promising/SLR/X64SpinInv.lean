/-
The per-thread invariant of the x64 `xchg` spinlock worker
(`X64SpinTrees.spinWorker`, x64 `spinlock2`) for `ThreadRuleRX`
(`SLR/ThreadRuleX.lean`; `InvX`), with the resource specification of
`SLR/SwpSpec.lean`. The x64 twin of
`SLR/SwpInv.lean` (AArch64 `swpWorker`).

The resource phases (`Fresh`, `Holding`, `CounterMax`, `CounterGood`,
`HoldMode`, `LockWritesIn`, `World`) are the ISA-neutral ones of
`SLR/SpinCommon.lean` over `Params.sys` (`SwpInv.lean` imports the AArch64
syntax, which cannot be imported next to the x64 syntax). The position map
to the AArch64 invariant: 1–5 ↔ 1, 3, 6, 7, 8 (`Fresh`); 6/7 (`%eax = 0`,
`ZF`) ↔ 4 (`x2 = 0`); 8 ↔ 10 (load of `C`); 9 ↔ 11; 10 ↔ 12; 11 ↔ 13
(unlock); 12, 14 ↔ 14, 16.

`Inv cl c r g` (thread `tid`, parameters `P`): thread `tid` of `c` runs the
laid-out worker with `%rdi = l`, `%rsi = c` (`Frame`), sits at one of the
cells (or at the end), and its resource `r` is in the phase of that cell:

- `Fresh` (before the lock is taken: positions 1–5, and 6/7 when the swap
  read a non-zero value);
- holding (6 after the swap read `0`, 7 with `ZF`, 8–11): `Holding S`, with
  `HoldMode` under the clean flag;
- `Done`-ward (12, and 14: the end): all of `K tid`, `Post` under the clean
  flag.

Under TSO the swap (5), the counter store (10) and the unlock (11) are
release writes, so each may have been promised and prepaid before it runs:
`Phase` has a prepaid alternative at 10 and `Prepaid` at 11, `PrepaidProm`
ties them to the thread's own promises, and `OwnPend` (in `InvX`) says what
an own pending promise is.

The worker (positions):
```
 0 worker:                 7   jne worker
 1   movl (%rdi),%eax      8   movl (%rsi),%ecx
 2   testl %eax,%eax       9   addl $1,%ecx
 3   jne worker           10   movl %ecx,(%rsi)
 4   movl $1,%eax         11   movl $0,(%rdi)
 5   xchgl %eax,(%rdi)    12   jmp done
 6   testl %eax,%eax      13 done:
```
-/
import Kraken.Promising.SLR.SpinCommon
import Kraken.Promising.SLR.X64SpinTrees

namespace Kraken.Promising.SLR.X64SpinInv

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SpinCommon
open Kraken.Promising.SLR.X64SpinTrees

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout spinWorker)]

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

end Params

/-- The thread-state facts every cell shares: the laid-out worker, no
declarations, the end address, `%rdi = l`, `%rsi = c`, both words outside
the private data memory. -/
structure Frame (P : Params) (st : State) : Prop where
  exe : st.exe = layout spinWorker
  decls : st.decls = {}
  endPc : st.endPc = (layout spinWorker).addrOf 14
  rdi : st.st.1.regs.get64 .rdi = P.l
  rsi : st.st.1.regs.get64 .rsi = P.c
  dl : Mem.loadInt st.st.1.dmem P.l 4 = none
  dc : Mem.loadInt st.st.1.dmem P.c 4 = none

/-- The thread is at position `i`. -/
def AtPos (st : State) (i : Nat) : Prop := st.st.2 = (layout spinWorker).addrOf i

/-- The ISA-neutral locations of these parameters (`SLR/SpinCommon.lean`). -/
abbrev Params.sys (P : Params) : Sys := ⟨P.N, P.Lk, P.C, P.K, P.F⟩

/-- Before taking the lock, with the thread id in range (so the own lock
share `1/N` is positive). -/
def FreshN (P : Params) (tid : Nat) (r : Res) : Prop := Fresh P.sys tid r ∧ tid < P.N

/-- Holding, with `HoldMode` (counter's maximal write below `vr`) under the
clean flag. -/
def Held (P : Params) (tid : Nat) (cl : Prop) (vr : View) (r : Res) : Prop :=
  ∃ S k, Holding P.sys tid S r ∧ (cl → HoldMode P.sys S k vr r)

/-- Before taking the lock, the thread's forwarding item for the lock (if
any) is from an exclusive write (its own `xchgl`s; only the unlock `movl
$0,(%rdi)` writes the lock non-exclusively, and the thread never takes the
lock again after it), so the acquire read of `xchgl` is not forwarded: it
reads at the message's timestamp. -/
def LkFwd (P : Params) (vs : Views) : Prop := ∀ f, vs.getFwd P.Lk = some f → f.xcl = true

/-- After prepaying the unlock (`prepay` at position 11): the pool is in the
slots of the pending unlock promise, the thread keeps all of `K tid` and a
positive share of `Lk` (which the pending fulfilment's write needs), and
`Post` under the clean flag. -/
def Prepaid (P : Params) (tid : Nat) (cl : Prop) (r : Res) : Prop :=
  (r.wr P.C).q = 0 ∧ 1 ≤ (r.wr (P.K tid)).q ∧ 0 < (r.wr P.Lk).q ∧ (cl → Post P.N P.Lk P.K r)

/-- The phase of the resource at each position (`eax`/`ecx`: the low words
of `%rax`/`%rcx`; `zf`: the zero flag; `vs`: the thread's views). As in
`SwpInv.Phase`, the counter's maximal write is below the read view before the
load of `C` (`vrNew`), below `coh C` after it, and below `vwOld` after the
store of `C`. Before the lock is taken, the lock is not forwarded from a
non-exclusive write (`LkFwd`).

Under TSO all three writes of the worker are releases, so each can be
promised and prepaid when it is the next instruction (`ThreadRuleRX.prepay`):

- the swap's write (position 5, `⟨Lk, 1⟩`) and the counter store's
  (position 10) have pure predicates: the prepayment only adds the promised
  write to the thread's write set. At 5 this keeps `Phase`; at 10 the
  counter's maximal write becomes the promised `(k + 1, ts)` above `coh C`
  (the third clean alternative; `PrepaidProm` says it is the thread's own
  message);
- the unlock (position 11) hands the pool over (`Prepaid`). -/
def Phase (P : Params) (tid : Nat) (cl : Prop) (i : Nat) (eax ecx : BitVec 32) (zf : Bool) (vs : Views)
    (r : Res) : Prop :=
  match i with
  | 1 | 2 | 3 | 4 => FreshN P tid r ∧ LkFwd P vs
  | 5 => FreshN P tid r ∧ LkFwd P vs ∧ eax = 1
  | 6 => if eax = 0 then Held P tid cl vs.vrNew r else FreshN P tid r ∧ LkFwd P vs
  | 7 => if zf then Held P tid cl vs.vrNew r else FreshN P tid r ∧ LkFwd P vs
  | 8 => Held P tid cl vs.vrNew r
  | 9 => ∃ S k, Holding P.sys tid S r ∧ (cl → 1 / P.N ≤ (r.wr P.Lk).q ∧
      ((∃ ts, CounterGood P.sys S k ts r ∧ ts ≤ vs.getCoh P.C ∧ ecx = BitVec.ofNat 32 k) ∨
        1 / P.N < (r.wr P.Lk).q))
  | 10 => ∃ S k, Holding P.sys tid S r ∧ (cl → 1 / P.N ≤ (r.wr P.Lk).q ∧
      ((∃ ts, CounterGood P.sys S k ts r ∧ ts ≤ vs.getCoh P.C ∧ ecx = BitVec.ofNat 32 (k + 1)) ∨
        1 / P.N < (r.wr P.Lk).q ∨
        (∃ ts, CounterMax P.sys (BitVec.ofNat 128 (k + 1)) ts r ∧ k = ((List.range P.N).filter S).length ∧
          vs.getCoh P.C < ts ∧ ecx = BitVec.ofNat 32 (k + 1))))
  | 11 => (∃ S k, Holding P.sys tid S r ∧ (cl → 1 / P.N ≤ (r.wr P.Lk).q ∧
      ((∃ ts, CounterMax P.sys (BitVec.ofNat 128 (k + 1)) ts r ∧ k = ((List.range P.N).filter S).length ∧
        ts ≤ vs.vwOld) ∨ 1 / P.N < (r.wr P.Lk).q))) ∨ Prepaid P tid cl r
  | 12 | 14 => 1 ≤ (r.wr (P.K tid)).q ∧ (cl → Post P.N P.Lk P.K r)
  | _ => False

/-- The registers `Phase` reads. -/
abbrev eaxOf (st : State) : BitVec 32 := st.st.1.regs.get (.low .rax .W32)

abbrev ecxOf (st : State) : BitVec 32 := st.st.1.regs.get (.low .rcx .W32)

/-- The facts about the thread's own promises behind the prepaid phases:

- at position 10, in the clean mode without a surplus of the lock, every
  write of `C` in the thread's write set above its `coh C` is a message of
  the thread (the prepaid counter store; with erasure and `ownCoh` it is an
  outstanding, hence pending, own promise, `OwnPend`);
- at position 11, a prepaid state (no counter permission) has the unlock
  promise outstanding. -/
def PrepaidProm (P : Params) (tid : Nat) (cl : Prop) (i : Nat) (t : Thread isa) (m : Memory) (r : Res) : Prop :=
  (i = 10 → cl → (r.wr P.Lk).q ≤ 1 / P.N → ∀ p, (r.wr P.C).X p → t.views.getCoh P.C < p.2 →
    ∃ w, m.get? p.2 = some w ∧ w.tid = tid) ∧
  (i = 11 → (r.wr P.C).q = 0 → ∃ ts ∈ t.prom, m.get? ts = some ⟨P.Lk, 0, tid⟩)

/-- **The invariant of thread `tid`** at clean flag `cl`. -/
def Inv (P : Params) (tid : Nat) (cl : Prop) (c : Config isa) (r : Res) (g : Ghost) : Prop :=
  World P.sys g ∧ ∃ t, c.threads[tid]? = some t ∧ Frame P t.st ∧ LockWritesIn P.sys r c.mem ∧
    ∃ i, AtPos t.st i ∧ Phase P tid cl i (eaxOf t.st) (ecxOf t.st) t.st.st.1.status.zf t.views r ∧
      PrepaidProm P tid cl i t c.mem r

/-- Every pending mark is a message of the memory (`Erase.pend` gives it
after every step; it survives the environment's memory growth). -/
def PendIn (g : Ghost) (m : Memory) : Prop := ∀ ts ∈ g.pend, ts ≤ m.last

/-- **An own pending promise is a prepaid release of the next
instruction**: the swap's `⟨Lk, eax⟩` at position 5, the counter store's
`⟨C, ecx⟩` at 10, or the unlock `⟨Lk, 0⟩` at 11 after the pool was given
away. It is the only own pending promise, and every other own promise of
its location lies above it (the prepayment's live run fulfils it at
`|M| + 1` leaving no promise dead, `Thread.RelFulfilsLive`; later promises
are above `|M|`). So the instruction's writes other than its fulfilment
overtake it. -/
def OwnPend (P : Params) (tid : Nat) (c : Config isa) (r : Res) (g : Ghost) : Prop :=
  ∀ t, c.threads[tid]? = some t → ∀ ts ∈ t.prom, ts ∈ g.pend →
    ((AtPos t.st 5 ∧ c.mem.get? ts = some ⟨P.Lk, BitVec.setWidth 128 (eaxOf t.st), tid⟩) ∨
      (AtPos t.st 10 ∧ c.mem.get? ts = some ⟨P.C, BitVec.setWidth 128 (ecxOf t.st), tid⟩) ∨
      (AtPos t.st 11 ∧ (r.wr P.C).q = 0 ∧ c.mem.get? ts = some ⟨P.Lk, 0, tid⟩)) ∧
    (∀ ts' ∈ t.prom, ts' ∈ g.pend → ts' = ts) ∧
    (∀ p ∈ t.prom, p ≠ ts → ∀ w w', c.mem.get? p = some w → c.mem.get? ts = some w' → w.loc = w'.loc → ts < p)

/-- **The instance invariant** of `ThreadRuleRX` (`SLR/ThreadRuleX.lean`):
`Inv` and the pending-mark facts, which are not stable under arbitrary
ghost growth but are transported from the `NPSafe` instance to the
extension by the own-pending transport (`X64SpinRule.ownPend_transport`). -/
def InvX (P : Params) (tid : Nat) (cl : Prop) (c : Config isa) (r : Res) (g : Ghost) : Prop :=
  Inv P tid cl c r g ∧ PendIn g c.mem ∧ OwnPend P tid c r g

end Kraken.Promising.SLR.X64SpinInv
