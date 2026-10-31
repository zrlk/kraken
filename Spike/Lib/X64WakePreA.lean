/-
**wake.w on x86-64: main's state at its `clone`** (the twin of
`Spike/Lib/WakePreA.lean`): `ClonePre`, the interface between the
one-thread consumer of main's code up to its `clone` and the clone's
spawn (`X64WakeParentAt.parent_at`, `X64WakeChildAt.child_at`).

At main's `syscall` (`.Lwc_main.x21 + 46`: `cloneAt`) the one-slot
configuration has one thread, at the system call, asking for
`clone(flags, stack, 0, 0, tls)` with `stack = %rsi` the child's stack top
(the top of the range `r1` the second take holds) and `tls = %r8` the
child's TCB; `%r12` the published cell's address and `%rbx` main's
`ThreadId` word, the worker's two arguments (the `syscall` keeps both);
every range held is held for index 0; the source thread at `main`'s
`spawn` term with `c` bound to the published cell and `me` to main's
`ThreadId`.

The x64 frame numbers are A64's: `scc_rt_start` sets `%rsp` to the stack's
top and `call`s `scc_rt_main` (return address and `%rbp`, 16 bytes, then
`subq $32`), which `call`s `wc_main` (16 more, then `subq $64`), so `%rsp`
at the clone is 128 bytes below the top; `wc_main`'s frame, its 64 bytes
below `%rbp` and the saved `%rbp` and return address above it, is the 80
bytes at `%rsp`.

The x64 labels are not numbered per program (`.Lwc_main.x21`), so there is
no label prefix: `cloneAt` and `ClonePre` drop A64's `pfx` argument.
`spawnTerm` and `mainTidLbl` are `Spike.Lib.X64WakeSrcDefs`' (ISA-free
restatements of the neutral ones, checked against them by `rfl` in
`Spike/Test/WakeSrcDefsEq.lean`).

- `cloneAt`: the clone's pc in an executable.
- `ClonePre`: the interface; `ClonePre.held`: every range held is main's;
  `ClonePre.disj`, `ClonePre.frame`, `ClonePre.spTop`: main's stack at the clone.
-/
import Spike.Lib.X64Consumer
import Spike.Lib.X64WakeClone
import Spike.Lib.Handover
import Spike.Lib.X64WakeA64
import Spike.Lib.X64WakeSrcDefs

namespace Spike.Lib.X64WakePreA

open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib.X64Consumer (Owned)
open Spike.Lib.X64WakeA64 (Cfg)
open Spike.Lib.X64.WakePh.WcClone (x21L)
open Spike.Lib.X64WakeSrcDefs (spawnTerm mainTidLbl)

/-- **The clone's address**: the `syscall` at `.Lwc_main.x21 + 46` (after
the stores, the `mfence`, the loads, the two zeroings and `movl $56`), in
executable `exe`. -/
def cloneAt (exe : _root_.Executable) : Int64 :=
  (_root_.Executable.labels exe).label x21L + 46

/-- **main's state at its `clone`** in the one-slot configuration `t`, the
source configuration `s`, the source label placement `lbl`, the layout `Λ`,
main's stack range `r0` and the child's `r1`, and the runtime facts `X` of
main's thread state there: one thread `th`, one source thread `th0`, and
- `th` at the clone's `syscall` (`cloneAt`), with no promise, asking for
  `clone(stack, tls)`, with `stack = %rsi` the top of `r1`, `tls = %r8`,
  `%r12` the worker's cell `cA` and `%rbx` main's `ThreadId` word `meW`;
- the ranges held exactly `r1` and `r0`, both for index 0, disjoint, both
  owned;
- main's frame (`wc_main`'s 80 bytes at `%rsp`) in `r0`; `%rsp` 128 bytes
  below `r0`'s top, `r0` of `thread_init`'s 16 KiB;
- `X th.st`;
- `th0` at `spawnTerm`, `c` bound to the locative of a label `l` placed at
  `cA`, and `me` to main's `ThreadId` locative (label `mainTidLbl 2`), placed
  at `meW`.

Use the projections (`ClonePre.held`, `disj`, `frame`, `spTop`); the field
order is not stable. -/
def ClonePre (Λ : Scc.Sem.Layout) (r0 r1 : Range) (X : State → Prop)
    (lbl : WeakMem.AllocLabel → Option Nat) (t : Cfg) (s : TermRun.Cfg) : Prop :=
  ∃ (th : Thread isa) (th0 : TermRun.TTh) (tls cA meW : Nat) (l : WeakMem.AllocLabel),
    t.1.threads = #[th] ∧ s.ths = #[th0] ∧
    th.st.st.2 = cloneAt th.st.exe ∧ abi.atSys th.st = true ∧ th.prom = [] ∧
    callOf abi th = some (.clone (r1.lo + r1.size) tls) ∧
    (th.st.st.1.regs.get64 .rsi).toNat = r1.lo + r1.size ∧ (th.st.st.1.regs.get64 .r8).toNat = tls ∧
    (th.st.st.1.regs.get64 .r12).toNat = cA ∧ (th.st.st.1.regs.get64 .rbx).toNat = meW ∧
    t.2.held = [(0, r1), (0, r0)] ∧ r1.Disjoint r0 ∧ Owned Λ r0 th.st ∧ Owned Λ r1 th.st ∧ X th.st ∧
    r0.lo ≤ (th.st.st.1.regs.get64 .rsp).toNat ∧ (th.st.st.1.regs.get64 .rsp).toNat + 80 ≤ r0.lo + r0.size ∧
    (th.st.st.1.regs.get64 .rsp).toNat + 128 = r0.lo + r0.size ∧ r0.size = 16384 ∧
    th0.term = spawnTerm ∧
    TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) ∧
    TermRun.evalAt th0.env (.var "me") = some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]) ∧
    th0.tidLbl = some (mainTidLbl 2) ∧
    ValRep lbl (.loc ⟨l, 0⟩ 0) cA ∧ ValRep lbl (.loc ⟨mainTidLbl 2, 0⟩ 0) meW

/-- **Every range held at the clone is main's**, one of them ending at the
child's stack top. -/
theorem ClonePre.held {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop}
    {lbl : WeakMem.AllocLabel → Option Nat} {t : Cfg} {s : TermRun.Cfg} (h : ClonePre Λ r0 r1 X lbl t s) :
    (∀ h ∈ t.2.held, h.1 = 0) ∧ (0, r1) ∈ t.2.held := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hh, -⟩ := h
  rw [hh]; simp

/-- **The child's stack range is off main's.** -/
theorem ClonePre.disj {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop}
    {lbl : WeakMem.AllocLabel → Option Nat} {t : Cfg} {s : TermRun.Cfg} (h : ClonePre Λ r0 r1 X lbl t s) :
    r1.Disjoint r0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hd, -⟩ := h
  exact hd

/-- **main's frame is in its stack range** at the clone (`wc_main`'s 80
bytes at `%rsp`), so off the child's (`ClonePre.disj`). -/
theorem ClonePre.frame {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop}
    {lbl : WeakMem.AllocLabel → Option Nat} {t : Cfg} {s : TermRun.Cfg} (h : ClonePre Λ r0 r1 X lbl t s) :
    ∃ th, t.1.threads = #[th] ∧ r0.lo ≤ (th.st.st.1.regs.get64 .rsp).toNat ∧
      (th.st.st.1.regs.get64 .rsp).toNat + 80 ≤ r0.lo + r0.size := by
  obtain ⟨th, -, -, -, -, -, ht, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h1, h2, -⟩ := h
  exact ⟨th, ht, h1, h2⟩

/-- **main's `%rsp` at the clone is 128 bytes below its stack top**, the
stack range of 16 KiB. -/
theorem ClonePre.spTop {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop}
    {lbl : WeakMem.AllocLabel → Option Nat} {t : Cfg} {s : TermRun.Cfg} (h : ClonePre Λ r0 r1 X lbl t s) :
    ∃ th, t.1.threads = #[th] ∧ (th.st.st.1.regs.get64 .rsp).toNat + 128 = r0.lo + r0.size ∧
      r0.size = 16384 := by
  obtain ⟨th, -, -, -, -, -, ht, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h1, h2, -⟩ := h
  exact ⟨th, ht, h1, h2⟩

/-- info: 'Spike.Lib.X64WakePreA.ClonePre.held' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClonePre.held

/-- info: 'Spike.Lib.X64WakePreA.ClonePre.disj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClonePre.disj

/-- info: 'Spike.Lib.X64WakePreA.ClonePre.frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClonePre.frame

/-- info: 'Spike.Lib.X64WakePreA.ClonePre.spTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClonePre.spTop

end Spike.Lib.X64WakePreA
