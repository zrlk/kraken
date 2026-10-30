/-
**wake.w on AArch64: main's state at its `clone`** (the
pre-spawn half): `ClonePre`, the interface between the one-thread consumer
of main's code up to its `clone` (`Wpre`, this branch) and the clone's
row, error path and spawn (`Spike.Lib.WakeClone`; the spawn
obligation).

At main's `svc #0` (the node `cloneN`, `.L21_wc_main.sp6` plus 13
instructions: `cloneAt`) the one-slot configuration has one thread, at the
system call, asking for `clone(stack, tls)` with `stack = x1` the child's
stack top (`thread_init`'s result: the top of the range `r1` the second
take holds) and `tls = x3` the child's TCB (`alloc_tcb`'s result); `x9`
the published cell's address and `x10` main's `ThreadId` word, the worker's
two arguments; every range held is held for index 0 (so the extra slot's
index holds none, `Pre1.held`); the source thread at `main`'s `spawn`
term with `c` bound to the published cell and `me` to main's `ThreadId`.

The thread's promises are empty there (`th.prom = []`, which the clone's row
and the spawn need: `Step.spawn` / `CertAfter`); the consumer gets it from
`CertOkC` (a certified run ends at a `clone`:
`Spike.Lib.Handover.prom_nil_of_clone`).

The clone's address is named from `wc_main`'s label prefix `pfx` (the
compiler numbers local labels per program: `.L21_wc_main` in wake.w), as
`Spike.Lib.A64Relabel`'s blocks are.

- `cloneAt`: the clone's pc in an executable, at `wc_main`'s label prefix.
- `spawnTerm`: main's term at the `spawn`.
- `ClonePre`: the interface; `ClonePre.held`: every range held is main's;
  `ClonePre.disj`, `ClonePre.frame`, `ClonePre.spTop`: main's stack at the clone.
-/
import Spike.Lib.WakePre
import Spike.Lib.A64WakeLabels

namespace Spike.Lib.WakePreA

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib.WakeA64 Spike.Lib.WakeT1
open Spike.Lib.A64Consumer (Owned)

/-- **The clone's address**: the `svc #0` after `scc_rt_thread_init`'s return
point `pfx ++ ".sp6"` (`pfx` `wc_main`'s label prefix, `.L21_wc_main` in
wake.w), 13 instructions on (`str`, `ldr`, `str`, `dmb`, four `ldr`, `movz`,
`movk`, three `movz`), in executable `exe`. -/
def cloneAt (pfx : String) (exe : _root_.Executable) : Int64 :=
  (_root_.Executable.labels exe).label (pfx ++ ".sp6") + Int64.ofNat (4 * 13)

/-- **main's term at the `spawn`** (wake.w's `main` after `z`, `o`, `c`,
`p`): `let t = spawn worker p in tail waitLoop c`. -/
def spawnTerm : CoreTerm.Expr :=
  .let_ "t"
    (.spawn "worker" (.var "p")
      (.prod (.ptr .pub .int) .tid) [])
    (.tail "waitLoop" [] (.var "c") [])

/-- `spawnTerm` is `main`'s body after `z`, `o`, `c`, `p`. -/
theorem main_body : (wakeSrc.find? (·.name = "main")).map (·.body) =
    some (.let_ "z" (.zero .int) (.let_ "o" (.new (.var "z")) (.let_ "c" (.publish (.var "o"))
      (.let_ "p" (.pair (.var "c") (.var "me")) spawnTerm)))) := rfl

/-- **main's state at its `clone`** in the one-slot configuration `t`, the
source configuration `s`, the source label placement `lbl`, `wc_main`'s
label prefix `pfx`, the layout `Λ`, main's stack range `r0` and the child's
`r1` (the second take's), and the runtime facts `X` of main's thread state
there (`tls` the TCB, `NthOk`, `TcbArea`, `stack_next`; stated in
`Spike/Lib/Rt/A64RtPreChild.lean`): one thread `th`, one source thread `th0`,
and
- `th` at the clone's `svc` (`cloneAt pfx`), with no promise, asking for
  `clone(stack, tls)`, with `stack = x1` the top of `r1`, `tls = x3`, `x9`
  the worker's cell `cA` and `x10` main's `ThreadId` word `meW`;
- the ranges held exactly `r1` and `r0`, both for index 0, disjoint (the
  second take's range is `Kernel.fresh`: off every range held), both owned;
- main's frame (`wc_main`'s 80 bytes at `sp`) in `r0`; `sp` 128 bytes
  below `r0`'s top (`scc_rt_start` sets `sp` to the top, `scc_rt_main`
  takes 48 bytes, `wc_main` 80), `r0` of `thread_init`'s 16 KiB;
- `X th.st`;
- `th0` at `spawnTerm`, `c` bound to the locative of a label `l` placed at
  `cA`, and `me` to main's `ThreadId` locative (label `mainTidLbl 2`), placed
  at `meW`.

Use the projections (`ClonePre.held`, `disj`, `frame`, `spTop`); the field
order is not stable. -/
def ClonePre (pfx : String) (Λ : Scc.Sem.Layout) (r0 r1 : Range) (X : State → Prop)
    (lbl : WeakMem.AllocLabel → Option Nat) (t : Cfg) (s : TermRun.Cfg) : Prop :=
  ∃ (th : Thread isaLSE2) (th0 : TermRun.TTh) (tls cA meW : Nat) (l : WeakMem.AllocLabel),
    t.1.threads = #[th] ∧ s.ths = #[th0] ∧
    th.st.st.2 = cloneAt pfx th.st.exe ∧ abi.atSys th.st = true ∧ th.prom = [] ∧
    callOf abi th = some (.clone (r1.lo + r1.size) tls) ∧
    (th.st.st.1.regs.getXReg .X1).toNat = r1.lo + r1.size ∧ (th.st.st.1.regs.getXReg .X3).toNat = tls ∧
    (th.st.st.1.regs.getXReg .X9).toNat = cA ∧ (th.st.st.1.regs.getXReg .X10).toNat = meW ∧
    t.2.held = [(0, r1), (0, r0)] ∧ r1.Disjoint r0 ∧ Owned Λ r0 th.st ∧ Owned Λ r1 th.st ∧ X th.st ∧
    r0.lo ≤ th.st.st.1.regs.SP.toNat ∧ th.st.st.1.regs.SP.toNat + 80 ≤ r0.lo + r0.size ∧
    th.st.st.1.regs.SP.toNat + 128 = r0.lo + r0.size ∧ r0.size = 16384 ∧
    th0.term = spawnTerm ∧
    TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) ∧
    TermRun.evalAt th0.env (.var "me") = some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]) ∧
    th0.tidLbl = some (mainTidLbl 2) ∧
    ValRep lbl (.loc ⟨l, 0⟩ 0) cA ∧ ValRep lbl (.loc ⟨mainTidLbl 2, 0⟩ 0) meW

/-- **Every range held at the clone is main's**, one of them ending at the
child's stack top. -/
theorem ClonePre.held {pfx : String} {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop}
    {lbl : WeakMem.AllocLabel → Option Nat} {t : Cfg} {s : TermRun.Cfg} (h : ClonePre pfx Λ r0 r1 X lbl t s) :
    (∀ h ∈ t.2.held, h.1 = 0) ∧ (0, r1) ∈ t.2.held := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hh, -⟩ := h
  rw [hh]; simp

/-- **The child's stack range is off main's** (the second take's range is
fresh: `Kernel.fresh` asks it off every range held). -/
theorem ClonePre.disj {pfx : String} {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop}
    {lbl : WeakMem.AllocLabel → Option Nat} {t : Cfg} {s : TermRun.Cfg} (h : ClonePre pfx Λ r0 r1 X lbl t s) :
    r1.Disjoint r0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hd, -⟩ := h
  exact hd

/-- **main's frame is in its stack range** at the clone (`wc_main`'s 80
bytes at `sp`), so off the child's (`ClonePre.disj`). -/
theorem ClonePre.frame {pfx : String} {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop}
    {lbl : WeakMem.AllocLabel → Option Nat} {t : Cfg} {s : TermRun.Cfg} (h : ClonePre pfx Λ r0 r1 X lbl t s) :
    ∃ th, t.1.threads = #[th] ∧ r0.lo ≤ th.st.st.1.regs.SP.toNat ∧
      th.st.st.1.regs.SP.toNat + 80 ≤ r0.lo + r0.size := by
  obtain ⟨th, -, -, -, -, -, ht, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h1, h2, -⟩ := h
  exact ⟨th, ht, h1, h2⟩

/-- **main's `sp` at the clone is 128 bytes below its stack top**
(`scc_rt_main`'s 48 and `wc_main`'s 80), the stack range of 16 KiB. -/
theorem ClonePre.spTop {pfx : String} {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop}
    {lbl : WeakMem.AllocLabel → Option Nat} {t : Cfg} {s : TermRun.Cfg} (h : ClonePre pfx Λ r0 r1 X lbl t s) :
    ∃ th, t.1.threads = #[th] ∧ th.st.st.1.regs.SP.toNat + 128 = r0.lo + r0.size ∧ r0.size = 16384 := by
  obtain ⟨th, -, -, -, -, -, ht, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h1, h2, -⟩ := h
  exact ⟨th, ht, h1, h2⟩

end Spike.Lib.WakePreA
