/-
**`print`'s byte count at the child's call on x86-64** (the twin of `Spike/Lib/HelloChildX1.lean`; the child
premise `hx1` of `Hello.SegR.ChildPrem`): at main's `clone` the slice's pair `m`, `n` is `2`, `13` in `%r13`,
`%r14` (`X64HelloPreA.sl_clone`, the packet's words); the worker's entry block puts `min n (8 m)` in `%rsi` at
`print`'s call (`Body.wkC_rsi`, from the frame cells `-40`, `-32` the entry invariant `wkJ` fills with those
words), so `%rsi = 13 = printN 13 2`.

- `hx1_clone`: `ChildPrem.hx1` at the clone's words `wordsX th` (at `ClonePreH` and main's one thread; any entry
  control, thread pointer, caller cells, stack pointer, flags and packet words).

## Differences from the AArch64 version

- The pair is in main's `%r13`, `%r14` (AArch64 `x11`, `x12`), the count in `%rsi` (AArch64 `x1`), read from the
  frame cells `-32`, `-40` (AArch64 `-80`, `-72`).
- x86-64's `wkJ` takes the stack pointer `sp` and `Body.wkC` the head's flags `fl` (the multiply leaves them
  undefined); `hx1_clone` holds at every `sp` and `fl`, `ChildPrem.hx1`'s form.
- `ClonePreH` takes no label prefix.
-/
import Spike.Lib.X64HelloChildWords
import Spike.Lib.X64HelloChildX
import Spike.Lib.X64HelloWorkerSeg
import Spike.Lib.X64HelloWorkerBody

namespace Spike.Lib.X64HelloChildX1

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64WakeA64 (Cfg)
open Spike.Lib.X64HelloPreA (ClonePreH)
open Spike.Lib.PrintSrc (printN)
open Spike.Lib.X64.Flow.Worker.Hello.Wk (wkJ)
open Spike.Lib.X64.Flow.Worker.Hello.SegR (wordsX)

/-- **`ChildPrem.hx1` at the clone** (module doc): at any entry control `c0`, caller cells, stack pointer, flags
and thread pointer. -/
theorem hx1_clone {Λ : Scc.Sem.Layout} {r0 r1 : Scc.Sem.Range} {X : State → Prop}
    {lbl : WeakMem.AllocLabel → Option Nat} {t : Cfg} {s : TermRun.Cfg} (h : ClonePreH Λ r0 r1 X lbl t s)
    {th : Thread isa} (hth : t.1.threads = #[th]) (lab : Label → Int64) (c0 : Spike.Lib.Ctl)
    (tp rbp ra sp : BitVec 64) (σ : Spike.Lib.X64.AS) (fl : StatusFlags)
    (hJ : wkJ c0 (wordsX th) rbp ra tp sp σ c0) :
    ((Spike.Lib.X64.Flow.Worker.Body.wkC lab σ fl).regs.get64 .rsi).toNat = printN 13 2 := by
  obtain ⟨h13, h14⟩ := Spike.Lib.X64HelloPreA.sl_clone h hth
  obtain ⟨-, -, -, h32, h40, -⟩ := hJ
  rw [Spike.Lib.X64.Flow.Worker.Body.wkC_rsi, h40, h32]
  show min (th.st.st.1.regs.get64 .r14).toNat ((th.st.st.1.regs.get64 .r13) * 8#64).toNat = printN 13 2
  rw [h14, BitVec.toNat_mul, h13]
  rfl

end Spike.Lib.X64HelloChildX1

/-- info: 'Spike.Lib.X64HelloChildX1.hx1_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloChildX1.hx1_clone
