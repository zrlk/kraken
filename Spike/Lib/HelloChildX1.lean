/-
**`print`'s byte count at the child's call** (AArch64; `Hello.SegR.ChildPrem`'s `hx1`): at
main's `clone` the slice's pair `m`, `n` is `2`, `13` in `x11`, `x12` (`HelloPreA.sl_clone`, the packet's words); the
worker's entry block puts `min n (8 m)` in `x1` at `print`'s call (`WorkerBody.wkC_x1`, from the frame cells
`-80`, `-72` the entry invariant `wkJ` fills with those words), so `x1 = 13 = printN 13 2`.

- `hx1_clone`: `ChildPrem.hx1` at the clone's words `wordsX th`, in `HelloRootCP.hCP_root`'s `hx1` form (at
  `ClonePreH` and main's one thread; any entry control, thread pointer and packet words).
-/
import Spike.Lib.HelloChildWords
import Spike.Lib.A64HelloChildX

namespace Spike.Lib.HelloChildX1

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.WakeA64 (Cfg)
open Spike.Lib.HelloPreA (ClonePreH)
open Spike.Lib.PrintSrc (printN)
open Spike.Lib.A64.Flow.Worker.Hello.Wk (wkJ)
open Spike.Lib.A64.Flow.Worker.Hello.SegR (wordsX)

/-- **`ChildPrem.hx1` at the clone** (module doc): at any entry control `c0`, caller cells and thread pointer. -/
theorem hx1_clone {pfx : String} {Λ : Scc.Sem.Layout} {r0 r1 : Scc.Sem.Range} {X : State → Prop}
    {lbl : WeakMem.AllocLabel → Option Nat} {t : Cfg} {s : TermRun.Cfg} (h : ClonePreH pfx Λ r0 r1 X lbl t s)
    {th : Thread isaLSE2} (hth : t.1.threads = #[th]) (lab : Label → Int64) (c0 : Spike.Lib.Ctl)
    (tp x29 ra : BitVec 64) (σ : Spike.Lib.A64.Flow.AS) (hJ : wkJ c0 (wordsX th) x29 ra tp σ c0) :
    (Spike.Lib.A64.Flow.Worker.Body.wkC lab σ).regs.X1.toBitVec.toNat = printN 13 2 := by
  obtain ⟨h11, h12⟩ := Spike.Lib.HelloPreA.sl_clone h hth
  obtain ⟨-, -, -, h80, h72, -⟩ := hJ
  rw [Spike.Lib.A64.Flow.Worker.Body.wkC_x1, h80, h72]
  show min th.st.st.1.regs.X12.toBitVec.toNat (th.st.st.1.regs.X11.toBitVec * 8#64).toNat = printN 13 2
  rw [h12, BitVec.toNat_mul, h11]
  rfl

end Spike.Lib.HelloChildX1

/-- info: 'Spike.Lib.HelloChildX1.hx1_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloChildX1.hx1_clone
