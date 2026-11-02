/-
**hello.w's worker segment's premises and data** (x86-64; the twin of `Spike/Lib/A64HelloWorkerSegP.lean`): the
premises the spawned child's segment asks for at a packet (`ChildPrem`), and the data it runs at (`ChildD`, its
region facts `ChildD.ok`).

- `ChildPrem`: the child segment's premises; `ChildD`: its data; `ChildD.ok`: the region's facts.

## Differences from the AArch64 version

- The stacks' bounds are `Ret0.LimOk` at the thread pointer's `tcb` word `tp + 8` (the shapes
  `Child.seg_thrWorkerSX` and `Wk.seg_wcWorkerSX` ask for): `hlimT` below the thread worker's frame (its stack
  pointer `sp0 - 8`, frame 64), `hlimW` below `wc_worker`'s (frame 80). The thread worker's load of its `tcb`
  word (`hT`) and its ownership at `.x13` (`hown`) are premises too (AArch64: inside `hlimT`'s shape and the
  thread worker's tail).
- The count register at `print`'s call (`hx1`) is `%rsi` after the `.entry` blocks at every flag value
  (`Body.wkC … σ fl`), at every frame `sp` of `wkJ`.
- `StOk` takes no executable or end (x86-64's `Ret0.StOk`).
- `ChildD.ok` has no alignment fact; its bounds are `R.lo ≤ -264` (the thread worker's re-based region
  `thrR R` at `-256`) and `0 ≤ R.hi`.
- `childP`, `seg_childP`, `SegTCS.of_imp` and `childP_of_clone` are not twinned.
-/
import Spike.Lib.X64HelloWorkerSegR

namespace Spike.Lib.X64.Flow.Worker.Hello.SegR

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Worker
open Spike.Lib.X64.Flow.Ret0 (StOk LdOk LimOk)
open Spike.Lib.X64HelloSplit (wcP)
open Spike.Lib.PrintSrc (printN)
open Spike.Lib.X64.Flow.Worker.Hello.Child (Words wcJE)
open Spike.Lib.X64.Flow.Worker.Hello.Wk (wkJ)

/-- **The child segment's premises** at a frame condition `F`, the machine's words `w`, the thread pointer `tp`,
the child's stack top `sp0`, the packet's words `w0 .. w4` and the slice's `n` bytes in `m` words. Not produced
here: discharged at the clone's data by the spawn's proof. -/
structure ChildPrem (exe : _root_.Executable) (endPc : Int64) (kp : Nat) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : List TermRun.Frame → MemSide isa) (F : MachineData → Prop) (w : Words) (tp sp0 : BitVec 64)
    (w0 w1 w2 w3 w4 : TermRun.Word) (n m : Nat) : Prop where
  hlimT : LimOk (ms []) F (tp + (8 : Int64).toBitVec) (sp0 - 8#64 - 8#64 - (64 : Int64).toBitVec)
  hT : LdOk (ms []) F tp
  hown : OwnAt (ms []) exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.x13") tp tp
  hlimW : ∀ rbp ra σ c, wcJE (wcP w0 w1 w2 w3 w4) w rbp ra tp σ c → σ.regs.rsp.toBitVec = sp0 - 8#64 - 80#64 →
      LimOk (ms []) F (tp + (8 : Int64).toBitVec) (σ.regs.rsp.toBitVec - 8#64 - (80 : Int64).toBitVec)
  hm : w.w2.toNat * 8 < 2 ^ 63
  hx1 : ∀ rbp ra sp σ fl, wkJ (wcP w0 w1 w2 w3 w4) w rbp ra tp sp σ (wcP w0 w1 w2 w3 w4) →
      ((Body.wkC (_root_.Executable.labels exe).label σ fl).regs.get64 .rsi).toNat = printN n m
  hwm : w1.val = .num m
  hm0 : m ≠ 0
  hwn : w2.val = .num n
  hsvc : SvcX exe endPc kp lbl ms F w tp w0 w1 w2 w3 w4 n m
  hdm : ∀ m, F m → Mem.loadInt m.dmem w.w4 8 = none
  hv : Scc.Sem.ValRep lbl w3.val w.w4.toNat
  htag : ∃ sa, w3.val = .loc sa 0
  hvu : Scc.Sem.ValRep lbl w4.val w.w5.toNat
  /- The packet's slice words: the buffer locative at `w0`, the pair's `m`, `n` at `w2`, `w3`. -/
  hv0 : Scc.Sem.ValRep lbl w0.val w.w0.toNat
  hv1 : Scc.Sem.ValRep lbl w1.val w.w2.toNat
  hv2 : Scc.Sem.ValRep lbl w2.val w.w3.toNat
  hS : StOk (ms []) F (w.w5 + 16#64) 1#64
  htp4 : (w.w5 + 16#64).toNat % 4 = 0
  hSx : StOk (ms []) F (tp + 24#64) 1#64
  habt : ∀ fr s, s.exe = exe → s.st.2 = (_root_.Executable.labels exe).label Abort.write.exit →
      (ms [fr]).abortAt s

/-- **The child segment's data**: its region and frame condition, the machine's six words, the thread pointer,
the stack's top, the packet's type and five words, the slice's bytes and words. -/
structure ChildD where
  R : Region
  F : MachineData → Prop
  w : Words
  tp : BitVec 64
  sp0 : BitVec 64
  T : Ty
  w0 : TermRun.Word
  w1 : TermRun.Word
  w2 : TermRun.Word
  w3 : TermRun.Word
  w4 : TermRun.Word
  n : Nat
  m : Nat

/-- The region's facts (the child's segment's `hF`, `hR`, `hlo`, `hhi`). -/
def ChildD.ok (d : ChildD) : Prop :=
  FStable d.R d.F ∧ d.R.OK ∧ d.R.lo ≤ -264 ∧ 0 ≤ d.R.hi

end Spike.Lib.X64.Flow.Worker.Hello.SegR
