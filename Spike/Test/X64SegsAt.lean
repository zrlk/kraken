/-
**The x86-64 runtime segments at any return point**
(`Spike/Lib/Rt/X64SegsAt.lean`): at `ret0.w`'s cells the `.x7` corollaries
give the hand `thread_init_segW` (as `Spike/Lib/Rt/X64SegsRet0.lean` does
from `threadInit_segW`), and at `hello1.w`'s cells, whose
`scc_rt_thread_init` returns to `.x8` (a setup block), `threadInit_segWAt`
applies with its code check from `rtCodeInTi_of_okS`, where
`threadInit_segW` does not (`threadInitIn` fails there).
-/
import Spike.Lib.Rt.X64SegsAt
import Spike.Test.X64RtCode

namespace Spike.Lib.X64.Rt.SegsAtTest

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Ret0 Spike.Lib.X64.Rt
open Scc.Cert.Rt.X64 (Lays endOf)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F F0 : MachineData → Prop}

/-- The hand `thread_init_segW`, by `threadInit_segW_ofAt`. -/
example {W : Frag isa} {rS : Scc.Sem.Range} (hp : Lays exe SccCode.ret0Cells)
    (hend : endPc = endOf exe SccCode.ret0Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -248) (hhi : 8 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TiG) (hk : q.k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields q.tcb (tiBase (_root_.Executable.labels exe).label q),
      StOk ms F0 (q.tcb + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F0 exe endPc q.k0)
    (hW : ∀ i, TiW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F (StackM rS) q
      i)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m)) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (tiN (_root_.Executable.labels exe).label q .e))
      (fun s c => ∃ x,
        At exe endPc R (fun m => F m ∧ StackM rS m) (tiX (_root_.Executable.labels exe).label q x) s c) :=
  threadInit_segW_ofAt hp hend ThreadInit.ret0_threadInitIn StackTake.ret0_stackTakeIn hF hR hlo hhi hFF q hk
    hfld htk hW hRS hfit hout hFt

/-- `hello1.w`'s `scc_rt_thread_init` is one segment, its return point at
`.x8`: the code checks from `hello1`'s `rtCodeOkS`. -/
example {W : Frag isa} {rS : Scc.Sem.Range} (hp : Lays exe SccCode.hello1Cells)
    (hend : endPc = endOf exe SccCode.hello1Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -248) (hhi : 8 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TiG) (hk : q.k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields q.tcb (tiBase (_root_.Executable.labels exe).label q),
      StOk ms F0 (q.tcb + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F0 exe endPc q.k0)
    (hW : ∀ i, TiWAt W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F (StackM rS)
      q x8L i)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m)) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (tiNAt (_root_.Executable.labels exe).label q x8L .e))
      (fun s c => ∃ x,
        At exe endPc R (fun m => F m ∧ StackM rS m) (tiX (_root_.Executable.labels exe).label q x) s c) :=
  have hc := rtCodeInTi_of_okS Test.hello1_rtCodeOkS
  threadInit_segWAt hp hend hc.ti hc.take hF hR hlo hhi hFF q hk hfld htk hW hRS hfit hout hFt

/-- The `.x7` check fails on `hello1.w`: only the `At` form applies there. -/
example : ThreadInit.threadInitIn SccCode.hello1Cells = false := by decide +kernel

end Spike.Lib.X64.Rt.SegsAtTest
