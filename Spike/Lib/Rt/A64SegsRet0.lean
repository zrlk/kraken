/-
**Oracle of the parametric callee segments on `ret0`**
(`Spike/Lib/Rt/A64Segs.lean`): the hand `alloc_tcb_segW`, `stack_take_segW`
and `thread_init_segW` (`Spike/Lib/A64Ret0.lean`) are the generic theorems at
`ret0Prog` with the hand code checks; each statement below is the hand one,
proved by the generic theorem.
-/
import Spike.Lib.Rt.A64Segs
import Spike.Lib.Rt.A64MainRet0

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Ret0
open Scc.Cert.Rt.A64 (Lays endOf)

section Oracle

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F F0 : MachineData → Prop}

example {W : Frag isaLSE2} {K : State → State → Prop} (hp : Lays exe SccCode.ret0Prog)
    (hend : endPc = endOf exe SccCode.ret0Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -192) (hhi : 0 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TcbG) (hn : q.n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F0 exe endPc (pinA (_root_.Executable.labels exe).label + q.n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F0 exe endPc q.n0) (hW : ∀ i, TcbW W K exe endPc R F q i) :
    SegW W K p lbl ms (At exe endPc R F (tcbN (_root_.Executable.labels exe).label q .e))
      (fun s c => ∃ x, At exe endPc R F (tcbX (_root_.Executable.labels exe).label q x) s c) :=
  allocTcb_segW hp hend AllocTcb.ret0_allocTcbIn hF hR hal hlo hhi hFF q hn hhdr htcb hW

example {W : Frag isaLSE2} {rS : Scc.Sem.Range} (hp : Lays exe SccCode.ret0Prog)
    (hend : endPc = endOf exe SccCode.ret0Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -208) (hhi : 0 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TakeG) (hk : q.k0.toNat + 16384 ≤ 536870912)
    (htk : TakeOk ms F0 exe endPc q.k0)
    (hW : ∀ i, TakeW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F (StackM rS) q i)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m)) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (takeNG (_root_.Executable.labels exe).label q false .e))
      (fun s c => ∃ x, At exe endPc R (fun m => F m ∧ StackM rS m)
        (takeXG (_root_.Executable.labels exe).label q true x) s c) :=
  stackTake_segW hp hend StackTake.ret0_stackTakeIn hF hR hal hlo hhi hFF q hk htk hW hRS hfit hout hFt

example {W : Frag isaLSE2} {rS : Scc.Sem.Range} (hp : Lays exe SccCode.ret0Prog)
    (hend : endPc = endOf exe SccCode.ret0Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -256) (hhi : 0 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TiG) (hk : q.k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields q.tcb (tiBase (_root_.Executable.labels exe).label q),
      StOk ms F0 exe endPc (q.tcb + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F0 exe endPc q.k0)
    (hW : ∀ i, TiW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F (StackM rS) q i)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m)) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (tiN (_root_.Executable.labels exe).label q .e))
      (fun s c => ∃ x,
        At exe endPc R (fun m => F m ∧ StackM rS m) (tiX (_root_.Executable.labels exe).label q x) s c) :=
  threadInit_segW hp hend ThreadInit.ret0_threadInitIn ret0_tiSpIn StackTake.ret0_stackTakeIn hF hR hal hlo hhi
    hFF q hk hfld htk hW hRS hfit hout hFt

example {W : Frag isaLSE2} {K : State → State → Prop} (hp : Lays exe SccCode.ret0Prog)
    (hend : endPc = endOf exe SccCode.ret0Prog) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ 0) (hhi : 0 ≤ R.hi) (c0 : Ctl)
    (hW : BlkW W K exe endPc R F (entryN (_root_.Executable.labels exe).label c0) entryB) :
    SegW W K p lbl ms (At exe endPc R F (entryN (_root_.Executable.labels exe).label c0))
      (At exe endPc R F (startN0 (_root_.Executable.labels exe).label c0)) :=
  entry_segW' hp hend ret0_entryIn hF hR hal hlo hhi c0 hW

example {W : Frag isaLSE2} {K : State → State → Prop} (hp : Lays exe SccCode.ret0Prog)
    (hend : endPc = endOf exe SccCode.ret0Prog)
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -240) (hhi : 0 ≤ R.hi) (n0 : BitVec 64) (c0 : Ctl) (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F exe endPc (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F exe endPc n0) (hW : Sp0W W K exe endPc R F n0 c0) :
    SegW W K p lbl ms (At exe endPc R F (startN0 (_root_.Executable.labels exe).label c0))
      (At exe endPc R F (Ret0.startN2 (_root_.Executable.labels exe).label n0 c0)) :=
  startSp2_segW hp hend ret0_startCallIn ret0_startIn AllocTcb.ret0_allocTcbIn hK hF hR hal hlo hhi n0 c0 hn hhdr
    htcb hW

example {W : Frag isaLSE2} {rS : Scc.Sem.Range} (hp : Lays exe SccCode.ret0Prog)
    (hend : endPc = endOf exe SccCode.ret0Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi)
    (n0 k0 : BitVec 64) (c0 : Ctl) (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk ms F exe endPc (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F exe endPc k0)
    (hW : Sp2W W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F rS n0 k0 c0)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m)) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (Ret0.startN2 (_root_.Executable.labels exe).label n0 c0))
      (At exe endPc R (fun m => F m ∧ StackM rS m) (startN5 (_root_.Executable.labels exe).label
        (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0)) :=
  startSp2Sw_segW hp hend ret0_startTailIn ThreadInit.ret0_threadInitIn ret0_tiSpIn StackTake.ret0_stackTakeIn
    hF hR hal hlo hhi n0 k0 c0 hk hfld htk hW hRS hfit hout hFt

/-- `scc_rt_main`'s and `wc_main`'s obligations after the switch on `ret0`
are the generic ones. -/
theorem swUW_ofW {W : Frag isaLSE2} {K : State → State → Prop} {rS : Scc.Sem.Range} {tcb top : BitVec 64}
    {c0 : Ctl} (hp : Lays exe SccCode.ret0Prog) (hend : endPc = endOf exe SccCode.ret0Prog)
    (hW : SwW W K exe endPc R F ms rS tcb top c0) :
    SwUW W K p lbl exe endPc R F ms rS tcb top c0 80 ret0MC 32 32 (ret0Post c0) :=
  ⟨hW.sw, hW.blk, fun v => mainUW_ofW (hW.main v), fun v => ret0_userCallW hp hend (hW.main v).wc⟩

example {W : Frag isaLSE2} {K : State → State → Prop} {rS : Scc.Sem.Range}
    (hp : Lays exe SccCode.ret0Prog) (hend : endPc = endOf exe SccCode.ret0Prog)
    (hK : ms.K = some Scc.Sem.A64.abi) (tcb top : BitVec 64) (c0 : Ctl)
    (h16 : top.toNat % 16 = 0) (hok : (swR top (-80) 0).OK)
    (hFS : ∀ m, F m → StackM rS m) (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (hsub : ∀ k, (swR top (-80) 0).Off k → ((swR top (-80) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR top (-80) 0).addr k).toNat ∧ rS.contains (((swR top (-80) 0).addr k).toNat + 7))
    (hfit : (limA (UInt64.ofBitVec tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec tcb)).toNat : Int) + 8 ≤ top.toNat + -80 ∨
      (top.toNat : Int) + 0 ≤ (limA (UInt64.ofBitVec tcb)).toNat)
    (hlimM : LimOk ms F exe endPc (limA (UInt64.ofBitVec tcb)) (top - (48 : Int64).toBitVec))
    (hlimW : LimOk ms F exe endPc (limA (UInt64.ofBitVec tcb)) (top - (48 : Int64).toBitVec - (32 : Int64).toBitVec))
    (hexit : ∀ R' F' s, At exe endPc R' F' (mainNX (_root_.Executable.labels exe).label) s c0 → ¬ ms.abortAt s →
      MainExit p ms s c0 42)
    (hW : SwW W K exe endPc R F ms rS tcb top c0)
    {Q : Frag isaLSE2} :
    SegW W K p lbl ms (At exe endPc R F (startN5 (_root_.Executable.labels exe).label tcb top c0)) Q :=
  startSwitchU_segW hp hend ret0_startTailIn ret0_mainUIn (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hK tcb top c0 h16 hok hFS hfitS hsub hfit hout hlimM hlimW
    (fun R' F' s c v ⟨hc, hv⟩ hAt hab => by subst hc hv; exact hexit R' F' s hAt hab) (swUW_ofW hp hend hW)

/-- **The hand `start_segW` from the generic `startU_segW`**: the same
statement, at `ret0MC`, `L = 80`, `D = ZU = 32`. -/
theorem start_segW_ofU {W : Frag isaLSE2} {rS : Scc.Sem.Range} (hp : Lays exe SccCode.ret0Prog)
    (hend : endPc = endOf exe SccCode.ret0Prog)
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (n0 k0 : BitVec 64) (c0 : Ctl)
    (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F exe endPc (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F exe endPc n0)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk ms F exe endPc (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F exe endPc k0)
    (h16 : (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat % 16 = 0)
    (hok : (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-80) 0).OK)
    (hsub : ∀ k, (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-80) 0).Off k →
      ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-80) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-80) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-80) 0).addr k).toNat + 7))
    (hfit : (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat : Int) + 8 ≤
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat + -80 ∨
      ((stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat : Int) + 0 ≤
        (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat)
    (hlimM : LimOk ms F exe endPc (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - (48 : Int64).toBitVec))
    (hlimW : LimOk ms F exe endPc (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - (48 : Int64).toBitVec - (32 : Int64).toBitVec))
    (hexit : ∀ R' F' s, At exe endPc R' F' (mainNX (_root_.Executable.labels exe).label) s c0 → ¬ ms.abortAt s →
      MainExit p ms s c0 42)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hW : StartAllW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F ms rS n0 k0 c0)
    {Q : Frag isaLSE2} :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (startN0 (_root_.Executable.labels exe).label c0)) Q :=
  startU_segW hp hend ret0_startCallIn ret0_startIn AllocTcb.ret0_allocTcbIn ret0_startTailIn
    ThreadInit.ret0_threadInitIn ret0_tiSpIn StackTake.ret0_stackTakeIn ret0_mainUIn (by decide) (by decide)
    (by decide) (D := 32) (ZU := 32) (by decide) (by decide) (by decide) hK hF hR hal hlo hhi n0 k0 c0 hn hhdr htcb
    hk hfld htk h16 hok hsub hfit hout hlimM hlimW
    (fun R' F' s c v ⟨hc, hv⟩ hAt hab => by subst hc hv; exact hexit R' F' s hAt hab) hRS hfitS houtS hFt
    ⟨hW.s1, hW.s2, swUW_ofW hp hend hW.s3⟩

end Oracle

end Spike.Lib.A64.Rt
