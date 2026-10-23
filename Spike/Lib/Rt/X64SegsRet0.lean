/-
**Oracle of the parametric x86-64 runtime segments on `ret0`**
(`Spike/Lib/Rt/X64Segs.lean`): the hand `alloc_tcb_segW`,
`stack_take_segW`, `thread_init_segW`, `start_x0_segW`, `start_x1_sw_segW`,
`start_x0_sw_segW`, `start_switch_segW` and `start_segW`
(`Spike/Lib/X64Ret0.lean`) are the generic theorems at `ret0Cells` with the
hand code checks; each statement below is the hand one, proved by the
generic theorem. The x86-64 twin of `Spike/Lib/Rt/A64SegsRet0.lean`.

- `swUW_ofW`: the hand obligations after the switch (`SwW`) give the generic
  ones at `ret0MC`, `L = 80`, `D = 24`, `ZU = 16`; the user function's
  interface at every stronger frame condition comes from `wc_main`'s
  obligations by `WcW.mono` and `ret0_userCallW`.
-/
import Spike.Lib.Rt.X64Segs
import Spike.Lib.Rt.X64MainRet0

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Ret0
open Scc.Cert.Rt.X64 (Lays endOf)

section Oracle

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F F0 : MachineData → Prop}

/-- The hand `alloc_tcb_segW`, by the generic theorem. -/
example {W : Frag isa} {K : State → State → Prop} (hp : Lays exe SccCode.ret0Cells)
    (hend : endPc = endOf exe SccCode.ret0Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -184) (hhi : 8 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TcbG) (hn : q.n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F0 (pinA (_root_.Executable.labels exe).label + q.n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F0 exe endPc q.n0) (hW : ∀ i, TcbW W K exe endPc R F q i) :
    SegW W K p lbl ms (At exe endPc R F (tcbN (_root_.Executable.labels exe).label q .e))
      (fun s c => ∃ x, At exe endPc R F (tcbX (_root_.Executable.labels exe).label q x) s c) :=
  allocTcb_segW hp hend AllocTcb.ret0_allocTcbIn hF hR hlo hhi hFF q hn hhdr htcb hW

/-- The hand `stack_take_segW`, by the generic theorem. -/
example {W : Frag isa} {rS : Scc.Sem.Range} (hp : Lays exe SccCode.ret0Cells)
    (hend : endPc = endOf exe SccCode.ret0Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -200) (hhi : 8 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TakeG) (hk : q.k0.toNat + 16384 ≤ 536870912)
    (htk : TakeOk ms F0 exe endPc q.k0)
    (hW : ∀ i, TakeW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F (StackM rS)
      q i)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m)) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (takeNG (_root_.Executable.labels exe).label q false .e))
      (fun s c => ∃ x, At exe endPc R (fun m => F m ∧ StackM rS m)
        (takeXG (_root_.Executable.labels exe).label q true x) s c) :=
  stackTake_segW hp hend StackTake.ret0_stackTakeIn hF hR hlo hhi hFF q hk htk hW hRS hfit hout hFt

/-- The hand `thread_init_segW`, by the generic theorem. -/
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
  threadInit_segW hp hend ThreadInit.ret0_threadInitIn StackTake.ret0_stackTakeIn hF hR hlo hhi hFF q hk
    hfld htk hW hRS hfit hout hFt

/-- The hand `start_x0_segW`, by the generic theorem. -/
example {W : Frag isa} {K : State → State → Prop} (hp : Lays exe SccCode.ret0Cells)
    (hend : endPc = endOf exe SccCode.ret0Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -232) (hhi : 0 ≤ R.hi) (n0 : BitVec 64) (c0 : Ctl) (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F exe endPc n0) (hW : St0W W K exe endPc R F n0 c0) :
    SegW W K p lbl ms (At exe endPc R F (startN0 (_root_.Executable.labels exe).label c0))
      (At exe endPc R F (startN2 (_root_.Executable.labels exe).label n0 c0)) :=
  startX0_segW hp hend ret0_startCallIn ret0_startIn AllocTcb.ret0_allocTcbIn hK hF hR hlo hhi n0 c0 hn hhdr
    htcb hW

/-- The hand `start_x1_sw_segW`, by the generic theorem. -/
example {W : Frag isa} {K : State → State → Prop} (hp : Lays exe SccCode.ret0Cells)
    (hend : endPc = endOf exe SccCode.ret0Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (n0 k0 : BitVec 64) (c0 : Ctl)
    (hfs : BlkW W K exe endPc R F (startN3 (_root_.Executable.labels exe).label n0 k0 c0) startFs)
    (hsys : NodeW W K exe endPc R F
      (startN4 (_root_.Executable.labels exe).label (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0))
    (hsw : BlkW W K exe endPc R F
      (startN5 (_root_.Executable.labels exe).label (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0) startSw) :
    SegW W K p lbl ms (At exe endPc R F (startN3 (_root_.Executable.labels exe).label n0 k0 c0))
      (At exe endPc R F (startN6 (_root_.Executable.labels exe).label
        (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0)) :=
  startX1Sw_segW hp hend ret0_startTailIn hK hF hR hlo hhi n0 k0 c0 hfs hsys hsw

/-- The hand `start_x0_sw_segW`, by the generic theorem. -/
example {W : Frag isa} {rS : Scc.Sem.Range} (hp : Lays exe SccCode.ret0Cells)
    (hend : endPc = endOf exe SccCode.ret0Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -296) (hhi : 8 ≤ R.hi)
    (n0 k0 : BitVec 64) (c0 : Ctl) (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk ms F (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F exe endPc k0)
    (hW : X0W W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F rS n0 k0 c0)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m)) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (startN2 (_root_.Executable.labels exe).label n0 c0))
      (At exe endPc R (fun m => F m ∧ StackM rS m) (startN6 (_root_.Executable.labels exe).label
        (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0)) :=
  startX0Sw_segW hp hend ret0_startCall2In ret0_startTailIn ThreadInit.ret0_threadInitIn
    StackTake.ret0_stackTakeIn hK hF hR hlo hhi n0 k0 c0 hk hfld htk hW hRS hfit hout hFt

/-- **`scc_rt_main`'s and `wc_main`'s obligations after the switch on
`ret0`** are the generic ones. -/
theorem swUW_ofW {W : Frag isa} {K : State → State → Prop} {rS : Scc.Sem.Range} {tcb top : BitVec 64}
    {c0 : Ctl} (hp : Lays exe SccCode.ret0Cells) (hend : endPc = endOf exe SccCode.ret0Cells)
    (hW : SwW W K exe endPc R F ms rS tcb top c0) :
    SwUW W K p lbl exe endPc R F ms rS tcb top c0 80 ret0MC 24 16 (ret0Post c0) :=
  ⟨hW.sw, hW.xor, hW.blk, fun v => mainUW_ofW (hW.main v), fun v _ hFF => ret0_userCallW hp hend
    fun g' hra hc htp => ((hW.main v).wc g' hra hc htp).mono fun m h => ⟨hFF m h.1, h.2⟩⟩

/-- The hand `start_switch_segW`, by the generic theorem. -/
example {W : Frag isa} {K : State → State → Prop} {rS : Scc.Sem.Range}
    (hp : Lays exe SccCode.ret0Cells) (hend : endPc = endOf exe SccCode.ret0Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (tcb top : BitVec 64) (c0 : Ctl)
    (hok : (swR top (-80) 0).OK)
    (hFS : ∀ m, F m → StackM rS m) (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (hsub : ∀ k, (swR top (-80) 0).Off k → ((swR top (-80) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR top (-80) 0).addr k).toNat ∧ rS.contains (((swR top (-80) 0).addr k).toNat + 7))
    (hfit : (limA (tpOf tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf tcb)).toNat : Int) + 8 ≤ top.toNat + -80 ∨ (top.toNat : Int) + 0 ≤ (limA (tpOf tcb)).toNat)
    (hlimM : LimOk ms F (limA (tpOf tcb)) (top - 8#64 - 8#64 - (32 : Int64).toBitVec))
    (hlimW : LimOk ms F (limA (tpOf tcb))
      (top - 8#64 - 8#64 - (32 : Int64).toBitVec - 8#64 - 8#64 - (16 : Int64).toBitVec))
    (hexit : ∀ R' F' s, At exe endPc R' F' (mainNX (_root_.Executable.labels exe).label) s c0 → ¬ ms.abortAt s →
      MainExit p ms s c0 42)
    (hW : SwW W K exe endPc R F ms rS tcb top c0)
    {Q : Frag isa} :
    SegW W K p lbl ms (At exe endPc R F (startN6 (_root_.Executable.labels exe).label tcb top c0)) Q :=
  startSwitchU_segW (D := 24) (ZU := 16) (L := 80) hp hend ret0_startTailIn ret0_mainUIn (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hK tcb top c0 hok hFS hfitS hsub hfit
    hout hlimM hlimW (fun R' F' s c v ⟨hc, hv⟩ hAt hab => by subst hc hv; exact hexit R' F' s hAt hab)
    (swUW_ofW hp hend hW)

/-- **The hand `start_segW` from the generic `startU_segW`**: the same
statement, at `ret0MC`, `L = 80`, `D = 24`, `ZU = 16`. -/
theorem start_segW_ofU {W : Frag isa} {rS : Scc.Sem.Range} (hp : Lays exe SccCode.ret0Cells)
    (hend : endPc = endOf exe SccCode.ret0Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -296) (hhi : 8 ≤ R.hi) (n0 k0 : BitVec 64) (c0 : Ctl) (hn : n0.toNat + 80 ≤ 131072)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hhdr : StOk ms F (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F exe endPc n0)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk ms F (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F exe endPc k0)
    (hok : (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-80) 0).OK)
    (hsub : ∀ k, (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-80) 0).Off k →
      ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-80) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-80) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-80) 0).addr k).toNat + 7))
    (hfit : (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat : Int) + 8 ≤
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat + -80 ∨
      ((stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat : Int) + 0 ≤
        (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat)
    (hlimM : LimOk ms F (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - 8#64 - 8#64 - (32 : Int64).toBitVec))
    (hlimW : LimOk ms F (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - 8#64 - 8#64 - (32 : Int64).toBitVec -
        8#64 - 8#64 - (16 : Int64).toBitVec))
    (hexit : ∀ R' F' s, At exe endPc R' F' (mainNX (_root_.Executable.labels exe).label) s c0 → ¬ ms.abortAt s →
      MainExit p ms s c0 42)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hW : StartAllW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F ms rS n0 k0 c0)
    {Q : Frag isa} :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (startN0 (_root_.Executable.labels exe).label c0)) Q :=
  startU_segW (D := 24) (ZU := 16) (L := 80) hp hend ret0_startCallIn ret0_startIn AllocTcb.ret0_allocTcbIn
    ret0_startCall2In ret0_startTailIn ThreadInit.ret0_threadInitIn StackTake.ret0_stackTakeIn ret0_mainUIn
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hK hF hR hlo
    hhi n0 k0 c0 hn hk hhdr htcb hfld htk hok hsub hfit hout hlimM hlimW
    (fun R' F' s c v ⟨hc, hv⟩ hAt hab => by subst hc hv; exact hexit R' F' s hAt hab) hRS hfitS houtS hFt
    ⟨hW.s1, hW.s2, swUW_ofW hp hend hW.s3⟩

end Oracle

end Spike.Lib.X64.Rt
