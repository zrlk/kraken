/-
**`wc_main`'s obligations past the box's store inside `h1`'s level `W1W`**
(AArch64, the pre-spawn consumer; the `W1W` half of
`A64WakeWcHat.wake_wc_mid_hatW`'s `hW`, the other half `wcMidW_k1`'s).

`WcMidW` splits into `wc_main`'s own nodes (`WcMainW`: the fence, the
reserve's call, `.sp3`'s block, `.sp4`'s and `.sp6`'s nodes and blocks)
and its callees' (`scc_rt_thread_reserve`'s `ReserveW`,
`scc_rt_alloc_tcb`'s `TcbWG`); `scc_rt_thread_init` is not a node of
`WcMidW` (`wake_wc_mid_hatW`'s `hti`).

- `WcMainW`: `wc_main`'s nodes of `WcMidW`.
- `WcMidW.of_main`: `WcMidW` from `WcMainW` and the callees' obligations.
- `wcMidW_w1`: `WcMidW` inside `W1W … l b n` (at `[]`), no outside moves,
  from the three named premises
  - `hwcWf`: `WcMainW` inside `W1W` (`A64WakeWcWf`,
    `blkW_wfC`/`nodeW_wfC`, and `A64WakeWfW` at the stores),
  - `hres`: the reserve's (`reserveW_wf`),
  - `htcb`: the second TCB's `scc_rt_alloc_tcb` (`tcbWG_wf`).
  Combine with `wcMidW_k1` by `WcMidW.and` (the K1 side first, its
  `TakeCKS` kept).

No absolute address appears in this file.
-/
import Spike.Lib.A64WakeWcK1
import Spike.Lib.WakeOPremW

namespace Spike.Lib.A64.Flow.WakeWc

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib
open Spike.Lib.A64.Flow (ND BlkW NodeW AS)
open Spike.Lib.A64.WakePh.WcSp4 (wcNI sp4A initCall sp6A cloneArgs)
open Spike.Lib.A64.WakePh.Tcb2Call (wcN3 tcb2Call tcb2Q)
open Spike.Lib.A64.Rt (TcbWG)
open Spike.Lib.A64.Rt.Reserve (ReserveW)
open Spike.Lib.A64.Flow.Ret0 (CallerCells)

/-- **`wc_main`'s own nodes of `WcMidW`** inside `W` at outside move `K`:
the fence (`rNQ`, at the source facts `Q`) and the reserve's call (`rN`),
`.sp3`'s block to the second TCB's call (`wcN3`), `.sp4`'s and `.sp6`'s
(`aN`, `wcNI`, `bN`, at the second TCB `t2`), at every ghost with `MidG`,
`FrG` and `FrMG` (as `WcMidW`). -/
structure WcMainW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F F₂ : MachineData → Prop) (ms : MemSide isaLSE2) (J0 : AS → Ctl → Prop)
    (S Q : WeakMem.AllocLabel → Nat → Ctl → Prop) : Prop where
  f : NodeW W K exe endPc R F (rNQ ms (_root_.Executable.labels exe).label J0 S Q .f)
  bl : BlkW W K exe endPc R F (rN ms (_root_.Executable.labels exe).label J0 S .bl) resB
  sp3 : ∀ c0 cA m fr, MidG S c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m →
    BlkW W K exe endPc R F (wcN3 (_root_.Executable.labels exe).label (j3 cA m fr) c0) tcb2Call
  n4 : ∀ c0 cA m fr, MidG S c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m →
    BlkW W K exe endPc R F (aN (_root_.Executable.labels exe).label c0 (t2 (_root_.Executable.labels exe).label)
      cA m fr .n4) sp4A
  n4s : ∀ c0 cA m fr, MidG S c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m →
    NodeW W K exe endPc R F (aN (_root_.Executable.labels exe).label c0 (t2 (_root_.Executable.labels exe).label)
      cA m fr .n4s)
  n5 : ∀ c0 cA m fr, MidG S c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m →
    BlkW W K exe endPc R F (aN (_root_.Executable.labels exe).label c0 (t2 (_root_.Executable.labels exe).label)
      cA m fr .n5) initCall
  nI : ∀ c0 cA m fr, MidG S c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m →
    NodeW W K exe endPc R F (wcNI (_root_.Executable.labels exe).label c0 (t2 (_root_.Executable.labels exe).label)
      cA m fr)
  n6 : ∀ c0 cA m fr, MidG S c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m →
    BlkW W K exe endPc R F₂ (bN (_root_.Executable.labels exe).label c0 (t2 (_root_.Executable.labels exe).label)
      cA m fr .n6) sp6A
  n6f : ∀ c0 cA m fr, MidG S c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m →
    NodeW W K exe endPc R F₂ (bN (_root_.Executable.labels exe).label c0 (t2 (_root_.Executable.labels exe).label)
      cA m fr .n6f)
  n6a : ∀ c0 cA m fr, MidG S c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m →
    BlkW W K exe endPc R F₂ (bN (_root_.Executable.labels exe).label c0 (t2 (_root_.Executable.labels exe).label)
      cA m fr .n6a) cloneArgs

/-- **`WcMidW` from `wc_main`'s nodes and its callees'** (`WcResW.res`'s
reserve, `WcSp3W.tcb`'s second TCB). -/
theorem WcMidW.of_main {W : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F F₂ : MachineData → Prop} {ms : MemSide isaLSE2} {J0 : AS → Ctl → Prop}
    {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop} (hm : WcMainW W K exe endPc R F F₂ ms J0 S Q)
    (hres : ∀ g : Flow.Reserve.G × Ctl, g.1.ra = ((_root_.Executable.labels exe).label ".L21_wc_main.sp3").toBitVec →
      ∀ i, ReserveW W K exe endPc (rAR R)
        (fun m => F m ∧ CallerCells R (-80) (-48) 0 m ∧ ResCtx (_root_.Executable.labels exe).label R
          (rN ms (_root_.Executable.labels exe).label J0 S .call).J g m) ⟨g.1, 0#64, g.2⟩ i)
    (htcb : ∀ c0 cA m fr, MidG S c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m →
      ∀ g : Ret0.AllocTcb.G, g.ra = ((_root_.Executable.labels exe).label ".L21_wc_main.sp4").toBitVec →
      ∀ i, TcbWG W K exe endPc (R.callee (-80) (-192) 0) (fun mm => F mm ∧ CallerCells R (-80) (-192) 0 mm ∧
        TcbCtx (_root_.Executable.labels exe).label R (wcNC' (_root_.Executable.labels exe).label c0 cA m fr).J c0 g mm)
        (tcb2Q g c0) i) :
    WcMidW W K exe endPc R F F₂ ms J0 S Q :=
  ⟨⟨hm.f, hm.bl, hres⟩, fun c0 cA m fr hM => ⟨hm.sp3 c0 cA m fr hM, htcb c0 cA m fr hM⟩,
    fun c0 cA m fr hM => ⟨hm.n4 c0 cA m fr hM, hm.n4s c0 cA m fr hM, hm.n5 c0 cA m fr hM, hm.nI c0 cA m fr hM,
      hm.n6 c0 cA m fr hM, hm.n6f c0 cA m fr hM, hm.n6a c0 cA m fr hM⟩⟩

section W1

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}

/-- **`WcMidW` inside `h1`'s level `W1W … l b n`** (at no frames), with no
outside moves, from `wc_main`'s nodes inside it (`hwcWf`) and the reserve's
(`hres`) and the second TCB's (`htcb`). -/
theorem wcMidW_w1 (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (E : Scc.Sem.Entry)
    (Dt : State → Prop) (Ctx : FragS isaLSE2) (ls0 : A64Consumer.Lsize) (l : WeakMem.AllocLabel) (b n : Nat)
    {exe : _root_.Executable} {endPc : Int64} {R : Region} {F F₂ : MachineData → Prop} {ms : MemSide isaLSE2}
    {J0 : AS → Ctl → Prop} {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (hwcWf : WcMainW (fun s c => WakeOPremW.W1W hp i E Dt Ctx ls0 l b n s c []) (fun _ _ => False)
      exe endPc R F F₂ ms J0 S Q)
    (hres : ∀ g : Flow.Reserve.G × Ctl, g.1.ra = ((_root_.Executable.labels exe).label ".L21_wc_main.sp3").toBitVec →
      ∀ nd, ReserveW (fun s c => WakeOPremW.W1W hp i E Dt Ctx ls0 l b n s c []) (fun _ _ => False) exe endPc (rAR R)
        (fun m => F m ∧ CallerCells R (-80) (-48) 0 m ∧ ResCtx (_root_.Executable.labels exe).label R
          (rN ms (_root_.Executable.labels exe).label J0 S .call).J g m) ⟨g.1, 0#64, g.2⟩ nd)
    (htcb : ∀ c0 cA m fr, MidG S c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m →
      ∀ g : Ret0.AllocTcb.G, g.ra = ((_root_.Executable.labels exe).label ".L21_wc_main.sp4").toBitVec →
      ∀ nd, TcbWG (fun s c => WakeOPremW.W1W hp i E Dt Ctx ls0 l b n s c []) (fun _ _ => False) exe endPc
        (R.callee (-80) (-192) 0) (fun mm => F mm ∧ CallerCells R (-80) (-192) 0 mm ∧
          TcbCtx (_root_.Executable.labels exe).label R (wcNC' (_root_.Executable.labels exe).label c0 cA m fr).J
            c0 g mm) (tcb2Q g c0) nd) :
    WcMidW (fun s c => WakeOPremW.W1W hp i E Dt Ctx ls0 l b n s c []) (fun _ _ => False) exe endPc R F F₂ ms J0 S Q :=
  WcMidW.of_main hwcWf hres htcb

end W1

end Spike.Lib.A64.Flow.WakeWc

/-- info: 'Spike.Lib.A64.Flow.WakeWc.WcMidW.of_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.WcMidW.of_main

/-- info: 'Spike.Lib.A64.Flow.WakeWc.wcMidW_w1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.wcMidW_w1
