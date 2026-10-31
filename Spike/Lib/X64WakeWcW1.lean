/-
**`wc_main`'s obligations past the box's store inside `h1`'s level `W1W`**
(x86-64, the pre-spawn consumer; the twin of `Spike/Lib/A64WakeWcW1.lean`:
the `W1W` half of the machine side of `X64WakeWcHat.wake_wc_mid_hatW`'s
`hW`, the other half `wcMidW_k1`'s).

`WcMidW` splits into `wc_main`'s own nodes (`WcMainW`: the reserve's call
block, `.x19`'s block, `.x20`'s nodes up to `scc_rt_thread_init`'s entry,
`.x21`'s through the `mfence` to the clone's `syscall`) and its callees'
(`scc_rt_thread_reserve`'s `ReserveW`, `scc_rt_alloc_tcb`'s `TcbWG`).

- `WcMainW`: `wc_main`'s nodes of `WcMidW`.
- `WcMidW.of_main`: `WcMidW` from `WcMainW` and the callees' obligations.
- `wcMidW_w1`: `WcMidW` inside `W1W asm … l b n` (at `[]`), no outside
  moves, from the three named premises
  - `hwcWf`: `WcMainW` inside `W1W` (the twins of `A64WakeWcWf`'s
    `blkW_wfC`/`nodeW_wfC` and of `A64WakeWfW` at the stores);
  - `hres`: the reserve's (the twin of `reserveW_wf`);
  - `htcb`: the second TCB's `scc_rt_alloc_tcb` (the twin of `tcbWG_wf`).
  Combine with `wcMidW_k1` by `WcMidW.and` (the K1 side first, its
  `TakeCKS` kept).

**Where this differs from AArch64** (forced by the x86-64 shape):
`WcMainW` has x86-64's nodes: no fence node `f` (`WcResW` has the call
block `bl` and the callee only; TSO); `.x19`'s block `wcN3 … tcb2Call`;
`.x20`'s `aN .n20`, `.n20s`, `.n20p` and the call node `wcNI` at the second
TCB `t2` (A64's `n4`, `n4s`, `n5`, `nI`); the clone's six nodes `wcN21`,
`wcNf` (the `mfence`, where the box is published), `wcNa`, `wcNd`, `wcN10`,
`wcNr` at `F₂`, the source past the fence at `boxPubCtl c0 ty l` (A64's
three `.sp6` nodes, no publication), guarded by `MidPG` (A64: `MidG`); the
regions are x86-64's (`rAR R`, `R.callee (-72) (-184) 8`, return addresses
`.x19`, `.x20`); there is no source parameter `S`; the level `W1W` takes
the assembly `asm`.

No absolute address appears in this file.
-/
import Spike.Lib.X64WakeWcK1
import Spike.Lib.X64WakeOPremW

namespace Spike.Lib.X64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.WakePh.WcSp4 (wcNI initCall)
open Spike.Lib.X64.WakePh.Tcb2Call (wcN3 tcb2Call tcb2Q)
open Spike.Lib.X64.Rt (TcbWG)
open Spike.Lib.X64.Rt.Reserve (ReserveW)
open Spike.Lib.X64.Flow.Ret0 (CallerCells)

/-- **`wc_main`'s own nodes of `WcMidW`** inside `W` at outside move `K`:
the reserve's call block (`rN .bl`), `.x19`'s block to the second TCB's
call (`wcN3`), `.x20`'s (`aN`, `wcNI`, at the second TCB `t2`) and
`.x21`'s to the clone's `syscall` (`WcClonePW`'s, at `F₂`), at every ghost
with `MidG`/`MidPG`, `FrG` and `FrMG` (as `WcMidW`). -/
structure WcMainW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F F₂ : MachineData → Prop) (ms : MemSide isa) (J0 : AS → Ctl → Prop)
    (Q : WeakMem.AllocLabel → Nat → Ctl → Prop) : Prop where
  bl : BlkW W K exe endPc R F (rN ms (_root_.Executable.labels exe).label R J0 Q .bl) resB
  sp3 : ∀ c0 cA m fr, MidG Q c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m →
    BlkW W K exe endPc R F (wcN3 (_root_.Executable.labels exe).label (j3 cA m fr) c0) tcb2Call
  pre : ∀ c0 ty l cA m fr, MidPG Q c0 ty l cA ∧ FrG J0 fr ∧ FrMG J0 fr m →
    WcSp4PreW W K exe endPc R F c0 (t2 (_root_.Executable.labels exe).label) cA m fr
  clone : ∀ c0 ty l cA m fr, MidPG Q c0 ty l cA ∧ FrG J0 fr ∧ FrMG J0 fr m →
    WcClonePW W K exe endPc R F₂ c0 ty l (t2 (_root_.Executable.labels exe).label)
      (kOf (_root_.Executable.labels exe).label) cA m fr

/-- **`WcMidW` from `wc_main`'s nodes and its callees'** (`WcResW.res`'s
reserve, `WcSp3W.tcb`'s second TCB). -/
theorem WcMidW.of_main {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F F₂ : MachineData → Prop} {ms : MemSide isa} {J0 : AS → Ctl → Prop}
    {Q : WeakMem.AllocLabel → Nat → Ctl → Prop} (hm : WcMainW W K exe endPc R F F₂ ms J0 Q)
    (hres : ∀ g : Flow.Ret0.AllocTcb.G × Ctl,
      g.1.ra = ((_root_.Executable.labels exe).label ".Lwc_main.x19").toBitVec →
      ∀ i, ReserveW W K exe endPc (rAR R)
        (fun m => F m ∧ CallerCells R (-72) (-40) 8 m ∧ ResCtx (_root_.Executable.labels exe).label R
          (rN ms (_root_.Executable.labels exe).label R J0 Q .call).J g m) ⟨g.1, 0#64, g.2⟩ i)
    (htcb : ∀ c0 cA m fr, MidG Q c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m →
      ∀ g : Ret0.AllocTcb.G, g.ra = ((_root_.Executable.labels exe).label ".Lwc_main.x20").toBitVec →
      ∀ i, TcbWG W K exe endPc (R.callee (-72) (-184) 8)
        (fun mm => F mm ∧ CallerCells R (-72) (-184) 8 mm ∧
          TcbCtx (_root_.Executable.labels exe).label R (wcNCR (_root_.Executable.labels exe).label c0 cA m fr).J
            c0 g mm)
        (tcb2Q g c0) i) :
    WcMidW W K exe endPc R F F₂ ms J0 Q :=
  ⟨⟨hm.bl, hres⟩, fun c0 cA m fr hM => ⟨hm.sp3 c0 cA m fr hM, htcb c0 cA m fr hM⟩,
    fun c0 ty l cA m fr hM => ⟨hm.pre c0 ty l cA m fr hM, hm.clone c0 ty l cA m fr hM⟩⟩

section W1

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}

/-- **`WcMidW` inside `h1`'s level `W1W asm … l b n`** (at no frames), with
no outside moves, from `wc_main`'s nodes inside it (`hwcWf`) and the
reserve's (`hres`) and the second TCB's (`htcb`). -/
theorem wcMidW_w1 (asm : Scc.Sem.X64.Asm) (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
    (E : Scc.Sem.Entry) (Dt : State → Prop) (Ctx : FragS isa) (ls0 : X64Consumer.Lsize) (l : WeakMem.AllocLabel)
    (b n : Nat) {exe : _root_.Executable} {endPc : Int64} {R : Region} {F F₂ : MachineData → Prop}
    {ms : MemSide isa} {J0 : AS → Ctl → Prop} {Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (hwcWf : WcMainW (fun s c => WakeOPremW.W1W asm hp i E Dt Ctx ls0 l b n s c []) (fun _ _ => False)
      exe endPc R F F₂ ms J0 Q)
    (hres : ∀ g : Flow.Ret0.AllocTcb.G × Ctl,
      g.1.ra = ((_root_.Executable.labels exe).label ".Lwc_main.x19").toBitVec →
      ∀ nd, ReserveW (fun s c => WakeOPremW.W1W asm hp i E Dt Ctx ls0 l b n s c []) (fun _ _ => False) exe endPc
        (rAR R) (fun m => F m ∧ CallerCells R (-72) (-40) 8 m ∧ ResCtx (_root_.Executable.labels exe).label R
          (rN ms (_root_.Executable.labels exe).label R J0 Q .call).J g m) ⟨g.1, 0#64, g.2⟩ nd)
    (htcb : ∀ c0 cA m fr, MidG Q c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m →
      ∀ g : Ret0.AllocTcb.G, g.ra = ((_root_.Executable.labels exe).label ".Lwc_main.x20").toBitVec →
      ∀ nd, TcbWG (fun s c => WakeOPremW.W1W asm hp i E Dt Ctx ls0 l b n s c []) (fun _ _ => False) exe endPc
        (R.callee (-72) (-184) 8) (fun mm => F mm ∧ CallerCells R (-72) (-184) 8 mm ∧
          TcbCtx (_root_.Executable.labels exe).label R (wcNCR (_root_.Executable.labels exe).label c0 cA m fr).J
            c0 g mm) (tcb2Q g c0) nd) :
    WcMidW (fun s c => WakeOPremW.W1W asm hp i E Dt Ctx ls0 l b n s c []) (fun _ _ => False) exe endPc R F F₂
      ms J0 Q :=
  WcMidW.of_main hwcWf hres htcb

end W1

end Spike.Lib.X64.Flow.WakeWc

/-- info: 'Spike.Lib.X64.Flow.WakeWc.WcMidW.of_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.WcMidW.of_main

/-- info: 'Spike.Lib.X64.Flow.WakeWc.wcMidW_w1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.wcMidW_w1
