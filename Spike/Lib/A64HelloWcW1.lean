/-
**hello.w's `wc_main` obligations past the box's store, split into its own
nodes and its callees'** (AArch64, hTop; the
level-generic twin of `Spike/Lib/A64WakeWcW1.lean` at frame 144).

`WcMidWH` splits into `wc_main`'s own nodes (`WcMainWH`: the fence, the
reserve's call, `.sp3`'s block, `.sp4`'s and `.sp6`'s nodes and blocks)
and its callees' (`scc_rt_thread_reserve`'s `ReserveW`,
`scc_rt_alloc_tcb`'s `TcbWG`).

- `WcMainWH`: `wc_main`'s nodes of `WcMidWH`.
- `WcMidWH.of_mainH`: `WcMidWH` from `WcMainWH` and the callees'
  obligations.
- `wcMidW_w1H`: `WcMidWH` inside any level `W1` at the frames `[]`, no
  outside moves, from the three named premises (`hwcWf`, `hres`, `htcb`).
  Wake's `wcMidW_w1` states this at `WakeOPremW.W1W hp i E Dt Ctx ls0 l b n`
  (the root's level after the allocation); hello's root level (row 5j,
  `HelloRootPrem`, B8 tier) instantiates `W1` here.

No absolute address appears in this file.
-/
import Spike.Lib.A64HelloWcMid

namespace Spike.Lib.A64.Flow.HelloWc

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib
open Spike.Lib.A64.Flow (ND BlkW NodeW AS)
open Spike.Lib.A64.Flow.WakeWc (MidG kOf)
open Spike.Lib.A64.HelloPh.WcSp6 (WcSp6W wcN6H wcN6fH wcN6aH sp6AH cloneArgsH)
open Spike.Lib.A64.Rt (TcbWG)
open Spike.Lib.A64.Rt.Reserve (ReserveW)
open Spike.Lib.A64.Flow.Ret0 (CallerCells)

/-- **`wc_main`'s own nodes of `WcMidWH`** inside `W` at outside move `K`:
the fence (at the source facts `Q`) and the reserve's call, `.sp3`'s block
to the second TCB's call, `.sp4`'s and `.sp6`'s (at the second TCB
`tH`), at every ghost with `MidG` and `FrMGH` (as `WcMidWH`). -/
structure WcMainWH (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F F₂ : MachineData → Prop) (ms : MemSide isaLSE2) (J1 : AS → Ctl → Prop)
    (S Q : WeakMem.AllocLabel → Nat → Ctl → Prop) : Prop where
  f : NodeW W K exe endPc R F (rNH ms (_root_.Executable.labels exe).label J1 S Q .f)
  bl : BlkW W K exe endPc R F (rNH ms (_root_.Executable.labels exe).label J1 S Q .bl) resBH
  sp3 : ∀ c0 sl me cA fr, MidG S c0 cA ∧ FrMGH J1 fr sl me →
    BlkW W K exe endPc R F (wcN3H (_root_.Executable.labels exe).label c0 sl me cA fr) tcb2CallH
  sp4 : ∀ c0 sl me cA fr, MidG S c0 cA ∧ FrMGH J1 fr sl me →
    WcSp4WH W K exe endPc R F c0 (tH (_root_.Executable.labels exe).label) sl me cA fr
  sp6 : ∀ c0 sl me cA fr, MidG S c0 cA ∧ FrMGH J1 fr sl me →
    WcSp6W W K exe endPc R F₂ c0 (tH (_root_.Executable.labels exe).label) (kOf (_root_.Executable.labels exe).label)
      sl me cA fr

/-- **`WcMidWH` from `wc_main`'s nodes and its callees'** (`WcResWH.res`'s
reserve, `WcSp3WH.tcb`'s second TCB). -/
theorem WcMidWH.of_mainH {W : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F F₂ : MachineData → Prop} {ms : MemSide isaLSE2} {J1 : AS → Ctl → Prop}
    {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop} (hm : WcMainWH W K exe endPc R F F₂ ms J1 S Q)
    (hres : ∀ g : Flow.Reserve.G × Ctl, g.1.ra = ((_root_.Executable.labels exe).label ".L22_wc_main.sp3").toBitVec →
      ∀ i, ReserveW W K exe endPc (rARH R)
        (fun m => F m ∧ CallerCells R (-144) (-48) 0 m ∧ ResCtxH (_root_.Executable.labels exe).label R
          (rNH ms (_root_.Executable.labels exe).label J1 S Q .call).J g m) ⟨g.1, 0#64, g.2⟩ i)
    (htcb : ∀ c0 sl me cA fr, MidG S c0 cA ∧ FrMGH J1 fr sl me →
      ∀ g : Ret0.AllocTcb.G, g.ra = ((_root_.Executable.labels exe).label ".L22_wc_main.sp4").toBitVec →
      ∀ i, TcbWG W K exe endPc (R.callee (-144) (-192) 0)
        (fun mm => F mm ∧ CallerCells R (-144) (-192) 0 mm ∧
          TcbCtxH (_root_.Executable.labels exe).label R (wcNCH (_root_.Executable.labels exe).label c0 sl me cA fr).J
            c0 g mm)
        (tcb2QH g c0) i) :
    WcMidWH W K exe endPc R F F₂ ms J1 S Q :=
  ⟨⟨hm.f, hm.bl, hres⟩, fun c0 sl me cA fr hM => ⟨hm.sp3 c0 sl me cA fr hM, htcb c0 sl me cA fr hM⟩,
    hm.sp4, hm.sp6⟩

/-- **`WcMidWH` inside a level `W1` at the frames `[]`**, with no outside
moves, from `wc_main`'s nodes inside it (`hwcWf`) and the reserve's
(`hres`) and the second TCB's (`htcb`). -/
theorem wcMidW_w1H (W1 : FragS isaLSE2) {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F F₂ : MachineData → Prop} {ms : MemSide isaLSE2} {J1 : AS → Ctl → Prop}
    {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (hwcWf : WcMainWH (fun s c => W1 s c []) (fun _ _ => False) exe endPc R F F₂ ms J1 S Q)
    (hres : ∀ g : Flow.Reserve.G × Ctl, g.1.ra = ((_root_.Executable.labels exe).label ".L22_wc_main.sp3").toBitVec →
      ∀ nd, ReserveW (fun s c => W1 s c []) (fun _ _ => False) exe endPc (rARH R)
        (fun m => F m ∧ CallerCells R (-144) (-48) 0 m ∧ ResCtxH (_root_.Executable.labels exe).label R
          (rNH ms (_root_.Executable.labels exe).label J1 S Q .call).J g m) ⟨g.1, 0#64, g.2⟩ nd)
    (htcb : ∀ c0 sl me cA fr, MidG S c0 cA ∧ FrMGH J1 fr sl me →
      ∀ g : Ret0.AllocTcb.G, g.ra = ((_root_.Executable.labels exe).label ".L22_wc_main.sp4").toBitVec →
      ∀ nd, TcbWG (fun s c => W1 s c []) (fun _ _ => False) exe endPc (R.callee (-144) (-192) 0)
        (fun mm => F mm ∧ CallerCells R (-144) (-192) 0 mm ∧
          TcbCtxH (_root_.Executable.labels exe).label R (wcNCH (_root_.Executable.labels exe).label c0 sl me cA fr).J
            c0 g mm)
        (tcb2QH g c0) nd) :
    WcMidWH (fun s c => W1 s c []) (fun _ _ => False) exe endPc R F F₂ ms J1 S Q :=
  WcMidWH.of_mainH hwcWf hres htcb

end Spike.Lib.A64.Flow.HelloWc

/-- info: 'Spike.Lib.A64.Flow.HelloWc.WcMidWH.of_mainH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.WcMidWH.of_mainH

/-- info: 'Spike.Lib.A64.Flow.HelloWc.wcMidW_w1H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.wcMidW_w1H
