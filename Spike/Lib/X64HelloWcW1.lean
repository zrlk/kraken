/-
**hello.w's `wc_main` obligations past the box's store, split into its own nodes and its callees'** (x86-64; the
twin of `Spike/Lib/A64HelloWcW1.lean`, the level-generic hello copy of `Spike/Lib/X64WakeWcW1.lean` at frame 128).

`WcMidWH` splits into `wc_main`'s own nodes (`WcMainWH`: the reserve's call block, `.x23`'s block, `.x24`'s and
`.x25`'s nodes and blocks) and its callees' (`scc_rt_thread_reserve`'s `ReserveW`, `scc_rt_alloc_tcb`'s `TcbWG`).

- `WcMainWH`: `wc_main`'s nodes of `WcMidWH`.
- `WcMidWH.of_mainH`: `WcMidWH` from `WcMainWH` and the callees' obligations.
- `wcMidW_w1H`: `WcMidWH` inside any level `W1` at the frames `[]`, no outside moves, from the three named premises
  (`hwcWf`, `hres`, `htcb`); hello's root level instantiates `W1` here.

No absolute address appears in this file.

## Differences from the AArch64 version

- `WcMainWH` has x86-64's nodes: no fence node `f` (TSO; `WcResWH` has the call block `bl` and the callee only),
  no source parameter `S` (the ghosts' guard is `MidG Q`, `X64HelloWcMid`).
- The callees' regions and return addresses are x86-64's: the reserve at `rARH R` with caller cells
  `CallerCells R (-136) (-40) 8`, returning to `.Lwc_main.x1`; the second TCB at `R.callee (-136) (-184) 8`,
  returning to `.Lwc_main.x2`, its call node `wcNCRH` (`%rbp` from the offsets); AArch64: `-144`, `.sp3`/`.sp4`.
-/
import Spike.Lib.X64HelloWcMid

namespace Spike.Lib.X64.Flow.HelloWc

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.WakeWc (MidG kOf)
open Spike.Lib.X64.HelloPh.WcSp6 (WcSp6PW MidPGH)
open Spike.Lib.X64HelloMainPreSrc (boxPubCtlH)
open Spike.Lib.X64.Rt (TcbWG)
open Spike.Lib.X64.Rt.Reserve (ReserveW)
open Spike.Lib.X64.Flow.Ret0 (CallerCells)

/-- **`wc_main`'s own nodes of `WcMidWH`** inside `W` at outside move `K`: the reserve's call block, `.x23`'s block
to the second TCB's call, `.x24`'s and `.x25`'s (at the second TCB `tH`), at every ghost with `MidG` and `FrMGH`
(as `WcMidWH`). -/
structure WcMainWH (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F F₂ : MachineData → Prop) (ms : MemSide isa) (J1 : AS → Ctl → Prop)
    (Q : WeakMem.AllocLabel → Nat → Ctl → Prop) : Prop where
  bl : BlkW W K exe endPc R F (rNH ms (_root_.Executable.labels exe).label R J1 Q .bl) resBH
  sp3 : ∀ c0 sl me cA fr, MidG Q c0 cA ∧ FrMGH J1 fr sl me →
    BlkW W K exe endPc R F (wcN3H (_root_.Executable.labels exe).label c0 sl me cA fr) tcb2CallH
  sp4 : ∀ c0 sl me cA fr, MidG Q c0 cA ∧ FrMGH J1 fr sl me →
    WcSp4WH W K exe endPc R F c0 (tH (_root_.Executable.labels exe).label) sl me cA fr
  sp6 : ∀ c0 ty l sl me cA fr, MidPGH Q c0 ty l cA ∧ FrMGH J1 fr sl me →
    WcSp6PW W K exe endPc R F₂ c0 (boxPubCtlH c0 ty l) (tH (_root_.Executable.labels exe).label)
      (kOf (_root_.Executable.labels exe).label) sl me cA fr

/-- `WcMainWH` is inhabited: the trivial predicate, with no outside moves. -/
example {exe : _root_.Executable} {endPc : Int64} {R : Region} {F F₂ : MachineData → Prop} {ms : MemSide isa}
    {J1 : AS → Ctl → Prop} {Q : WeakMem.AllocLabel → Nat → Ctl → Prop} :
    WcMainWH (fun _ _ => True) (fun _ _ => False) exe endPc R F F₂ ms J1 Q :=
  ⟨BlkW.triv, fun _ _ _ _ _ _ => BlkW.triv, fun _ _ _ _ _ _ => WcSp4WH.triv, fun _ _ _ _ _ _ _ _ => WcSp6PW.triv⟩

/-- **`WcMidWH` from `wc_main`'s nodes and its callees'** (`WcResWH.res`'s reserve, `WcSp3WH.tcb`'s second
TCB). -/
theorem WcMidWH.of_mainH {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F F₂ : MachineData → Prop} {ms : MemSide isa} {J1 : AS → Ctl → Prop}
    {Q : WeakMem.AllocLabel → Nat → Ctl → Prop} (hm : WcMainWH W K exe endPc R F F₂ ms J1 Q)
    (hres : ∀ g : Flow.Ret0.AllocTcb.G × Ctl,
      g.1.ra = ((_root_.Executable.labels exe).label ".Lwc_main.x1").toBitVec →
      ∀ i, ReserveW W K exe endPc (rARH R)
        (fun m => F m ∧ CallerCells R (-136) (-40) 8 m ∧ ResCtxH (_root_.Executable.labels exe).label R
          (rNH ms (_root_.Executable.labels exe).label R J1 Q .call).J g m) ⟨g.1, 0#64, g.2⟩ i)
    (htcb : ∀ c0 sl me cA fr, MidG Q c0 cA ∧ FrMGH J1 fr sl me →
      ∀ g : Ret0.AllocTcb.G, g.ra = ((_root_.Executable.labels exe).label x24L).toBitVec →
      ∀ i, TcbWG W K exe endPc (R.callee (-136) (-184) 8)
        (fun mm => F mm ∧ CallerCells R (-136) (-184) 8 mm ∧
          TcbCtxH (_root_.Executable.labels exe).label R
            (wcNCRH (_root_.Executable.labels exe).label c0 sl me cA fr).J c0 g mm)
        (tcb2QH g c0) i) :
    WcMidWH W K exe endPc R F F₂ ms J1 Q :=
  ⟨⟨hm.bl, hres⟩, fun c0 sl me cA fr hM => ⟨hm.sp3 c0 sl me cA fr hM, htcb c0 sl me cA fr hM⟩,
    hm.sp4, hm.sp6⟩

/-- **`WcMidWH` inside a level `W1` at the frames `[]`**, with no outside moves, from `wc_main`'s nodes inside it
(`hwcWf`) and the reserve's (`hres`) and the second TCB's (`htcb`). -/
theorem wcMidW_w1H (W1 : FragS isa) {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F F₂ : MachineData → Prop} {ms : MemSide isa} {J1 : AS → Ctl → Prop}
    {Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (hwcWf : WcMainWH (fun s c => W1 s c []) (fun _ _ => False) exe endPc R F F₂ ms J1 Q)
    (hres : ∀ g : Flow.Ret0.AllocTcb.G × Ctl,
      g.1.ra = ((_root_.Executable.labels exe).label ".Lwc_main.x1").toBitVec →
      ∀ nd, ReserveW (fun s c => W1 s c []) (fun _ _ => False) exe endPc (rARH R)
        (fun m => F m ∧ CallerCells R (-136) (-40) 8 m ∧ ResCtxH (_root_.Executable.labels exe).label R
          (rNH ms (_root_.Executable.labels exe).label R J1 Q .call).J g m) ⟨g.1, 0#64, g.2⟩ nd)
    (htcb : ∀ c0 sl me cA fr, MidG Q c0 cA ∧ FrMGH J1 fr sl me →
      ∀ g : Ret0.AllocTcb.G, g.ra = ((_root_.Executable.labels exe).label x24L).toBitVec →
      ∀ nd, TcbWG (fun s c => W1 s c []) (fun _ _ => False) exe endPc (R.callee (-136) (-184) 8)
        (fun mm => F mm ∧ CallerCells R (-136) (-184) 8 mm ∧
          TcbCtxH (_root_.Executable.labels exe).label R
            (wcNCRH (_root_.Executable.labels exe).label c0 sl me cA fr).J c0 g mm)
        (tcb2QH g c0) nd) :
    WcMidWH (fun s c => W1 s c []) (fun _ _ => False) exe endPc R F F₂ ms J1 Q :=
  WcMidWH.of_mainH hwcWf hres htcb

end Spike.Lib.X64.Flow.HelloWc

/-- info: 'Spike.Lib.X64.Flow.HelloWc.WcMidWH.of_mainH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.WcMidWH.of_mainH

/-- info: 'Spike.Lib.X64.Flow.HelloWc.wcMidW_w1H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.wcMidW_w1H
