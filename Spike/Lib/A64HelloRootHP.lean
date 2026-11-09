/-
**hello.w's `HelloRootPrem.hP` at the box's real ghost** (AArch64): the box's ghost
pinned to the real run's region and frame condition (`GJ1RH`: `GJ1H` with `R = wcR (swR v (-helloLsw) 0) helloD`
and `F = wcF … (FS …) m1 σ1`), the box's landing producing it (`boxMH_landingRH`), and `H1GAH` at such a ghost from
the fields that depend on more than the region and frame condition (`H1GAH0`, the twin of wake's `WakeH1A.H1GA`):
`hi80`, `hR8` (the region's bounds `-400`, `0`), `fcg`, `fcl`, `hF0` (`BoxRF.wcF_dmemH`, `wcF_takeMemH`,
`stackOff_r0_boxH`), `hFr`, `hunF` (`FS`'s `WordsNoneP`, `BoxRF.rtF_of_wn`, `unF_of_wn`) and `hpl` (`GJ1H`'s
entry slice, `SpawnPl.hpl_GJ1H`) are discharged.

- `box_regRH`: `Box.box_regH` with the region and frame condition named.
- `GJ1RH`, `boxMH_landingRH`: the pinned ghost; a pinned box store's landing is `BoxMH` at it.
- `H1GAH0`: `H1GAH` without `hi80`, `fcl`, `fcg`, `hR8`, `hFr`, `hunF`, `hF0`, `hpl`. All its fields are discharged at
  the root instance: `wcWf`, `wcl`, `res`, `tcb` by `CalRootI.h0V_I` (rows hP-wcWf, hP-wcl, hP-res, hP-tcb);
  `resA`, `hdrA`, `tcbA`, `tid`, `hfld`, `htk` by `H2Rt` at `ms2H` via `HelloRootBase.h0W_I` (row hP-H1GAH0);
  `hWX` by `HelloRootInst.hWX_I` (row hP-hWX).
- `hCI_RH`, `hland2_boxMRU`: `Box.hCI_H` and `LandR1U.hland2_ofU` with `boxMH_landingRH` at `GJ1RH` (`h2`'s Box,
  `HelloH2Root.h2Stmt_root`).
- `H1GAH0W`, `H1GAH0W.toH0`: `H1GAH0` but `hWX` (discharged at the root by `HelloRootInst.hWX_I`), and back given
  `hWX`.
- `H1GAH0V`, `H1GAH0V.toW`: `H1GAH0W` but its runtime fields (`H2Rt` proves those at `ms2H`,
  `HelloRootBase.h0W_I` plugs them; `H1GAH0V` itself is `CalRootI.h0V_I` at the root), and back given them.
- `hP_of`: `H1GAH` from `BoxPureH`, `GJ1RH` and `H1GAH0`.
-/
import Spike.Lib.A64HelloBoxRF
import Spike.Lib.A64HelloLandR1U
import Spike.Lib.A64HelloH1A
import Spike.Lib.A64HelloSpawnPl
import Spike.Lib.HelloGOf2H

namespace Spike.Lib.A64.HelloPh.RootHP

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.HelloWc (WcMainWH FrMGH rNH ResCtxH TcbCtxH wcNCH tcb2QH tH rARH bXH)
open Spike.Lib.A64.HelloPh.WcSp6 (wcNSH)
open Spike.Lib.A64.Flow.WakeWc (MidG kOf tiQ)
open Spike.Lib.A64.Flow.Ret0 (CallerCells StackM pinA)
open Spike.Lib.A64.Flow.Ret0.StackTake (siteL)
open Spike.Lib.A64.Rt (TcbOkGA hdrA RuntimeLayout TcbWG)
open Spike.Lib.A64.Rt.Reserve (ResOkA ReserveW)
open Spike.Lib.A64.Rt.PreChild (r1Of)
open Spike.Lib.A64.KeepTP (tpXa TP)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.HelloHMid (BoxPureH BoxMH SBH QBH slWsH)
open Spike.Lib.HelloMainPreSrc (SpawnSrcH)
open Spike.Lib.A64.HelloPh.StartWf (WSH)
open Spike.Lib.A64.HelloPh.Ti2 (X0TH)
open Spike.Lib.A64.Flow.Hello1 (mWC)
open Spike.Lib.A64.Flow.HelloM (wcF wcJ0)
open Spike.Lib.A64.WakePh.MainGlue (FS)
open Spike.Lib.A64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.A64.HelloPh.Land (ref1H Jr1LH fstable_FS)
open Spike.Lib.HelloH2G (GJ1H)
open Spike.Lib.WakeLoadT (L0T)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

/-- `wc_main`'s region at the call (`HelloM.wcR`). -/
local notation "WR" => Spike.Lib.A64.Flow.HelloM.wcR

/-! ## The pinned ghost -/

/-- **The box's ghost at the real run** (`GJ1H` with the region and frame condition pinned): `R` is `wc_main`'s
region `wcR (swR v (-helloLsw) 0) helloD` and `F` its frame condition at the call over the start's `FS` at `v`, from
the caller's state `m1`, `σ1`. -/
def GJ1RH (L : RuntimeLayout) (lbl1 : Lbl) (lr : WeakMem.AllocLabel) (R : Region) (F : MachineData → Prop)
    (J1 : FAS → Ctl → Prop) (t : UInt64) : Prop :=
  GJ1H L lbl1 lr R F J1 t ∧ ∃ (v : BitVec 64) (m1 : MachineData) (σ1 : FAS),
    R = WR (swR v (-helloLsw) 0) helloD ∧
      F = wcF (swR v (-helloLsw) 0) helloD (FS L (Spike.Lib.A64.Rt.rS0 L) helloLsw 0#64 v) m1 σ1

/-- **`H1GAH` but its region and frame condition fields and `hpl`** (`hi80`, `fcl`, `fcg`, `hR8`, `hFr`, `hunF`,
`hF0`, `hpl`, which `hP_of` discharges at `GJ1RH`); the owners of the rest in the module doc. -/
structure H1GAH0 (L : RuntimeLayout) (W X : FragS isaLSE2) (Wc : Frag isaLSE2)
    (ms : List TermRun.Frame → MemSide isaLSE2) (p : Prog) (lbl : Lbl) (l : WeakMem.AllocLabel) (b : Nat)
    (ws : List TermRun.Word) (a : BitVec 64) (ar : Arena) (Dt Cw : State → Prop) (Ctx : FragS isaLSE2) (lsize : Lsize)
    (frM : Ctl → TermRun.Frame) (R : Region) (F : MachineData → Prop) (J1 : FAS → Ctl → Prop) (tp : UInt64) :
    Prop where
  /-- `HMidPAH.wcWf`. -/
  wcWf : WcMainWH (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc R F F (tpXa (ms []) tp) J1 (SBH l b ws)
    (QBH l b ws)
  /-- `HMidPAH.res`. -/
  res : ∀ g : Reserve.G × Ctl, g.1.ra = (L.lab ".L22_wc_main.sp3").toBitVec →
    ∀ nd, ReserveW (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc (rARH R)
      (fun m => F m ∧ CallerCells R (-144) (-48) 0 m ∧ ResCtxH L.lab R
        (rNH (tpXa (ms []) tp) L.lab J1 (SBH l b ws) (QBH l b ws) .call).J g m) ⟨g.1, 0#64, g.2⟩ nd
  /-- `HMidPAH.tcb`. -/
  tcb : ∀ c0 sl me cA fr, MidG (SBH l b ws) c0 cA ∧ FrMGH J1 fr sl me →
    ∀ g : Ret0.AllocTcb.G, g.ra = (L.lab ".L22_wc_main.sp4").toBitVec →
    ∀ nd, TcbWG (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc (R.callee (-144) (-192) 0)
      (fun mm => F mm ∧ CallerCells R (-144) (-192) 0 mm ∧ TcbCtxH L.lab R (wcNCH L.lab c0 sl me cA fr).J c0 g mm)
      (tcb2QH g c0) nd
  /-- `HMidPAH.resA`. -/
  resA : ∀ g : Reserve.G × Ctl, ResOkA (ms []) F L.exe L.endPc (rARH R) F ⟨g.1, 0#64, g.2⟩
  /-- `HMidPAH.hdrA`. -/
  hdrA : ∀ c0 g, Ret0.StOk (ms []) F L.exe L.endPc (hdrA L.lab (tcb2QH g c0)) ((tcb2QH g c0).h ||| 1#64 <<< 36)
  /-- `HMidPAH.tcbA`. -/
  tcbA : ∀ c0 g, TcbOkGA (ms []) F L.exe L.endPc (R.callee (-144) (-192) 0) F (tcb2QH g c0)
  /-- `HMidPAH.tid`. -/
  tid : (ms []).rt (tH L.lab + 56#64).toNat ∧ (ms []).mp ⟨tH L.lab + 56#64, 8⟩ true ∧
    (ms []).G ⟨tH L.lab + 56#64, 8⟩ ((1#64).setWidth 128) ∧
    ∀ m', F m' → Mem.loadInt m'.dmem (tH L.lab + 56#64) 8 = none
  /-- `HMidPAH.wcl`. -/
  wcl : ∀ s c sl me cA fr, At L.exe L.endPc R F (wcNSH L.lab c (tH L.lab) (kOf L.lab) sl me cA fr) s c →
    SpawnSrcH l ws c → cA.toNat = b → FrMGH J1 fr sl me → StackM (r1Of L.lab) s.st.1 → W s c [] ∧ Wc s c
  /-- The level lift from `WSH` at main's frame, at a state writing off the arena (`hti_H`'s `hWX`). -/
  hWX : ∀ c0 cA, MidG (SBH l b ws) c0 cA → ∀ s c,
    WSH L a ar p Dt Cw Ctx lbl lsize (frM c0) (X0TH L (L.lab siteL)) s c → Spike.Lib.A64.HelloW2.OffW ar s →
      W s c [] ∧ X s c []
  /-- The thread init's fields (`hti_H`'s `hfld`). -/
  hfld : ∀ e ∈ Ret0.ThreadInit.fields (tH L.lab) (Ret0.stacksA L.lab + 16384#64),
    Ret0.StOk (ms []) F L.exe L.endPc (tH L.lab + BitVec.ofNat 64 e.1) e.2
  /-- The take's facts (`hti_H`'s `htk`). -/
  htk : ∀ (c0 : Ctl) (R' : Region) (F' : MachineData → Prop), (∀ m, F' m → F m) →
    R' = R.callee (-144) (-256) 0 → ∀ (g : Ret0.ThreadInit.G) (g' : Ret0.StackTake.G),
    Spike.Lib.A64.Rt.TakeOkA (ms []) F L.exe L.endPc (R'.callee (-48) (-208) 0) F'
      (Ret0.tiTake (tiQ (tH L.lab) c0 g) g')

/-- **`H1GAH0` but `hWX`** (the level lift, a projection at the root's choices: `HelloRootInst.hWX_I`); `toH0`
adds it back. -/
structure H1GAH0W (L : RuntimeLayout) (W X : FragS isaLSE2) (Wc : Frag isaLSE2)
    (ms : List TermRun.Frame → MemSide isaLSE2) (p : Prog) (lbl : Lbl) (l : WeakMem.AllocLabel) (b : Nat)
    (ws : List TermRun.Word) (a : BitVec 64) (ar : Arena) (Dt Cw : State → Prop) (Ctx : FragS isaLSE2) (lsize : Lsize)
    (frM : Ctl → TermRun.Frame) (R : Region) (F : MachineData → Prop) (J1 : FAS → Ctl → Prop) (tp : UInt64) :
    Prop where
  /-- `HMidPAH.wcWf`. -/
  wcWf : WcMainWH (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc R F F (tpXa (ms []) tp) J1 (SBH l b ws)
    (QBH l b ws)
  /-- `HMidPAH.res`. -/
  res : ∀ g : Reserve.G × Ctl, g.1.ra = (L.lab ".L22_wc_main.sp3").toBitVec →
    ∀ nd, ReserveW (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc (rARH R)
      (fun m => F m ∧ CallerCells R (-144) (-48) 0 m ∧ ResCtxH L.lab R
        (rNH (tpXa (ms []) tp) L.lab J1 (SBH l b ws) (QBH l b ws) .call).J g m) ⟨g.1, 0#64, g.2⟩ nd
  /-- `HMidPAH.tcb`. -/
  tcb : ∀ c0 sl me cA fr, MidG (SBH l b ws) c0 cA ∧ FrMGH J1 fr sl me →
    ∀ g : Ret0.AllocTcb.G, g.ra = (L.lab ".L22_wc_main.sp4").toBitVec →
    ∀ nd, TcbWG (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc (R.callee (-144) (-192) 0)
      (fun mm => F mm ∧ CallerCells R (-144) (-192) 0 mm ∧ TcbCtxH L.lab R (wcNCH L.lab c0 sl me cA fr).J c0 g mm)
      (tcb2QH g c0) nd
  /-- `HMidPAH.resA`. -/
  resA : ∀ g : Reserve.G × Ctl, ResOkA (ms []) F L.exe L.endPc (rARH R) F ⟨g.1, 0#64, g.2⟩
  /-- `HMidPAH.hdrA`. -/
  hdrA : ∀ c0 g, Ret0.StOk (ms []) F L.exe L.endPc (hdrA L.lab (tcb2QH g c0)) ((tcb2QH g c0).h ||| 1#64 <<< 36)
  /-- `HMidPAH.tcbA`. -/
  tcbA : ∀ c0 g, TcbOkGA (ms []) F L.exe L.endPc (R.callee (-144) (-192) 0) F (tcb2QH g c0)
  /-- `HMidPAH.tid`. -/
  tid : (ms []).rt (tH L.lab + 56#64).toNat ∧ (ms []).mp ⟨tH L.lab + 56#64, 8⟩ true ∧
    (ms []).G ⟨tH L.lab + 56#64, 8⟩ ((1#64).setWidth 128) ∧
    ∀ m', F m' → Mem.loadInt m'.dmem (tH L.lab + 56#64) 8 = none
  /-- `HMidPAH.wcl`. -/
  wcl : ∀ s c sl me cA fr, At L.exe L.endPc R F (wcNSH L.lab c (tH L.lab) (kOf L.lab) sl me cA fr) s c →
    SpawnSrcH l ws c → cA.toNat = b → FrMGH J1 fr sl me → StackM (r1Of L.lab) s.st.1 → W s c [] ∧ Wc s c
  /-- The thread init's fields (`hti_H`'s `hfld`). -/
  hfld : ∀ e ∈ Ret0.ThreadInit.fields (tH L.lab) (Ret0.stacksA L.lab + 16384#64),
    Ret0.StOk (ms []) F L.exe L.endPc (tH L.lab + BitVec.ofNat 64 e.1) e.2
  /-- The take's facts (`hti_H`'s `htk`). -/
  htk : ∀ (c0 : Ctl) (R' : Region) (F' : MachineData → Prop), (∀ m, F' m → F m) →
    R' = R.callee (-144) (-256) 0 → ∀ (g : Ret0.ThreadInit.G) (g' : Ret0.StackTake.G),
    Spike.Lib.A64.Rt.TakeOkA (ms []) F L.exe L.endPc (R'.callee (-48) (-208) 0) F'
      (Ret0.tiTake (tiQ (tH L.lab) c0 g) g')

/-- **`H1GAH0` from `H1GAH0W` and the level lift `hWX`.** -/
theorem H1GAH0W.toH0 {L : RuntimeLayout} {W X : FragS isaLSE2} {Wc : Frag isaLSE2}
    {ms : List TermRun.Frame → MemSide isaLSE2} {p : Prog} {lbl : Lbl} {l : WeakMem.AllocLabel} {b : Nat}
    {ws : List TermRun.Word} {a : BitVec 64} {ar : Arena} {Dt Cw : State → Prop} {Ctx : FragS isaLSE2} {lsize : Lsize}
    {frM : Ctl → TermRun.Frame} {R : Region} {F : MachineData → Prop} {J1 : FAS → Ctl → Prop} {tp : UInt64}
    (h : H1GAH0W L W X Wc ms p lbl l b ws a ar Dt Cw Ctx lsize frM R F J1 tp)
    (hWX : ∀ c0 cA, MidG (SBH l b ws) c0 cA → ∀ s c,
      WSH L a ar p Dt Cw Ctx lbl lsize (frM c0) (X0TH L (L.lab siteL)) s c → Spike.Lib.A64.HelloW2.OffW ar s →
        W s c [] ∧ X s c []) :
    H1GAH0 L W X Wc ms p lbl l b ws a ar Dt Cw Ctx lsize frM R F J1 tp :=
  ⟨h.wcWf, h.res, h.tcb, h.resA, h.hdrA, h.tcbA, h.tid, h.wcl, hWX, h.hfld, h.htk⟩

/-- **`H1GAH0W` but its runtime fields** (`resA`, `hdrA`, `tcbA`, `tid`, `hfld`, `htk`, which `H2Rt` proves at
`h2`'s side `ms2H` and the root instance plugs: `HelloRootBase.h0W_I`); discharged at the root instance by
`CalRootI.h0V_I` (`wcWf`, `wcl`, `res`, `tcb`); `toW` adds the runtime fields back. -/
structure H1GAH0V (L : RuntimeLayout) (W : FragS isaLSE2) (Wc : Frag isaLSE2)
    (ms : List TermRun.Frame → MemSide isaLSE2) (l : WeakMem.AllocLabel) (b : Nat)
    (ws : List TermRun.Word) (R : Region) (F : MachineData → Prop) (J1 : FAS → Ctl → Prop) (tp : UInt64) :
    Prop where
  /-- `HMidPAH.wcWf`. -/
  wcWf : WcMainWH (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc R F F (tpXa (ms []) tp) J1 (SBH l b ws)
    (QBH l b ws)
  /-- `HMidPAH.res`. -/
  res : ∀ g : Reserve.G × Ctl, g.1.ra = (L.lab ".L22_wc_main.sp3").toBitVec →
    ∀ nd, ReserveW (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc (rARH R)
      (fun m => F m ∧ CallerCells R (-144) (-48) 0 m ∧ ResCtxH L.lab R
        (rNH (tpXa (ms []) tp) L.lab J1 (SBH l b ws) (QBH l b ws) .call).J g m) ⟨g.1, 0#64, g.2⟩ nd
  /-- `HMidPAH.tcb`. -/
  tcb : ∀ c0 sl me cA fr, MidG (SBH l b ws) c0 cA ∧ FrMGH J1 fr sl me →
    ∀ g : Ret0.AllocTcb.G, g.ra = (L.lab ".L22_wc_main.sp4").toBitVec →
    ∀ nd, TcbWG (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc (R.callee (-144) (-192) 0)
      (fun mm => F mm ∧ CallerCells R (-144) (-192) 0 mm ∧ TcbCtxH L.lab R (wcNCH L.lab c0 sl me cA fr).J c0 g mm)
      (tcb2QH g c0) nd
  /-- `HMidPAH.wcl`. -/
  wcl : ∀ s c sl me cA fr, At L.exe L.endPc R F (wcNSH L.lab c (tH L.lab) (kOf L.lab) sl me cA fr) s c →
    SpawnSrcH l ws c → cA.toNat = b → FrMGH J1 fr sl me → StackM (r1Of L.lab) s.st.1 → W s c [] ∧ Wc s c

/-- **`H1GAH0V.res`'s statement**, named so the root's base can carry it as a field. -/
abbrev ResV (L : RuntimeLayout) (W : FragS isaLSE2) (ms : List TermRun.Frame → MemSide isaLSE2) (l : WeakMem.AllocLabel)
    (b : Nat) (ws : List TermRun.Word) (R : Region) (F : MachineData → Prop) (J1 : FAS → Ctl → Prop) (tp : UInt64) :
    Prop :=
  ∀ g : Reserve.G × Ctl, g.1.ra = (L.lab ".L22_wc_main.sp3").toBitVec →
    ∀ nd, ReserveW (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc (rARH R)
      (fun m => F m ∧ CallerCells R (-144) (-48) 0 m ∧ ResCtxH L.lab R
        (rNH (tpXa (ms []) tp) L.lab J1 (SBH l b ws) (QBH l b ws) .call).J g m) ⟨g.1, 0#64, g.2⟩ nd

/-- **`H1GAH0V.tcb`'s statement**, named so the root's base can carry it as a field. -/
abbrev TcbV (L : RuntimeLayout) (W : FragS isaLSE2) (l : WeakMem.AllocLabel) (b : Nat) (ws : List TermRun.Word)
    (R : Region) (F : MachineData → Prop) (J1 : FAS → Ctl → Prop) : Prop :=
  ∀ c0 sl me cA fr, MidG (SBH l b ws) c0 cA ∧ FrMGH J1 fr sl me →
    ∀ g : Ret0.AllocTcb.G, g.ra = (L.lab ".L22_wc_main.sp4").toBitVec →
    ∀ nd, TcbWG (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc (R.callee (-144) (-192) 0)
      (fun mm => F mm ∧ CallerCells R (-144) (-192) 0 mm ∧ TcbCtxH L.lab R (wcNCH L.lab c0 sl me cA fr).J c0 g mm)
      (tcb2QH g c0) nd

/-- **`H1GAH0W` from `H1GAH0V` and the runtime fields.** -/
theorem H1GAH0V.toW {L : RuntimeLayout} {W X : FragS isaLSE2} {Wc : Frag isaLSE2}
    {ms : List TermRun.Frame → MemSide isaLSE2} {p : Prog} {lbl : Lbl} {l : WeakMem.AllocLabel} {b : Nat}
    {ws : List TermRun.Word} {a : BitVec 64} {ar : Arena} {Dt Cw : State → Prop} {Ctx : FragS isaLSE2} {lsize : Lsize}
    {frM : Ctl → TermRun.Frame} {R : Region} {F : MachineData → Prop} {J1 : FAS → Ctl → Prop} {tp : UInt64}
    (h : H1GAH0V L W Wc ms l b ws R F J1 tp)
    (resA : ∀ g : Reserve.G × Ctl, ResOkA (ms []) F L.exe L.endPc (rARH R) F ⟨g.1, 0#64, g.2⟩)
    (hdrA : ∀ c0 g, Ret0.StOk (ms []) F L.exe L.endPc (hdrA L.lab (tcb2QH g c0)) ((tcb2QH g c0).h ||| 1#64 <<< 36))
    (tcbA : ∀ c0 g, TcbOkGA (ms []) F L.exe L.endPc (R.callee (-144) (-192) 0) F (tcb2QH g c0))
    (tid : (ms []).rt (tH L.lab + 56#64).toNat ∧ (ms []).mp ⟨tH L.lab + 56#64, 8⟩ true ∧
      (ms []).G ⟨tH L.lab + 56#64, 8⟩ ((1#64).setWidth 128) ∧
      ∀ m', F m' → Mem.loadInt m'.dmem (tH L.lab + 56#64) 8 = none)
    (hfld : ∀ e ∈ Ret0.ThreadInit.fields (tH L.lab) (Ret0.stacksA L.lab + 16384#64),
      Ret0.StOk (ms []) F L.exe L.endPc (tH L.lab + BitVec.ofNat 64 e.1) e.2)
    (htk : ∀ (c0 : Ctl) (R' : Region) (F' : MachineData → Prop), (∀ m, F' m → F m) →
      R' = R.callee (-144) (-256) 0 → ∀ (g : Ret0.ThreadInit.G) (g' : Ret0.StackTake.G),
      Spike.Lib.A64.Rt.TakeOkA (ms []) F L.exe L.endPc (R'.callee (-48) (-208) 0) F'
        (Ret0.tiTake (tiQ (tH L.lab) c0 g) g')) :
    H1GAH0W L W X Wc ms p lbl l b ws a ar Dt Cw Ctx lsize frM R F J1 tp :=
  ⟨h.wcWf, h.res, h.tcb, resA, hdrA, tcbA, tid, h.wcl, hfld, htk⟩

section Land

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Scc.Sem.Entry) (rd : TermRun.Word → Prop) (ls : Lsize)

set_option hygiene false in
local notation "IH" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw IH

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)

/-- **`Box.box_regH` with the region and frame condition named**: at a box store's landing in `wc_main`'s region
at `v` and frame condition over `FS` at `v`, `v` is the first stack's top, the region OK, 16-aligned, its frame
condition stable in it and inside `F0`, `helloD` deep, its base `80` under the first stack's top. -/
theorem box_regRH {F0 : MachineData → Prop}
    (hF0 : ∀ v m1 σ1 m, wcF (swR v (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 v) m1 σ1 m → F0 m)
    {l : WeakMem.AllocLabel} {b n : Nat} {v : BitVec 64} {σC : FAS} {m1 : MachineData} {σ1 : FAS}
    {Jc : FAS → Ctl → Prop} {l' : WeakMem.AllocLabel} {A : Nat} {s : State} {c : Ctl}
    (hA : Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc (WR (swR v (-helloLsw) 0) helloD)
      (wcF (swR v (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 v) m1 σ1)
      (bXH (ref1H (asm := asm) hpw i0 E rd ls l b n []) (Ly).lab (wcJ0 (mWC (Ly).lab σC Jc).J σ1) l' A) s c) :
    ((WR (swR v (-helloLsw) 0) helloD).OK ∧ (WR (swR v (-helloLsw) 0) helloD).base.toNat % 16 = 0 ∧
      FStable (WR (swR v (-helloLsw) 0) helloD)
        (wcF (swR v (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 v) m1 σ1) ∧
      (WR (swR v (-helloLsw) 0) helloD).lo ≤ -helloD ∧ 0 ≤ (WR (swR v (-helloLsw) 0) helloD).hi ∧
      (WR (swR v (-helloLsw) 0) helloD).base.toNat + 80 = (Ly).stacksA.toNat + 16384) ∧
      (∀ m, wcF (swR v (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 v) m1 σ1 m → F0 m) := by
  have hA0 := hA
  obtain ⟨-, -, -, -, σ, -, hFm, -⟩ := hA
  have hv : v = Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64 := hFm.1.2.1.1
  subst hv
  obtain ⟨hok, hal, hF⟩ := fstable_FS hpw i0
  obtain ⟨hR, hRal, hRF⟩ := Spike.Lib.A64.Flow.HelloM.wcR_ok (D := helloD) (by decide) (by decide) hok hal hF
    (by show (-helloLsw : Int) ≤ -80 - helloD; decide) (by show (0 : Int) ≤ 0; decide) m1 σ1
  have hT : (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64).toNat = (Ly).stacksA.toNat + 16384 := by
    rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.top0_toNat _
  have hb : ((WR (swR (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-helloLsw) 0) helloD).base.toNat
      : Int) = (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64).toNat + -80 :=
    Spike.Lib.Region.callee_base (hi' := 0) hok (kc := -80) (lo' := -helloD)
      (by show (-helloLsw : Int) ≤ -80 + -helloD; decide) (by decide) (by simp [swR])
  rw [hT] at hb
  have hRlo : (WR (swR (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-helloLsw) 0) helloD).lo =
    -helloD := rfl
  have hRhi : (WR (swR (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-helloLsw) 0) helloD).hi =
    0 := rfl
  exact ⟨⟨hR, hRal, hRF, by rw [hRlo]; exact Int.le_refl _, by rw [hRhi]; decide, by omega⟩, hF0 _ m1 σ1⟩

/-- **A pinned box store's landing is `BoxMH` at the pinned ghost** (`Box.boxMH_landingH` at `GJ1RH`): the ghost's
witness `v`, `m1`, `σ1` is the landing's own (`GsH1`'s), produced, not assumed. -/
theorem boxMH_landingRH {F0 : MachineData → Prop}
    (hF0 : ∀ v m1 σ1 m, wcF (swR v (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 v) m1 σ1 m → F0 m)
    {l : WeakMem.AllocLabel} {b n : Nat} {v : BitVec 64} {σC : FAS} {m1 : MachineData} {σ1 : FAS}
    {l' : WeakMem.AllocLabel} {A : Nat} {s : State} {c : Ctl}
    (hslot : σC.slot (-80) = pinA (Ly).lab + 0#64 + 8#64)
    (hA : Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc (WR (swR v (-helloLsw) 0) helloD)
      (wcF (swR v (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 v) m1 σ1)
      (bXH (ref1H (asm := asm) hpw i0 E rd ls l b n []) (Ly).lab (wcJ0 (mWC (Ly).lab σC (Jr1LH hpw i0 l b)).J σ1) l'
          A) s c)
    (htp : TP (TV) s) :
    BoxMH (Ly) (ref1H (asm := asm) hpw i0 E rd ls l b n []) F0 (GJ1RH (Ly) (Spike.Lib.A64ConsumerA.upd (LB) l b) l) l' A
      (slWsH l) 1 s c := by
  obtain ⟨⟨hR, hRal, hRF, hlo, hhi, hbase⟩, hF⟩ := box_regRH hpw i0 E rd ls hF0 hA
  have hA0 := hA
  obtain ⟨-, -, -, -, σ, -, -, q, ⟨σe, ⟨-, σx, ⟨hq0, -⟩, -⟩, -⟩, -, hc, -⟩ := hA
  obtain ⟨T, ht⟩ := q.2.term
  rw [hq0] at ht
  obtain ⟨hx, ha, hee⟩ := Expr.let_.inj ht
  have ha' := (Op.new.inj ha).1
  have hev := q.2.ev
  rw [hq0, ← ha'] at hev
  have hτ : q.1.τ = .int := (Prod.mk.inj (Option.some.inj hev)).1.symm
  rw [← hx, ← hee, hτ, hq0] at hc
  subst hc
  refine ⟨_, _, _, TV, ⟨hR, hRal, hRF, hlo, hhi, hbase, Spike.Lib.A64.HelloPh.Box.tv_toNat hpw i0, rfl, hF⟩,
    ⟨⟨σC, σ1, Jr1LH hpw i0 l b, hslot, fun _ _ h => h.2, rfl⟩, v, m1, σ1, rfl, rfl⟩, ⟨hA0, htp⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Non-vacuity: `GJ1RH` holds at the real run's region and frame condition**: for `wc_main`'s region at any `v`
and its frame condition from any caller's state `m1`, `σ1`, given a caller's state `σC` whose slot `-80` holds
main's TCB (as `GsH1` pins it), with `J1` the pinned entry invariant (`Jr1LH`). `boxMH_landingRH` produces exactly
this witness at every pinned landing. -/
example {l : WeakMem.AllocLabel} {b : Nat} {v : BitVec 64} {σC : FAS} {m1 : MachineData} {σ1 : FAS}
    (hslot : σC.slot (-80) = pinA (Ly).lab + 0#64 + 8#64) :
    GJ1RH (Ly) (Spike.Lib.A64ConsumerA.upd (LB) l b) l (WR (swR v (-helloLsw) 0) helloD)
      (wcF (swR v (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 v) m1 σ1)
      (wcJ0 (mWC (Ly).lab σC (Jr1LH hpw i0 l b)).J σ1) (TV) :=
  ⟨⟨σC, σ1, Jr1LH hpw i0 l b, hslot, fun _ _ h => h.2, rfl⟩, v, m1, σ1, rfl, rfl⟩

/-- **`hCP_of`'s `hCI` at the pinned ghosts** (`Box.hCI_H` at `GJ1RH`, `GJ1H`'s half read). -/
theorem hCI_RH {F0 : MachineData → Prop} {W : FragS isaLSE2} {Wc : Spike.Lib.Frag isaLSE2}
    {l : WeakMem.AllocLabel} {b : Nat} {l' : WeakMem.AllocLabel} {b' n' : Nat}
    (hl : (LB) l = none) (hl' : Spike.Lib.A64ConsumerA.upd (LB) l b l' = none) :
    ∀ s c fs, Spike.Lib.HelloHMid.CloneMidH (Ly) F0 (GJ1RH (Ly) (Spike.Lib.A64ConsumerA.upd (LB) l b) l) W Wc l' b'
        (slWsH l) n' s c fs →
      Spike.Lib.HelloPreA.CloneInvH (Ly) (Ly).endPc
        (Spike.Lib.A64ConsumerA.upd (Spike.Lib.A64ConsumerA.upd (LB) l b) l' b') s c [] :=
  Spike.Lib.HelloH2CP.cloneInvH_of_mid (by simp [Spike.Lib.A64ConsumerA.upd])
    fun R F J1 t h => Spike.Lib.HelloH2G.hG_of hl' (Spike.Lib.A64.HelloPh.Box.hmt_H hpw i0 hl) R F J1 t h.1

set_option hygiene false in
local notation "AR" => Spike.Lib.WakeOD.arW hpw IH

set_option hygiene false in
local notation "R1" => Spike.Lib.A64.Rt.PreChild.r1Of (Ly).lab

/-- **The box's landings in `h2`'s fragment at the pinned ghosts** (`LandR1U.hland2_ofU` with `boxMH_landingRH`):
from `H2StmtH` at the root's box `BoxMH … (GJ1RH (Ly) (upd LB l b) l) … ∧ U r1`, every pinned landing with `r1Of`
unmapped is in the level's allocation fragment. -/
theorem hland2_boxMRU {W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {K : State → State → Prop}
    {ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
    {L : RuntimeLayout} {endPc : Int64} {F0 : MachineData → Prop}
    {inv0 : FragS isaLSE2} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {l : WeakMem.AllocLabel} {b n : Nat}
    (h2 : Spike.Lib.HelloPreA.H2StmtH W2 K (AR) (LB) ms2 L endPc
      (fun l b n l' A n' s c => BoxMH (Ly) (ref1H (asm := asm) hpw i0 E rd ls l b n []) F0
        (GJ1RH (Ly) (Spike.Lib.A64ConsumerA.upd (LB) l b) l) l' A (slWsH l) n' s c ∧
        Spike.Lib.A64.KeepUn.U (R1) s) inv2)
    (hl : (LB) l = none) (hb : Spike.Lib.HeapLand.AllocLand (AR).heap (AR).cells b n)
    (hF0 : ∀ v m1 σ1 m, wcF (swR v (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 v) m1 σ1 m → F0 m) :
    Spike.Lib.A64.HelloPh.LandR1U.HLand2U (asm := asm) hpw i0 E rd ls l b n
      ((Spike.Lib.A64ConsumerA.msOfA (Ly).Λ
        ((Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks asm (Ly).Λ) rd
        (Spike.Lib.HelloGOf2H.gWH hpw IH (Spike.Lib.WakeHG.cTW hpw IH))
        (fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) s) (AR)
        (Spike.Lib.A64ConsumerA.I3 (AR) (LB) (Spike.Lib.WakeLoadT.ls0T ls) inv0 inv1 inv2)
        (Spike.Lib.A64ConsumerA.upd (LB) l b) (Spike.Lib.A64ConsumerA.updN (Spike.Lib.WakeLoadT.ls0T ls) l n) []).xa) :=
  Spike.Lib.A64.HelloPh.LandR1U.hland2_ofU hpw i0 E rd ls l b n h2 hl hb fun Lnd hG l' A s c _ hL hu => by
    obtain ⟨v, σC, m1, σ1, hslot, rfl⟩ := hG
    obtain ⟨-, hA, htp⟩ := hL
    exact ⟨boxMH_landingRH hpw i0 E rd ls hF0 hslot hA htp, hu⟩

end Land

/-! ## `hP` at the pinned ghost -/

section HP

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw i

/-- **`H1GAH` at the pinned ghost** (`HelloRootPrem.hP`'s conclusion): the region and frame condition fields from
`GJ1RH`'s `wcR`/`wcF` (`hi80`, `hR8`: the bounds `0`, `-400`; `fcg`, `fcl`, `hF0`: `BoxRF.wcF_dmemH`,
`wcF_takeMemH`, `stackOff_r0_boxH`; `hFr`, `hunF`: `FS`'s `WordsNoneP` by `BoxRF.rtF_of_wn`, `unF_of_wn`), the
placement `hpl` from `GJ1H` at the box's label `l` fresh at `lbl1` and main's id at the TCB (`SpawnPl.hpl_GJ1H`, at
the placement `upd lbl1 l b` and rodata's slice `slWsH lr`), the rest `H1GAH0`'s. -/
theorem hP_of (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    {W X : FragS isaLSE2} {Wc : Frag isaLSE2} {ms : List TermRun.Frame → MemSide isaLSE2} {p : Prog}
    {l : WeakMem.AllocLabel} {b : Nat} {a : BitVec 64} {ar : Arena} {Dt Cw : State → Prop}
    {Ctx : FragS isaLSE2} {lsize : Lsize} {frM : Ctl → TermRun.Frame} {lbl1 : Lbl} {lr : WeakMem.AllocLabel}
    {R : Region} {F : MachineData → Prop} {J1 : FAS → Ctl → Prop} {tp : UInt64}
    (hl : lbl1 l = none) (hmt : lbl1 (Spike.Lib.WakeT1.mainTidLbl 2) = some ((Ly).pinA.toNat + 8))
    (hG : GJ1RH (Ly) lbl1 lr R F J1 tp)
    (h0 : H1GAH0 (Ly) W X Wc ms p (Spike.Lib.A64ConsumerA.upd lbl1 l b) l b (slWsH lr) a ar Dt Cw Ctx lsize frM R F
      J1 tp) :
    Spike.Lib.HelloH1A.H1GAH (Ly) W X Wc ms p (Spike.Lib.A64ConsumerA.upd lbl1 l b) l b (slWsH lr) a ar Dt Cw Ctx lsize
      frM R F J1 tp := by
  have hpl := Spike.Lib.A64.HelloPh.SpawnPl.hpl_GJ1H (b' := b) hl hmt hG.1
  obtain ⟨-, v, m1, σ1, rfl, rfl⟩ := hG
  exact {
    wcWf := h0.wcWf
    res := h0.res
    tcb := h0.tcb
    resA := h0.resA
    hdrA := h0.hdrA
    tcbA := h0.tcbA
    tid := h0.tid
    wcl := h0.wcl
    hi80 := by show (0 : Int) ≤ 80; decide
    fcl := Spike.Lib.A64.HelloPh.BoxRF.wcF_takeMemH hpw i hA13
    fcg := Spike.Lib.A64.HelloPh.BoxRF.wcF_dmemH
    hR8 := by show (-helloD : Int) % 8 = 0 ∧ (0 : Int) % 8 = 0; decide
    hWX := h0.hWX
    hpl := hpl
    hFr := fun _ h => Spike.Lib.A64.HelloPh.BoxRF.rtF_of_wn _ h.1.1
    hunF := fun a ha _ h => Spike.Lib.A64.HelloPh.BoxRF.unF_of_wn hpw i hpin2 h.1.1 a ha
    hF0 := Spike.Lib.A64.HelloPh.BoxRF.stackOff_r0_boxH hpw i
    hfld := h0.hfld
    htk := h0.htk }

end HP

end Spike.Lib.A64.HelloPh.RootHP

/-- info: 'Spike.Lib.A64.HelloPh.RootHP.box_regRH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootHP.box_regRH

/-- info: 'Spike.Lib.A64.HelloPh.RootHP.boxMH_landingRH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootHP.boxMH_landingRH

/-- info: 'Spike.Lib.A64.HelloPh.RootHP.hCI_RH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootHP.hCI_RH

/-- info: 'Spike.Lib.A64.HelloPh.RootHP.hland2_boxMRU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootHP.hland2_boxMRU

/-- info: 'Spike.Lib.A64.HelloPh.RootHP.H1GAH0W.toH0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootHP.H1GAH0W.toH0

/-- info: 'Spike.Lib.A64.HelloPh.RootHP.hP_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootHP.hP_of

/-- info: 'Spike.Lib.A64.HelloPh.RootHP.H1GAH0V.toW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootHP.H1GAH0V.toW
