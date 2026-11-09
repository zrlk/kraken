/-
**hello.w's `HelloRootPrem.hP` at the box's real ghost** (x86-64; twin of `Spike/Lib/A64HelloRootHP.lean`):
`H1GAHG` at the pinned ghost `X64HelloRootHPD.GJ1RH` from the fields that depend on more than the region and frame
condition (`H1GAH0`, the twin of wake's `WakeH1A.H1GA`), and its splits by who discharges them at the root.

- `H1GAH0`: `H1GAHG` at `WSH` without `hi96`, `fcl`, `fcg`, `hR8`, `hFr`, `hunF`, `hF0`, `hpl`, which the pinned ghost's
  region and frame condition discharge.
- `H1GAH0W`, `H1GAH0W.toH0`: `H1GAH0` but `hWX` (the level lift, a projection at the root's choices), and back given
  `hWX`.
- `H1GAH0V`, `H1GAH0V.toW`: `H1GAH0W` but its runtime fields (`resA`, `hdrA`, `tcbA`, `tid`, `hfld`, `htk`, which
  `h2`'s runtime facts prove), and back given them.
- `ResV`, `TcbV`: `H1GAH0V.res`'s and `.tcb`'s statements, named so the root's base can carry them as fields.
- `hCI_RH`: `X64HelloH2CP.cloneInvH_of_mid`'s `hCI` at `GJ1RH` (`h2`'s Box).
- `hP_ofG`: `H1GAHG` from `GJ1RH`, `H1GAH0W` and a level lift at any start level: `hi96`, `hR8` (the region's
  bounds `-392`, `16`), `fcg`, `fcl`, `hF0` (`BoxRF.wcF_dmemH`, `wcF_takeMemH`, `stackOff_r0_boxH`), `hFr`, `hunF`
  (`FS`'s `WordsNoneP`, `BoxRF.rtF_of_wn`, `unF_of_wn`) and `hpl` (`GJ1H`'s entry slice, `SpawnPl.hplQ_GJ1H`) are
  discharged (AArch64's `hP_of` is the same at `H1GAH0`).

## Unlike AArch64

- As `X64HelloH1A.H1GAHG` against AArch64's `H1GAH`: `wcWf`, `tcb` and `hWX` are at `MidG (QBH l b ws)` (the box
  is published at `.x25`'s `mfence`; AArch64 `SBH`), the reserve returns to `.Lwc_main.x1` and the TCB's
  allocation to `x24L` (AArch64 `.sp3`, `.sp4`), the callees sit at `-136` with `hi' = 8` (AArch64 `-144`,
  `hi' = 0`), the stores are `Ret0.StOk (ms []) F` (no `exe`, `endPc`), and the take's ghosts are two
  `Ret0.AllocTcb.G`.
- The pinned ghost's region is `wc_main`'s frame at the saved `%rbp`, `(wcR (RS helloLsw v) helloD).fp (-8)`
  (`X64HelloRootHPD`), its bounds `-392` and `16`.
-/
import Spike.Lib.X64HelloH1A
import Spike.Lib.X64HelloRootHPD
import Spike.Lib.X64HelloBoxRF
import Spike.Lib.X64HelloBoxM
import Spike.Lib.X64HelloSpawnPl
import Spike.Lib.X64HelloH2CP

namespace Spike.Lib.X64.HelloPh.RootHP

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.HelloWc (WcMainWH FrMGH rNH ResCtxH TcbCtxH wcNCRH tcb2QH tH rARH x24L)
open Spike.Lib.X64.HelloPh.WcSp6 (wcNSH)
open Spike.Lib.X64.Flow.WakeWc (MidG kOf tiQ)
open Spike.Lib.X64.Flow.Ret0 (CallerCells StackM StOk)
open Spike.Lib.X64.Flow.Ret0.StackTake (siteL)
open Spike.Lib.X64.Rt (TcbOkGA hdrA RuntimeLayout TcbWG)
open Spike.Lib.X64.Rt.Reserve (ResOkA ReserveW)
open Spike.Lib.X64.Rt.PreChild (r1Of)
open Spike.Lib.X64.KeepTP (tpXa)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64HelloHMid (QBH)
open Spike.Lib.X64HelloMainPreSrc (SpawnSrcH)
open Spike.Lib.X64.HelloPh.StartWf (WSH)
open Spike.Lib.X64.HelloPh.Ti2 (X0TH)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

/-! ## `H1GAHG` without its region and frame condition fields -/

/-- **`H1GAHG` at `WSH` but its region and frame condition fields and `hpl`** (`hi96`, `fcl`, `fcg`, `hR8`, `hFr`,
`hunF`, `hF0`, `hpl`, which the pinned ghost discharges). -/
structure H1GAH0 (L : RuntimeLayout) (W X : FragS isa) (Wc : Frag isa)
    (ms : List TermRun.Frame → MemSide isa) (p : Prog) (lbl : Lbl) (l : WeakMem.AllocLabel) (b : Nat)
    (ws : List TermRun.Word) (a : BitVec 64) (ar : Arena) (Dt Cw : State → Prop) (Ctx : FragS isa) (lsize : Lsize)
    (frM : Ctl → TermRun.Frame) (R : Region) (F : MachineData → Prop) (J1 : FAS → Ctl → Prop) (tp : UInt64) :
    Prop where
  /-- `HMidPAH.wcWf`. -/
  wcWf : WcMainWH (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc R F F (tpXa (ms []) tp) J1 (QBH l b ws)
  /-- `HMidPAH.res`. -/
  res : ∀ g : Ret0.AllocTcb.G × Ctl, g.1.ra = (L.lab ".Lwc_main.x1").toBitVec →
    ∀ nd, ReserveW (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc (rARH R)
      (fun m => F m ∧ CallerCells R (-136) (-40) 8 m ∧ ResCtxH L.lab R
        (rNH (tpXa (ms []) tp) L.lab R J1 (QBH l b ws) .call).J g m) ⟨g.1, 0#64, g.2⟩ nd
  /-- `HMidPAH.tcb`. -/
  tcb : ∀ c0 sl me cA fr, MidG (QBH l b ws) c0 cA ∧ FrMGH J1 fr sl me →
    ∀ g : Ret0.AllocTcb.G, g.ra = (L.lab x24L).toBitVec →
    ∀ nd, TcbWG (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc (R.callee (-136) (-184) 8)
      (fun mm => F mm ∧ CallerCells R (-136) (-184) 8 mm ∧
        TcbCtxH L.lab R (wcNCRH L.lab c0 sl me cA fr).J c0 g mm)
      (tcb2QH g c0) nd
  /-- `HMidPAH.resA`. -/
  resA : ∀ g : Ret0.AllocTcb.G × Ctl, ResOkA (ms []) F L.exe L.endPc (rARH R) F ⟨g.1, 0#64, g.2⟩
  /-- `HMidPAH.hdrA`. -/
  hdrA : ∀ c0 g, StOk (ms []) F (hdrA L.lab (tcb2QH g c0)) ((tcb2QH g c0).h ||| 1#64 <<< 36)
  /-- `HMidPAH.tcbA`. -/
  tcbA : ∀ c0 g, TcbOkGA (ms []) F L.exe L.endPc (R.callee (-136) (-184) 8) F (tcb2QH g c0)
  /-- `HMidPAH.tid`. -/
  tid : (ms []).rt (tH L.lab + 56#64).toNat ∧ (ms []).mp ⟨tH L.lab + 56#64, 8⟩ true ∧
    (ms []).G ⟨tH L.lab + 56#64, 8⟩ ((1#64).setWidth 128) ∧
    ∀ m', F m' → Mem.loadInt m'.dmem (tH L.lab + 56#64) 8 = none
  /-- `HMidPAH.wcl`. -/
  wcl : ∀ s c sl me cA fr, At L.exe L.endPc R F (wcNSH L.lab c (tH L.lab) (kOf L.lab) sl me cA fr) s c →
    SpawnSrcH l ws c → cA.toNat = b → FrMGH J1 fr sl me → StackM (r1Of L.lab) s.st.1 → W s c [] ∧ Wc s c
  /-- The level lift from `WSH` at main's frame, at a state writing off the arena (`hti_HOX`'s `hWX`). -/
  hWX : ∀ c0 cA, MidG (QBH l b ws) c0 cA → ∀ s c,
    WSH L a ar p Dt Cw Ctx lbl lsize (frM c0) (X0TH L (L.lab siteL)) s c → Spike.Lib.X64.HelloW2.OffW ar s →
      W s c [] ∧ X s c []
  /-- The thread init's fields (`hti_HOX`'s `hfld`). -/
  hfld : ∀ e ∈ Ret0.ThreadInit.fields (tH L.lab) (Ret0.stacksA L.lab + 16384#64),
    StOk (ms []) F (tH L.lab + BitVec.ofNat 64 e.1) e.2
  /-- The take's facts (`hti_HOX`'s `htk`). -/
  htk : ∀ (c0 : Ctl) (R' : Region) (F' : MachineData → Prop), (∀ m, F' m → F m) →
    R' = R.callee (-136) (-248) 8 → ∀ (g g' : Ret0.AllocTcb.G),
    Spike.Lib.X64.Rt.TakeOkA (ms []) F L.exe L.endPc (R'.callee (-48 - 0) (-200) 8) F'
      (Ret0.tiTake (tiQ (tH L.lab) c0 g) g')

/-- **`H1GAH0` but `hWX`** (the level lift, a projection at the root's choices); `toH0` adds it back. -/
structure H1GAH0W (L : RuntimeLayout) (W X : FragS isa) (Wc : Frag isa)
    (ms : List TermRun.Frame → MemSide isa) (p : Prog) (lbl : Lbl) (l : WeakMem.AllocLabel) (b : Nat)
    (ws : List TermRun.Word) (a : BitVec 64) (ar : Arena) (Dt Cw : State → Prop) (Ctx : FragS isa) (lsize : Lsize)
    (frM : Ctl → TermRun.Frame) (R : Region) (F : MachineData → Prop) (J1 : FAS → Ctl → Prop) (tp : UInt64) :
    Prop where
  /-- `HMidPAH.wcWf`. -/
  wcWf : WcMainWH (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc R F F (tpXa (ms []) tp) J1 (QBH l b ws)
  /-- `HMidPAH.res`. -/
  res : ∀ g : Ret0.AllocTcb.G × Ctl, g.1.ra = (L.lab ".Lwc_main.x1").toBitVec →
    ∀ nd, ReserveW (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc (rARH R)
      (fun m => F m ∧ CallerCells R (-136) (-40) 8 m ∧ ResCtxH L.lab R
        (rNH (tpXa (ms []) tp) L.lab R J1 (QBH l b ws) .call).J g m) ⟨g.1, 0#64, g.2⟩ nd
  /-- `HMidPAH.tcb`. -/
  tcb : ∀ c0 sl me cA fr, MidG (QBH l b ws) c0 cA ∧ FrMGH J1 fr sl me →
    ∀ g : Ret0.AllocTcb.G, g.ra = (L.lab x24L).toBitVec →
    ∀ nd, TcbWG (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc (R.callee (-136) (-184) 8)
      (fun mm => F mm ∧ CallerCells R (-136) (-184) 8 mm ∧
        TcbCtxH L.lab R (wcNCRH L.lab c0 sl me cA fr).J c0 g mm)
      (tcb2QH g c0) nd
  /-- `HMidPAH.resA`. -/
  resA : ∀ g : Ret0.AllocTcb.G × Ctl, ResOkA (ms []) F L.exe L.endPc (rARH R) F ⟨g.1, 0#64, g.2⟩
  /-- `HMidPAH.hdrA`. -/
  hdrA : ∀ c0 g, StOk (ms []) F (hdrA L.lab (tcb2QH g c0)) ((tcb2QH g c0).h ||| 1#64 <<< 36)
  /-- `HMidPAH.tcbA`. -/
  tcbA : ∀ c0 g, TcbOkGA (ms []) F L.exe L.endPc (R.callee (-136) (-184) 8) F (tcb2QH g c0)
  /-- `HMidPAH.tid`. -/
  tid : (ms []).rt (tH L.lab + 56#64).toNat ∧ (ms []).mp ⟨tH L.lab + 56#64, 8⟩ true ∧
    (ms []).G ⟨tH L.lab + 56#64, 8⟩ ((1#64).setWidth 128) ∧
    ∀ m', F m' → Mem.loadInt m'.dmem (tH L.lab + 56#64) 8 = none
  /-- `HMidPAH.wcl`. -/
  wcl : ∀ s c sl me cA fr, At L.exe L.endPc R F (wcNSH L.lab c (tH L.lab) (kOf L.lab) sl me cA fr) s c →
    SpawnSrcH l ws c → cA.toNat = b → FrMGH J1 fr sl me → StackM (r1Of L.lab) s.st.1 → W s c [] ∧ Wc s c
  /-- The thread init's fields (`hti_HOX`'s `hfld`). -/
  hfld : ∀ e ∈ Ret0.ThreadInit.fields (tH L.lab) (Ret0.stacksA L.lab + 16384#64),
    StOk (ms []) F (tH L.lab + BitVec.ofNat 64 e.1) e.2
  /-- The take's facts (`hti_HOX`'s `htk`). -/
  htk : ∀ (c0 : Ctl) (R' : Region) (F' : MachineData → Prop), (∀ m, F' m → F m) →
    R' = R.callee (-136) (-248) 8 → ∀ (g g' : Ret0.AllocTcb.G),
    Spike.Lib.X64.Rt.TakeOkA (ms []) F L.exe L.endPc (R'.callee (-48 - 0) (-200) 8) F'
      (Ret0.tiTake (tiQ (tH L.lab) c0 g) g')

/-- **`H1GAH0` from `H1GAH0W` and the level lift `hWX`.** -/
theorem H1GAH0W.toH0 {L : RuntimeLayout} {W X : FragS isa} {Wc : Frag isa}
    {ms : List TermRun.Frame → MemSide isa} {p : Prog} {lbl : Lbl} {l : WeakMem.AllocLabel} {b : Nat}
    {ws : List TermRun.Word} {a : BitVec 64} {ar : Arena} {Dt Cw : State → Prop} {Ctx : FragS isa} {lsize : Lsize}
    {frM : Ctl → TermRun.Frame} {R : Region} {F : MachineData → Prop} {J1 : FAS → Ctl → Prop} {tp : UInt64}
    (h : H1GAH0W L W X Wc ms p lbl l b ws a ar Dt Cw Ctx lsize frM R F J1 tp)
    (hWX : ∀ c0 cA, MidG (QBH l b ws) c0 cA → ∀ s c,
      WSH L a ar p Dt Cw Ctx lbl lsize (frM c0) (X0TH L (L.lab siteL)) s c → Spike.Lib.X64.HelloW2.OffW ar s →
        W s c [] ∧ X s c []) :
    H1GAH0 L W X Wc ms p lbl l b ws a ar Dt Cw Ctx lsize frM R F J1 tp :=
  ⟨h.wcWf, h.res, h.tcb, h.resA, h.hdrA, h.tcbA, h.tid, h.wcl, hWX, h.hfld, h.htk⟩

/-- **`H1GAH0W` but its runtime fields** (`resA`, `hdrA`, `tcbA`, `tid`, `hfld`, `htk`, which `h2`'s runtime
facts prove); `toW` adds them back. -/
structure H1GAH0V (L : RuntimeLayout) (W : FragS isa) (Wc : Frag isa)
    (ms : List TermRun.Frame → MemSide isa) (l : WeakMem.AllocLabel) (b : Nat)
    (ws : List TermRun.Word) (R : Region) (F : MachineData → Prop) (J1 : FAS → Ctl → Prop) (tp : UInt64) :
    Prop where
  /-- `HMidPAH.wcWf`. -/
  wcWf : WcMainWH (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc R F F (tpXa (ms []) tp) J1 (QBH l b ws)
  /-- `HMidPAH.res`. -/
  res : ∀ g : Ret0.AllocTcb.G × Ctl, g.1.ra = (L.lab ".Lwc_main.x1").toBitVec →
    ∀ nd, ReserveW (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc (rARH R)
      (fun m => F m ∧ CallerCells R (-136) (-40) 8 m ∧ ResCtxH L.lab R
        (rNH (tpXa (ms []) tp) L.lab R J1 (QBH l b ws) .call).J g m) ⟨g.1, 0#64, g.2⟩ nd
  /-- `HMidPAH.tcb`. -/
  tcb : ∀ c0 sl me cA fr, MidG (QBH l b ws) c0 cA ∧ FrMGH J1 fr sl me →
    ∀ g : Ret0.AllocTcb.G, g.ra = (L.lab x24L).toBitVec →
    ∀ nd, TcbWG (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc (R.callee (-136) (-184) 8)
      (fun mm => F mm ∧ CallerCells R (-136) (-184) 8 mm ∧
        TcbCtxH L.lab R (wcNCRH L.lab c0 sl me cA fr).J c0 g mm)
      (tcb2QH g c0) nd
  /-- `HMidPAH.wcl`. -/
  wcl : ∀ s c sl me cA fr, At L.exe L.endPc R F (wcNSH L.lab c (tH L.lab) (kOf L.lab) sl me cA fr) s c →
    SpawnSrcH l ws c → cA.toNat = b → FrMGH J1 fr sl me → StackM (r1Of L.lab) s.st.1 → W s c [] ∧ Wc s c

/-- **`H1GAH0V.res`'s statement**, named so the root's base can carry it as a field. -/
abbrev ResV (L : RuntimeLayout) (W : FragS isa) (ms : List TermRun.Frame → MemSide isa) (l : WeakMem.AllocLabel)
    (b : Nat) (ws : List TermRun.Word) (R : Region) (F : MachineData → Prop) (J1 : FAS → Ctl → Prop) (tp : UInt64) :
    Prop :=
  ∀ g : Ret0.AllocTcb.G × Ctl, g.1.ra = (L.lab ".Lwc_main.x1").toBitVec →
    ∀ nd, ReserveW (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc (rARH R)
      (fun m => F m ∧ CallerCells R (-136) (-40) 8 m ∧ ResCtxH L.lab R
        (rNH (tpXa (ms []) tp) L.lab R J1 (QBH l b ws) .call).J g m) ⟨g.1, 0#64, g.2⟩ nd

/-- **`H1GAH0V.tcb`'s statement**, named so the root's base can carry it as a field. -/
abbrev TcbV (L : RuntimeLayout) (W : FragS isa) (l : WeakMem.AllocLabel) (b : Nat) (ws : List TermRun.Word)
    (R : Region) (F : MachineData → Prop) (J1 : FAS → Ctl → Prop) : Prop :=
  ∀ c0 sl me cA fr, MidG (QBH l b ws) c0 cA ∧ FrMGH J1 fr sl me →
    ∀ g : Ret0.AllocTcb.G, g.ra = (L.lab x24L).toBitVec →
    ∀ nd, TcbWG (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc (R.callee (-136) (-184) 8)
      (fun mm => F mm ∧ CallerCells R (-136) (-184) 8 mm ∧
        TcbCtxH L.lab R (wcNCRH L.lab c0 sl me cA fr).J c0 g mm)
      (tcb2QH g c0) nd

/-- **`H1GAH0W` from `H1GAH0V` and the runtime fields.** -/
theorem H1GAH0V.toW {L : RuntimeLayout} {W X : FragS isa} {Wc : Frag isa}
    {ms : List TermRun.Frame → MemSide isa} {p : Prog} {lbl : Lbl} {l : WeakMem.AllocLabel} {b : Nat}
    {ws : List TermRun.Word} {a : BitVec 64} {ar : Arena} {Dt Cw : State → Prop} {Ctx : FragS isa} {lsize : Lsize}
    {frM : Ctl → TermRun.Frame} {R : Region} {F : MachineData → Prop} {J1 : FAS → Ctl → Prop} {tp : UInt64}
    (h : H1GAH0V L W Wc ms l b ws R F J1 tp)
    (resA : ∀ g : Ret0.AllocTcb.G × Ctl, ResOkA (ms []) F L.exe L.endPc (rARH R) F ⟨g.1, 0#64, g.2⟩)
    (hdrA : ∀ c0 g, StOk (ms []) F (hdrA L.lab (tcb2QH g c0)) ((tcb2QH g c0).h ||| 1#64 <<< 36))
    (tcbA : ∀ c0 g, TcbOkGA (ms []) F L.exe L.endPc (R.callee (-136) (-184) 8) F (tcb2QH g c0))
    (tid : (ms []).rt (tH L.lab + 56#64).toNat ∧ (ms []).mp ⟨tH L.lab + 56#64, 8⟩ true ∧
      (ms []).G ⟨tH L.lab + 56#64, 8⟩ ((1#64).setWidth 128) ∧
      ∀ m', F m' → Mem.loadInt m'.dmem (tH L.lab + 56#64) 8 = none)
    (hfld : ∀ e ∈ Ret0.ThreadInit.fields (tH L.lab) (Ret0.stacksA L.lab + 16384#64),
      StOk (ms []) F (tH L.lab + BitVec.ofNat 64 e.1) e.2)
    (htk : ∀ (c0 : Ctl) (R' : Region) (F' : MachineData → Prop), (∀ m, F' m → F m) →
      R' = R.callee (-136) (-248) 8 → ∀ (g g' : Ret0.AllocTcb.G),
      Spike.Lib.X64.Rt.TakeOkA (ms []) F L.exe L.endPc (R'.callee (-48 - 0) (-200) 8) F'
        (Ret0.tiTake (tiQ (tH L.lab) c0 g) g')) :
    H1GAH0W L W X Wc ms p lbl l b ws a ar Dt Cw Ctx lsize frM R F J1 tp :=
  ⟨h.wcWf, h.res, h.tcb, resA, hdrA, tcbA, tid, h.wcl, hfld, htk⟩

/-! ## `hCI` at the pinned ghost -/

section CI

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : Spike.Lib.PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "IH" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw IH

set_option hygiene false in
local notation "LB" => Spike.Lib.X64WakeLoadT.L0T (Ly).Λ

/-- **`hCP_of`'s `hCI` at the pinned ghosts** (`X64HelloH2CP.cloneInvH_of_mid` at `GJ1RH`, `GJ1H`'s half read
by `X64HelloH2G.hG_of`, main's id at its TCB by `Box.hmt_H`). -/
theorem hCI_RH {F0 : MachineData → Prop} {W : FragS isa} {Wc : Frag isa}
    {l : WeakMem.AllocLabel} {b : Nat} {l' : WeakMem.AllocLabel} {b' n' : Nat}
    (hl : (LB) l = none) (hl' : Spike.Lib.X64ConsumerA.upd (LB) l b l' = none) :
    ∀ s c fs, Spike.Lib.X64HelloHMid.CloneMidH (Ly) F0 (GJ1RH (Ly) (Spike.Lib.X64ConsumerA.upd (LB) l b) l) W Wc
        l' b' (Spike.Lib.X64HelloHMid.slWsH l) n' s c fs →
      Spike.Lib.X64HelloPreA.CloneInvH (Ly) (Ly).endPc
        (Spike.Lib.X64ConsumerA.upd (Spike.Lib.X64ConsumerA.upd (LB) l b) l' b') s c [] :=
  Spike.Lib.X64HelloH2CP.cloneInvH_of_mid (by simp [Spike.Lib.X64ConsumerA.upd])
    fun R F J1 t h => Spike.Lib.X64HelloH2G.hG_of hl' (Spike.Lib.X64.HelloPh.Box.hmt_H hpw i0 hl) R F J1 t h.1

end CI

/-! ## `hP` at the pinned ghost -/

section HP

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : Spike.Lib.PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw i

/-- **`H1GAHG` at the pinned ghost at any start level `V`** (`HelloRootPremG.hP`'s conclusion): the region and
frame condition fields from `GJ1RH`'s `(wcR …).fp (-8)`/`wcF` (`hi96`, `hR8`: the bounds `16`, `-392`; `fcg`, `fcl`,
`hF0`: `BoxRF.wcF_dmemH`, `wcF_takeMemH`, `stackOff_r0_boxH`; `hFr`, `hunF`: `FS`'s `WordsNoneP` by
`BoxRF.rtF_of_wn`, `unF_of_wn`), the placement `hpl` from `GJ1H` at the box's label `l` fresh at `lbl1` and main's
id at the TCB (`SpawnPl.hplQ_GJ1H`, at the placement `upd lbl1 l b` and rodata's slice `slWsH lr`), the level lift
`hWX` from `V`, the rest `H1GAH0W`'s. -/
theorem hP_ofG (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    {W X : FragS isa} {Wc : Frag isa} {ms : List TermRun.Frame → MemSide isa} {p : Prog}
    {l : WeakMem.AllocLabel} {b : Nat} {a : BitVec 64} {ar : Arena} {Dt Cw : State → Prop}
    {Ctx : FragS isa} {lsize : Lsize} {frM : Ctl → TermRun.Frame} {lbl1 : Lbl} {lr : WeakMem.AllocLabel}
    {V : Ctl → Frag isa} {R : Region} {F : MachineData → Prop} {J1 : FAS → Ctl → Prop} {tp : UInt64}
    (hl : lbl1 l = none) (hmt : lbl1 (Spike.Lib.X64WakeSrcDefs.mainTidLbl 2) = some ((Ly).pinA.toNat + 8))
    (hG : GJ1RH (Ly) lbl1 lr R F J1 tp)
    (h0 : H1GAH0W (Ly) W X Wc ms p (Spike.Lib.X64ConsumerA.upd lbl1 l b) l b (Spike.Lib.X64HelloHMid.slWsH lr) a
      ar Dt Cw Ctx lsize frM R F J1 tp)
    (hWX : ∀ c0 cA, MidG (QBH l b (Spike.Lib.X64HelloHMid.slWsH lr)) c0 cA → ∀ s c, V c0 s c →
      Spike.Lib.X64.HelloW2.OffW ar s → W s c [] ∧ X s c []) :
    Spike.Lib.X64.HelloH1A.H1GAHG (Ly) W X Wc ms p (Spike.Lib.X64ConsumerA.upd lbl1 l b) l b
      (Spike.Lib.X64HelloHMid.slWsH lr) ar V R F J1 tp := by
  have hpl := Spike.Lib.X64.HelloPh.SpawnPl.hplQ_GJ1H (b' := b) hl hmt hG.1
  have hlh := gj1RH_lo hG
  obtain ⟨-, v, m1, σ1, rfl, rfl, -⟩ := hG
  exact {
    wcWf := h0.wcWf
    res := h0.res
    tcb := h0.tcb
    resA := h0.resA
    hdrA := h0.hdrA
    tcbA := h0.tcbA
    tid := h0.tid
    wcl := h0.wcl
    hi96 := by rw [hlh.2]; decide
    fcl := Spike.Lib.X64.HelloPh.BoxRF.wcF_takeMemH hpw i hA13 (by decide) (by decide)
    fcg := Spike.Lib.X64.HelloPh.BoxRF.wcF_dmemH
    hR8 := by rw [hlh.1, hlh.2]; decide
    hWX := hWX
    hpl := hpl
    hFr := fun _ h => Spike.Lib.X64.HelloPh.BoxRF.rtF_of_wn _ h.1.1.1
    hunF := fun a ha _ h => Spike.Lib.X64.HelloPh.BoxRF.unF_of_wn hpw i hpin2 h.1.1.1 a ha
    hF0 := Spike.Lib.X64.HelloPh.BoxRF.stackOff_r0_boxH hpw i (by decide) (by decide) (by decide) (by decide)
    hfld := h0.hfld
    htk := h0.htk }

end HP

end Spike.Lib.X64.HelloPh.RootHP

/-! ## Axioms -/

/--
info: 'Spike.Lib.X64.HelloPh.RootHP.H1GAH0W.toH0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootHP.H1GAH0W.toH0

/--
info: 'Spike.Lib.X64.HelloPh.RootHP.H1GAH0V.toW' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootHP.H1GAH0V.toW

/-- info: 'Spike.Lib.X64.HelloPh.RootHP.hCI_RH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootHP.hCI_RH

/-- info: 'Spike.Lib.X64.HelloPh.RootHP.hP_ofG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootHP.hP_ofG
