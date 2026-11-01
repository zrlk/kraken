/-
**`HabCtlRdH` at the root's immediate table `iRdM`** (AArch64): `HabCtlRdI.placedS_rdCN`'s two immediates (`rdCN`'s
`m` at `eB`, the frame's
`me` at `tcb0` at `SrcCalls.setupCont`) hold at the layout `ofPlaceW hp (ImmsMe.iRdM Λ0)` (`ImmsMe.hm_iRdM`,
`ImmsMe.hmeC_iRdM`), so the placement `habCtlRdH_rdCN` asks at every state is discharged
there with no further premise: the non-vacuity of `placedS_rdCN`'s premises at the root.

- `placedSE_rdCN_iRdM`: `rdCN` under `frH c0S.env` placed at `L0T` at every state, at `iRdM`'s layout.
- `habCtlRdH_iRdM`: `HabCtlRdH` at `[frH c0S.env]` at `iRdM`'s layout, from `hJ1` and the arena facts alone.
-/
import Spike.Lib.A64HelloHabCtlRdI
import Spike.Lib.A64HelloImmsMe

namespace Spike.Lib.A64.HelloPh.HabCtlRdM

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib (Arena)
open Spike.Lib.WakeLoadT (L0T)
open Spike.Lib.HelloRdCf (frH)
open Spike.Lib.HelloRodataSrc (rdCN)
open Spike.Lib.Hello1RodataSrc (τ8)
open Spike.Lib.A64.HelloPh.C0S (c0S)
open Spike.Lib.A64.HelloPh.HabCtlRd (HabCtlRdH)
open Spike.Lib.A64.HelloPh.ImmsMe (iRdM hm_iRdM hmeC_iRdM)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}

/-- **`rdCN` placed at every state at `iRdM`'s layout**: `placedS_rdCN` at `hm_iRdM`, `hmeC_iRdM`. -/
theorem placedSE_rdCN_iRdM (hp : PlaceW pcfg Λ0 o) (s : State) :
    PlacedSE (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp (iRdM Λ0)).Λ
      (L0T (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp (iRdM Λ0)).Λ) s rdCN [frH c0S.env] :=
  .inl (Spike.Lib.A64.HelloPh.HabCtlRdI.placedS_rdCN (hm_iRdM hp) (hmeC_iRdM hp) s)

/-- **`HabCtlRdH` at `iRdM`'s layout**: `habCtlRdH_rdCN` with the placement `placedSE_rdCN_iRdM`; what is left
is the call invariant's controls (`hJ1`; at the root `fun _ _ h => h.2.1`) and the arena facts. -/
theorem habCtlRdH_iRdM (hp : PlaceW pcfg Λ0 o) {ms : Spike.Lib.MemSide isaLSE2} {lab : String → Int64}
    {ar : Arena} {J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    (hJ1 : ∀ σ c, J1 σ c → c = rdCN) (hctr : ms.ctr = ar.ctr) (hcells : ms.cells = ar.cells)
    (hu : ms.units 2 τ8 = 3) :
    HabCtlRdH ms lab Spike.Lib.HelloSrc.helloSrc (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp (iRdM Λ0)).Λ
      (L0T (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp (iRdM Λ0)).Λ) ar [frH c0S.env] J1 :=
  Spike.Lib.A64.HelloPh.HabCtlRdI.habCtlRdH_rdCN hJ1 hctr hcells hu (placedSE_rdCN_iRdM hp)

end Spike.Lib.A64.HelloPh.HabCtlRdM

/-- info: 'Spike.Lib.A64.HelloPh.HabCtlRdM.placedSE_rdCN_iRdM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HabCtlRdM.placedSE_rdCN_iRdM

/-- info: 'Spike.Lib.A64.HelloPh.HabCtlRdM.habCtlRdH_iRdM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HabCtlRdM.habCtlRdH_iRdM
