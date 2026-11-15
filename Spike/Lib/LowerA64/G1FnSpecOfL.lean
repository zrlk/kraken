/-
**Every compiled block's segment at a base context at every reachable
placement, from the construct statements** (AArch64): `fnSpecC2At_of`
(`Spike/Lib/LowerA64/G1FnSpecOf.lean`) at the placement `L`, `ls`: the
plain calls (`callC2_ofCxG2L`), the lane stores and buffers
(`LaneBuf2StmtL`) and the output calls (`Print2StmtL`).

- `fnSpecC2AtL_of`: `FnSpecC2AtL` from the plain call's statement
  `CallC2FW`, the callee prologues (`ProCallG2L`), the calls' blocks
  (`WCallG2L`) and the step statements at a reachable placement.
-/
import Spike.Lib.LowerA64.G1CallC2RL
import Spike.Lib.LowerA64.G1FnSpecOf

namespace Spike.Lib.LowerA64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region FrameRunM)
open Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.A64.Flow
open Spike.Lib.LowerNode (compiled2 TailAt2 imms2Me)

section G1OfL

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

/-- **Every compiled block's segment at every reachable placement**
(`FnSpecC2AtL`, `fnSpecC2At_of` at the placement `L`, `ls`). -/
theorem fnSpecC2AtL_of (hFW : CallC2FW) (hp : Scc.Lower.Accepted2 p = true) (hown : Room2OwnStmt h hp)
    (hrc : Room2CalleeStmt h hp) (hlc : Lim2CalleeStmt h hp) (hlok : LimOk2StmtL h hp)
    (hlb : LaneBuf2StmtL h hp) (hpr : Print2StmtL h hp)
    (htg : tgOkB (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))) = true)
    (hpc : ProCallG2L h hp) (hwc : WCallG2L h hp) {Dt : State → Prop}
    (hDt : ∀ (R' : Region) (F' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (σC : AS) s c',
      Spike.Lib.A64.Flow.At (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)).exe
        (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)).endPc R' F'
        (Spike.Lib.A64.Flow.PrintCall.pN
          (_root_.Executable.labels (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)).exe).label
          Pc Qc σC .svc) s c' → Dt s)
    (J : InvS) (Bot : StkKey → List TermRun.Frame → Prop) : FnSpecC2AtL h hp Dt J Bot := by
  intro L ls _
  refine fnSpecC2_allI (lbl := L) (lsize := ls) (fnCode2OfPMe hp h Λ)
    (hord_ofAccepted2 hp (fnCode2OfPMe hp h Λ) fun j d hd => by
      rw [(fnCode2OfPMe_spec hp h Λ j d hd).1]) ?_
  intro j d hd hIH
  refine bodySpecC2_of (fnCode2OfPMe hp h Λ j d hd) fun R F fs fp ra tp G0 Ab hcx hra => ?_
  obtain ⟨hlane, hbuf⟩ := hlb Dt J L ls j d hd R F fs fp ra tp G0 Ab hcx.1.1 hra
  exact ⟨callC2_ofCxG2L h hFW hp hown hrc hlc hlok htg hpc hwc hd hcx hra hIH, hlane, hbuf,
    hpr Dt hDt J L ls j d hd R F fs fp ra tp G0 Ab hcx.1.1 hra⟩

end G1OfL

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.fnSpecC2AtL_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.fnSpecC2AtL_of
