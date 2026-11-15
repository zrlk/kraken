/-
**Every compiled block's segment at a base context at every reachable
placement, from the construct statements** (x86-64; the twin of
`Spike/Lib/LowerA64/G1FnSpecOfL.lean`): `fnSpecC2At_of`
(`Spike/Lib/LowerX64/G1FnSpecOf.lean`) at the placement `L`, `ls`: the
plain calls (`callC2_ofCxG2L`), the lane stores and buffers
(`LaneBuf2StmtL`) and the output calls (`Print2StmtL`).

- `fnSpecC2AtL_of`: `FnSpecC2AtL` from the plain call's statement
  `CallC2FW`, the callee prologues (`ProCallG2L`), the calls' blocks
  (`WCallG2L`) and the step statements at a reachable placement.
-/
import Spike.Lib.LowerX64.G1CallC2RL
import Spike.Lib.LowerX64.G1FnSpecOf

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region FrameRunM)
open Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS
open Spike.Lib.X64 (AS)
open Spike.Lib.LowerNode (compiled2 TailAt2 imms2Me)

section G1OfL

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

/-- **Every compiled block's segment at every reachable placement**
(`FnSpecC2AtL`, `fnSpecC2At_of` at the placement `L`, `ls`). -/
theorem fnSpecC2AtL_of (hFW : CallC2FW) (hp : Scc.Lower.Accepted2 p = true) (hown : Room2OwnStmt h hp)
    (hrc : Room2CalleeStmt h hp) (hlc : Lim2CalleeStmt h hp) (hlok : LimOk2StmtL h hp)
    (hlb : LaneBuf2StmtL h hp) (hpr : Print2StmtL h hp)
    (htg : tgOkB (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)) = true)
    (hpc : ProCallG2L h hp) (hwc : WCallG2L h hp) {Dt : State → Prop}
    (hDt : ∀ (R' : Region) (F' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (ko : Int) (σC : AS) s c',
      Spike.Lib.X64.At (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)).exe
        (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)).endPc R' F'
        (Spike.Lib.X64.PrintCall.pN
          (_root_.Executable.labels (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)).exe).label
          Pc Qc ko σC .sys) s c' → Dt s)
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

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.fnSpecC2AtL_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.fnSpecC2AtL_of
