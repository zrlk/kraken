/-
**Every compiled block's segment at a base context, from the construct
statements** (x86-64; the twin of `Spike/Lib/LowerA64/G1FnSpecOf.lean`):
`FnSpecC2At` by strong induction on the block's index (`fnSpecC2_allI`, the
callees earlier, `hord_ofAccepted2`), each body's segment from its
constructs (`bodySpecC2_of`, in the rebased region): the plain calls
(`callC2_ofCxG2`), the lane stores and buffers (`LaneBuf2Stmt`) and the
output calls (`Print2Stmt`).

- `fnSpecC2At_of`: `FnSpecC2At` from the plain call's statement
  `CallC2FW`, the callee prologues (`ProCallG2`), the calls' blocks
  (`WCallG2`) and the step statements of `G1FnSpec`.
-/
import Spike.Lib.LowerX64.G1CallG2
import Spike.Lib.LowerX64.HordC2

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region FrameRunM)
open Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS
open Spike.Lib.X64 (AS)
open Spike.Lib.LowerNode (compiled2 TailAt2 imms2Me)

section G1Of

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

/-- **Every compiled block's segment at one instance** (`FnSpecC2At`) from
the construct statements: `fnSpecC2_allI` at the placement check's code
facts (whose lowering contexts have the frontend's externs, so the callees
are earlier, `hord_ofAccepted2`), each body by `bodySpecC2_of` with its
plain calls from `callC2_ofCxG2` at the callees' segments of the
induction, its lane stores, buffers and output calls from `LaneBuf2Stmt`
and `Print2Stmt` (at the context's `CxG2M`); the write tail `Dt` holding at
the output call's system call (`hDt`). -/
theorem fnSpecC2At_of (hFW : CallC2FW) (hp : Scc.Lower.Accepted2 p = true) (hown : Room2OwnStmt h hp)
    (hrc : Room2CalleeStmt h hp) (hlc : Lim2CalleeStmt h hp) (hlok : LimOk2Stmt h hp)
    (hlb : LaneBuf2Stmt h hp) (hpr : Print2Stmt h hp)
    (htg : tgOkB (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)) = true)
    (hpc : ProCallG2 h hp) (hwc : WCallG2 h hp) {Dt : State → Prop}
    (hDt : ∀ (R' : Region) (F' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (ko : Int) (σC : AS) s c',
      Spike.Lib.X64.At (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)).exe
        (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)).endPc R' F'
        (Spike.Lib.X64.PrintCall.pN
          (_root_.Executable.labels (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)).exe).label
          Pc Qc ko σC .sys) s c' → Dt s)
    (J : InvS) (Bot : StkKey → List TermRun.Frame → Prop) : FnSpecC2At h hp Dt J Bot := by
  refine fnSpecC2_allI (fnCode2OfPMe hp h Λ)
    (hord_ofAccepted2 hp (fnCode2OfPMe hp h Λ) fun j d hd => by
      rw [(fnCode2OfPMe_spec hp h Λ j d hd).1]) ?_
  intro j d hd hIH
  refine bodySpecC2_of (fnCode2OfPMe hp h Λ j d hd) fun R F fs fp ra tp G0 Ab hcx hra => ?_
  obtain ⟨hlane, hbuf⟩ := hlb Dt J j d hd R F fs fp ra tp G0 Ab hcx.1.1 hra
  exact ⟨callC2_ofCxG2 h hFW hp hown hrc hlc hlok htg hpc hwc hd hcx hra hIH, hlane, hbuf,
    hpr Dt hDt J j d hd R F fs fp ra tp G0 Ab hcx.1.1 hra⟩

end G1Of

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.fnSpecC2At_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.fnSpecC2At_of
