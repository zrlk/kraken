/-
**Every compiled block of an `Accepted2` program is one segment inside
`W2`, at every reachable placement** (AArch64): the statement
`FnSpecC2StmtL`, `FnSpecC2Stmt` (`Spike/Lib/LowerA64/G1FnSpec.lean`) at
`FnSpecC2AtL` (`Spike/Lib/LowerA64/G1FnSpecL.lean`).
-/
import Spike.Lib.LowerA64.G1FnSpecL

namespace Spike.Lib.LowerA64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.LowerNode (imms2Me)

/-- **The program-wide function segment of an `Accepted2` program at
every reachable placement**: at every instance of `Closed2InA` whose
output's user code passes the branch-target check `tgOkB` and whose write
tail `Dt` holds at the output call's system call, every invariant `J` and
bottom keys `Bot`, `FnSpecC2AtL`. -/
def FnSpecC2StmtL : Prop :=
  ∀ (cfg : Scc.Config) (pcfg : Scc.Cert.PlaceOK.Config) (p : Prog) (Λ : Scc.Sem.Layout)
    (hp : Scc.Lower.Accepted2 p = true),
    CfgNeedOkA pcfg = true →
    ∀ (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true),
    tgOkB (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))) = true →
    ∀ (Dt : State → Prop),
    (∀ (R' : Region) (F' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (σC : AS) s c',
      Spike.Lib.A64.Flow.At (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)).exe
        (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)).endPc R' F'
        (Spike.Lib.A64.Flow.PrintCall.pN (_root_.Executable.labels (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)).exe).label
          Pc Qc σC .svc) s c' → Dt s) →
    ∀ (J : InvS) (Bot : StkKey → List TermRun.Frame → Prop), FnSpecC2AtL h hp Dt J Bot

end Spike.Lib.LowerA64
