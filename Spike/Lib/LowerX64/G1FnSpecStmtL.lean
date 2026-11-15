/-
**Every compiled block of an `Accepted2` program is one segment inside
`W2`, at every reachable placement** (x86-64; the twin of
`Spike/Lib/LowerA64/G1FnSpecStmtL.lean`): the statement `FnSpecC2StmtL`,
`FnSpecC2Stmt` (`Spike/Lib/LowerX64/G1FnSpec.lean`) at `FnSpecC2AtL`
(`Spike/Lib/LowerX64/G1FnSpecL.lean`).
-/
import Spike.Lib.LowerX64.G1FnSpecL

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (AS)
open Spike.Lib.LowerNode (imms2Me)

/-- **The program-wide function segment of an `Accepted2` program at
every reachable placement**: at every instance of `Closed2In` whose
output's user code passes the branch-target check `tgOkB` and whose write
tail `Dt` holds at the output call's system call, every invariant `J` and
bottom keys `Bot`, `FnSpecC2AtL`. -/
def FnSpecC2StmtL : Prop :=
  ∀ (cfg : Scc.Config) (pcfg : Scc.Cert.PlaceOK.Config) (p : Prog) (sizes : List Nat)
    (labelOffs : List (String × Nat)) (Λ : Scc.Sem.Layout) (hp : Scc.Lower.Accepted2 p = true),
    CfgNeedOk pcfg = true →
    ∀ (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true),
    tgOkB (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)) = true →
    ∀ (Dt : State → Prop),
    (∀ (R' : Region) (F' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (ko : Int) (σC : AS) s c',
      Spike.Lib.X64.At (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)).exe
        (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)).endPc R' F'
        (Spike.Lib.X64.PrintCall.pN
          (_root_.Executable.labels (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)).exe).label
          Pc Qc ko σC .sys) s c' → Dt s) →
    ∀ (J : InvS) (Bot : StkKey → List TermRun.Frame → Prop), FnSpecC2AtL h hp Dt J Bot

end Spike.Lib.LowerX64
