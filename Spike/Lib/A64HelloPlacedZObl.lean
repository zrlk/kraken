/-
**hello.w's spawned child placed at every node** (AArch64):
`SegRP.ZObl (PlacedSE Λ lbl)`, the placement input of `XH.zObl_XH`, given the packet's five words represented
by the child's six machine words' last five (`hv0 .. hvu`: word `i` by `w.w(i+1)`) and the thread worker's
frame cells `-72 .. -40` in the region (`hlo`, `hhi`).

- the stub, the thread worker's prologue, head and tail: `PlacedZKid`'s `zc_placed`, `zT_placed`,
  `zEt_placed`, `zTT_placed`;
- `wc_worker`'s prologue, head, call, tail and `scc_rt_unpark`: `PlacedZWc`'s `wz_placed`, `wZE_placed`,
  `wZC_placed`, `wZW_placed`, `wZU_placed`;
- `print`'s nodes and its abort path on `uFrame`: `PlacedZPr`'s `zP_placed`, `zA_placed`.

- `wcObl_placed`: `WcObl (PlacedSE Λ lbl)` in a region reaching `-192 .. 0`.
- `zObl_placed`: `ZObl (PlacedSE Λ lbl)`; `zObl_placed_ok`: at a child datum, the region premises from
  `ChildD.ok`.
-/
import Spike.Lib.A64HelloPlacedZKid
import Spike.Lib.A64HelloPlacedZWc
import Spike.Lib.A64HelloPlacedZPr

namespace Spike.Lib.A64.Flow.Worker.Hello.PlacedZ

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (ValRep)
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Worker.Hello.Child (Words)
open Spike.Lib.A64.Flow.Worker.Hello.SegRP (WcObl ZObl)
open Spike.Lib.A64.Flow.Worker.Hello.SegR (ChildD)
open Spike.Lib.A64Consumer (Lbl)
open Spike.Lib.A64ConsumerS (PlacedSE)

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {exe : _root_.Executable} {endPc : Int64}
  {ms : List TermRun.Frame → MemSide isaLSE2} {w : Words} {tp sp0 : BitVec 64} {w0 w1 w2 w3 w4 : TermRun.Word}
  {n m : Nat}

/-- **`WcObl` at `PlacedSE`** in a region reaching `-192 .. 0`. -/
theorem wcObl_placed {R' : Region} {F' : MachineData → Prop} {x29 ra : BitVec 64} (hlo : R'.lo ≤ -192)
    (hhi : 0 ≤ R'.hi) (hv0 : ValRep lbl w0.val w.w0.toNat) (hv1 : ValRep lbl w1.val w.w2.toNat)
    (hv2 : ValRep lbl w2.val w.w3.toNat) (hv : ValRep lbl w3.val w.w4.toNat) (hvu : ValRep lbl w4.val w.w5.toNat) :
    WcObl (fun s c fs => PlacedSE Λ lbl s c fs) exe endPc ms R' F' x29 ra w tp sp0 w0 w1 w2 w3 w4 n m where
  hz := wz_placed hlo hhi hv0 hv1 hv2 hv hvu
  hZE := wZE_placed hlo hhi hv0 hv1 hv2 hv hvu
  hZC := wZC_placed hlo hhi hv0 hv1 hv2 hv hvu
  hZP := zP_placed (by omega) (by omega) hv hvu
  hZA := zA_placed (by omega) (by omega) hv hvu
  hZW := wZW_placed hlo hhi hv hvu
  hZU := wZU_placed hvu

/-- **`ZObl` at `PlacedSE`**: every node of the spawned child's run placed. -/
theorem zObl_placed {R : Region} {F : MachineData → Prop} {T : Ty} (hlo : R.lo ≤ -80) (hhi : -32 ≤ R.hi)
    (hv0 : ValRep lbl w0.val w.w0.toNat) (hv1 : ValRep lbl w1.val w.w2.toNat) (hv2 : ValRep lbl w2.val w.w3.toNat)
    (hv : ValRep lbl w3.val w.w4.toNat) (hvu : ValRep lbl w4.val w.w5.toNat) :
    ZObl (fun s c fs => PlacedSE Λ lbl s c fs) exe endPc ms R F w tp sp0 T w0 w1 w2 w3 w4 n m where
  hZc := zc_placed hv0 hv1 hv2 hv hvu
  hzT := zT_placed hv0 hv1 hv2 hv hvu
  hZEt := zEt_placed hv0 hv1 hv2 hv hvu hlo hhi
  hZT := zTT_placed
  hwc _ _ _ _ hlo' hhi' _ _ _ _ _ := wcObl_placed hlo' hhi' hv0 hv1 hv2 hv hvu

/-- **`zObl_placed`'s region premises from the child datum's** (`ChildD.ok`: `R.lo ≤ -272`, `0 ≤ R.hi`). -/
theorem zObl_placed_ok {d : ChildD} (ho : d.ok) (hv0 : ValRep lbl d.w0.val d.w.w0.toNat)
    (hv1 : ValRep lbl d.w1.val d.w.w2.toNat) (hv2 : ValRep lbl d.w2.val d.w.w3.toNat)
    (hv : ValRep lbl d.w3.val d.w.w4.toNat) (hvu : ValRep lbl d.w4.val d.w.w5.toNat) :
    ZObl (fun s c fs => PlacedSE Λ lbl s c fs) exe endPc ms d.R d.F d.w d.tp d.sp0 d.T d.w0 d.w1 d.w2 d.w3 d.w4
      d.n d.m :=
  zObl_placed (by have := ho.2.2.2.1; omega) (by have := ho.2.2.2.2; omega) hv0 hv1 hv2 hv hvu

end Spike.Lib.A64.Flow.Worker.Hello.PlacedZ

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.zObl_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.zObl_placed

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.zObl_placed_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.zObl_placed_ok
