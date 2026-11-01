/-
**The spawned child's segment inside the worker's landing fact with the flag** (AArch64; rows 5j-wit-W,
5j-wit-E-call, SegTCSX-inhab): `SegRP.seg_childPPXc` at `X := XH.XHF Λ lbl cS`, the per-record `hseg` of
`HelloWorkerRR.helloDR` at `Z := ZHR exe kp ∧ XHF`.

Its node obligations split by `XH.zObl_XHF`: `XHNode.zObl_XH` (from `PlacedZ.zObl_placed_ok`, the packet's five
words represented: `ChildPrem.hv0` … `hvu`, and the root's immediate table) and `FlagObl.zObl_flag`; its landings
by `SegRP.ZXObl.and`: `XHLand.zXObl_XH` (the packet's words 3 and 4 represented: `ChildPrem.hv`, `hvu`) and
`FlagR.zXObl_flag`. Every fact is per child datum `d`, from `d.ok`, its `ChildPrem` and the flag word
`d.w3 = cS` (`childPX`'s witness); the segment has no premise beyond the layout's.

- `ImmsKid`, `ImmsKid.ofIH`: the two facts of the layout's immediate table the segment reads (no immediate at the
  child's control `kidC` nor at `workerCallH`); at the root's table `ImmsH.iH` by `iH_kid`, `iH_wcall`.
- `seg_childXHF`: the segment.
-/
import Spike.Lib.A64HelloXHNode
import Spike.Lib.A64HelloXHLand
import Spike.Lib.A64HelloFlagR
import Spike.Lib.A64HelloPlacedZObl

namespace Spike.Lib.A64.HelloPh.XHFSeg

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.A64.Flow.Worker.Hello.Z (ZHR)
open Spike.Lib.A64.Flow.Worker.Hello.SegR (ChildPrem ChildD)
open Spike.Lib.A64.Flow.Worker.Hello.SegRP (ZObl ZXObl childPX seg_childPPXc)
open Spike.Lib.A64.HelloPh.XH (XHF zObl_XHF iH_kid)
open Scc.Cert.Rt.A64 (Lays endOf)
open SccCode (helloProg)

/-- **The layout's immediate table has no immediate at the child's controls**: none at `kidC` (`hkid`) nor at
`workerCallH` (`hwc`). These are the only facts of the table the child's segment reads (`XHNode.zObl_XH`'s `hik`,
`hiw`). -/
structure ImmsKid (Λ : Scc.Sem.Layout) : Prop where
  /-- No immediate at the child's control `kidC`. -/
  hkid : ∀ (T : Ty) (w0 w1 w2 w3 w4 : TermRun.Word) (y : String) (k : Nat),
    Λ.imms (XH.kidC T w0 w1 w2 w3 w4).term y k = none
  /-- No immediate at `workerCallH`. -/
  hwc : ∀ (y : String) (k : Nat), Λ.imms Spike.Lib.HelloSplit.workerCallH y k = none

/-- **`ImmsKid` at the table `ImmsH.iH`** (`iH_kid`, `XHNode.iH_wcall`). -/
theorem ImmsKid.ofIH {Λ Λ0 : Scc.Sem.Layout} (hi : Λ.imms = Spike.Lib.A64.HelloPh.ImmsH.iH Λ0) : ImmsKid Λ :=
  ⟨fun _ _ _ _ _ _ y k => by rw [hi]; exact iH_kid Λ0 y k, fun y k => by rw [hi]; exact XHNode.iH_wcall Λ0 y k⟩

/-- **The spawned child's segment inside `XHF`**, at a layout whose immediate table has none at the child's
controls (`hI`), given per
child datum: `PlacedSE` at every node from the packet's words represented (`ChildPrem.hv0` … `hvu`). -/
theorem seg_childXHF {Λ : Scc.Sem.Layout} (hI : ImmsKid Λ)
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    {cS : WeakMem.Address} (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    (hK : ∀ fs, (ms fs).K = some Scc.Sem.A64.abi) :
    SegTCSX (fun s c fs => NNH exe endPc s ∧ ZHR exe kp s c fs ∧ XHF Λ lbl cS s c fs) (XHF Λ lbl cS) helloSrc lbl
      ms (childPX exe endPc kp lbl ms cS) (fun _ _ _ => False) :=
  seg_childPPXc hp hend hK
    (fun d ho hc hcS => zObl_XHF
      (XHNode.zObl_XH hcS (fun y k => hI.hkid _ _ _ _ _ _ y k) hI.hwc
        (Hello.PlacedZ.zObl_placed_ok (d := d) ho hc.hv0 hc.hv1 hc.hv2 hc.hv hc.hvu))
      (Hello.FlagObl.zObl_flag hcS))
    (fun d ho hc hcS => ZXObl.and (XHLand.zXObl_XH hc.hv hc.hvu)
      (Hello.FlagR.zXObl_flag hcS))

end Spike.Lib.A64.HelloPh.XHFSeg

/-- info: 'Spike.Lib.A64.HelloPh.XHFSeg.seg_childXHF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.XHFSeg.seg_childXHF

/-- info: 'Spike.Lib.A64.HelloPh.XHFSeg.ImmsKid.ofIH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.XHFSeg.ImmsKid.ofIH
