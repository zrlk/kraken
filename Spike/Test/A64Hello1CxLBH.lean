/-
**The base context `CxLB` from `hello1`'s landing contexts** (AArch64):
`SetupCxLB` (`Spike/Test/A64Hello1HsOf.lean`) at a context `CxOkH`
(`Spike/Test/A64Hello1CxOkH.lean`) and any family `J`, by
`setupCxLB_ofPre` at the context's setup-frame data. The context's aborts
are `AbU2` at its own family; the heap aborts `AbAl2` read the memory side
only through the call's premises and the counter, not the allocation
fragment, so they are the same at `J`. Left as a premise: the allocator's
`W2` instance (`hAW`, `AllocW2At` with no label placed).

- `cxLB_ofCxOkH`: `SetupCxLB … J` at a `CxOkH` context, given `hAW`.
-/
import Spike.Test.A64Hello1CxOkH

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Rt (setupMC rS0 arOf)
open Spike.Lib.A64.WriteAb (Ab)
open Spike.Lib.LowerNode (setupWords2 compiled2 TailAt2 imms2Me)
open Spike.Lib.AllocReach (IN)

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates (`fnCode2OfP`'s). -/
local notation "LY0" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))

set_option hygiene false in
/-- The canonical load's memory of the output. -/
local notation "M0" => Spike.Lib.A64.PhRec.m0Of (Ly).Λ OP (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).secs

set_option hygiene false in
/-- `MSAt` at `Closed2AtA`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max =>
  MSAt h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

/-- **`SetupCxLB` at a `CxOkH` context** (`setupCxLB_ofPre` at the
context's block, bounds, `PRE` and `hwn`): at any family `J` and the
context's own block `hd`, given the allocator's `W2` instance with no label
placed at the context's data (`hAW`); the context's aborts `AbU2` at its
own family hold the heap aborts at `J` (the memory sides differ only in the
allocation fragment, which `nbX`'s abort node does not read). -/
theorem cxLB_ofCxOkH (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {Dt : State → Prop} (J : InvS) {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) {R : Region}
    {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop}
    {Ab' : FragS isaLSE2} (hc : CxOkH h hp j R F fs fp ra tp G0 Ab')
    (hAW : AllocW2At p (fun _ => none) (fun _ => 0) (fnCode2OfPMe hp h Λ j d hd).lcx (fnCode2OfPMe hp h Λ j d hd).cx
      (CdCLE OP (Spike.Lib.A64.PhRec.okPc LY0) (Spike.Lib.A64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec ra))
      ((fnCode2OfPMe hp h Λ j d hd).Bl ra)
      (fun lbl lsize s c => W2 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum
        (Spike.Lib.A64.PhRec.GOf Ly M0) (Spike.Lib.A64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly))
        (arOf (Ly).Λ) (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) Dt (Ab (Ly).lab) lbl lsize s c fs)
      (KT) (Ly).exe (Ly).endPc R F ((MSS J) fs) fp ra tp G0 (imms2Me Λ p) (TailAt2 p j) (RetLk d.retTy)) :
    SetupCxLB h hp Dt J hd j R F fs fp ra tp G0 Ab' := by
  obtain ⟨d', hd', L, D1, fS, nS, v, g, fr, J0, hn, hfS, hnS, hL0, hLm, hL8, hD18, hL1, hrow,
    ⟨hR0, hal, hF', hFF, -, -, hct, -⟩, hwn, -, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hc
  cases (Option.some.inj (hd.symm.trans hd'))
  have H := setupCxLB_ofPre h hp hty J v hfS hnS hL0 hLm hL8 hD18 hL1 hrow hd hn hR0 hal hF' hFF hct hwn hAW
  refine { H with hAb := fun Jc pcR s c hJ _ hA => .inr ⟨rfl, Jc, pcR, hJ, ?_⟩ }
  obtain ⟨he, hen, hde, hpc, σ, hAbs, hFm, hx0, ⟨q, hq⟩, hJf, hσC⟩ := hA
  refine ⟨he, hen, hde, hpc, σ, hAbs, hFm, hx0, ⟨q, ?_⟩, ?_, hσC⟩
  · dsimp only [MSAt] at hq ⊢
    generalize ab2 p _ = ab at hq ⊢
    cases ab <;>
      exact ⟨hq.term, hq.ev, hq.num, hq.hold, hq.n_lt, hq.ctr, hq.heap, hq.room, hq.cells, hq.units, hq.off, hq.accs,
        hq.rt, hq.mp, hq.grow, hq.hdr⟩
  · dsimp only [MSAt] at hJf ⊢
    generalize ab2 p _ = ab at hJf ⊢
    cases ab <;> exact hJf

end Assembled

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.cxLB_ofCxOkH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cxLB_ofCxOkH

end Spike.Lib.LowerA64
