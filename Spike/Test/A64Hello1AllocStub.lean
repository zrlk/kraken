/-
**`AllocPtW.hstub` from the allocation call node's `NbJcOf`** (AArch64; the
twin of `Spike/Test/X64Hello1AllocStub.lean`): the heap abort path's
obligations without code (`StubHN`) inside `W2` at the record, at a state of
the allocator's held abort node `HeldAb` over a call node `Jc` placing its
controls at the frame's register slots (`NbJcOf`), at the rows' memory side
`msOfAX` of any family `I` and abort `ab`: `stubHN_nbCore`
(`Spike/Lib/LowerA64/HeapAbA.lean`) at the slot file of `HeldAb`'s caller
state, the memory side's units, arena, aborts and ABI from `msOfAX`'s.

- `hstub_ofNbJc`: `AllocPtW.hstub`'s conclusion with the start family
  abstracted to `I` and the call node to `Jc`.
-/
import Spike.Lib.LowerA64.HeapAbA
import Spike.Lib.LowerA64.AllocW2AtOf
import Spike.Lib.LowerA64.NewBufC2
import Spike.Lib.LowerA64.Start2W2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (At FStable Abs CKept leave AS)
open Spike.Lib.A64.Flow.Ret0 (StackOff TakeK)
open Spike.Lib.A64.Flow.NewBuf (allocAbortDepth)
open Spike.Lib.A64.Alloc (Call)
open Scc.Emit.A64 (FnCtx)
open Scc.Lower.InvA64 (FrameOk)

section Place

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.PhRec (μ)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)
include h

/-- **`AllocPtW.hstub` from the call node's `NbJcOf`**: at a state `c0'`
of the allocator's held abort node over a call node `Jc` placing its
controls at the frame of `cx`'s register slots at `newBuf`s of `elem2`
element types (`hJc`), the heap abort path's obligations without code
inside `W2` at the record (`stubHN_nbCore` at the slot file of the held
caller state, which the allocator's return `leave`s outside its region),
the memory side the rows' `msOfAX` at the record's layout and marks at any
family `I` and abort `ab`; in a 16-aligned region holding the frame
(`FrameOk`, 16-aligned), the allocator's frame and the dispatcher's 48
bytes below it. -/
theorem hstub_ofNbJc {cx : FnCtx} (hf : FrameOk cx) (h16 : cx.frame % 16 = 0) {R : Region}
    {F : MachineData → Prop} {rS : Range} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -allocAbortDepth cx.frame - 48) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hF : FStable R F) (hsub : rS.Sub (RuntimeLayout.ofPlaceOK h i).Λ.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI (RuntimeLayout.ofPlaceOK h i).Λ lbl s fs B)
    {Dt : State → Prop}
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R' F'
        (A64.Abort.N (RuntimeLayout.ofPlaceOK h i).lab A64.Abort.heap c .svc) s c' → Dt s)
    {Jc : AS → Ctl → Prop} (hJc : NbJcOf (RuntimeLayout.ofPlaceOK h i).Λ.imms lbl cx Jc)
    {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {I : InvS} {ab : Option (State → Prop)} :
    ∀ q : Call, q.OK (msOfAX (RuntimeLayout.ofPlaceOK h i).Λ (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
        (fun s _ => Spike.Lib.A64.PhRec.own (RuntimeLayout.ofPlaceOK h i) s)
        (Spike.Lib.A64.Rt.arOf (RuntimeLayout.ofPlaceOK h i).Λ) I ab lbl lsize fs)
        (_root_.Executable.labels (RuntimeLayout.ofPlaceOK h i).exe).label →
      ∀ m0 σC c0', (HeldAb (_root_.Executable.labels (RuntimeLayout.ofPlaceOK h i).exe).label
        (msOfAX (RuntimeLayout.ofPlaceOK h i).Λ (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
          (fun s _ => Spike.Lib.A64.PhRec.own (RuntimeLayout.ofPlaceOK h i) s)
          (Spike.Lib.A64.Rt.arOf (RuntimeLayout.ofPlaceOK h i).Λ) I ab lbl lsize fs)
        q lbl R cx.frame (fun σC => Jc σC q.c0)).J σC c0' →
      StubHN (fun s c => W2 (RuntimeLayout.ofPlaceOK h i).Λ (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
          (Spike.Lib.A64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) rS
          (Spike.Lib.A64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i))
          (Spike.Lib.A64.Rt.arOf (RuntimeLayout.ofPlaceOK h i).Λ) I Dt
          (Spike.Lib.A64.WriteAb.Ab (RuntimeLayout.ofPlaceOK h i).lab) lbl lsize s c fs)
        (TakeK ((RuntimeLayout.ofPlaceOK h i).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL) rS)
        (msOfAX (RuntimeLayout.ofPlaceOK h i).Λ (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
          (fun s _ => Spike.Lib.A64.PhRec.own (RuntimeLayout.ofPlaceOK h i) s)
          (Spike.Lib.A64.Rt.arOf (RuntimeLayout.ofPlaceOK h i).Λ) I ab lbl lsize fs)
        (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc
        (R.callee (-(cx.frame : Int) + -160) (-48) 0)
        (fun m => F m ∧ CKept R (-(cx.frame : Int) + -160) (-48) 0 m0 m ∧
          Abs R ⟨-(cx.frame : Int) + -160, []⟩ m0 σC) c0' := by
  intro q hq m0 σC c0' hJ
  obtain ⟨σx, σC', ⟨-, hfull⟩, hJC, rfl⟩ := hJ
  obtain ⟨hrep, x, cn, τ, e, hte, hel⟩ := hJc σC' q.c0 hJC
  have e1 : -(cx.frame : Int) + -160 = -allocAbortDepth (cx.frame : Int) := by
    simp only [allocAbortDepth, Spike.Lib.A64.Flow.NewBuf.allocFrame]; omega
  rw [e1]
  refine stubHN_nbCore h i hf h16 hR hal hlo hhi hl hh hF hsub hfit hFO hfp ?_ ?_ ?_ ?_ msOfAX_K_abi hwr hq
    hfull hrep hte hel ?_
  · intro n τ' us hus
    cases ab <;>
      (show (Spike.Lib.A64.Rt.arOf (RuntimeLayout.ofPlaceOK h i).Λ).units n τ' ≤ _
       unfold Spike.Lib.A64.Rt.arOf; exact Arena.ofWords_units_le hus)
  · cases ab <;> rfl
  · cases ab <;> rfl
  · cases ab <;> exact fun _ h' => h'
  · intro k _ hn
    simp only [leave, hn, ite_false]

end Place

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.hstub_ofNbJc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hstub_ofNbJc
