/-
**`AllocPtW.hstub` from the allocation call node's `NbJcOf`** (x86-64):
the heap abort path's obligations without code (`StubHN`) inside `W2` at
the record, at a state of the allocator's held abort node `HeldAb` over a
call node `Jc` placing its controls at the frame's register slots
(`NbJcOf`), at the rows' memory side `msOfAX` of any family `I` and abort
`ab`: `stubHN_nbCore` (`Spike/Lib/LowerX64/StubCoreX.lean`) at the slot
file of `HeldAb`'s caller state, the memory side's units, arena, aborts and
ABI from `msOfAX`'s.

- `hstub_ofNbJc`: `AllocPtW.hstub`'s conclusion with the start family
  abstracted to `I` and the call node to `Jc`.
-/
import Spike.Lib.LowerX64.StubCoreX
import Spike.Lib.LowerX64.AllocW2AtOf
import Spike.Lib.LowerX64.NewBufC2
import Spike.Lib.LowerX64.Start2W2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (At FStable Abs CKept leave AS)
open Spike.Lib.X64.Flow.Ret0 (StackOff TakeK)
open Spike.Lib.X64.Flow.NewBuf (allocAbortDepth)
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.X64

section Place

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.PhRec (μ)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)
include h

/-- **`AllocPtW.hstub` from the call node's `NbJcOf`**: at a state `c0'`
of the allocator's held abort node over a call node `Jc` placing its
controls at the frame `fr`'s register slots at `newBuf`s of `elem2`
element types (`hJc`), the heap abort path's obligations without code
inside `W2` at the record (`stubHN_nbCore` at the slot file of the held
caller state, which the allocator's return `leave`s outside its region),
the memory side the rows' `msOfAX` at the record's layout and marks at any
family `I` and abort `ab`; in an 8-aligned region holding the frame, the
allocator's frame and the dispatcher's 24 bytes below it. -/
theorem hstub_ofNbJc {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) {R : Region} {F : MachineData → Prop}
    {rS : Range} (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -allocAbortDepth (fr.size : Int) - 32)
    (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hF : FStable R F) (hsub : rS.Sub (RuntimeLayout.ofPlaceOK h i).Λ.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI (RuntimeLayout.ofPlaceOK h i).Λ lbl s fs B)
    {Dt : State → Prop}
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R' F'
        (Abort.N (RuntimeLayout.ofPlaceOK h i).lab Abort.heap c .sys) s c' → Dt s)
    {Jc : AS → Ctl → Prop} (hJc : NbJcOf (RuntimeLayout.ofPlaceOK h i).Λ.imms lbl fr Jc)
    {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {I : InvS} {ab : Option (State → Prop)} :
    ∀ q : Call, q.OK (msOfAX (RuntimeLayout.ofPlaceOK h i).Λ (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
        (fun s _ => Spike.Lib.X64.PhRec.own (RuntimeLayout.ofPlaceOK h i) s)
        (Spike.Lib.X64.Rt.arOf (RuntimeLayout.ofPlaceOK h i).Λ) I ab lbl lsize fs)
        (_root_.Executable.labels (RuntimeLayout.ofPlaceOK h i).exe).label →
      ∀ m0 σC c0', (HeldAb (_root_.Executable.labels (RuntimeLayout.ofPlaceOK h i).exe).label
        (msOfAX (RuntimeLayout.ofPlaceOK h i).Λ (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
          (fun s _ => Spike.Lib.X64.PhRec.own (RuntimeLayout.ofPlaceOK h i) s)
          (Spike.Lib.X64.Rt.arOf (RuntimeLayout.ofPlaceOK h i).Λ) I ab lbl lsize fs)
        q lbl R fr.size (fun σC => Jc σC q.c0)).J σC c0' →
      StubHN (fun s c => W2 (RuntimeLayout.ofPlaceOK h i).Λ (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
          (Spike.Lib.X64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) rS
          (Spike.Lib.X64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i))
          (Spike.Lib.X64.Rt.arOf (RuntimeLayout.ofPlaceOK h i).Λ) I Dt
          (Spike.Lib.X64.WriteAb.Ab (RuntimeLayout.ofPlaceOK h i).lab) lbl lsize s c fs)
        (TakeK ((RuntimeLayout.ofPlaceOK h i).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL) rS)
        (msOfAX (RuntimeLayout.ofPlaceOK h i).Λ (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
          (fun s _ => Spike.Lib.X64.PhRec.own (RuntimeLayout.ofPlaceOK h i) s)
          (Spike.Lib.X64.Rt.arOf (RuntimeLayout.ofPlaceOK h i).Λ) I ab lbl lsize fs)
        (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc
        (R.callee (-(fr.size : Int) - 8 + -160 - 8) (-24) 16)
        (fun m => F m ∧ CKept R (-(fr.size : Int) - 8 + -160 - 8) (-24) 16 m0 m ∧
          Abs R ⟨-(fr.size : Int) - 8 + -160, []⟩ m0 σC) c0' := by
  intro q hq m0 σC c0' hJ
  obtain ⟨σx, σC', ⟨-, hfull⟩, hJC, rfl⟩ := hJ
  obtain ⟨hrep, x, cn, τ, e, hte, hel⟩ := hJc σC' q.c0 hJC
  have e1 : -(fr.size : Int) - 8 + -160 - 8 = -allocAbortDepth (fr.size : Int) - 8 := by
    simp only [allocAbortDepth, Spike.Lib.X64.Flow.NewBuf.allocFrame]; omega
  have e2 : -(fr.size : Int) - 8 + -160 = -allocAbortDepth (fr.size : Int) := by
    simp only [allocAbortDepth, Spike.Lib.X64.Flow.NewBuf.allocFrame]; omega
  rw [e1, e2]
  refine stubHN_nbCore h i hf hR hR8 hlo hhi hl hh hF hsub hfit hFO hfp ?_ ?_ ?_ ?_ msOfAX_K_abi hwr hq hfull
    hrep hte hel ?_
  · intro n τ' us hus
    cases ab <;>
      (show (Spike.Lib.X64.Rt.arOf (RuntimeLayout.ofPlaceOK h i).Λ).units n τ' ≤ _
       unfold Spike.Lib.X64.Rt.arOf; exact arena_ofWords_units_le hus)
  · cases ab <;> rfl
  · cases ab <;> rfl
  · cases ab <;> exact fun _ h' => h'
  · intro k _ hn
    simp only [leave, hn, ite_false]

end Place

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hstub_ofNbJc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hstub_ofNbJc
