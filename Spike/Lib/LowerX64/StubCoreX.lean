/-
**A buffer allocation's heap abort path inside `W2` for one call**
(x86-64; the twin of `Spike/Lib/LowerA64/HeapAbA.lean`'s `stubHN_nbCore`):
`stubHN_nbAb` (`Spike/Lib/LowerX64/HeapAbX.lean`) at a call `q`, a control
`c0` of its `Jfull` and a slot file `sl` placing `q`'s control at the
frame's register slots, rather than at a state of `nbX … .abort` (the
shape `AllocPtW.hstub`'s `HeldAb` gives).

- `stubHN_nbCore`: the heap abort path's obligations without code
  (`StubHN`) inside `W2` at the record, for one call.
-/
import Spike.Lib.LowerX64.HeapAbX

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region FrameRun HeapAbortObl)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND At FStable Abs CKept)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.X64.Flow.NewBuf (nbX allocAbortDepth)
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.X64.StubW (NbCtl)
open Spike.Lib.LowerNode (SlotRepAt)
open Spike.Lib.X64

section Place

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.PhRec (μ K)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)
include h

variable {R : Region} {F : MachineData → Prop} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {ar : Arena} {J : InvS} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}
  {rS : Range} {Λw : Scc.Sem.Layout}

/-- **The heap abort path inside `W2` at the record for one call**
(`stubHN_w2_ofPlaceOKw` in the dispatcher's region below the allocator's
frame): at a control `c0` of `Jfull` for a call `q` with its premises from
a frame `fr` (`FrameOk`), `q`'s control placed in a slot file `sl` at the
frame's register slots (`hrep`) and at a `newBuf` of an `elem2` element
type (`hte`, `hel`), the abstract state `σC` holding `sl` off the
allocator's region (`hsl`), the frame condition placing the suspended
frames `fs` (`hfp`); the memory side's units at most the source's (`hu`),
its arena the allocator's (`hcl`, `hct`), its aborts at the record's abort
sites (`hma`), the write tail at the stub's `write` (`hwr`); in an
8-aligned region holding the frame, the allocator's frame and the
dispatcher's 24 bytes below it. -/
theorem stubHN_nbCore {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -allocAbortDepth (fr.size : Int) - 32)
    (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hF : FStable R F) (hsub : rS.Sub Λw.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λw lbl s fs B)
    {ms : MemSide isa}
    (hu : ∀ n τ us, TermRun.accs (TermRun.close [] τ) = some us → ms.units n τ ≤ n * TermRun.nWords us + 1)
    (hcl : ms.cells = ar.cells) (hct : ms.ctr = ar.ctr)
    (hma : ∀ s : State, (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      ms.abortAt s)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R' F'
        (Abort.N (RuntimeLayout.ofPlaceOK h i).lab Abort.heap c .sys) s c' → Dt s)
    {q : Call} (hq : q.OK ms (_root_.Executable.labels (RuntimeLayout.ofPlaceOK h i).exe).label)
    {c0 : Ctl} (hfull : Spike.Lib.X64.Alloc.Jfull ms q c0) {sl : Int → BitVec 64}
    (hrep : SlotRepAt Λw.imms lbl (rsOf fr) sl q.c0) {x : String} {cn : At} {τ : Ty} {e : Expr}
    (hte : q.c0.term = .let_ x (.newBuf cn τ) e) (hel : Scc.Lower.elem2 τ = true)
    {m0 : MachineData} {σC : AS}
    (hsl : ∀ k, R.Off k → ¬ (R.callee (-(fr.size : Int) - 8) (-160) 8).Off (k - (-(fr.size : Int) - 8)) →
      σC.slot k = sl k) :
    StubHN (fun s c => W2 Λw (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
        (Spike.Lib.X64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) rS
        (Spike.Lib.X64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i)) ar J Dt
        (Spike.Lib.X64.WriteAb.Ab (RuntimeLayout.ofPlaceOK h i).lab) lbl lsize s c fs)
      (K (RuntimeLayout.ofPlaceOK h i) rS) ms (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc (R.callee (-allocAbortDepth (fr.size : Int) - 8) (-24) 16)
      (fun m => F m ∧ CKept R (-allocAbortDepth (fr.size : Int) - 8) (-24) 16 m0 m ∧
        Abs R ⟨-allocAbortDepth (fr.size : Int), []⟩ m0 σC) c0 := by
  haveI := (RuntimeLayout.ofPlaceOK h i).valid
  have h8 : (fr.size : Int) % 8 = 0 := by have := frame_mod8 hf; omega
  have hkc : -allocAbortDepth (fr.size : Int) - 8 = -(fr.size : Int) - 176 := by
    simp only [allocAbortDepth, Spike.Lib.X64.Flow.NewBuf.allocFrame]; omega
  have hkc8 : (-allocAbortDepth (fr.size : Int) - 8) % 8 = 0 := by omega
  have hτ : q.τ = τ := by
    have := hq.term; rw [hte] at this; injection this with _ h2; injection h2 with _ h3; exact h3.symm
  have hobl := jfull_heapAbortObl_le hq (hτ ▸ hel) (fun us hus => hu _ _ us hus) hfull
  rw [hcl, hct] at hobl
  have ht0 : c0.term = q.c0.term := by
    rcases hfull with ⟨rfl, -⟩ | ⟨o, rfl, -⟩ <;> rfl
  have hrep0 : SlotRepAt Λw.imms lbl (rsOf fr) sl c0 := by
    rcases hfull with ⟨rfl, -⟩ | ⟨o, rfl, -⟩
    · exact hrep
    · exact hrep
  refine stubHN_w2_ofPlaceOKw h i (Region.callee_ok hR (by omega) (by decide) (by omega) (by omega))
    (addr_toNat_mod8 R hR8 hkc8) (Int.le_refl _) (Int.le_refl _)
    (by show (-24 : Int) % 8 = 0; decide) (by show (16 : Int) % 8 = 0; decide)
    (fstable_enter hR hF (by omega) (by decide) (by omega) (by omega) hkc8 (by decide) (by decide))
    hsub hfit ?_ ⟨⟨x, cn, τ, e, ht0.trans hte⟩, ?_, ?_, fun _ _ _ _ => rfl⟩ hobl hma hK (hwr _ _ _)
  · rintro m ⟨hFm, hck, hA⟩
    refine Spike.Lib.X64.Rt.stackOff_callee hR hR8 hl hh (by omega) (by decide) (by omega) hkc8
      (hFO m hFm) fun k hk hn => ?_
    rw [hck k hk hn]
    obtain ⟨j, hj, -⟩ := hA.slot k hk
    rw [hj]; rfl
  · intro x' a' τ' e' h'
    rw [ht0, hte] at h'
    cases h'
    exact Spike.Lib.LowerNode.zeroOkTy_of_elem2 hel
  · rintro s ⟨hFm, hck, hA⟩
    refine PlacedS.ofFrames (placed_of_slotRep (pf := fun k => .slot (R.addr k).toNat) hrep0
        fun r k hr => ?_) (hfp s hFm).choose_spec.toFramesPlaced
    obtain ⟨h1, h2, h3⟩ := rsOf_bounds hf hr
    have hk : R.Off k := ⟨h2, by omega, by omega⟩
    have hn : ¬ (R.callee (-allocAbortDepth (fr.size : Int) - 8) (-24) 16).Off
        (k - (-allocAbortDepth (fr.size : Int) - 8)) := by
      rintro ⟨-, -, h4⟩
      simp only [Region.callee] at h4
      omega
    have hn2 : ¬ (R.callee (-(fr.size : Int) - 8) (-160) 8).Off (k - (-(fr.size : Int) - 8)) := by
      rintro ⟨-, -, h4⟩
      simp only [Region.callee] at h4
      omega
    obtain ⟨j, hj, hjs⟩ := hA.slot k hk
    show (Scc.Sem.X64.privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    show ((s.st.1.dmem.loadInt (R.addr k) 8).map (BitVec.ofInt 64)).map (·.toNat) = _
    rw [hck k hk hn, hj, Option.map_some, hjs, ← hsl k hk hn2]; rfl

end Place

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.stubHN_nbCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.stubHN_nbCore
