/-
**A buffer allocation's heap abort exit never ends, at the record of an
output passing `placeOK`** (AArch64): at a call node whose controls the
frame's register slots place (`NbJcOf`), the heap abort path's obligations
without code (`StubHN`) inside `W2` at the write abort's phase, at any
layout `Λw` (`stubHN_w2_ofPlaceOKw` with `NbCtl` from the allocator's
`Jfull` and the call node's placement, `HeapAbortObl` from
`jfull_heapAbortObl_le`), and the exit as a segment to any fragment
(`heapAbSeg2`).

- `nWords_eq_one_of_elem2`, `Arena.ofWords_units_le`, `jfull_heapAbortObl_le`: the
  allocator's `Jfull` discharges the heap disjunct at an `elem2` call whose
  units are at most the source's (a placement's saturating arena's);
- `stubHN_nbCore`: `StubHN` inside `W2` at a control of the allocator's
  `Jfull` for one call, its control placed in a slot file the abstract state
  holds off the allocator's region;
- `stubHN_nbAb`: `heapAbSeg2`'s `hstub` at a state of `nbX … .abort`;
- `heapAb_seg`: the heap abort exit of an allocation's call never ends.
-/
import Spike.Lib.LowerA64.MainAbA
import Spike.Lib.LowerA64.NewBufC2
import Spike.Lib.A64HeapObl
import Spike.Lib.Src.HeapBuf

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Spike.Lib (Region FrameRun HeapAbortObl AtNewBuf Arena)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (At FStable Abs CKept)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.A64.Flow.NewBuf (nbX allocAbortDepth nbX_abort_heapAbortObl)
open Spike.Lib.A64.Alloc (Call)
open Spike.Lib.LowerNode (SlotRepAt)
open Scc.Emit.A64 (FnCtx)
open Scc.Lower.InvA64 (FrameOk)

section Units

/-- **An `elem2` element type takes one word** (`accs_elem2` at its
closure). -/
theorem nWords_eq_one_of_elem2 {τ : Ty} {us : List TermRun.Acc} (hel : Scc.Lower.elem2 τ = true)
    (hus : TermRun.accs (TermRun.close [] τ) = some us) : TermRun.nWords us = 1 := by
  rw [Spike.Lib.LowerNode.accs_elem2 (Spike.Lib.LowerNode.elem2_close hel)] at hus
  cases hus; rfl

/-- **An arena of a placement's units are at most the source's**
(`Arena.ofWords` saturates at `2 ^ 63 - 1`). -/
theorem Arena.ofWords_units_le {heap cells ctr : Nat} {m : Ty → Nat} {n : Nat} {τ : Ty} {us : List TermRun.Acc}
    (hus : TermRun.accs (TermRun.close [] τ) = some us) :
    (Arena.ofWords heap cells ctr m).units n τ ≤ n * TermRun.nWords us + 1 := by
  simp only [Arena.ofWords, hus]; split <;> omega

/-- **`Jfull` discharges the heap disjunct at an `elem2` call**
(`Jfull.heapAbortObl` with the call's units at most the source's, `hu`, in
place of equal to them: a saturating memory side's). -/
theorem jfull_heapAbortObl_le {ms : MemSide isaLSE2} {lab : Label → Int64} {q : Call} {c : Ctl}
    (hq : q.OK ms lab) (hel : Scc.Lower.elem2 q.τ = true)
    (hu : ∀ us, TermRun.accs (TermRun.close [] q.τ) = some us → ms.units q.n q.τ ≤ q.n * TermRun.nWords us + 1)
    (hJ : Spike.Lib.A64.Alloc.Jfull ms q c) : HeapAbortObl ms.cells ms.ctr c := by
  intro old h
  obtain ⟨us, hus⟩ := hq.accs
  have hw := nWords_eq_one_of_elem2 hel hus
  have hun := hu us hus
  have hnb : AtNewBuf c := by
    rcases hJ with ⟨rfl, -⟩ | ⟨o, rfl, -⟩
    · exact ⟨_, _, _, _, hq.term⟩
    · exact ⟨_, _, _, _, hq.term⟩
  obtain ⟨hle, hwd⟩ := h hnb
  rcases hJ with ⟨rfl, hbig⟩ | ⟨o, rfl, -, ho⟩
  · refine ⟨q.x, q.a, q.τ, q.e, q.ta, q.ws, q.n, us, hq.term, hq.ev, hq.num, hus, hle, ?_⟩
    have := hq.cells
    rw [hw]; omega
  · have e := hwd _ rfl
    have hold' : old = o.toNat := by
      have := congrArg (·.val) e
      simp only [TermRun.cst, Promises.TVal.mk0] at this
      injection this with h'
      omega
    subst hold'
    exact ⟨q.x, q.a, q.τ, q.e, q.ta, q.ws, q.n, us, hq.term, hq.ev, hq.num, hus, hle, by omega⟩

end Units

section Place

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.PhRec (μ K)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)
include h

variable {R : Region} {F : MachineData → Prop} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {ar : Arena} {J : InvS} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}
  {rS : Range} {Λw : Scc.Sem.Layout}

/-- **The heap abort path inside `W2` at the record for one call**
(`stubHN_w2_ofPlaceOKw` in the dispatcher's region below the allocator's
frame): at a control `c0` of `Jfull` for a call `q` with its premises from
a frame of `cx` (`FrameOk`, 16-aligned), `q`'s control placed in a slot
file `sl` at the frame's register slots (`hrep`) and at a `newBuf` of an
`elem2` element type (`hte`, `hel`), the abstract state `σC` holding `sl`
off the allocator's region (`hsl`), the frame condition placing the
suspended frames `fs` (`hfp`); the call's source units (`hu`),
the memory side's arena the allocator's (`hcl`, `hct`), its aborts at the
record's abort sites (`hma`), the write tail at the stub's `write`
(`hwr`); in a 16-aligned region holding the frame, the allocator's and
the dispatcher's 48 bytes below it. -/
theorem stubHN_nbCore {cx : FnCtx} (hf : FrameOk cx) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -allocAbortDepth cx.frame - 48)
    (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λw.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λw lbl s fs B)
    {ms : MemSide isaLSE2}
    (hu : ∀ n τ us, TermRun.accs (TermRun.close [] τ) = some us → ms.units n τ ≤ n * TermRun.nWords us + 1)
    (hcl : ms.cells = ar.cells) (hct : ms.ctr = ar.ctr)
    (hma : ∀ s : State, (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      ms.abortAt s)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R' F'
        (A64.Abort.N (RuntimeLayout.ofPlaceOK h i).lab A64.Abort.heap c .svc) s c' → Dt s)
    {q : Call} (hq : q.OK ms (_root_.Executable.labels (RuntimeLayout.ofPlaceOK h i).exe).label)
    {c0 : Ctl} (hfull : Spike.Lib.A64.Alloc.Jfull ms q c0) {sl : Int → BitVec 64}
    (hrep : SlotRepAt Λw.imms lbl (rsOf cx) sl q.c0) {x : String} {cn : At} {τ : Ty} {e : Expr}
    (hte : q.c0.term = .let_ x (.newBuf cn τ) e) (hel : Scc.Lower.elem2 τ = true)
    {m0 : MachineData} {σC : Spike.Lib.A64.Flow.AS}
    (hsl : ∀ k, R.Off k → ¬ (R.callee (-(cx.frame : Int)) (-160) 0).Off (k - -(cx.frame : Int)) →
      σC.slot k = sl k) :
    StubHN (fun s c => W2 Λw (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
        (Spike.Lib.A64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) rS
        (Spike.Lib.A64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i)) ar J Dt
        (Spike.Lib.A64.WriteAb.Ab (RuntimeLayout.ofPlaceOK h i).lab) lbl lsize s c fs)
      (K (RuntimeLayout.ofPlaceOK h i) rS) ms (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc (R.callee (-allocAbortDepth cx.frame) (-48) 0)
      (fun m => F m ∧ CKept R (-allocAbortDepth cx.frame) (-48) 0 m0 m ∧
        Abs R ⟨-allocAbortDepth cx.frame, []⟩ m0 σC) c0 := by
  haveI := (RuntimeLayout.ofPlaceOK h i).valid
  have hτ : q.τ = τ := by
    have := hq.term; rw [hte] at this; injection this with _ h2; injection h2 with _ h3; exact h3.symm
  have hobl := jfull_heapAbortObl_le hq (hτ ▸ hel) (fun us hus => hu _ _ us hus) hfull
  rw [hcl, hct] at hobl
  have hge := frame_ge16 hf
  have hkc : -allocAbortDepth (cx.frame : Int) = -(cx.frame : Int) - 160 := by
    simp only [allocAbortDepth, Spike.Lib.A64.Flow.NewBuf.allocFrame]; omega
  have ht0 : c0.term = q.c0.term := by
    rcases hfull with ⟨rfl, -⟩ | ⟨o, rfl, -⟩ <;> rfl
  have hrep0 : SlotRepAt Λw.imms lbl (rsOf cx) sl c0 := by
    rcases hfull with ⟨rfl, -⟩ | ⟨o, rfl, -⟩
    · exact hrep
    · exact hrep
  have hcb := Region.callee_base (hi' := 0) hR (kc := -allocAbortDepth (cx.frame : Int)) (lo' := -48)
    (by omega) (by decide) (by omega)
  refine stubHN_w2_ofPlaceOKw h i (Region.callee_ok hR (by omega) (by decide) (by omega) (by omega))
    (by simp only [Region.callee] at hcb ⊢; omega) (Int.le_refl _) (Int.le_refl _)
    (by show (-48 : Int) % 8 = 0; decide) (by show (0 : Int) % 8 = 0; decide)
    (Spike.Lib.A64.Flow.fstable_enter hR hF (by omega) (by decide) (by omega) (Int.le_refl _) (by omega)
      (by decide) (by decide))
    hsub hfit ?_ ⟨⟨x, cn, τ, e, ht0.trans hte⟩, ?_, ?_, fun _ _ _ _ => rfl⟩ hobl hma hK (hwr _ _ _)
  · rintro m ⟨hFm, hck, hA⟩
    refine Spike.Lib.A64.Flow.Ret0.Inst.stackOff_callee hR (by omega) hl hh (by omega) (by decide) (by omega)
      (by omega) (hFO m hFm) fun k hk hn => ?_
    rw [hck k hk hn]
    obtain ⟨j, hj, -⟩ := hA.slot k hk
    rw [hj]; rfl
  · intro x' a' τ' e' h'
    rw [ht0, hte] at h'
    cases h'
    exact Spike.Lib.LowerNode.zeroOkTy_of_elem2 hel
  · rintro s ⟨hFm, hck, hA⟩
    refine Spike.Lib.A64ConsumerS.PlacedS.ofFrames
      (Spike.Lib.A64ConsumerS.placed_of_slotRep (pf := fun k => .slot (R.addr k).toNat) hrep0
        fun r k hr => ?_) (hfp s hFm).choose_spec.toFramesPlaced
    obtain ⟨h1, h2, h3⟩ := rsOf_bounds hf h16 hr
    have hk : R.Off k := ⟨h2, by omega, by omega⟩
    have hn : ¬ (R.callee (-allocAbortDepth (cx.frame : Int)) (-48) 0).Off
        (k - -allocAbortDepth (cx.frame : Int)) := by
      rintro ⟨-, -, h4⟩
      simp only [Region.callee] at h4
      omega
    have hn2 : ¬ (R.callee (-(cx.frame : Int)) (-160) 0).Off (k - -(cx.frame : Int)) := by
      rintro ⟨-, -, h4⟩
      simp only [Region.callee] at h4
      omega
    obtain ⟨j, hj, hjs⟩ := hA.slot k hk
    show (Scc.Sem.A64.privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, ← hsl k hk hn2]
    simp only [Scc.Sem.A64.privLoad, hck k hk hn, hj, Option.map_some, hjs]

/-- **`heapAbSeg2`'s `hstub` at the record** (`stubHN_nbCore` at a state
`σC`, `c0` of the heap abort exit of a call from a frame of `cx` at a call
node placing its controls, `NbJcOf`), with `stubHN_nbCore`'s premises. -/
theorem stubHN_nbAb {cx : FnCtx} (hf : FrameOk cx) (h16 : cx.frame % 16 = 0) {pcR : Int64}
    {Jc : Spike.Lib.A64.Flow.AS → Ctl → Prop} (hJc : NbJcOf Λw.imms lbl cx Jc)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -allocAbortDepth cx.frame - 48)
    (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λw.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λw lbl s fs B)
    {ms : MemSide isaLSE2}
    (hu : ∀ n τ us, TermRun.accs (TermRun.close [] τ) = some us → ms.units n τ ≤ n * TermRun.nWords us + 1)
    (hcl : ms.cells = ar.cells) (hct : ms.ctr = ar.ctr)
    (hma : ∀ s : State, (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      ms.abortAt s)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R' F'
        (A64.Abort.N (RuntimeLayout.ofPlaceOK h i).lab A64.Abort.heap c .svc) s c' → Dt s)
    {m0 : MachineData} {σC : Spike.Lib.A64.Flow.AS} {c0 : Ctl}
    (hJ : (nbX ms (_root_.Executable.labels (RuntimeLayout.ofPlaceOK h i).exe).label lbl R cx.frame pcR Jc
      .abort).J σC c0) :
    StubHN (fun s c => W2 Λw (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
        (Spike.Lib.A64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) rS
        (Spike.Lib.A64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i)) ar J Dt
        (Spike.Lib.A64.WriteAb.Ab (RuntimeLayout.ofPlaceOK h i).lab) lbl lsize s c fs)
      (K (RuntimeLayout.ofPlaceOK h i) rS) ms (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc (R.callee (-allocAbortDepth cx.frame) (-48) 0)
      (fun m => F m ∧ CKept R (-allocAbortDepth cx.frame) (-48) 0 m0 m ∧
        Abs R ⟨-allocAbortDepth cx.frame, []⟩ m0 σC) c0 := by
  obtain ⟨-, ⟨q, hq⟩, hfull, σJ, hJJ, hsl⟩ := hJ
  obtain ⟨hrep, x, cn, τ, e, hte, hel⟩ := hJc σJ q.c0 hJJ
  exact stubHN_nbCore h i hf h16 hR hal hlo hhi hl hh hF hsub hfit hFO hfp hu hcl hct hma hK hwr hq hfull hrep hte hel
    hsl

/-- **The heap abort exit of a buffer allocation's call never ends** (a
segment to any `Q` inside `W2` at the write abort's phase, at the frames
`fs`; `heapAbSeg2` with `stubHN_nbAb`): from `nbX … .abort` of a call from
a frame of `cx` at a call node placing its controls (`NbJcOf`), with
`stubHN_nbAb`'s premises. -/
theorem heapAb_seg {cx : FnCtx} (hf : FrameOk cx) (h16 : cx.frame % 16 = 0) {pcR : Int64}
    {Jc : Spike.Lib.A64.Flow.AS → Ctl → Prop} (hJc : NbJcOf Λw.imms lbl cx Jc)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -allocAbortDepth cx.frame - 48)
    (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λw.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λw lbl s fs B)
    {ms : List TermRun.Frame → MemSide isaLSE2}
    (hu : ∀ n τ us, TermRun.accs (TermRun.close [] τ) = some us →
      (ms fs).units n τ ≤ n * TermRun.nWords us + 1)
    (hcl : (ms fs).cells = ar.cells) (hct : (ms fs).ctr = ar.ctr)
    (hma : ∀ s : State, (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      (ms fs).abortAt s)
    (hK : (ms fs).K = some Scc.Sem.A64.abi)
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R' F'
        (A64.Abort.N (RuntimeLayout.ofPlaceOK h i).lab A64.Abort.heap c .svc) s c' → Dt s)
    (Q : FragS isaLSE2) :
    SegWS (fun s c fs => W2 Λw (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
        (Spike.Lib.A64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) rS
        (Spike.Lib.A64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i)) ar J Dt
        (Spike.Lib.A64.WriteAb.Ab (RuntimeLayout.ofPlaceOK h i).lab) lbl lsize s c fs)
      (K (RuntimeLayout.ofPlaceOK h i) rS) p lbl ms
      ((At (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc R F
        (nbX (ms fs) (_root_.Executable.labels (RuntimeLayout.ofPlaceOK h i).exe).label lbl R cx.frame pcR Jc
          .abort)).at fs)
      Q := by
  haveI := (RuntimeLayout.ofPlaceOK h i).valid
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK (rS := rS) h i
  have hge := frame_ge16 hf
  exact heapAbSeg2 hI.lays hI.endOk (hprog_ofPlaceOK h i) hF hR hal hlo
    (by simp only [allocAbortDepth, Spike.Lib.A64.Flow.NewBuf.allocFrame]; omega) (by omega) hK
    (fun _ _ _ hJ => stubHN_nbAb h i hf h16 hJc hR hal hlo hhi hl hh hF hsub hfit hFO hfp hu hcl hct hma hK hwr hJ)
    Q

end Place

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.nWords_eq_one_of_elem2' depends on axioms: [propext] -/
#guard_msgs in #print axioms nWords_eq_one_of_elem2

/-- info: 'Spike.Lib.LowerA64.Arena.ofWords_units_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Arena.ofWords_units_le

/-- info: 'Spike.Lib.LowerA64.jfull_heapAbortObl_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms jfull_heapAbortObl_le

/-- info: 'Spike.Lib.LowerA64.stubHN_nbCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stubHN_nbCore

/-- info: 'Spike.Lib.LowerA64.stubHN_nbAb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stubHN_nbAb

/-- info: 'Spike.Lib.LowerA64.heapAb_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms heapAb_seg

end Spike.Lib.LowerA64
