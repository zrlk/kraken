/-
**A buffer allocation's heap abort exit never ends, at a node of another
world** (AArch64): `HeapAbA`'s `heapAb_seg` with the call node's memory
side `msN` and labels `lblN` apart from the segment's (`ms`, `lbl`). The
call's premises (`Call.OK`, `Jfull`) and the arena facts sit at `msN`; the
node's slot placement moves to `lbl` by `SlotRepAt.mono_lbl` at labels
`lblN` contained in `lbl`. (`Call.OK`'s header condition reads the memory
side's free-range `rt`, which shrinks as labels are placed, so it does not
transfer between the worlds; the node keeps its own.)

- `stubHN_nbCoreX`: `stubHN_nbCore` with the call at `msN`;
- `stubHN_nbAbX`: `heapAbSeg2`'s `hstub` at a state of `nbX msN … lblN … .abort`;
- `heapAb_segX`: the heap abort exit from `nbX msN … lblN … .abort` never
  ends, as a segment at (`ms`, `lbl`).
-/
import Spike.Lib.LowerA64.HeapAbA
import Spike.Lib.Src.LevelMono2

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

/-- **`stubHN_nbCore` at a call of another memory side** (`msN`: the
call's premises, `Jfull` and the arena facts `hu`, `hcl`, `hct` at `msN`;
the `StubHN`, its aborts `hma` and ABI `hK` at the segment's `ms`). -/
theorem stubHN_nbCoreX {cx : FnCtx} (hf : FrameOk cx) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -allocAbortDepth cx.frame - 48)
    (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λw.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λw lbl s fs B)
    {ms msN : MemSide isaLSE2}
    (hu : ∀ n τ us, TermRun.accs (TermRun.close [] τ) = some us → msN.units n τ ≤ n * TermRun.nWords us + 1)
    (hcl : msN.cells = ar.cells) (hct : msN.ctr = ar.ctr)
    (hma : ∀ s : State, (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      ms.abortAt s)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R' F'
        (A64.Abort.N (RuntimeLayout.ofPlaceOK h i).lab A64.Abort.heap c .svc) s c' → Dt s)
    {q : Call} (hq : q.OK msN (_root_.Executable.labels (RuntimeLayout.ofPlaceOK h i).exe).label)
    {c0 : Ctl} (hfull : Spike.Lib.A64.Alloc.Jfull msN q c0) {sl : Int → BitVec 64}
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

/-- **`stubHN_nbAb` at a node of another world** (`stubHN_nbCoreX` at a
state of `nbX msN … lblN … .abort`, its slots placed at `lbl ⊇ lblN` by
`SlotRepAt.mono_lbl`). -/
theorem stubHN_nbAbX {cx : FnCtx} (hf : FrameOk cx) (h16 : cx.frame % 16 = 0) {pcR : Int64} {lblN : Lbl}
    {Jc : Spike.Lib.A64.Flow.AS → Ctl → Prop} (hJc : NbJcOf Λw.imms lblN cx Jc)
    (hlbl : ∀ l b, lblN l = some b → lbl l = some b)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -allocAbortDepth cx.frame - 48)
    (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λw.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λw lbl s fs B)
    {ms msN : MemSide isaLSE2}
    (hu : ∀ n τ us, TermRun.accs (TermRun.close [] τ) = some us → msN.units n τ ≤ n * TermRun.nWords us + 1)
    (hcl : msN.cells = ar.cells) (hct : msN.ctr = ar.ctr)
    (hma : ∀ s : State, (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      ms.abortAt s)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R' F'
        (A64.Abort.N (RuntimeLayout.ofPlaceOK h i).lab A64.Abort.heap c .svc) s c' → Dt s)
    {m0 : MachineData} {σC : Spike.Lib.A64.Flow.AS} {c0 : Ctl}
    (hJ : (nbX msN (_root_.Executable.labels (RuntimeLayout.ofPlaceOK h i).exe).label lblN R cx.frame pcR Jc
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
  exact stubHN_nbCoreX h i hf h16 hR hal hlo hhi hl hh hF hsub hfit hFO hfp hu hcl hct hma hK hwr hq hfull
    (hrep.mono_lbl hlbl) hte hel hsl

/-- **The heap abort exit of a buffer allocation's call never ends, at a
node of another world** (a segment to any `Q` inside `W2` at the write
abort's phase at (`ms`, `lbl`), at the frames `fs`; `Disp.seg_jabort2WS`
with `stubHN_nbAbX`): from `nbX msN … lblN … .abort` of a call from a frame
of `cx` at a call node placing its controls at `lblN` (`NbJcOf`), `lblN`
contained in `lbl` (`hlbl`), the arena facts at `msN`, with
`heapAb_seg`'s other premises. -/
theorem heapAb_segX {cx : FnCtx} (hf : FrameOk cx) (h16 : cx.frame % 16 = 0) {pcR : Int64} {lblN : Lbl}
    {Jc : Spike.Lib.A64.Flow.AS → Ctl → Prop} (hJc : NbJcOf Λw.imms lblN cx Jc)
    (hlbl : ∀ l b, lblN l = some b → lbl l = some b)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -allocAbortDepth cx.frame - 48)
    (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λw.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λw lbl s fs B)
    {ms : List TermRun.Frame → MemSide isaLSE2} {msN : MemSide isaLSE2}
    (hu : ∀ n τ us, TermRun.accs (TermRun.close [] τ) = some us → msN.units n τ ≤ n * TermRun.nWords us + 1)
    (hcl : msN.cells = ar.cells) (hct : msN.ctr = ar.ctr)
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
        (nbX msN (_root_.Executable.labels (RuntimeLayout.ofPlaceOK h i).exe).label lblN R cx.frame pcR Jc
          .abort)).at fs)
      Q := by
  haveI := (RuntimeLayout.ofPlaceOK h i).valid
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK (rS := rS) h i
  have hge := frame_ge16 hf
  have h16' : (-allocAbortDepth (cx.frame : Int)) % 16 = 0 := by
    simp only [allocAbortDepth, Spike.Lib.A64.Flow.NewBuf.allocFrame]; omega
  have hkc : -allocAbortDepth (cx.frame : Int) < R.hi := by
    simp only [allocAbortDepth, Spike.Lib.A64.Flow.NewBuf.allocFrame]; omega
  refine A64.Abort.Disp.seg_jabort2WS (W := fun s c => W2 Λw (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
        (Spike.Lib.A64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) rS
        (Spike.Lib.A64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i)) ar J Dt
        (Spike.Lib.A64.WriteAb.Ab (RuntimeLayout.ofPlaceOK h i).lab) lbl lsize s c fs)
    (nC := nbX msN (_root_.Executable.labels (RuntimeLayout.ofPlaceOK h i).exe).label lblN R cx.frame pcR Jc
      .abort) rfl (fun σ c hJ => by rw [hJ.1]; rfl) hF hR hal hlo hkc h16' hK (fun m0 σC c0 hJ => ?_) ms fs rfl
    (fun _ _ h => h) Q
  refine (stubHN_nbAbX h i hf h16 hJc hlbl hR hal hlo hhi hl hh hF hsub hfit hFO hfp hu hcl hct hma hK hwr
    hJ).stubHW hI.lays hI.endOk (hprog_ofPlaceOK h i) hK ?_
  exact Spike.Lib.A64.Flow.fstable_enter (kc := -allocAbortDepth (cx.frame : Int)) hR hF (by omega) (by decide)
    hkc (by decide) (by omega) (by decide) (by decide)

end Place

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.stubHN_nbCoreX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stubHN_nbCoreX

/-- info: 'Spike.Lib.LowerA64.stubHN_nbAbX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stubHN_nbAbX

/-- info: 'Spike.Lib.LowerA64.heapAb_segX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms heapAb_segX

end Spike.Lib.LowerA64
