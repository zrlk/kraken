/-
**An abort of `print` never ends, the caller's frame placed from the
landing** (AArch64): `printAb_seg` (`Spike/Lib/LowerA64/MainAbA.lean`) at
`printNAS`, the abort landing holding the caller's slots, with the source
control's facts (`RefCtl`) discharged instead of given: `print`'s control is
a model term of the output extern, so only its frames need placing
(`PlacedSE.of_printTop`); the caller's frame is placed at the landing's
slots, which every state of the write path keeps (`CKept`,
`framesPlaced_ofSlotRepS`); the frame runs from it are `ZBad`-free
(`frOk2_printC`, `runOk2_of`). The twin of
`Spike/Lib/LowerX64/PrintAbP.lean`.

- `printAb_segP`: the segment.
-/
import Spike.Lib.LowerA64.MainAbA
import Spike.Lib.LowerA64.PrintCallInstA
import Spike.Lib.LowerA64.PrintPlacedSE
import Spike.Lib.LowerA64.PrintW2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (NodeW BlkW ND At FStable Abs CKept)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.LowerNode (FrOk2 ZBad SlotRepAt printFrame runOk2_of)
open Spike.Lib.A64.StubW (RefCtl)
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
  {ar : Arena} {J : InvS} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize}
  {rS : Range} {Λw : Scc.Sem.Layout}

/-- **An abort of `print` landing with the caller's slots never ends** (a
segment to any `Q` inside `W2` at the write abort's phase, at the frames
`printFrame x e c1 :: fs`): `printAbSeg2P` with `stubWN_w2_ofPlaceOK` at the
record, the source control's facts from the landing: the caller's control
`c1` placed at the landing's slots (at the table `it`, the layout's at `e`,
`hie`), kept along the write path off its region; the frames `fs` placed
under `F` (`hFP`); the continuation `e` and the frames' bodies `ZBad`-free
(`he`, `hfs`). In a 16-aligned region holding the frame and `print`'s 96
bytes below it. -/
theorem printAb_segP {cx : FnCtx} (hf : FrameOk cx) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - 96)
    (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hF : FStable R F)
    (hsub : rS.Sub Λw.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hp : ProgNoS ZBad p) {it : Expr → String → Nat → Option Nat} {x : String} {e : Expr} {c1 : Ctl}
    {fs : List TermRun.Frame} (hie : it e = Λw.imms e) (he : NoS ZBad e) (hfs : ∀ fr ∈ fs, NoS ZBad fr.body)
    (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λw lbl s fs A)
    {ms : List TermRun.Frame → MemSide isaLSE2}
    (hma : ∀ s : State, (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      (ms (printFrame x e c1 :: fs)).abortAt s)
    (hK : (ms (printFrame x e c1 :: fs)).K = some Scc.Sem.A64.abi)
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R' F'
        (A64.Abort.N (RuntimeLayout.ofPlaceOK h i).lab A64.Abort.write c .svc) s c' → Dt s)
    (Q : FragS isaLSE2) :
    SegWS (fun s c fs => W2 Λw (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
        (Spike.Lib.A64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) rS
        (Spike.Lib.A64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i)) ar J Dt
        (Spike.Lib.A64.WriteAb.Ab (RuntimeLayout.ofPlaceOK h i).lab) lbl lsize s c fs)
      (K (RuntimeLayout.ofPlaceOK h i) rS) p lbl ms
      ((At (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc R F
        (printNAS (_root_.Executable.labels (RuntimeLayout.ofPlaceOK h i).exe).label cx lbl it x e c1)).at
        (printFrame x e c1 :: fs)) Q := by
  haveI := (RuntimeLayout.ofPlaceOK h i).valid
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK (rS := rS) h i
  have hR8 : R.base.toNat % 8 = 0 := by omega
  have hk8 : (-(cx.frame : Int) + -48) % 8 = 0 := by omega
  refine printAbSeg2P hI.lays hI.endOk (hprog_ofPlaceOK h i) hF hR hal hlo (by omega) (by omega) hK
    (fun m0 σC c0 hJ => ?_) Q
  obtain ⟨⟨-, pw, wn, nv, mv, k, hPC⟩, hsr⟩ := hJ
  rw [hie] at hsr
  have hro := runOk2_of hp (frOk2_printC (x := x) (c1 := c1) hPC he hfs)
  -- the caller's frame's cells: in `R`, off the write path's region
  have hoff : ∀ r k, rsOf cx r = some k → R.Off k ∧
      ¬ (R.callee (-(cx.frame : Int) + -48) (-48) 0).Off (k - (-(cx.frame : Int) + -48)) := by
    intro r k hk
    obtain ⟨hk1, hk2, hk3⟩ := rsOf_bounds hf h16 hk
    simp only [Region.Off, Region.callee]
    omega
  have hc : RefCtl Λw p (fun s _ => Spike.Lib.A64.PhRec.own (RuntimeLayout.ofPlaceOK h i) s) lbl
      (fun m => F m ∧ CKept R (-(cx.frame : Int) + -48) (-48) 0 m0 m ∧
        Abs R ⟨-(cx.frame : Int) + -48, []⟩ m0 σC) c0 (printFrame x e c1 :: fs) :=
    { noRet := fun h => (List.cons_ne_nil _ _ h).elim
      cell := hro.cell
      place := fun s hs => by
        obtain ⟨hFs, hk, hA⟩ := hs
        obtain ⟨A2, h2⟩ := hFP s hFs
        refine PlacedSE.of_printTop (printC_top hPC)
          (framesPlaced_ofSlotRepS (R := R) (sl := σC.slot) (fun r k hr => ?_) hsr h2).choose_spec.toFramesPlaced
        obtain ⟨ho1, ho2⟩ := hoff r k hr
        rw [hk k ho1 ho2]
        exact hA.slot k ho1
      runOut := fun _ _ _ _ => rfl
      runIn := fun _ _ _ _ => rfl
      zero := hro.zero }
  have hcf := Spike.Lib.A64.Flow.Ret0.Inst.callee_facts (kc := -(cx.frame : Int) + -48) (lo' := -48) hR hal
    (by omega) (by decide) (by omega) (by omega)
  refine stubWN_w2_ofPlaceOK h i hcf.1 hcf.2
    (by show (-48 : Int) ≤ -48; omega) (by show (0 : Int) ≤ 0; omega)
    (by show (-48 : Int) % 8 = 0; decide) (by show (0 : Int) % 8 = 0; decide)
    (Spike.Lib.A64.Flow.fstable_enter (kc := -(cx.frame : Int) + -48) hR hF (by omega) (by decide) (by omega)
      (by decide) hk8 (by decide) (by decide)) hsub hfit ?_ hc hma hK (hwr _ _ c0)
  intro m hm
  refine Spike.Lib.A64.Flow.Ret0.Inst.stackOff_callee hR hR8 hl hh (by omega) (by decide) (by omega) hk8
    (hFO m hm.1) ?_
  intro k hk hn
  rw [hm.2.1 k hk hn]
  obtain ⟨j, hj, -⟩ := hm.2.2.slot k hk
  rw [hj]; rfl

end Place

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.printAb_segP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printAb_segP
