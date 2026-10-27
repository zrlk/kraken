/-
**An abort of `print` never ends, the caller's frame placed from the
landing** (x86-64): `printAb_seg` (`Spike/Lib/LowerX64/MainAbX.lean`) at
`printNAS`, the abort landing holding the caller's slots, with the source
control's facts (`RefCtl`) discharged instead of given: `print`'s control is
a model term of the output extern, so only its frames need placing
(`PlacedSE.of_printTop`); the caller's frame is placed at the landing's
slots, which every state of the write path keeps (`CKept`,
`framesPlaced_ofSlotRepS`); the frame runs from it are `ZBad`-free
(`frOk2_printC`, `runOk2_of`).

- `printAb_segP`: the segment.
-/
import Spike.Lib.LowerX64.MainAbX
import Spike.Lib.LowerX64.PrintCallInstA
import Spike.Lib.LowerX64.PrintPlacedSE

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND At FStable)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.LowerNode (FrOk2 ZBad SlotRepAt printFrame runOk2_of)
open Spike.Lib.X64.StubW (RefCtl)
open A9NoSpawn (NoS)
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
  {ar : Arena} {J : InvS} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize}
  {rS : Scc.Sem.Range} {Λw : Scc.Sem.Layout}

/-- **An abort of `print` landing with the caller's slots never ends** (a
segment to any `Q` inside `W2` at the write abort's phase, at the frames
`printFrame x e c1 :: fs`): `printAbSeg2P` with `stubWN_w2_ofPlaceOK` at the
record, the source control's facts from the landing: the caller's control
`c1` placed at the landing's slots (at the table `it`, the layout's at `e`,
`hie`), kept along the write path off its region; the frames `fs` placed
under `F` (`hFP`); the continuation `e` and the frames' bodies `ZBad`-free
(`he`, `hfs`). In an 8-aligned region holding the frame, `print`'s 88 bytes
below it and the frame record. -/
theorem printAb_segP {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 88)
    (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hF : FStable R F)
    (hsub : rS.Sub Λw.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hp : ProgNoS ZBad p) {it : Expr → String → Nat → Option Nat} {x : String} {e : Expr} {c1 : Ctl}
    {fs : List TermRun.Frame} (hie : it e = Λw.imms e) (he : NoS ZBad e) (hfs : ∀ fr ∈ fs, NoS ZBad fr.body)
    (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λw lbl s fs A)
    {ms : List TermRun.Frame → MemSide isa}
    (hma : ∀ s : State, (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      (ms (printFrame x e c1 :: fs)).abortAt s)
    (hK : (ms (printFrame x e c1 :: fs)).K = some Scc.Sem.X64.abi)
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R' F' (Abort.N (RuntimeLayout.ofPlaceOK h i).lab Abort.write c .sys)
        s c' → Dt s)
    (Q : FragS isa) :
    SegWS (fun s c fs => W2 Λw (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
        (Spike.Lib.X64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) rS
        (Spike.Lib.X64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i)) ar J Dt
        (Spike.Lib.X64.WriteAb.Ab (RuntimeLayout.ofPlaceOK h i).lab) lbl lsize s c fs)
      (K (RuntimeLayout.ofPlaceOK h i) rS) p lbl ms
      ((At (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc R F
        (printNAS (_root_.Executable.labels (RuntimeLayout.ofPlaceOK h i).exe).label fr lbl it x e c1)).at
        (printFrame x e c1 :: fs)) Q := by
  haveI := (RuntimeLayout.ofPlaceOK h i).valid
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK (rS := rS) h i
  have h8 : (fr.size : Int) % 8 = 0 := by have := frame_mod8 hf; omega
  have hkc8 : (-(fr.size : Int) - 56 - 8) % 8 = 0 := by omega
  refine printAbSeg2P hI.lays hI.endOk (hprog_ofPlaceOK h i) hF hR hlo (by omega) h8 hK
    (fun m0 σC c0 hJ => ?_) Q
  obtain ⟨⟨-, pw, wn, nv, mv, k, hPC⟩, hsr⟩ := hJ
  rw [hie] at hsr
  have hro := runOk2_of hp (frOk2_printC (x := x) (c1 := c1) hPC he hfs)
  -- the caller's frame's cells: in `R`, off the write path's region
  have hoff : ∀ r k, rsOf fr r = some k → R.Off k ∧
      ¬ (R.callee (-(fr.size : Int) - 56 - 8) (-24) 16).Off (k - (-(fr.size : Int) - 56 - 8)) := by
    intro r k hk
    obtain ⟨hk1, hk2, hk3⟩ := rsOf_bounds hf hk
    simp only [Region.Off, Region.callee]
    omega
  have hc : RefCtl Λw p (fun s _ => Spike.Lib.X64.PhRec.own (RuntimeLayout.ofPlaceOK h i) s) lbl
      (fun m => F m ∧ CKept R (-(fr.size : Int) - 56 - 8) (-24) 16 m0 m ∧
        Abs R ⟨-(fr.size : Int) - 56, []⟩ m0 σC) c0 (printFrame x e c1 :: fs) :=
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
  refine stubWN_w2_ofPlaceOK h i
    (Region.callee_ok hR (by omega) (by decide) (by omega) (by omega)) (addr_toNat_mod8 R hR8 hkc8)
    (by show (-24 : Int) ≤ -24; omega) (by show (16 : Int) ≤ 16; omega)
    (by show (-24 : Int) % 8 = 0; decide) (by show (16 : Int) % 8 = 0; decide)
    (fstable_enter (kb := -(fr.size : Int) - 56 - 8) hR hF (by omega) (by decide) (by omega) (by omega)
      (by omega) (by decide) (by decide)) hsub hfit ?_ hc hma hK (hwr _ _ c0)
  intro m hm
  refine Spike.Lib.X64.Rt.stackOff_callee hR hR8 hl hh (by omega) (by decide) (by omega) hkc8 (hFO m hm.1) ?_
  intro k hk hn
  rw [hm.2.1 k hk hn]
  obtain ⟨j, hj, -⟩ := hm.2.2.slot k hk
  rw [hj]; rfl

end Place

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.printAb_segP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printAb_segP
