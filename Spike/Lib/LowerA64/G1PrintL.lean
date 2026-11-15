/-
**The output calls at a generic base context at a reachable placement**
(AArch64): `Print2StmtL` (`Spike/Lib/LowerA64/G1FnSpecL.lean`), `print2`'s
(`Spike/Lib/LowerA64/G1Print.lean`) at a context `CxG2ML` whose placement
`L`, `ls` is reachable by allocations from the start's.

As `print2`, the output call's frame and abort states at `L`: the placed
labels in the heap (`lblRange_reach`, from `CxCore2L.hre`) where `print2`
had them vacuous at no label placed, the frames placed at `L`
(`CxCore2L.hfp`), the output calls' abort states at `L` one of `AbG2L`'s.

- `print2L`: `Print2StmtL`.
-/
import Spike.Lib.LowerA64.G1Print
import Spike.Lib.LowerA64.G1FnSpecL
import Spike.Lib.LblRangeReach

namespace Spike.Lib.LowerA64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (Marks Range)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Rt (rS0)
open Spike.Lib.LowerNode (compiled2 TailAt2 TailOf IsNum imms2Me ZBad FrOk2)
open Scc.Lower (hasPrint)

section Place

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates. -/
local notation "LY0" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))

/-- **`Print2StmtL`**: at every context `CxG2ML` of the `j`th compiled
block at a reachable placement `L`, `ls` (return address in the code facts'
`RaOk`), the output calls (`printCallC_instAI`, the placed labels in the
heap from the placement's reachability), given the write tail at the output
call's system call. -/
theorem print2L (hp : Scc.Lower.Accepted2 p = true) : Print2StmtL h hp := by
  intro Dt hDtP J L ls j d hd R F fs fp ra tp G0 Ab hcx hra
  obtain ⟨H, hAb⟩ := hcx
  have hsp := fnCode2OfPMe_spec hp h Λ j d hd
  have hlo := room2Own h hp j d hd 256 R.lo (H.room d hd)
  have hBl0 : ∀ pc g' k, (fnCode2OfPMe hp h Λ j d hd).Bl ra pc g' k →
      BlC2L OP (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (Ly).lab
        (fnCode2OfPMe hp h Λ j d hd).cx (Int64.ofBitVec ra) pc g' k := by
    intro pc g' k hb
    rw [hsp.2.1] at hb
    rw [okPc_imms h]
    exact hb
  intro c0 pc pc' kk env n x g is a ts e xe dg t b o m cw lits cs bufs hc0 hT hfr hlp henv hgrp hcnt hsh hxe hdg
    hret hat hins hfv himm hlb
  have hxe' := hxe
  rw [hsp.1] at hxe'
  obtain ⟨rfl, rfl⟩ := extern_call_print hp hd (hT d hd) hxe'
  have hP : hasPrint p = true := by
    obtain ⟨dx, hdx, hex⟩ := List.mem_filterMap.1 (List.mem_of_find?_eq_some hxe')
    obtain ⟨ex, hex', -⟩ := Option.map_eq_some_iff.1 hex
    exact hasPrint_of_externOf hp hdx hex'
  have hab : ab2 p (Ly).lab = some (Spike.Lib.A64.WriteAb.Ab (Ly).lab) := by
    simp only [ab2, hP, ↓reduceIte]
  simp only [hab]
  exact printCallC_instAI (Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (imms2Me Λ p) (rS := rS0 (Ly)))
    (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h)
    (Spike.Lib.A64.PrintG.printPhOkF_of_tailPhOk (Spike.Lib.A64.Rt.tailPhOk_ofPlaceOK h _))
    (fnCode2OfPMe hp h Λ j d hd).hf (fnCode2OfPMe hp h Λ j d hd).h1 (fnCode2OfPMe hp h Λ j d hd).h16
    H.hR H.hal (by omega) H.hhi H.hl H.hh
    (Spike.Lib.A64.Rt.rS0_sub (Ly)) (Spike.Lib.A64.Rt.fitS_of_sub _ (Spike.Lib.A64.Rt.rS0_sub (Ly)))
    H.hFO (Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp) H.hFS
    (fun _ _ hc => by rw [okPc_imms h]; exact CdCLE.toCdCL hc)
    (fun _ _ _ hb => ⟨(hBl0 _ _ _ hb).1.1, BlC2L.posOff (hBl0 _ _ _ hb)⟩)
    hsp.2.2.1 (fun _ _ hb => (hBl0 _ _ _ hb).1)
    (Spike.Lib.LowerNode.printDecl_of_accepted2 hp hP) (hd2 hp h hP) (by rw [hsp.1])
    (Spike.Lib.lblRange_reach (Spike.Lib.A64.Rt.arOf_sub h) (fun _ => rfl) H.hre) (below32_of_placeOKAt h)
    (H.hG0F c0 hc0).2 H.hfp H.hG0F
    (fun _ _ _ _ _ _ _ ht hx => extern_call_print hp hd (ht d hd) (by rw [hsp.1] at hx; exact hx))
    fp ra tp
    (fun _ _ _ _ ht => noS_cont hp hd (ht d hd))
    hDtP
    (fun c0' x' is' a' e' c1 s c hc0' ht hX =>
      hAb s c _ ⟨j, d, hd, R, F, fs, fp, ra, tp, G0, H, .inr (.inr ⟨c0', x', is', a', e', c1, hc0', ht, rfl, hX⟩)⟩)
    (fun _ _ _ _ h' => h') (fun _ _ _ _ _ => rfl)
    c0 pc pc' kk env n x "print" is a [] e xe dg t b o m cw lits cs bufs hc0 hT hfr hlp henv hgrp hcnt hsh hxe hdg
    hret hat hins hfv himm hlb

end Place

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.print2L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.print2L
