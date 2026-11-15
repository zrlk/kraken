/-
**The lane stores and buffers at a generic base context at a reachable
placement** (x86-64; the twin of `Spike/Lib/LowerA64/G1LaneBufL.lean`):
`LaneBuf2StmtL` (`Spike/Lib/LowerX64/G1FnSpecL.lean`), `laneBuf2`'s
(`Spike/Lib/LowerX64/G1LaneBuf.lean`) at a context `CxG2ML` whose placement
`L`, `ls` is reachable by allocations from the start's, in the rebased
region.

As `laneBuf2`, with the placement's facts the lane stores ask for from its
reachability (`CxCore2L.hre`) where `laneBuf2` had them vacuous at no label
placed: every placed label has room after it (`Reach.lblRoom`), lies in the
heap (`lblRange_reach`) and its words are heap words (`heapW_ofReach`, the
counter's item a zeroed word by `ctrZ_ofPlaceOK`); the allocations'
`AllocW2At` at `L`, `ls` from `CxCore2L.hAW`, their heap abort at `L` one of
`AbG2L`'s.

- `laneBuf2L`: `LaneBuf2StmtL`.
-/
import Spike.Lib.LowerX64.G1LaneBuf
import Spike.Lib.LowerX64.G1FnSpecL
import Spike.Lib.LowerX64.HeapWOf
import Spike.Lib.AllocReachRoom
import Spike.Lib.LblRangeReach
import Spike.Lib.Rt.X64CtrZOfEmitted

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem (Marks Range)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region)
open Spike.Lib.X64.Rt (rS0)
open Spike.Lib.LowerNode (compiled2 TailAt2 TailOf IsNum imms2Me)

section Place

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates. -/
local notation "LY0" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

/-- **`LaneBuf2StmtL`**: at every context `CxG2ML` of the `j`th compiled
block at a reachable placement `L`, `ls` (return address in the code
facts' `RaOk`), in the rebased region, the lane stores (`laneC_w2E`, the
placed labels' room, range and heap words from the placement's
reachability) and the buffers (`newBufC_of`). -/
theorem laneBuf2L (hp : Scc.Lower.Accepted2 p = true) : LaneBuf2StmtL h hp := by
  intro Dt J L ls j d hd R F fs fp ra tp G0 Ab hcx hra
  obtain ⟨H, hAb⟩ := hcx
  have hlo := room2Own h hp j d hd 256 _ (H.room d hd)
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (imms2Me Λ p) (rS := rS0 (Ly))
  have hI0 := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms2Of p) (rS := rS0 (Ly))
  have hsp := fnCode2OfPMe_spec hp h Λ j d hd
  have hs := Spike.Lib.X64.Rt.arOf_sub h
  refine ⟨?_, ?_⟩
  · rw [okPc_imms h] at hI
    exact laneC_w2E hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) (fnCode2OfPMe hp h Λ j d hd).hf
      (fnCode2OfPMe hp h Λ j d hd).h1 H.hR H.hR8 (by omega) H.hhi H.hl H.hh
      (Spike.Lib.X64.Rt.rS0_sub (Ly)) (Spike.Lib.X64.Rt.fitS_of_sub _ (Spike.Lib.X64.Rt.rS0_sub (Ly))) H.hFO H.hFS
      (Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp) (H.hrs d hd) H.hfp
      (lcx := (fnCode2OfPMe hp h Λ j d hd).lcx) (tp := tp) (fun _ _ h' => h') H.hrd
      (H.hre.lblRoom Spike.Lib.AllocReach.lblRoom_none hs (below32_of_placeOKAt h))
      (Spike.Lib.lblRange_reach hs (fun _ => rfl) H.hre) H.hwn
      (heapW_ofReach h (Spike.Lib.X64.Rt.ctrZ_ofPlaceOK h) H.hwn (fun _ => rfl) H.hre) H.hG0F
  · refine newBufC_of (fnCode2OfPMe hp h Λ j d hd).hf (fnCode2OfPMe hp h Λ j d hd).h1
      (fnCode2OfPMe hp h Λ j d hd).hp (fnCode2OfPMe hp h Λ j d hd).hend
      (allocIn_of_placeOKAt h) H.hFS H.hR ?_ H.hhi ((fnCode2OfPMe hp h Λ j d hd).hCd ra hra) ?_
      (W₀ := fun lbl lsize s c => W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p IsNum
        (Spike.Lib.X64.PhRec.GOf Ly (Spike.Lib.X64.PhRec.m0Of (Ly).Λ
          (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))
          (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).secs))
        (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly)) (Spike.Lib.X64.Rt.arOf (Ly).Λ)
        (Spike.Lib.AllocReach.IN (Spike.Lib.X64.Rt.arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) Dt
        (Spike.Lib.X64.WriteAb.Ab (Ly).lab) lbl lsize s c fs)
      (fun _ _ h' => h') H.hK H.hG0 (fun x cn τ e ht => elem2_of_tailOf hp hd (ht d hd)) _ ?_ ?_
    · simp only [Spike.Lib.X64.Flow.NewBuf.allocAbortDepth, Spike.Lib.X64.Flow.NewBuf.allocFrame]; omega
    · intro pc zc g k hb
      rw [hsp.2.1] at hb
      exact cdOf_blC hI0.lays hI0.endOk pc zc g k (by rw [hI0.labOk]; exact hb.1.1)
    · intro c0 pc kk x cn τ e env n lits cs bufs tk kv en em hh hc0 hT
      exact H.hAW d hd ⟨x, cn, τ, e, hT⟩ c0 pc kk x cn τ e env n lits cs bufs tk kv en em hh hc0 hT
    · intro Jc pcR s c hJc hJT hX
      exact hAb s c fs ⟨j, d, hd, rbR R, F, fs, fp, ra, tp, G0, H, .inr (.inl ⟨rfl, Jc, pcR, hJc, hJT, hX⟩)⟩

end Place

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.laneBuf2L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.laneBuf2L
