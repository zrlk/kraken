/-
**The lane stores and buffers at a generic base context** (x86-64; the
twin of `Spike/Lib/LowerA64/G1LaneBuf.lean`): `LaneBuf2Stmt`
(`Spike/Lib/LowerX64/G1FnSpec.lean`), the `LaneC` and `NewBufC` conjuncts
of `bodySpecC2_of`'s `hcon` in the rebased region `rbR R` at every context
`CxG2M` of the `j`th compiled block of an `Accepted2` program, at the
assembled theorem's world `W2At`/`MSAt` and the placement check's code
facts `fnCode2OfPMe`, both at the theorem's immediates `imms2Me Λ p`.

The lane stores by `laneC_w2E` (`Spike/Lib/LowerX64/LaneCW2.lean`) at the
record's instance at `imms2Me Λ p` (`instOk_ofPlaceOK`), the buffers by
`newBufC_of` (`Spike/Lib/LowerX64/NewBufC2.lean`), as `fnSpecC2_ofCxLB`
(`Spike/Lib/LowerX64/CxLB.lean`) takes them: the region's facts, frames,
reads, ghosts and the memory side's kernel from `CxCore2` (at the rebased
region); the room below the frame from the stack need table's row
(`room2Own`, at the region's lowest offset below the entry `%rsp`); the
allocations' `AllocW2At` from `CxCore2.hAW` (at a block with a buffer);
their heap abort, from a call node, one of `AbG2`'s, so in the context's
aborts; the calls' `callq` in the code (`cdOf_blC`). From the placement
check: the runtime's print, abort and allocator code, the first stack in
the pool; from `Accepted2`: no `ZBad` (`progNoS_zbad_of_accepted2`), the
allocations' one-word elements (`elem2_of_tailOf`). No label is placed
(`LblRoom`, `LblRange`, `HeapW` vacuous).

- `okPc_imms`: the record's sites at either immediates' table;
- `elem2_of_tailOf`: a buffer allocation of a compiled block has a
  one-word element type;
- `laneBuf2`: `LaneBuf2Stmt`.
-/
import Spike.Lib.LowerX64.G1Room2

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem (Marks Range)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region)
open Spike.Lib.X64.Rt (rS0)
open Spike.Lib.LowerNode (compiled2 TailAt2 TailOf IsNum imms2Me)

/-- **A buffer allocation of a compiled block has a one-word element
type** (`body2`'s check at the allocation's `let`). -/
theorem elem2_of_tailOf {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) {x : String} {cn : At} {τ : Ty} {e : Expr}
    (ht : TailOf (.let_ x (.newBuf cn τ) e) d.body) : Scc.Lower.elem2 τ = true := by
  obtain ⟨hdp, hdc⟩ := List.mem_filter.1 (List.mem_of_getElem? hd)
  have hdc' : ((Scc.Frontend.externs p).any (·.1 == d.name)) = false := by simpa using hdc
  obtain ⟨A, B, hpe⟩ := List.append_of_mem hdp
  obtain ⟨c2, cs, bufs, scope, hb, -, -⟩ := Spike.Lib.LowerNode.body2_of_compiled hp hpe hdc'
  obtain ⟨_, _, _, hb'⟩ := Spike.Lib.LowerNode.body2_tail ht hb
  simp only [Scc.Lower.body2, Bool.and_eq_true] at hb'
  exact hb'.1.2

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

/-- **The record's sites at either immediates' table**: `okPcOf` reads the
layout only through its code's base and abort labels. -/
theorem okPc_imms : Spike.Lib.X64.PhRec.okPc (Ly) = Spike.Lib.X64.PhRec.okPc (LY0) := by
  have e1 : (Ly).Λ.code.lo = (LY0).Λ.code.lo := rfl
  have e2 : (Ly).prog = (LY0).prog := rfl
  have e3 : (Ly).Λ.abortLbl = (LY0).Λ.abortLbl := rfl
  unfold Spike.Lib.X64.PhRec.okPc
  rw [e1, e2]
  funext pc
  unfold Scc.Cert.Rt.X64.okPcOf Scc.Cert.Rt.X64.sitesOf Scc.Cert.Rt.X64.sitesBy Scc.Cert.Rt.X64.siteLabels
  rw [e3]

/-- **`LaneBuf2Stmt`**: at every context `CxG2M` of the `j`th compiled
block (return address in the code facts' `RaOk`), in the rebased region,
the lane stores (`laneC_w2E`) and the buffers (`newBufC_of`). -/
theorem laneBuf2 (hp : Scc.Lower.Accepted2 p = true) : LaneBuf2Stmt h hp := by
  intro Dt J j d hd R F fs fp ra tp G0 Ab hcx hra
  obtain ⟨H, hAb⟩ := hcx
  have hlo := room2Own h hp j d hd 256 _ (H.room d hd)
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (imms2Me Λ p) (rS := rS0 (Ly))
  have hI0 := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms2Of p) (rS := rS0 (Ly))
  have hsp := fnCode2OfPMe_spec hp h Λ j d hd
  refine ⟨?_, ?_⟩
  · rw [okPc_imms h] at hI
    exact laneC_w2E hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) (fnCode2OfPMe hp h Λ j d hd).hf
      (fnCode2OfPMe hp h Λ j d hd).h1 H.hR H.hR8 (by omega) H.hhi H.hl H.hh
      (Spike.Lib.X64.Rt.rS0_sub (Ly)) (Spike.Lib.X64.Rt.fitS_of_sub _ (Spike.Lib.X64.Rt.rS0_sub (Ly))) H.hFO H.hFS
      (Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp) (H.hrs d hd) H.hfp
      (lcx := (fnCode2OfPMe hp h Λ j d hd).lcx) (tp := tp) (fun _ _ h' => h') H.hrd
      (fun _ _ hn => by cases hn) (fun _ _ hb => by cases hb) H.hwn (fun _ _ _ _ hl => by cases hl) H.hG0F
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

/-- info: 'Spike.Lib.LowerX64.elem2_of_tailOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.elem2_of_tailOf

/-- info: 'Spike.Lib.LowerX64.okPc_imms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.okPc_imms

/-- info: 'Spike.Lib.LowerX64.laneBuf2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.laneBuf2
