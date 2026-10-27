/-
**`H1OpenA.hAW` at `hello1`'s landing contexts** (AArch64): at every
context `CxOkH` (the setup frame of the block `rodata`,
`Spike/Test/A64Hello1CxOkH.lean`), the region's bound below the allocator's
frame and the returned base's store `AllocStoreAt` inside `W2` at every
reachable placement, from `allocStore_w2` at each allocation of the body
(`H1OpenA`, `Spike/Lib/LowerA64/H1InLandA.lean`).

The region's facts are `PRE`'s and the bounds' (as `setupCxLB_ofPre`), the
frame `[fr]` placed at no label (`framesPlaced_setup`) and so at every
placement (`framesPlacedInI_mono_lbl`), the walk's facts at the
continuation from the allocation's resumption facts (`PtC2.newBufW`), the
ghosts `FrOk2` along the setup frame's run.

- `hAW_CxOkH`: `H1OpenA.hAW` at `CxOkH`, given the setup type and the
  bodies' one-word elements (`H1OpenA.hTn`'s shape);
- `hAW_H1OpenA`: the field's shape (`H1OpenA.hAW`, `H1LandAW.hAW`) at any start
  frame condition;
- `hello1_hAWA`: `hAW_H1OpenA` at `hello1o` (`hello1_htyA`, `hello1_hTnA`).
-/
import Spike.Test.A64Hello1H1Of
import Spike.Lib.LowerA64.AllocW2Full
import Spike.Lib.LowerA64.AllocW2AtOf

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.LowerNode (FrOk2 compiled2 TailAt2 imms2Me)
open Spike.Lib.AllocReach (Reach IN)

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.A64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The record's marks. -/
local notation "Mk" => Spike.Lib.A64.PhRec.μ (Ly)

set_option hygiene false in
/-- **`W2` at the record** at a placement `L`, `ls`, over `IN … J` (as in `H1InLandA`). -/
local notation "W2R" J:max Dt:max L:max ls:max =>
  fun s c fs => W2 (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (Spike.Lib.A64.PhRec.own (Ly))
    (Spike.Lib.A64.Rt.rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly)) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J) Dt
    (Spike.Lib.A64.WriteAb.Ab (Ly).lab) L ls s c fs

set_option hygiene false in
/-- **The rows' memory side at the record** at the nodes' abort `ab2` (as in `H1InLandA`). -/
local notation "MSR" J:max L:max ls:max =>
  msOfAX (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (fun s _ => Spike.Lib.A64.PhRec.own (Ly) s) (Ar)
    (IN (Ar) (fun _ => none) (fun _ => 0) J) (ab2 p (Ly).lab) L ls

set_option hygiene false in
/-- The take's step relation at the record. -/
local notation "KT" => TakeK ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL) (Spike.Lib.A64.Rt.rS0 (Ly))

/-- **`H1OpenA.hAW` at the setup frame's contexts `CxOkH`**: at every
family `J`, reachable placement `L`, `ls` and context `CxOkH` of the
`j`th block, the region below the allocator's frame (`-D1` past the frame
row `fS ≤ nS` and `nS + 48 + 208 ≤ D1`) and at every allocation of the body
the returned base's store inside `W2` (`allocStore_w2`: the region's facts
from `PRE` and the bounds, `hFO` by `stackOff_callee`, the frame `[fr]`
placed at no label and so at every placement, the continuation's walk facts
by `PtC2.newBufW`, `elem2` by `hTn`, `FrOk2` along the setup frame's run). -/
theorem hAW_CxOkH (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hTn : ∀ j d, (compiled2 p)[j]? = some d →
      ∀ x cn τ e, TailAt2 p j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    {Dt : State → Prop} (J : InvS) :
    ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
    ∀ j d (hd : (compiled2 p)[j]? = some d) R F fs fp ra tp G0 Ab, CxOkH h hp j R F fs fp ra tp G0 Ab →
      R.lo ≤ -Spike.Lib.A64.Flow.NewBuf.allocAbortDepth ((fnCode2OfPMe hp h Λ j d hd).cx.frame : Int) ∧
      AllocStoreAt p L ls (fnCode2OfPMe hp h Λ j d hd).lcx (fnCode2OfPMe hp h Λ j d hd).cx
        (CdCLE (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog
          (Spike.Lib.A64.PhRec.okPc (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)))
          (Spike.Lib.A64.PhRec.ph (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)))
          (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)).lab (Int64.ofBitVec ra))
        ((fnCode2OfPMe hp h Λ j d hd).Bl ra)
        (fun L ls s c => (W2R J Dt L ls) s c fs) KT (Ly).exe (Ly).endPc R F ((MSR J L ls) fs) fp ra tp G0
        (imms2Me Λ p) (TailAt2 p j) (RetLk d.retTy) := by
  intro L ls _ j d hd R F fs fp ra tp G0 Ab hc
  obtain ⟨d', hd', L', D1, fS, nS, v, g, fr, J', hn, hfS, hnS, hL0, hLm, hL8, hD18, hL1, hrow,
    ⟨hR0, hal, hF', hFF, -, -, hct, -⟩, -, -, rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := hc
  obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
  obtain ⟨w, fi, -, -, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  have hframe : (fnCode2OfPMe hp h Λ j d hd).cx.frame = fS := by
    rw [hcx]; exact hrow _ _ hmem rfl (by show Scc.Lower.Names.user d.name = _; rw [hn])
  have hpN := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  have hlo : -D1 ≤ -Spike.Lib.A64.Flow.NewBuf.allocAbortDepth ((fnCode2OfPMe hp h Λ j d hd).cx.frame : Int) := by
    simp only [Spike.Lib.A64.Flow.NewBuf.allocAbortDepth, Spike.Lib.A64.Flow.NewBuf.allocFrame]
    rw [hframe]; omega
  have hlo0 : -D1 ≤ -((fnCode2OfPMe hp h Λ j d hd).cx.frame : Int) := by rw [hframe]; omega
  have hhi : (0 : Int) ≤ 0 := Int.le_refl _
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2A h hp hs') (rtCodeOkS_setupWords2A h hp hs')).1
  have hZ := setupMC_Z _ hsw
  refine ⟨hlo, ?_⟩
  intro c0 pc kk x cn τ e env n lits cs bufs tk kv en em hh hc0 hT hfr _ _ _ hpt
  obtain ⟨-, -, -, -, -, hIt, hIc, hlbe⟩ := PtC2.newBufW hpt
  intro la ls' k _ hls _ _ _ _ _ _ hCd' lbl' lsize' hl' _
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms2Of p) (rS := Spike.Lib.A64.Rt.rS0 (Ly))
  exact allocStore_w2 hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) (fnCode2OfPMe hp h Λ j d hd).hf
    (fnCode2OfPMe hp h Λ j d hd).h1 (fnCode2OfPMe hp h Λ j d hd).h16 hR0 hal hlo hhi
    (by show (-D1) % 8 = 0; omega) (by show (0 : Int) % 8 = 0; rfl)
    (Spike.Lib.A64.Rt.rS0_sub _) (Spike.Lib.A64.Rt.fitS_of_sub _ (Spike.Lib.A64.Rt.rS0_sub _))
    (by
      intro m hm
      obtain ⟨⟨⟨hv, -⟩, hoff⟩, hcc⟩ := hFF m hm
      subst hv
      have hok : (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L') 0).OK := by
        rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hLm
      have h8 : (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L') 0).base.toNat % 8 = 0 := by
        show (stacksA (Ly).lab + 0#64 + 16384#64).toNat % 8 = 0
        rw [Spike.Lib.A64.Rt.stacksA_lab0]; have := Spike.Lib.A64.Rt.rt_h16 (Ly); omega
      exact Spike.Lib.A64.Flow.Ret0.Inst.stackOff_callee hok h8 (by show (-L') % 8 = 0; omega)
        (by show (0 : Int) % 8 = 0; rfl)
        (by show -L' ≤ _; omega) (by omega) (by show _ < (0 : Int); omega) (by omega) hoff hcc)
    hF' hpN (fun _ _ hr => regionOff_of_rsOf (fnCode2OfPMe hp h Λ j d hd).hf hlo0 hhi hr)
    (fun s _ => (framesPlaced_setup h hp hty hct s).imp fun _ hB =>
      framesPlacedInI_mono_lbl (fun _ _ hl => by cases hl) hB)
    (hTn j d hd x cn τ e hT) hfr hl' (fun h => nomatch h)
    (FrOk2.runM hpN hc0 (FrOk2.step hpN (hct.step []) (hf0_start2A hty _))) hls hCd' hIt hIc hlbe

/-- **`H1OpenA.hAW` at `CxOkH`** in the field's shape (`hAW_CxOkH`, the
family's start premise and the return's phase unused): at the code
`fnCode2OfPMe`, any start frame condition `FE` (`rtF` for `H1OpenA`, `WordsNone ∧ rtF` for
`H1LandAW`), bottoms `Bot` and write tail `Dt`. -/
theorem hAW_H1OpenA (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hTn : ∀ j d, (compiled2 p)[j]? = some d →
      ∀ x cn τ e, TailAt2 p j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    {E : Entry} {FE : MachineData → Prop} {Bot : StkKey → List TermRun.Frame → Prop} {Dt : State → Prop} :
    ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSA h E FE (ElA h (fnCode2OfPMe hp h Λ) (CxOkH h hp) Bot) Dt (ab2 p (Ly).lab)
        L ls s c fs → J L ls s c fs) →
    ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
    ∀ j d (hd : (compiled2 p)[j]? = some d) R F fs fp ra tp G0 Ab, CxOkH h hp j R F fs fp ra tp G0 Ab →
      Spike.Lib.A64.PhRec.ph (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p))
          (Int64.ofBitVec ra).toBitVec.toNat =
        Spike.Lib.A64.PhRec.ph (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p))
          (Int64.ofBitVec ((Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)).lab
            Spike.Lib.A64.Rt.bareMC.e0 + 4).toBitVec).toBitVec.toNat →
      R.lo ≤ -Spike.Lib.A64.Flow.NewBuf.allocAbortDepth ((fnCode2OfPMe hp h Λ j d hd).cx.frame : Int) ∧
      AllocStoreAt p L ls (fnCode2OfPMe hp h Λ j d hd).lcx (fnCode2OfPMe hp h Λ j d hd).cx
        (CdCLE (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog
          (Spike.Lib.A64.PhRec.okPc (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)))
          (Spike.Lib.A64.PhRec.ph (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)))
          (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)).lab (Int64.ofBitVec ra))
        ((fnCode2OfPMe hp h Λ j d hd).Bl ra)
        (fun L ls s c => (W2R J Dt L ls) s c fs) KT (Ly).exe (Ly).endPc R F ((MSR J L ls) fs) fp ra tp G0
        (imms2Me Λ p) (TailAt2 p j) (RetLk d.retTy) :=
  fun J _ L ls hR j d hd R F fs fp ra tp G0 Ab hc _ =>
    hAW_CxOkH h hp hty hTn J L ls hR j d hd R F fs fp ra tp G0 Ab hc

end Assembled

/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

variable {Λx : Scc.Sem.Layout}

set_option hygiene false in
/-- The layout: any layout at which the placement check passes (`h`). -/
local notation "LeA" => Λx

set_option hygiene false in
/-- The runtime's layout of `hello1o`'s output at the theorem's immediates. -/
local notation "LyH" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h' (imms2Me LeA P1A)

set_option hygiene false in
/-- The runtime's layout of `hello1o`'s output at the compiler's immediates. -/
local notation "LY0" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h' (Scc.Lower.imms2Of P1A)

set_option hygiene false in
/-- The allocator's arena of `hello1o`'s output. -/
local notation "ArH" => Spike.Lib.A64.Rt.arOf (lay2 LeA P1A)

/-- **`hello1`'s `H1OpenA.hAW`** at every placement check of `hello1o`'s
output at any layout passing it and every start frame condition `FE`
(`hAW_H1OpenA` at `hello1_htyA`, `hello1_hTnA`). -/
theorem hello1_hAWA
    (h' : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A)
      (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)) = true)
    {E : Entry} {FE : MachineData → Prop} {Bot : StkKey → List TermRun.Frame → Prop} {Dt : State → Prop} :
    ∀ J : InvS, (∀ L ls, Reach (ArH) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSA h' E FE
        (ElA h' (fnCode2OfPMe Spike.Lib.LowerNode.hello1o_accepted2 h' LeA)
          (CxOkH h' Spike.Lib.LowerNode.hello1o_accepted2) Bot) Dt (ab2 P1A (LyH).lab) L ls s c fs →
        J L ls s c fs) →
    ∀ L ls, Reach (ArH) (fun _ => none) (fun _ => 0) L ls →
    ∀ j d (hd : (compiled2 P1A)[j]? = some d) R F fs fp ra tp G0 Ab,
      CxOkH h' Spike.Lib.LowerNode.hello1o_accepted2 j R F fs fp ra tp G0 Ab →
      Spike.Lib.A64.PhRec.ph (LY0) (Int64.ofBitVec ra).toBitVec.toNat =
        Spike.Lib.A64.PhRec.ph (LY0)
          (Int64.ofBitVec ((LY0).lab Spike.Lib.A64.Rt.bareMC.e0 + 4).toBitVec).toBitVec.toNat →
      R.lo ≤ -Spike.Lib.A64.Flow.NewBuf.allocAbortDepth
        ((fnCode2OfPMe Spike.Lib.LowerNode.hello1o_accepted2 h' LeA j d hd).cx.frame : Int) ∧
      AllocStoreAt P1A L ls (fnCode2OfPMe Spike.Lib.LowerNode.hello1o_accepted2 h' LeA j d hd).lcx
        (fnCode2OfPMe Spike.Lib.LowerNode.hello1o_accepted2 h' LeA j d hd).cx
        (CdCLE (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)).prog
          (Spike.Lib.A64.PhRec.okPc (LY0)) (Spike.Lib.A64.PhRec.ph (LY0)) (LY0).lab (Int64.ofBitVec ra))
        ((fnCode2OfPMe Spike.Lib.LowerNode.hello1o_accepted2 h' LeA j d hd).Bl ra)
        (fun L ls s c => W2 (lay2 LeA P1A) (Spike.Lib.A64.PhRec.μ (LyH)) P1A Spike.Lib.LowerNode.IsNum (G2 h' P1A)
          (Spike.Lib.A64.PhRec.own (LyH)) (Spike.Lib.A64.Rt.rS0 (LyH)) (Spike.Lib.A64.PhRec.Tk (LyH)) (ArH)
          (IN (ArH) (fun _ => none) (fun _ => 0) J) Dt (Spike.Lib.A64.WriteAb.Ab (LyH).lab) L ls s c fs)
        (TakeK ((LyH).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL) (Spike.Lib.A64.Rt.rS0 (LyH)))
        (LyH).exe (LyH).endPc R F
        (msOfAX (lay2 LeA P1A) (Spike.Lib.A64.PhRec.μ (LyH)) P1A Spike.Lib.LowerNode.IsNum (G2 h' P1A)
          (fun s _ => Spike.Lib.A64.PhRec.own (LyH) s) (ArH) (IN (ArH) (fun _ => none) (fun _ => 0) J)
          (ab2 P1A (LyH).lab) L ls fs) fp ra tp G0
        (imms2Me LeA P1A) (TailAt2 P1A j) (RetLk d.retTy) :=
  hAW_H1OpenA h' Spike.Lib.LowerNode.hello1o_accepted2 hello1_htyA.choose_spec hello1_hTnA

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.hAW_CxOkH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hAW_CxOkH

/-- info: 'Spike.Lib.LowerA64.hAW_H1OpenA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hAW_H1OpenA

/-- info: 'Spike.Lib.LowerA64.hello1_hAWA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_hAWA
