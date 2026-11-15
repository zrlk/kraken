/-
**The output calls held at `print`'s `ret ()` at a base context at a
reachable placement** (AArch64): `Print2HStmtL`, `Print2StmtL`
(`Spike/Lib/LowerA64/G1FnSpecL.lean`) at `PrintCallCH`
(`Spike/Lib/LowerA64/HeldC.lean`), and its proof `print2HL`, `print2L`
(`Spike/Lib/LowerA64/G1PrintL.lean`) with the output call's instance at the
held post (`printCallCH_instAI`, the same premises as
`printCallC_instAI`).

- `Print2HStmtL`: the statement;
- `print2HL`: its proof.
-/
import Spike.Lib.LowerA64.G1PrintL

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

open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow.Ret0 (StackOff limA pinA)
open Spike.Lib.AllocReach (IN Reach)
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2 imms2Me IsNum)

section G1PrintHL

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates. -/
local notation "LY0" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output. -/
local notation "OUT" => Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))

set_option hygiene false in
/-- The canonical load's memory of the output. -/
local notation "M0" => Spike.Lib.A64.PhRec.m0Of (Ly).Λ OP (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).secs

set_option hygiene false in
/-- `W2AtL` at `Closed2AtA`'s instance and the placement `L`, `ls`. -/
local notation "W2L" J:max L:max ls:max => W2AtL h (imms2Me Λ p) p IsNum (rS0 (Ly)) J Dt (fun _ => 0) L ls

set_option hygiene false in
/-- `MSAtL` at `Closed2AtA`'s instance (the nodes' abort `ab2`) and the
placement `L`, `ls`. -/
local notation "MSL" J:max L:max ls:max => MSAtL h (imms2Me Λ p) p IsNum J (ab2 p (Ly).lab) (fun _ => 0) L ls

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => Spike.Lib.A64.Flow.Ret0.TakeK ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The `j`th compiled block's code facts at the theorem's immediates. -/
local notation "FC" j:max d:max hd:max => fnCode2OfPMe hp h Λ j d hd

set_option hygiene false in
/-- The code predicate at the return address `ra`. -/
local notation "CD" ra:max => CdCLE OP (Spike.Lib.A64.PhRec.okPc LY0) (Spike.Lib.A64.PhRec.ph LY0) (LY0).lab
  (Int64.ofBitVec ra)

/-- **The output calls held at `print`'s `ret ()` at a base context at a
reachable placement** (`Print2StmtL` at `PrintCallCH`: `main`'s held
output calls). -/
def Print2HStmtL (hp : Scc.Lower.Accepted2 p = true) : Prop :=
  ∀ (Dt : State → Prop),
    (∀ (R' : Region) (F' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (σC : AS) s c',
      Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc R' F'
        (Spike.Lib.A64.Flow.PrintCall.pN (_root_.Executable.labels (Ly).exe).label Pc Qc σC .svc) s c' → Dt s) →
    ∀ (J : InvS) (L : WeakMem.AllocLabel → Option Nat) (ls : WeakMem.AllocLabel → Nat)
    (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d) (R : Region)
    (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop)
    (Ab : FragS isaLSE2),
    CxG2ML h hp Dt J L ls j R F fs fp ra tp G0 Ab →
    Spike.Lib.A64.PhRec.ph LY0 (Int64.ofBitVec ra).toBitVec.toNat =
      Spike.Lib.A64.PhRec.ph LY0 (Int64.ofBitVec ((LY0).lab Spike.Lib.A64.Rt.bareMC.e0 + 4).toBitVec).toBitVec.toNat →
    PrintCallCH p L ls (FC j d hd).lcx (FC j d hd).cx (CD ra) ((FC j d hd).Bl ra) (LY0).exe
      (LY0).endPc R F (W2L J L ls) (KT) (MSL J L ls) fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j) Ab

/-- **`Print2HStmtL`** (`print2L` at the held post): the output calls at
`PrintCallCH` (`printCallCH_instAI`, `printCallC_instAI`'s premises). -/
theorem print2HL (hp : Scc.Lower.Accepted2 p = true) : Print2HStmtL h hp := by
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
  exact printCallCH_instAI (Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (imms2Me Λ p) (rS := rS0 (Ly)))
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

end G1PrintHL

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.print2HL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.print2HL
