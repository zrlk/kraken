/-
**The plain calls held at the callee's return at a base context at a
reachable placement** (AArch64): `CallC2H`
(`Spike/Lib/LowerA64/HeldC.lean`) at the placement `L`, `ls` from
`callC2H_ofFW` (`Spike/Lib/LowerA64/G1CallHW.lean`), the call's blocks
inside `W2` (`wCallG2L`, `Spike/Lib/LowerA64/G1WCallG2L.lean`), the
result's store at its held node (`callW2_hWH`,
`Spike/Lib/LowerA64/G1CallHW2.lean`) and the callee as
`callC2R_ofCxG2MSL`'s (`Spike/Lib/LowerA64/G1CallC2RL.lean`).

- `callC2H_ofCxG2MSL`: `CallC2H` at a base context at any frames
  (`CxG2ML`), the callee's records from its base context;
  `callC2H_ofCxG2ML`: the callee's records at the bottom (`main`'s held
  calls).
-/
import Spike.Lib.LowerA64.G1CallC2RL
import Spike.Lib.LowerA64.G1WCallG2L
import Spike.Lib.LowerA64.G1CallHW
import Spike.Lib.LowerA64.G1CallHW2

namespace Spike.Lib.LowerA64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region FrameRunM)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (StackOff limA pinA)
open Spike.Lib.A64.Rt (rS0)
open Spike.Lib.AllocReach (Reach)
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2 imms2Me IsNum SlotRepAt)

section G1CallC2HL

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
/-- The `j`th compiled block's code facts at the theorem's immediates. -/
local notation "FC" j:max d:max hd:max => fnCode2OfPMe hp h Λ j d hd

set_option hygiene false in
/-- The code predicate at the return address `ra`. -/
local notation "CD" ra:max => CdCLE OP (Spike.Lib.A64.PhRec.okPc LY0) (Spike.Lib.A64.PhRec.ph LY0) (LY0).lab
  (Int64.ofBitVec ra)

set_option hygiene false in
/-- The contexts with their records over the base context at the placement
`L`, `ls`. -/
local notation "CXS" => CxOkS (p := p) (lbl := L) (lsize := ls) (fnCode2OfPMe hp h Λ)
  (CxG2L h hp Dt J L ls) Bot

set_option hygiene false in
/-- The code facts' return address condition. -/
local notation "RAOK" ra:max => Spike.Lib.A64.PhRec.ph LY0 (Int64.ofBitVec ra).toBitVec.toNat =
  Spike.Lib.A64.PhRec.ph LY0 (Int64.ofBitVec ((LY0).lab Spike.Lib.A64.Rt.bareMC.e0 + 4).toBitVec).toBitVec.toNat

/-- **The plain calls held at the callee's return at a base context at
any frames and a reachable placement** (`CallC2H`, `main`'s held calls):
`callC2H_ofFW` at the caller's depth `D = -R.lo - frame` (at least the
room's slack, `Room2OwnStmt`), the call's blocks inside `W2` (`wCallG2L`),
the result's store at its held node (`callW2_hWH`), each callee's segment
as `callC2R_ofCxG2MSL`'s (`hIH`, `hS`, `calleePre2_callG2ML`,
`hcal_ofSO`). -/
theorem callC2H_ofCxG2MSL (hp : Scc.Lower.Accepted2 p = true) (hown : Room2OwnStmt h hp)
    (hrc : Room2CalleeStmt h hp) (hlc : Lim2CalleeStmt h hp) (hlok : LimOk2StmtL h hp)
    (htg : tgOkB OP = true) (hpc : ProCallG2L h hp)
    {Dt : State → Prop} {J : InvS} {L : WeakMem.AllocLabel → Option Nat} {ls : WeakMem.AllocLabel → Nat} {Bot : StkKey → List TermRun.Frame → Prop}
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) {R : Region} {F : MachineData → Prop}
    {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isaLSE2}
    (hcx : CxG2ML h hp Dt J L ls j R F fs fp ra tp G0 Ab) (hra : RAOK ra)
    (hS : ∀ (D : Int), R.lo = -((FC j d hd).cx.frame : Int) - D →
      ∀ (g : String) (q : CallG) (frm : TermRun.Frame) (F' : MachineData → Prop),
      FStable (R.callee (-((FC j d hd).cx.frame : Int)) (-D) 0) F' →
      CalleeF2 p L ls (FC j d hd).cx R F D fp ra (imms2Me Λ p) (TailAt2 p j) q frm F' →
      (∃ c x a e, G0 c ∧ TailAt2 p j (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
        CallTo p c q.cE frm) →
      (∃ pcB k, (FC j d hd).Bl ra pcB (Scc.Lower.Names.user g) k ∧ q.ra = (pcB + 4).toBitVec) →
      CallSite2F p L ls (FC j d hd).lcx (FC j d hd).cx (CD ra) ((FC j d hd).Bl ra) G0
        (TailAt2 p j) (_root_.Executable.labels (LY0).exe).label (imms2Me Λ p) (RetLk d.retTy) g q R D fp ra
        frm F' →
      ∀ (j' : Nat) (dg : Decl), (compiled2 p)[j']? = some dg → p.find? (·.name == g) = some dg →
      CxG2L h hp Dt J L ls j' (R.callee (-((FC j d hd).cx.frame : Int)) (-D) 0) F' (frm :: fs) q.fp q.ra tp
        (fun c => FrameRunM p (q.cE, frm :: fs) (c, frm :: fs)) Ab →
      CXS j' (R.callee (-((FC j d hd).cx.frame : Int)) (-D) 0) F' (frm :: fs) q.fp q.ra tp
        (fun c => FrameRunM p (q.cE, frm :: fs) (c, frm :: fs)) Ab)
    (hIH : ∀ g dg, CallIn2 (FC j d hd).lcx d.body g → p.find? (·.name == g) = some dg →
      ∃ j' : Nat, j' < j ∧ ∃ hd' : (compiled2 p)[j']? = some dg,
        FnSpecC2 (W2L J L ls) (KT) p L ls (MSL J L ls) (CXS j') (FC j' dg hd')) :
    CallC2H p L ls (FC j d hd).lcx (FC j d hd).cx (CD ra) ((FC j d hd).Bl ra) (LY0).exe
      (LY0).endPc R F (W2L J L ls) (KT) (MSL J L ls) fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j) Ab (RetLk d.retTy) := by
  have hc := hcx.1
  have hR := hc.hR
  have hl := hc.hl
  have hf := (FC j d hd).hf
  have h1 := (FC j d hd).h1
  have h16 := (FC j d hd).h16
  have hrow := hown j d hd 256 R.lo (hc.room d hd)
  have hlo : R.lo ≤ -((FC j d hd).cx.frame : Int) := by omega
  have he1 := (fnCode2OfPMe_spec hp h Λ j d hd).1
  obtain ⟨hWB, -, hWBl, hWC⟩ := wCallG2L h hp hown Dt J L ls j d hd R F fs fp ra tp G0 Ab hcx hra
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (imms2Me Λ p) (rS := rS0 (Ly))
  have hpN := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
  have hfit := Spike.Lib.A64.Rt.fitS_of_sub (Ly) hsub
  have hx : ∀ g, Spike.Lib.LowerCall.Callee (FC j d hd).lcx g →
      (Scc.Frontend.externs p).find? (·.1 == g) = none := by
    intro g hcl
    have := hcl.1
    rw [he1] at this
    exact this
  refine callC2H_ofFW hf h1 h16 (by rw [he1]) hc.hFS hR hc.hal
    (D := -R.lo - ((FC j d hd).cx.frame : Int)) (by omega) (by omega) (by omega) hc.hhi
    ((FC j d hd).hCd ra hra) ?_ hc.hG0 hWB hWBl hWC
    (fun x g is a ts e hT hcl => Spike.Lib.LowerNode.callee_nilIdx hp hd (hT d hd) (hx g hcl)) ?_
    (callW2_hWH (rd := IsNum)
      (G := Spike.Lib.A64.PhRec.GOf (Ly) (Spike.Lib.A64.PhRec.m0Of (Ly).Λ OP (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).secs))
      (ar := Spike.Lib.A64.Rt.arOf (Ly).Λ)
      (Jv := Spike.Lib.AllocReach.IN (Spike.Lib.A64.Rt.arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) (Dt := Dt)
      (lbl := L) (lsize := ls) (fp := fp) (ra := ra) (tp := tp)
      hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hf h1 h16 hc.hFS hR hc.hal hlo hc.hhi hl hc.hh
      hsub hfit hc.hFO hpN hc.hfp hc.hG0F hc.hG0 (fun _ _ h => h))
  · intro pc g k hb
    rw [(fnCode2OfPMe_spec hp h Λ j d hd).2.1] at hb
    exact cdOf_of_blC hI hb.1.1
  · intro g q frm F' hF' hCF hex hav hbl hsite
    obtain ⟨c, x, a, e, hc0, hT, hterm, hct⟩ := hex
    obtain ⟨x', f', a', e', dg, t', ws', hct', hfd, hev, hcE, hfr⟩ := hct
    rw [hterm] at hct'
    cases hct'
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcl, -⟩ := id hsite
    obtain ⟨j', -, hd', hs⟩ := hIH g dg ⟨x, [], a, [], e, hT d hd, hcl.1⟩ hfd
    have hgn : dg.name = g := by simpa using List.find?_some hfd
    have hint : dg.retTy = .int := Spike.Lib.LowerNode.callee_int hp hd (hT d hd) (hx g hcl) hfd
    have hex : ∃ c x a e, G0 c ∧ TailAt2 p j (.let_ x (.call g [] a []) e) ∧
        c.term = .let_ x (.call g [] a []) e ∧ CallTo p c q.cE frm :=
      ⟨c, x, a, e, hc0, hT, hterm, x, g, a, e, dg, t', ws', hterm, hfd, hev, hcE, hfr⟩
    have hDe : R.lo = -((FC j d hd).cx.frame : Int) - (-R.lo - ((FC j d hd).cx.frame : Int)) := by omega
    have hpre := calleePre2_callG2ML h hp hown hlok htg hd hcx hra hF' hex hav hbl hsite hd' hfd
      (hpc Dt J L ls j d hd R F fs fp ra tp G0 Ab hcx hra _ hDe g q frm F' hF' hCF hex hav hbl hsite j' dg hd' hfd)
      (hS _ hDe g q frm F' hF' hCF hex hbl hsite j' dg hd' hfd
        (CxG2ML.callG2 h hp hown hrc hlc hd hcx hDe hF' hCF hex hsite hd' hfd))
    subst hfr
    exact hcal_ofSO hgn hint rfl hpre hs

/-- **The plain calls held at the callee's return, the callee's records at
the bottom** (`callC2H_ofCxG2MSL`, the callee's context `CxOkS.bot`): at
bottom keys `Bot` holding at every frame pushed on `fs` (`main`'s held
calls at no frames, under a `Bot` admitting the call's frame). -/
theorem callC2H_ofCxG2ML (hp : Scc.Lower.Accepted2 p = true) (hown : Room2OwnStmt h hp)
    (hrc : Room2CalleeStmt h hp) (hlc : Lim2CalleeStmt h hp) (hlok : LimOk2StmtL h hp)
    (htg : tgOkB OP = true) (hpc : ProCallG2L h hp)
    {Dt : State → Prop} {J : InvS} {L : WeakMem.AllocLabel → Option Nat} {ls : WeakMem.AllocLabel → Nat} {Bot : StkKey → List TermRun.Frame → Prop}
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) {R : Region} {F : MachineData → Prop}
    {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isaLSE2}
    (hcx : CxG2ML h hp Dt J L ls j R F fs fp ra tp G0 Ab) (hra : RAOK ra)
    (hB : ∀ k f, Bot k (f :: fs))
    (hIH : ∀ g dg, CallIn2 (FC j d hd).lcx d.body g → p.find? (·.name == g) = some dg →
      ∃ j' : Nat, j' < j ∧ ∃ hd' : (compiled2 p)[j']? = some dg,
        FnSpecC2 (W2L J L ls) (KT) p L ls (MSL J L ls) (CXS j') (FC j' dg hd')) :
    CallC2H p L ls (FC j d hd).lcx (FC j d hd).cx (CD ra) ((FC j d hd).Bl ra) (LY0).exe
      (LY0).endPc R F (W2L J L ls) (KT) (MSL J L ls) fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j) Ab (RetLk d.retTy) :=
  callC2H_ofCxG2MSL h hp hown hrc hlc hlok htg hpc hd hcx hra
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc' => CxOkS.bot hc' (hB _ _)) hIH

end G1CallC2HL

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.callC2H_ofCxG2MSL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.callC2H_ofCxG2MSL

/-- info: 'Spike.Lib.LowerA64.callC2H_ofCxG2ML' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.callC2H_ofCxG2ML
