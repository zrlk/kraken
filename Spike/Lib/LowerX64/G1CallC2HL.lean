/-
**The plain calls held at the callee's return at a base context at a
reachable placement** (x86-64; the twin of
`Spike/Lib/LowerA64/G1CallC2HL.lean`): `CallC2H`
(`Spike/Lib/LowerX64/HeldC.lean`) at the placement `L`, `ls` from
`callC2H_ofFW` (`Spike/Lib/LowerX64/G1CallHW.lean`), the call's blocks
inside `W2` (`wCallG2L`, `Spike/Lib/LowerX64/G1WCallG2L.lean`), the
result's store at its held node (`callW2_hWH`,
`Spike/Lib/LowerX64/G1CallHW2.lean`) and the callee as
`callC2R_ofCxG2MSL`'s (`Spike/Lib/LowerX64/G1CallC2RL.lean`).

- `callC2H_ofCxG2MSL`: `CallC2H` at a base context at any frames
  (`CxG2ML`), the callee's records from its base context;
  `callC2H_ofCxG2ML`: the callee's records at the bottom (`main`'s held
  calls).
-/
import Spike.Lib.LowerX64.G1CallC2RL
import Spike.Lib.LowerX64.G1WCallG2L
import Spike.Lib.LowerX64.G1CallHW
import Spike.Lib.LowerX64.G1CallHW2

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region FrameRunM)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Emit.X64 (i64 rel)
open Spike.Lib.X64.Flow.Ret0 (StackOff limA pinA tpOf)
open Spike.Lib.X64.Rt (rS0)
open Spike.Lib.AllocReach (Reach)
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2 imms2Me IsNum SlotRepAt)

section G1CallC2HL

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates. -/
local notation "LY0" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)

set_option hygiene false in
/-- `W2AtL` at `Closed2At`'s instance and the placement `L`, `ls`. -/
local notation "W2L" J:max L:max ls:max => W2AtL h (imms2Me Λ p) p IsNum (rS0 (Ly)) J Dt (fun _ => 0) L ls

set_option hygiene false in
/-- `MSAtL` at `Closed2At`'s instance (the nodes' abort `ab2`) and the
placement `L`, `ls`. -/
local notation "MSL" J:max L:max ls:max => MSAtL h (imms2Me Λ p) p IsNum J (ab2 p (Ly).lab) (fun _ => 0) L ls

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => Spike.Lib.X64.Flow.Ret0.TakeK ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The `j`th compiled block's code facts at the theorem's immediates. -/
local notation "FC" j:max d:max hd:max => fnCode2OfPMe hp h Λ j d hd

set_option hygiene false in
/-- The code predicate at the return address `ra`. -/
local notation "CD" ra:max => CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab
  (Int64.ofBitVec ra)

set_option hygiene false in
/-- The contexts with their records over the base context. -/
local notation "CXS" => CxOkS (p := p) (lbl := L) (lsize := ls) (fnCode2OfPMe hp h Λ)
  (CxG2L h hp Dt J L ls) Bot

set_option hygiene false in
/-- The code facts' return address condition. -/
local notation "RAOK" ra:max => Spike.Lib.X64.PhRec.ph LY0 (Int64.ofBitVec ra).toBitVec.toNat =
  Spike.Lib.X64.PhRec.ph LY0 ((LY0).lab raL).toBitVec.toNat

/-- **The plain calls held at the callee's return at a base context at
any frames and a reachable placement** (`CallC2H` in the rebased region
`rbR R`, `main`'s held calls): `callC2H_ofFW` at the caller's depth
`D = -(rbR R).lo - frame - 8` (at least the room's slack,
`Room2OwnStmt`), the call's blocks inside `W2` (`wCallG2L`), the result's
store at its held node (`callW2_hWH`), each callee's segment as
`callC2R_ofCxG2MSL`'s (`hIH`, `hS`, `calleePre2_callG2ML`, `hcal_ofSO`). -/
theorem callC2H_ofCxG2MSL (hp : Scc.Lower.Accepted2 p = true) (hown : Room2OwnStmt h hp)
    (hrc : Room2CalleeStmt h hp) (hlc : Lim2CalleeStmt h hp) (hlok : LimOk2StmtL h hp)
    (htg : tgOkB OP = true) (hpc : ProCallG2L h hp)
    {Dt : State → Prop} {J : InvS} {L : WeakMem.AllocLabel → Option Nat} {ls : WeakMem.AllocLabel → Nat} {Bot : StkKey → List TermRun.Frame → Prop}
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) {R : Region} {F : MachineData → Prop}
    {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isa}
    (hcx : CxG2ML h hp Dt J L ls j R F fs fp ra tp G0 Ab) (hra : RAOK ra)
    (hS : ∀ (D : Int), (rbR R).lo = -((FC j d hd).fr.size : Int) - 8 - D →
      ∀ (g : String) (q : CallG) (frm : TermRun.Frame) (F' : MachineData → Prop),
      FStable (calleeR (rbR R) (FC j d hd).fr.size D) F' →
      CalleeF2 p L ls (FC j d hd).fr (rbR R) F D fp ra (imms2Me Λ p) (TailAt2 p j) q frm F' →
      (∃ c x a e, G0 c ∧ TailAt2 p j (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
        CallTo p c q.cE frm) →
      (∃ pcB zc k, (FC j d hd).Bl ra pcB zc (Scc.Lower.Names.user g) k ∧ q.ra = (pcB + Int64.ofNat zc).toBitVec) →
      CallSite2F p L ls (FC j d hd).lcx (FC j d hd).fr (CD ra) ((FC j d hd).Bl ra) G0
        (TailAt2 p j) (_root_.Executable.labels (LY0).exe).label (imms2Me Λ p) (RetLk d.retTy) g q (rbR R) D fp ra
        frm F' →
      ∀ (j' : Nat) (dg : Decl), (compiled2 p)[j']? = some dg → p.find? (·.name == g) = some dg →
      CxG2L h hp Dt J L ls j' (calleeR (rbR R) (FC j d hd).fr.size D) F' (frm :: fs) q.fp q.ra tp
        (fun c => FrameRunM p (q.cE, frm :: fs) (c, frm :: fs)) Ab →
      CXS j' (calleeR (rbR R) (FC j d hd).fr.size D) F' (frm :: fs) q.fp q.ra tp
        (fun c => FrameRunM p (q.cE, frm :: fs) (c, frm :: fs)) Ab)
    (hIH : ∀ g dg, CallIn2 (FC j d hd).lcx d.body g → p.find? (·.name == g) = some dg →
      ∃ j' : Nat, j' < j ∧ ∃ hd' : (compiled2 p)[j']? = some dg,
        FnSpecC2 (W2L J L ls) (KT) p L ls (MSL J L ls) (CXS j') (FC j' dg hd')) :
    CallC2H p L ls (FC j d hd).lcx (FC j d hd).fr (CD ra) ((FC j d hd).Bl ra) (LY0).exe
      (LY0).endPc (rbR R) F (W2L J L ls) (KT) (MSL J L ls) fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j) Ab (RetLk d.retTy) := by
  have hc := hcx.1
  have hR := hc.hR
  have hl := hc.hl
  have hf := (FC j d hd).hf
  have h1 := (FC j d hd).h1
  have h16 := (FC j d hd).h16
  have hrow := hown j d hd 256 ((rbR R).lo - 8) (hc.room d hd)
  have he1 := (fnCode2OfPMe_spec hp h Λ j d hd).1
  obtain ⟨hWB, -, hWBl, hWC⟩ := wCallG2L h hp hown Dt J L ls j d hd R F fs fp ra tp G0 Ab hcx hra
  have hI0 := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms2Of p) (rS := rS0 (Ly))
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (imms2Me Λ p) (rS := rS0 (Ly))
  have hpN := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  have hsub := Spike.Lib.X64.Rt.rS0_sub (Ly)
  have hfit := Spike.Lib.X64.Rt.fitS_of_sub (Ly) hsub
  have hx : ∀ g, Spike.Lib.LowerCall.Callee (FC j d hd).lcx g →
      (Scc.Frontend.externs p).find? (·.1 == g) = none := by
    intro g hcl
    have := hcl.1
    rw [he1] at this
    exact this
  refine callC2H_ofFW hf h1 (by rw [he1]) hc.hFS hR
    (D := -(rbR R).lo - ((FC j d hd).fr.size : Int) - 8) (by omega) (by omega) (by omega) hc.hhi
    ((FC j d hd).hCd ra hra) ?_ hc.hG0 hWB hWBl hWC
    (fun x g is a ts e hT hcl => Spike.Lib.LowerNode.callee_nilIdx hp hd (hT d hd) (hx g hcl)) ?_
    (callW2_hWH (lbl := L) (lsize := ls) (fp := fp) (ra := ra) (tp := tp)
      hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hf h1 hc.hFS hR hc.hal (by omega) hc.hhi hl hc.hh
      hsub hfit hc.hFO hpN hc.hfp hc.hG0F hc.hG0 (fun _ _ h => h))
  · intro pc zc g k hb
    rw [(fnCode2OfPMe_spec hp h Λ j d hd).2.1] at hb
    exact cdOf_blC hI0.lays hI0.endOk pc zc g k (by rw [hI0.labOk]; exact hb.1.1)
  · intro g q frm F' hF' hCF hex hav hbl hsite
    obtain ⟨c, x, a, e, hc0, hT, hterm, hct⟩ := hex
    obtain ⟨x', f', a', e', dg, t', ws', hct', hfd, hev, hcE, hfr⟩ := hct
    rw [hterm] at hct'
    cases hct'
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcl, -⟩ := id hsite
    obtain ⟨j', -, hd', hs⟩ := hIH g dg ⟨x, [], a, [], e, hT d hd, hcl.1⟩ hfd
    have hgn : dg.name = g := by simpa using List.find?_some hfd
    have hint : dg.retTy = .int := Spike.Lib.LowerNode.callee_int hp hd (hT d hd) (hx g hcl) hfd
    have hex : ∃ c x a e, G0 c ∧ TailAt2 p j (.let_ x (.call g [] a []) e) ∧
        c.term = .let_ x (.call g [] a []) e ∧ CallTo p c q.cE frm :=
      ⟨c, x, a, e, hc0, hT, hterm, x, g, a, e, dg, t', ws', hterm, hfd, hev, hcE, hfr⟩
    have hDe : (rbR R).lo = -((FC j d hd).fr.size : Int) - 8 -
        (-(rbR R).lo - ((FC j d hd).fr.size : Int) - 8) := by omega
    have hpre := calleePre2_callG2ML h hp hown hlok htg hd hcx hra hDe hF' hex hav hbl hsite hd' hfd
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
    {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isa}
    (hcx : CxG2ML h hp Dt J L ls j R F fs fp ra tp G0 Ab) (hra : RAOK ra)
    (hB : ∀ k f, Bot k (f :: fs))
    (hIH : ∀ g dg, CallIn2 (FC j d hd).lcx d.body g → p.find? (·.name == g) = some dg →
      ∃ j' : Nat, j' < j ∧ ∃ hd' : (compiled2 p)[j']? = some dg,
        FnSpecC2 (W2L J L ls) (KT) p L ls (MSL J L ls) (CXS j') (FC j' dg hd')) :
    CallC2H p L ls (FC j d hd).lcx (FC j d hd).fr (CD ra) ((FC j d hd).Bl ra) (LY0).exe
      (LY0).endPc (rbR R) F (W2L J L ls) (KT) (MSL J L ls) fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j) Ab (RetLk d.retTy) :=
  callC2H_ofCxG2MSL h hp hown hrc hlc hlok htg hpc hd hcx hra
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc' => CxOkS.bot hc' (hB _ _)) hIH

end G1CallC2HL

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.callC2H_ofCxG2MSL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.callC2H_ofCxG2MSL

/-- info: 'Spike.Lib.LowerX64.callC2H_ofCxG2ML' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.callC2H_ofCxG2ML
