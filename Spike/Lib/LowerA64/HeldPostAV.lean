/-
**`main`'s held exits at the post control's value facts** (AArch64; the
twin of `Spike/Lib/LowerX64/HeldPostXV.lean`): `HeldPostA`'s producer at
`Q := MainCtlV` (`RtMainXVA`), the form `h0`'s `hU` consumes.

- `mainCtlV_held`: a held pair reading its value back, run to the return
  of `v`, has `MainCtlV` (`heldCtlV`), at any layout and labels;
- `mainCallWSF_ofPlaceOKHMV`: `mainCallWSF_ofPlaceOKHV` at
  `Q := MainCtlV Λv lbl` (with `Λv := lay2 Λ p`, `lbl := fun _ => none`
  the post `UPostRF p (fun _ => none) ∧ MainCtlV (lay2 Λ p) (fun _ => none)`);
  `mainCallWSF_ofPlaceOKHMVC` the same from `mainCallWSF_ofPlaceOKHVC`.
-/
import Spike.Lib.LowerA64.HeldPostA
import Spike.Lib.LowerA64.RtMainXVA

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64 (CodeAt)
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.Form (WordPl group)
open Spike.Lib.LowerNode
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.Flow.Ret0 (StackOff WcG CallerCells)
open Scc.Lower.Inv (regName)

/-- **`MainCtlV` at a held pair reading its value back** (`heldCtlV`). -/
theorem mainCtlV_held {p : Prog} {Λ : Scc.Sem.Layout} {lbl : Lbl} {c : Ctl} {fs : List TermRun.Frame}
    {v : BitVec 64} (hH : HeldTail c fs) (hrd : HeldRd c fs) (hU : UPostRF p lbl c fs v) :
    MainCtlV Λ lbl c fs v :=
  heldCtlV hH hrd hU

section Place

open Scc.Sem (Range ValRep)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.A64Consumer (K0)
open Spike.Lib.A64ConsumerS (InvS)
open Spike.Lib.A64.Rt (RuntimeLayout setupMC rtCodeOkS SetupArgs)
open Spike.Lib.A64.Flow.Ret0 (StackOff limA)

variable {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
  {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

local notation "LY" => RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))

set_option hygiene false in
/-- `W2` at the record's instance (`mainCallWSF_ofPlaceOKH`'s). -/
local notation "WW" => fun s c fs => W2 Λw (Spike.Lib.A64.PhRec.μ LY) p rd G (Spike.Lib.A64.PhRec.own LY) rS
  (Spike.Lib.A64.PhRec.Tk LY) ar J Dt (A64.WriteAb.Ab (LY).lab) lbl lsize s c fs

set_option hygiene false in
/-- `main`'s code at the return address `ra` (`fnCode2OfP`'s code predicate). -/
local notation "CD" ra:max => CdCLE OP (Spike.Lib.A64.PhRec.okPc LY) (Spike.Lib.A64.PhRec.ph LY) (LY).lab
  (Int64.ofBitVec ra)

/-- **`main`'s call after the setup block from the placement check at the
post control's value facts** (`mainCallWSF_ofPlaceOKHV` at
`Q := MainCtlV Λv lbl`, `mainCtlV_held`). -/
theorem mainCallWSF_ofPlaceOKHMV {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    {Λw : Scc.Sem.Layout} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {rS : Range} {ar : Arena} {J : InvS}
    {Dt : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ms : List TermRun.Frame → MemSide isaLSE2}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop}
    (hint : d.retTy = .int) (hok : Scc.Lower.heldRetOk d.body = true)
    (hlitP : ∀ x g is a ts k, TailOf (.let_ x (.call g is a ts) (.ret (.lit k))) d.body →
      g = "print" ∧ is.length = 1)
    {Λv : Scc.Sem.Layout} {sw : Nat}
    (hc : rtCodeOkS OP (setupMC sw) = true)
    {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int} {ZU : Int64} {tp : UInt64}
    (hfn : fn = (fnCode2OfP hp h j d hd).fn)
    (hL : PosOff OP (LY).lab ((LY).lab (proL (fnCode2OfP hp h j d hd).cx)))
    {ty : Ty} (hdT : d.argTy = .prod ty (.ptr .pub .void)) (hfd : p.find? (·.name == "main") = some d)
    (hna : (fnCode2OfP hp h j d hd).na = sw + 1) (hnl : Scc.Lower.shapeOf ty ≠ .loc)
    (hZU : ZU = Int64.ofInt (fnCode2OfP hp h j d hd).cx.frame)
    {c0 : Ctl} {x0 : BitVec 64}
    (hsT : Scc.Lower.simpleTy ty = true) (hw : Scc.Obj.valWords ty = some sw) (hsw : sw ≤ 7)
    (hc0t : c0.term = Scc.Sem.SrcSem.setupTerm) {tm : Ty} {meW : TermRun.Word}
    (hmeL : TermRun.lookupE c0.env "me" = some (tm, [meW])) (hmeN : IsNum meW)
    (hmeV : ValRep lbl meW.val x0.toNat)
    (hme : ∀ y t ws, TermRun.lookupE c0.env y = some (t, ws) → ∀ k (hk : k < ws.length),
      ValRep lbl ws[k].val x0.toNat)
    (hfo : ∀ c regs, SetupArgs (SPostC p lbl ty c0) sw x0 c regs → FrOk2 c [])
    (hmr : Scc.Sem.Kernel.mapped (K0 Λw) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λw.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hpN : ProgNoS ZBad p)
    (hpre : ∀ F' : MachineData → Prop, (R.callee (-Z.toInt) (-D) 0).OK →
      (R.callee (-Z.toInt) (-D) 0).base.toNat % 16 = 0 → FStable (R.callee (-Z.toInt) (-D) 0) F' →
      (∀ m, F' m → F m ∧ CallerCells R (-Z.toInt) (-D) 0 m) →
      ∀ g : WcG, g.ra = ((LY).lab (setupMC sw).sp1).toBitVec → g.tp = tp → ∀ cP : Ctl,
      FrOk2 cP [] →
      ∃ (G0 : Ctl → Prop) (Ab : FragS isaLSE2),
        CalleePre2R (WW) (Spike.Lib.A64.PhRec.K LY rS) p lbl lsize ms CxOk (fnCode2OfP hp h j d hd) rS
          (R.callee (-Z.toInt) (-D) 0) F' [] g.fp g.ra tp G0 Ab cP ∧
        CallC2 p lbl lsize (fnCode2OfP hp h j d hd).lcx (fnCode2OfP hp h j d hd).cx (CD g.ra)
          ((fnCode2OfP hp h j d hd).Bl g.ra) (LY).exe (LY).endPc (R.callee (-Z.toInt) (-D) 0) F' (WW)
          (Spike.Lib.A64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 (Scc.Lower.imms2Of p) (TailAt2 p j) Ab
          (RetLk d.retTy) ∧
        LaneC p lbl lsize (fnCode2OfP hp h j d hd).lcx (fnCode2OfP hp h j d hd).cx (CD g.ra)
          ((fnCode2OfP hp h j d hd).Bl g.ra) (LY).exe (LY).endPc (R.callee (-Z.toInt) (-D) 0) F' (WW)
          (Spike.Lib.A64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 (Scc.Lower.imms2Of p) (TailAt2 p j) Ab ∧
        NewBufC p lbl lsize (fnCode2OfP hp h j d hd).lcx (fnCode2OfP hp h j d hd).cx (CD g.ra)
          ((fnCode2OfP hp h j d hd).Bl g.ra) (LY).exe (LY).endPc (R.callee (-Z.toInt) (-D) 0) F' (WW)
          (Spike.Lib.A64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 (Scc.Lower.imms2Of p) (TailAt2 p j) Ab
          (RetLk d.retTy) ∧
        PrintCallC p lbl lsize (fnCode2OfP hp h j d hd).lcx (fnCode2OfP hp h j d hd).cx (CD g.ra)
          ((fnCode2OfP hp h j d hd).Bl g.ra) (LY).exe (LY).endPc (R.callee (-Z.toInt) (-D) 0) F' (WW)
          (Spike.Lib.A64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 (Scc.Lower.imms2Of p) (TailAt2 p j) Ab ∧
        CallC2H p lbl lsize (fnCode2OfP hp h j d hd).lcx (fnCode2OfP hp h j d hd).cx (CD g.ra)
          ((fnCode2OfP hp h j d hd).Bl g.ra) (LY).exe (LY).endPc (R.callee (-Z.toInt) (-D) 0) F' (WW)
          (Spike.Lib.A64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 (Scc.Lower.imms2Of p) (TailAt2 p j) Ab
          (RetLk d.retTy) ∧
        PrintCallCH p lbl lsize (fnCode2OfP hp h j d hd).lcx (fnCode2OfP hp h j d hd).cx (CD g.ra)
          ((fnCode2OfP hp h j d hd).Bl g.ra) (LY).exe (LY).endPc (R.callee (-Z.toInt) (-D) 0) F' (WW)
          (Spike.Lib.A64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 (Scc.Lower.imms2Of p) (TailAt2 p j) Ab ∧
        SegWS (WW) (Spike.Lib.A64.PhRec.K LY rS) p lbl ms Ab (fun _ _ _ => False)) :
    Spike.Lib.A64.Rt.MainCallWSF (WW) (Spike.Lib.A64.PhRec.K LY rS) p lbl ms (LY).exe (LY).endPc R F fn Z D ZU
      (SetupArgs (SPostC p lbl ty c0) sw x0) (fun c fs v => UPostRF p lbl c fs v ∧ MainCtlV Λv lbl c fs v)
      ((LY).lab (setupMC sw).sp1).toBitVec tp :=
  mainCallWSF_ofPlaceOKHV hp h hd hint hok hlitP (fun _ _ _ => mainCtlV_held) hc hfn hL hdT hfd hna hnl hZU hsT hw
    hsw hc0t hmeL hmeN hmeV hme hfo hmr hun hsub hfit hpN hpre

include hp in
/-- **`mainCallWSF_ofPlaceOKHMV` at any code facts of the check's output**
(`mainCallWSF_ofPlaceOKHVC` at `Q := MainCtlV Λv lbl`; e.g. `fnCode2OfPMe`). -/
theorem mainCallWSF_ofPlaceOKHMVC {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    {im : Expr → String → Nat → Option Nat}
    (c : FnCode2 (LY).exe (LY).prog (LY).endPc
      (fun ra => Spike.Lib.A64.PhRec.ph LY (Int64.ofBitVec ra).toBitVec.toNat =
        Spike.Lib.A64.PhRec.ph LY (Int64.ofBitVec ((LY).lab Spike.Lib.A64.Rt.bareMC.e0 + 4).toBitVec).toBitVec.toNat)
      (fun ra => CdCLE OP (Spike.Lib.A64.PhRec.okPc LY) (Spike.Lib.A64.PhRec.ph LY) (LY).lab
        (Int64.ofBitVec ra))
      im (TailAt2 p j) d)
    (hcPro : ProOK LY c) (hlcx : c.lcx = lcx2 p cfg.layout.obj d)
    {Λw : Scc.Sem.Layout} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {rS : Range} {ar : Arena} {J : InvS}
    {Dt : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ms : List TermRun.Frame → MemSide isaLSE2}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop}
    (hint : d.retTy = .int) (hok : Scc.Lower.heldRetOk d.body = true)
    (hlitP : ∀ x g is a ts k, TailOf (.let_ x (.call g is a ts) (.ret (.lit k))) d.body →
      g = "print" ∧ is.length = 1)
    {Λv : Scc.Sem.Layout} {sw : Nat}
    (hc : rtCodeOkS OP (setupMC sw) = true)
    {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int} {ZU : Int64} {tp : UInt64}
    (hfn : fn = c.fn)
    (hL : PosOff OP (LY).lab ((LY).lab (proL c.cx)))
    {ty : Ty} (hdT : d.argTy = .prod ty (.ptr .pub .void)) (hfd : p.find? (·.name == "main") = some d)
    (hna : c.na = sw + 1) (hnl : Scc.Lower.shapeOf ty ≠ .loc)
    (hZU : ZU = Int64.ofInt c.cx.frame)
    {c0 : Ctl} {x0 : BitVec 64}
    (hsT : Scc.Lower.simpleTy ty = true) (hw : Scc.Obj.valWords ty = some sw) (hsw : sw ≤ 7)
    (hc0t : c0.term = Scc.Sem.SrcSem.setupTerm) {tm : Ty} {meW : TermRun.Word}
    (hmeL : TermRun.lookupE c0.env "me" = some (tm, [meW])) (hmeN : IsNum meW)
    (hmeV : ValRep lbl meW.val x0.toNat)
    (hme : ∀ y t ws, TermRun.lookupE c0.env y = some (t, ws) → ∀ k (hk : k < ws.length),
      ValRep lbl ws[k].val x0.toNat)
    (hfo : ∀ c regs, SetupArgs (SPostC p lbl ty c0) sw x0 c regs → FrOk2 c [])
    (hmr : Scc.Sem.Kernel.mapped (K0 Λw) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λw.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hpN : ProgNoS ZBad p)
    (hpre : ∀ F' : MachineData → Prop, (R.callee (-Z.toInt) (-D) 0).OK →
      (R.callee (-Z.toInt) (-D) 0).base.toNat % 16 = 0 → FStable (R.callee (-Z.toInt) (-D) 0) F' →
      (∀ m, F' m → F m ∧ CallerCells R (-Z.toInt) (-D) 0 m) →
      ∀ g : WcG, g.ra = ((LY).lab (setupMC sw).sp1).toBitVec → g.tp = tp → ∀ cP : Ctl,
      FrOk2 cP [] →
      ∃ (G0 : Ctl → Prop) (Ab : FragS isaLSE2),
        CalleePre2R (WW) (Spike.Lib.A64.PhRec.K LY rS) p lbl lsize ms CxOk c rS
          (R.callee (-Z.toInt) (-D) 0) F' [] g.fp g.ra tp G0 Ab cP ∧
        CallC2 p lbl lsize c.lcx c.cx (CD g.ra)
          (c.Bl g.ra) (LY).exe (LY).endPc (R.callee (-Z.toInt) (-D) 0) F' (WW)
          (Spike.Lib.A64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 im (TailAt2 p j) Ab
          (RetLk d.retTy) ∧
        LaneC p lbl lsize c.lcx c.cx (CD g.ra)
          (c.Bl g.ra) (LY).exe (LY).endPc (R.callee (-Z.toInt) (-D) 0) F' (WW)
          (Spike.Lib.A64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 im (TailAt2 p j) Ab ∧
        NewBufC p lbl lsize c.lcx c.cx (CD g.ra)
          (c.Bl g.ra) (LY).exe (LY).endPc (R.callee (-Z.toInt) (-D) 0) F' (WW)
          (Spike.Lib.A64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 im (TailAt2 p j) Ab
          (RetLk d.retTy) ∧
        PrintCallC p lbl lsize c.lcx c.cx (CD g.ra)
          (c.Bl g.ra) (LY).exe (LY).endPc (R.callee (-Z.toInt) (-D) 0) F' (WW)
          (Spike.Lib.A64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 im (TailAt2 p j) Ab ∧
        CallC2H p lbl lsize c.lcx c.cx (CD g.ra)
          (c.Bl g.ra) (LY).exe (LY).endPc (R.callee (-Z.toInt) (-D) 0) F' (WW)
          (Spike.Lib.A64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 im (TailAt2 p j) Ab
          (RetLk d.retTy) ∧
        PrintCallCH p lbl lsize c.lcx c.cx (CD g.ra)
          (c.Bl g.ra) (LY).exe (LY).endPc (R.callee (-Z.toInt) (-D) 0) F' (WW)
          (Spike.Lib.A64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 im (TailAt2 p j) Ab ∧
        SegWS (WW) (Spike.Lib.A64.PhRec.K LY rS) p lbl ms Ab (fun _ _ _ => False)) :
    Spike.Lib.A64.Rt.MainCallWSF (WW) (Spike.Lib.A64.PhRec.K LY rS) p lbl ms (LY).exe (LY).endPc R F fn Z D ZU
      (SetupArgs (SPostC p lbl ty c0) sw x0) (fun c fs v => UPostRF p lbl c fs v ∧ MainCtlV Λv lbl c fs v)
      ((LY).lab (setupMC sw).sp1).toBitVec tp :=
  mainCallWSF_ofPlaceOKHVC hp h hd c hcPro hlcx hint hok hlitP (fun _ _ _ => mainCtlV_held) hc hfn hL hdT hfd hna
    hnl hZU hsT hw hsw hc0t hmeL hmeN hmeV hme hfo hmr hun hsub hfit hpN hpre

end Place

end Spike.Lib.LowerA64

/-- info: 'Spike.Lib.LowerA64.mainCtlV_held' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.mainCtlV_held

/-- info: 'Spike.Lib.LowerA64.mainCallWSF_ofPlaceOKHMV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.mainCallWSF_ofPlaceOKHMV

/-- info: 'Spike.Lib.LowerA64.mainCallWSF_ofPlaceOKHMVC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.mainCallWSF_ofPlaceOKHMVC
