/-
**`main`'s held exits at the post control's value facts** (x86-64):
`HeldPostX`'s producer at `Q := MainCtlV` (`RtMainXV`), the form `h0`'s
`hU` consumes.

- `mainCtlV_held`: a held pair reading its value back, run to the return
  of `v`, has `MainCtlV` (`heldCtlV`), at any layout and labels;
- `mainCallWSF_ofPlaceOKHMV`: `mainCallWSF_ofPlaceOKHV` at
  `Q := MainCtlV Λv lbl` (with `Λv := lay2 Λ p`, `lbl := fun _ => none`
  the post `UPostRF p (fun _ => none) ∧ MainCtlV (lay2 Λ p) (fun _ => none)`);
  `mainCallWSF_ofPlaceOKHMVC` the same from `mainCallWSF_ofPlaceOKHVC`.
-/
import Spike.Lib.LowerX64.HeldPostX
import Spike.Lib.LowerX64.RtMainXV

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64
open Scc.Emit.X64 (Item)
open Scc.Lower.InvX64
open Spike.Lib.Form (WordPl group)
open Spike.Lib.LowerNode
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.Flow.Ret0 (StackOff WcG CallerCells)
open Scc.Lower.Inv (atomV regName)
open Spike.Lib.LowerShape (lowerC2 Res2 lowerC2_call_inv walk2_tail_call walk2_tail_print lowerC2_ret_inv
  lowerC2_fv)

/-- **`MainCtlV` at a held pair reading its value back** (`heldCtlV`). -/
theorem mainCtlV_held {p : Prog} {Λ : Scc.Sem.Layout} {lbl : Lbl} {c : Ctl} {fs : List TermRun.Frame}
    {v : BitVec 64} (hH : HeldTail c fs) (hrd : HeldRd c fs) (hU : UPostRF p lbl c fs v) :
    MainCtlV Λ lbl c fs v :=
  heldCtlV hH hrd hU

section Place

open Scc.Sem (Range ValRep)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64Consumer (K0)
open Spike.Lib.X64ConsumerS (InvS)
open Spike.Lib.X64.Rt (RuntimeLayout setupMC rtCodeOkS SetupArgs)
open Spike.Lib.X64.Flow.Ret0 (StackOff limA)

variable {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
  {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

local notation "LY" => RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)

/-- **`main`'s call after the setup block from the placement check at the
post control's value facts** (`mainCallWSF_ofPlaceOKHV` at
`Q := MainCtlV Λv lbl`, `mainCtlV_held`). -/
theorem mainCallWSF_ofPlaceOKHMV {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    {Λw : Scc.Sem.Layout} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {rS : Range} {ar : Arena} {J : InvS}
    {Dt : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ms : List TermRun.Frame → MemSide isa}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    (hint : d.retTy = .int) (hok : Scc.Lower.heldRetOk d.body = true)
    (hlitP : ∀ x g is a ts k, TailOf (.let_ x (.call g is a ts) (.ret (.lit k))) d.body →
      g = "print" ∧ is.length = 1)
    {Λv : Scc.Sem.Layout} {sw : Nat}
    (hc : rtCodeOkS OP (setupMC sw) = true)
    {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int} {ZU : Int64} {tp : UInt64}
    (hfn : fn = (fnCode2OfP hp h j d hd).fn)
    (hL : PosOff OP (LY).lab ((LY).lab (proL (fnCode2OfP hp h j d hd).fr)))
    {ty : Ty} {c0 : Ctl} {x0 : BitVec 64}
    (hsT : Scc.Lower.simpleTy ty = true) (hw : Scc.Obj.valWords ty = some sw) (hsw : sw ≤ 5)
    (hme : ∀ y t ws, TermRun.lookupE c0.env y = some (t, ws) → ∀ k (hk : k < ws.length),
      ValRep lbl ws[k].val x0.toNat)
    (hE : ∀ x f a e, c0.term = .let_ x (.call f [] a []) e → ∀ b, e ≠ .ret b)
    (hfo : ∀ c regs, SetupArgs (SPostC p lbl ty c0) sw x0 c regs → FrOk2 c [])
    (hmr : Scc.Sem.Kernel.mapped (K0 Λw) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λw.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hpN : ProgNoS ZBad p)
    (hpre : ∀ F' : MachineData → Prop, (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).OK →
      FStable (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' →
      (∀ m, F' m → F m ∧ CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m) →
      ∀ g : WcG, g.ra = ((LY).lab (setupMC sw).sp1).toBitVec → g.tp = tp →
      (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).base = g.sp → ∀ cP : Ctl,
      FrOk2 cP [] →
      ∃ (G0 : Ctl → Prop) (Ab : FragS isa) (c0' : Ctl),
        CalleePre2R (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) p lbl lsize ms CxOk (fnCode2OfP hp h j d hd) rS
          (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' [] g.fp g.ra tp G0 Ab
          (Spike.Lib.X64.Rt.uNM (_root_.Executable.labels (LY).exe).label (ms []) F fn ZU
            (fun c rs => SetupArgs (SPostC p lbl ty c0) sw x0 c rs ∧ c = cP) g).J c0' ∧
        CallC2 p lbl lsize (fnCode2OfP hp h j d hd).lcx (fnCode2OfP hp h j d hd).fr
          (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab (Int64.ofBitVec g.ra))
          ((fnCode2OfP hp h j d hd).Bl g.ra) (LY).exe (LY).endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F'
          (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 (Scc.Lower.imms2Of p) (TailAt2 p j) Ab
          (RetLk d.retTy) ∧
        LaneC p lbl lsize (fnCode2OfP hp h j d hd).lcx (fnCode2OfP hp h j d hd).fr
          (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab (Int64.ofBitVec g.ra))
          ((fnCode2OfP hp h j d hd).Bl g.ra) (LY).exe (LY).endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F'
          (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 (Scc.Lower.imms2Of p) (TailAt2 p j) Ab ∧
        NewBufC p lbl lsize (fnCode2OfP hp h j d hd).lcx (fnCode2OfP hp h j d hd).fr
          (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab (Int64.ofBitVec g.ra))
          ((fnCode2OfP hp h j d hd).Bl g.ra) (LY).exe (LY).endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F'
          (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 (Scc.Lower.imms2Of p) (TailAt2 p j) Ab
          (RetLk d.retTy) ∧
        PrintCallC p lbl lsize (fnCode2OfP hp h j d hd).lcx (fnCode2OfP hp h j d hd).fr
          (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab (Int64.ofBitVec g.ra))
          ((fnCode2OfP hp h j d hd).Bl g.ra) (LY).exe (LY).endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F'
          (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 (Scc.Lower.imms2Of p) (TailAt2 p j) Ab ∧
        CallC2H p lbl lsize (fnCode2OfP hp h j d hd).lcx (fnCode2OfP hp h j d hd).fr
          (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab (Int64.ofBitVec g.ra))
          ((fnCode2OfP hp h j d hd).Bl g.ra) (LY).exe (LY).endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F'
          (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 (Scc.Lower.imms2Of p) (TailAt2 p j) Ab
          (RetLk d.retTy) ∧
        PrintCallCH p lbl lsize (fnCode2OfP hp h j d hd).lcx (fnCode2OfP hp h j d hd).fr
          (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab (Int64.ofBitVec g.ra))
          ((fnCode2OfP hp h j d hd).Bl g.ra) (LY).exe (LY).endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F'
          (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 (Scc.Lower.imms2Of p) (TailAt2 p j) Ab ∧
        SegWS (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) p lbl ms Ab (fun _ _ _ => False)) :
    Spike.Lib.X64.Rt.MainCallWSF
      (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
        (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
      (Spike.Lib.X64.PhRec.K LY rS) p lbl ms (LY).exe (LY).endPc R F fn Z D ZU
      (SetupArgs (SPostC p lbl ty c0) sw x0) (fun c fs v => UPostRF p lbl c fs v ∧ MainCtlV Λv lbl c fs v)
      ((LY).lab (setupMC sw).sp1).toBitVec tp :=
  mainCallWSF_ofPlaceOKHV hp h hd hint hok hlitP (fun _ _ _ => mainCtlV_held) hc hfn hL hsT hw hsw hme hE hfo hmr hun
    hsub hfit hpN hpre

include hp in
/-- **`mainCallWSF_ofPlaceOKHMV` at any code facts of the check's output**
(`mainCallWSF_ofPlaceOKHVC` at `Q := MainCtlV Λv lbl`; e.g. `fnCode2OfPMe`). -/
theorem mainCallWSF_ofPlaceOKHMVC {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    {im : Expr → String → Nat → Option Nat}
    (c : FnCode2 (LY).exe (LY).prog (LY).endPc
      (fun ra => Spike.Lib.X64.PhRec.ph LY (Int64.ofBitVec ra).toBitVec.toNat =
        Spike.Lib.X64.PhRec.ph LY ((LY).lab raL).toBitVec.toNat)
      (fun ra => CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab
        (Int64.ofBitVec ra))
      im (TailAt2 p j) d)
    (hcPro : ProOK LY d c) (hlcx : c.lcx = lcx2 p cfg.layout.obj d)
    {Λw : Scc.Sem.Layout} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {rS : Range} {ar : Arena} {J : InvS}
    {Dt : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ms : List TermRun.Frame → MemSide isa}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    (hint : d.retTy = .int) (hok : Scc.Lower.heldRetOk d.body = true)
    (hlitP : ∀ x g is a ts k, TailOf (.let_ x (.call g is a ts) (.ret (.lit k))) d.body →
      g = "print" ∧ is.length = 1)
    {Λv : Scc.Sem.Layout} {sw : Nat}
    (hc : rtCodeOkS OP (setupMC sw) = true)
    {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int} {ZU : Int64} {tp : UInt64}
    (hfn : fn = c.fn)
    (hL : PosOff OP (LY).lab ((LY).lab (proL c.fr)))
    {ty : Ty} {c0 : Ctl} {x0 : BitVec 64}
    (hsT : Scc.Lower.simpleTy ty = true) (hw : Scc.Obj.valWords ty = some sw) (hsw : sw ≤ 5)
    (hme : ∀ y t ws, TermRun.lookupE c0.env y = some (t, ws) → ∀ k (hk : k < ws.length),
      ValRep lbl ws[k].val x0.toNat)
    (hE : ∀ x f a e, c0.term = .let_ x (.call f [] a []) e → ∀ b, e ≠ .ret b)
    (hfo : ∀ c regs, SetupArgs (SPostC p lbl ty c0) sw x0 c regs → FrOk2 c [])
    (hmr : Scc.Sem.Kernel.mapped (K0 Λw) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λw.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hpN : ProgNoS ZBad p)
    (hpre : ∀ F' : MachineData → Prop, (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).OK →
      FStable (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' →
      (∀ m, F' m → F m ∧ CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m) →
      ∀ g : WcG, g.ra = ((LY).lab (setupMC sw).sp1).toBitVec → g.tp = tp →
      (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).base = g.sp → ∀ cP : Ctl,
      FrOk2 cP [] →
      ∃ (G0 : Ctl → Prop) (Ab : FragS isa) (c0' : Ctl),
        CalleePre2R (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) p lbl lsize ms CxOk c rS
          (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' [] g.fp g.ra tp G0 Ab
          (Spike.Lib.X64.Rt.uNM (_root_.Executable.labels (LY).exe).label (ms []) F fn ZU
            (fun c rs => SetupArgs (SPostC p lbl ty c0) sw x0 c rs ∧ c = cP) g).J c0' ∧
        CallC2 p lbl lsize c.lcx c.fr
          (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab (Int64.ofBitVec g.ra))
          (c.Bl g.ra) (LY).exe (LY).endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F'
          (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 im (TailAt2 p j) Ab
          (RetLk d.retTy) ∧
        LaneC p lbl lsize c.lcx c.fr
          (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab (Int64.ofBitVec g.ra))
          (c.Bl g.ra) (LY).exe (LY).endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F'
          (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 im (TailAt2 p j) Ab ∧
        NewBufC p lbl lsize c.lcx c.fr
          (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab (Int64.ofBitVec g.ra))
          (c.Bl g.ra) (LY).exe (LY).endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F'
          (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 im (TailAt2 p j) Ab
          (RetLk d.retTy) ∧
        PrintCallC p lbl lsize c.lcx c.fr
          (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab (Int64.ofBitVec g.ra))
          (c.Bl g.ra) (LY).exe (LY).endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F'
          (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 im (TailAt2 p j) Ab ∧
        CallC2H p lbl lsize c.lcx c.fr
          (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab (Int64.ofBitVec g.ra))
          (c.Bl g.ra) (LY).exe (LY).endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F'
          (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 im (TailAt2 p j) Ab
          (RetLk d.retTy) ∧
        PrintCallCH p lbl lsize c.lcx c.fr
          (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab (Int64.ofBitVec g.ra))
          (c.Bl g.ra) (LY).exe (LY).endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F'
          (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 im (TailAt2 p j) Ab ∧
        SegWS (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) p lbl ms Ab (fun _ _ _ => False)) :
    Spike.Lib.X64.Rt.MainCallWSF
      (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
        (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
      (Spike.Lib.X64.PhRec.K LY rS) p lbl ms (LY).exe (LY).endPc R F fn Z D ZU
      (SetupArgs (SPostC p lbl ty c0) sw x0) (fun c fs v => UPostRF p lbl c fs v ∧ MainCtlV Λv lbl c fs v)
      ((LY).lab (setupMC sw).sp1).toBitVec tp :=
  mainCallWSF_ofPlaceOKHVC hp h hd c hcPro hlcx hint hok hlitP (fun _ _ _ => mainCtlV_held) hc hfn hL hsT hw hsw
    hme hE hfo hmr hun hsub hfit hpN hpre

end Place

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.mainCtlV_held' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainCtlV_held

/-- info: 'Spike.Lib.LowerX64.mainCallWSF_ofPlaceOKHMV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainCallWSF_ofPlaceOKHMV

/-- info: 'Spike.Lib.LowerX64.mainCallWSF_ofPlaceOKHMVC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainCallWSF_ofPlaceOKHMVC
