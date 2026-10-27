/-
**`main` with its paths held, from its label to the exits at pending
frames** (AArch64; the twin of `Spike/Lib/LowerX64/MainHeldX.lean`): a
compiled block whose paths all end in a held return tail (`heldRetOk`),
from its label at a context's premises (`CalleePre2`) to `ExitC2SLF`, and
`main`'s call after the setup block from it (`MainCallWSF` at `UPostRF`).

- `CalleePre2.segH`: the prologue (`proSeg2`) then the body's segment
  (`body2_segS_ofXH`) at the context's construct premises and a
  `HeldTailCX` instance (e.g. `heldTailCX_of`);
- `mainCallWSF_ofHeld`: `MainCallWSF … UPostRF` from `CalleePre2.segH` at
  every frame condition, ghost and entry control of the interface
  (`mainCallWSF_of_exitC2SLF` under `MainCallWSF.ofCtl`);
- `mainCallWSF_ofPlaceOKH`: `mainCallWSF_ofHeld` at `main`'s compiled block
  from the placement check (`fnCode2OfP`): the return address, the prologue
  and its edge (`raOk_main`, `hpro_main_ofPlaceOK`, `proEdge2_ofUNM`), the held tails by
  `heldTailCX_of` (the instance `instOk_ofPlaceOK`, `main`'s code
  `CdCLE.toCdCL`, `scc_rt_main`'s return point off the write abort by
  `posOff_mainRetS`);
- `mainCallWSF_ofPlaceOKHC`: the same at any code facts `c` of the check's
  output with `fnCode2OfP`'s return-address phase and code predicate and
  any immediates (e.g. `fnCode2OfPMe`), its prologue's facts given;
  `mainCallWSF_ofPlaceOKH` is it at `fnCode2OfP`.

Where AArch64 differs from x86-64: no return address between the caller's
frame and the callee's entry `sp`, so no rebased region (`rbR`): the
constructs and the held tails are in the callee's region
`R.callee (-Z.toInt) (-D) 0` itself, 16-aligned.
-/
import Spike.Lib.LowerA64.MainCallOf
import Spike.Lib.LowerA64.MainTailP
import Spike.Lib.LowerA64.MainRetPos

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.LowerNode
open Spike.Lib.A64.Flow.Ret0 (WcG CallerCells)

section Held

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive}
  {endPc : Int64} {W : FragS isaLSE2} {K : State → State → Prop}

/-- **A held function's segment at a context** (`CalleePre2.seg` for a
body whose paths all end in a held return tail, `hok`): the prologue
(`proSeg2`), then the body's segment from its entry node
(`body2_segS_ofXH`) at the context's construct premises (`hcall`, `hlane`,
`hbuf`, `hprint`) and the held tails' (`hheld`), to the exits held at
pending frames (`ExitC2SLF`). -/
theorem CalleePre2.segH {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop}
    {c : FnCode2 exe prog endPc RaOk Cd i T d} {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame}
    {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isaLSE2} {J : AS → Ctl → Prop} {c0 : Ctl}
    (h : CalleePre2 W K p lbl lsize ms CxOk c R F fs fp ra tp G0 Ab J c0)
    (hcall : CallC2 p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i T Ab
      (RetLk d.retTy))
    (hlane : LaneC p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hbuf : NewBufC p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i T Ab
      (RetLk d.retTy))
    (hprint : PrintCallC p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hheld : HeldTailCX p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i T
      (fun _ => True) (RetLk d.retTy) (fun c0 => ExitC2SLF p lbl exe endPc R F fp ra tp c0 fs d.retTy Ab))
    (hok : Scc.Lower.heldRetOk d.body = true) (hT : ∀ t, T t → ContNR t) :
    SegWS W K p lbl ms ((At exe endPc R F ⟨(_root_.Executable.labels exe).label c.fn, ⟨0, []⟩, J⟩).at fs)
      (ExitC2SLF p lbl exe endPc R F fp ra tp c0 fs d.retTy Ab) := by
  have hCd := c.hCd ra h.hra
  have hW₀ : ∀ s c', (fun s c => W s c fs) s c' → W s c' fs := fun _ _ h => h
  exact (SegWS.liftS fs (proSeg2 c h.hF h.hR h.hal h.hlo h.hhi h.hpro h.hedge) hW₀).seq
    (body2_segS_ofXH h.hG0 c.hfrm (fun _ _ hr => ExitC2SLF.trans hr) (fun _ _ _ _ h => .inr h) hcall hlane hbuf
      hprint (addC2_ofQ (Q := fun t => fs = [] → ∀ a, t ≠ .ret a)
        c.hf c.h1 c.h16 h.hF h.hR h.hal h.hlo h.hhi hCd hW₀
        h.hW h.hWp (ContNR.qAdd hT) h.hab c.lcx tp)
      (subC2_ofQ (Q := fun t => fs = [] → ∀ a, t ≠ .ret a)
        c.hf c.h1 c.h16 h.hF h.hR h.hal h.hlo h.hhi hCd hW₀
        h.hW h.hWp (ContNR.qSub hT) c.lcx tp)
      (pureMv2_of c.lcx tp) (splitMv2_of c.lcx tp) (unpackMv2_of c.lcx tp)
      (ifC2_ofQ (Q := fun t => fs = [] → ∀ a, t ≠ .ret a)
        c.hf c.h1 c.h16 h.hF h.hR h.hal h.hlo h.hhi hCd hW₀
        h.hW (ContNR.qIf hT) c.lcx tp) hheld
      d.body c.env 0 "entry" 0 c.r 0 _ c.lits [] [] c.hr c.hfr (c.hcode ra h.hra) (c.hbl ra h.hra)
      (fun q hq => have h := c.hWk q hq; ⟨h.1, h.2.1, trivial, h.2.2⟩)
      (fun q hq => ⟨c.hlit q hq, c.hcallL q hq, fun a ha => c.hretL a q.2 (by rw [← ha]; exact hq)⟩)
      c.hcnt c.hxchg hok c0 h.hg0)

/-- **The user `main` after the setup block, its paths held**
(`main`'s call for a body whose paths all end in a held return tail,
`hok`): at every frame condition `F'`, ghost `g` and entry control
`cP` of the interface, a context's premises at the entry invariant of
`uNM` (`CalleePre2`), the construct premises in the callee's region and the
held tails' (`HeldTailCX`, e.g. `heldTailCX_of`), its aborts never ending;
`main`'s return type `int` (`hint`). -/
theorem mainCallWSF_ofHeld {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop}
    (c : FnCode2 exe prog endPc RaOk Cd i T d) (hint : d.retTy = .int) (hok : Scc.Lower.heldRetOk d.body = true)
    (hT : ∀ t, T t → ContNR t)
    {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int} {ZU : Int64}
    {Pre : Ctl → Reg64s → Prop} {ra : BitVec 64} {tp : UInt64} (hfn : fn = c.fn)
    (hpre : ∀ F' : MachineData → Prop, (R.callee (-Z.toInt) (-D) 0).OK →
      (R.callee (-Z.toInt) (-D) 0).base.toNat % 16 = 0 → FStable (R.callee (-Z.toInt) (-D) 0) F' →
      (∀ m, F' m → F m ∧ CallerCells R (-Z.toInt) (-D) 0 m) →
      ∀ g : WcG, g.ra = ra → g.tp = tp → ∀ cP : Ctl,
      (∃ rs, Pre cP rs) →
      ∃ (G0 : Ctl → Prop) (Ab : FragS isaLSE2) (c0' : Ctl),
        CalleePre2 W K p lbl lsize ms CxOk c (R.callee (-Z.toInt) (-D) 0) F' [] g.fp g.ra tp G0 Ab
          (Spike.Lib.A64.Rt.uNM (_root_.Executable.labels exe).label (ms []) F exe endPc fn ZU
            (fun c rs => Pre c rs ∧ c = cP) g).J c0' ∧
        CallC2 p lbl lsize c.lcx c.cx (Cd g.ra) (c.Bl g.ra) exe endPc (R.callee (-Z.toInt) (-D) 0) F' W K ms
          g.fp g.ra tp [] G0 i T Ab (RetLk d.retTy) ∧
        LaneC p lbl lsize c.lcx c.cx (Cd g.ra) (c.Bl g.ra) exe endPc (R.callee (-Z.toInt) (-D) 0) F' W K ms
          g.fp g.ra tp [] G0 i T Ab ∧
        NewBufC p lbl lsize c.lcx c.cx (Cd g.ra) (c.Bl g.ra) exe endPc (R.callee (-Z.toInt) (-D) 0) F' W K ms
          g.fp g.ra tp [] G0 i T Ab (RetLk d.retTy) ∧
        PrintCallC p lbl lsize c.lcx c.cx (Cd g.ra) (c.Bl g.ra) exe endPc (R.callee (-Z.toInt) (-D) 0) F' W K ms
          g.fp g.ra tp [] G0 i T Ab ∧
        HeldTailCX p lbl lsize c.lcx c.cx (Cd g.ra) (c.Bl g.ra) exe endPc (R.callee (-Z.toInt) (-D) 0) F' W K ms
          g.fp g.ra tp [] G0 i T (fun _ => True) (RetLk d.retTy)
          (fun c0 => ExitC2SLF p lbl exe endPc (R.callee (-Z.toInt) (-D) 0) F' g.fp g.ra tp c0 [] d.retTy Ab) ∧
        SegWS W K p lbl ms Ab (fun _ _ _ => False)) :
    Spike.Lib.A64.Rt.MainCallWSF W K p lbl ms exe endPc R F fn Z D ZU Pre (UPostRF p lbl) ra tp :=
  MainCallWSF.ofCtl fun cP hcP => mainCallWSF_of_exitC2SLF fun F' hR0 hal hF' hFF g hra htp => by
    obtain ⟨G0, Ab, c0', hP, hcall, hlane, hbuf, hprint, hheld, hAb⟩ := hpre F' hR0 hal hF' hFF g hra htp cP hcP
    have H := hP.segH hcall hlane hbuf hprint hheld hok hT
    rw [hint] at H
    subst hfn
    exact ⟨Ab, c0', H, hAb⟩

end Held

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

/-- **`main`'s call after the setup block from the placement check, its
paths held, at any code facts of the check's output** (the body of
`mainCallWSF_ofPlaceOKH` at `c` with the return address's phase and
`main`'s code as `fnCode2OfP`'s, any immediates `im`, e.g.
`fnCode2OfPMe`'s `imms2Me`): its prologue's facts `hcPro`; the rest as
`mainCallWSF_ofPlaceOKH`. -/
theorem mainCallWSF_ofPlaceOKHC {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    {im : Expr → String → Nat → Option Nat}
    (c : FnCode2 (LY).exe (LY).prog (LY).endPc
      (fun ra => Spike.Lib.A64.PhRec.ph LY (Int64.ofBitVec ra).toBitVec.toNat =
        Spike.Lib.A64.PhRec.ph LY (Int64.ofBitVec ((LY).lab Spike.Lib.A64.Rt.bareMC.e0 + 4).toBitVec).toBitVec.toNat)
      (fun ra => CdCLE OP (Spike.Lib.A64.PhRec.okPc LY) (Spike.Lib.A64.PhRec.ph LY) (LY).lab
        (Int64.ofBitVec ra))
      im (TailAt2 p j) d)
    (hcPro : ProOK LY c)
    {Λw : Scc.Sem.Layout} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {rS : Range} {ar : Arena} {J : InvS}
    {Dt : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ms : List TermRun.Frame → MemSide isaLSE2}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop}
    (hint : d.retTy = .int) (hok : Scc.Lower.heldRetOk d.body = true) {sw : Nat}
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
      (SetupArgs (SPostC p lbl ty c0) sw x0) (UPostRF p lbl) ((LY).lab (setupMC sw).sp1).toBitVec tp := by
  refine mainCallWSF_ofHeld (lsize := lsize) (CxOk := CxOk) c hint hok
    (fun _ ht => contNR_tailAt2 hd hok ht) hfn
    fun F' hR0 hal hF' hFF g hra htp cP hcP => ?_
  obtain ⟨G0, Ab, hP, hcall, hlane, hbuf, hprint, hcallH, hprintH, hAb⟩ :=
    hpre F' hR0 hal hF' hFF g hra htp cP (hfo _ _ hcP.choose_spec)
  refine ⟨G0, Ab, cP, hP.toPre ?_ ?_ ?_, hcall, hlane, hbuf, hprint, ?_, hAb⟩
  · rw [hra]; exact RaMain.raOk_main h _ hc
  · exact hpro_main_ofPlaceOK h c hcPro hL (fun _ _ h => h)
      hP.hR hP.hal hP.hlo hP.hhi hP.hl hP.hh (htp ▸ hmr)
      (fun m hm => htp ▸ hun m (hFF m hm).1) hsub hfit hP.hFO hpN
      (fun c regs hc' => hPl_setupArgs hsT hw hsw hme Λw c regs hc'.1)
      (fun c regs hc' => hnr_setupArgs (hE_setupTerm hc0t) c regs hc'.1) (fun c regs hc' => hfo c regs hc'.1)
  · have he := proEdge2_ofUNM (lsize := lsize) c hdT hfd hna (by omega) hnl hc0t hmeL
      hmeN hmeV (g := g) (lab := (_root_.Executable.labels (LY).exe).label) (ms0 := ms []) (ms1 := ms [])
      (F := F) (F' := F') (fn := fn) hZU (fun _ _ h => h)
      (fun m hm => (hFF m hm).1) (cP := cP) (fun _ _ h => h)
    rwa [htp] at he
  exact heldTailCX_of hpN (Spike.Lib.A64.PhRec.instOk_ofPlaceOK h _) (printIn_of_placeOKAt h)
    (abortIn_of_placeOKAt h) c.hf c.h1
    c.h16 hP.hF hP.hR hP.hal hP.hlo hP.hhi hP.hl hP.hh hsub hfit hP.hFO
    (fun _ _ h => CdCLE.toCdCL h)
    (by rw [hra]; exact posOff_mainRetS (Spike.Lib.A64.Rt.mainSIn_of_okS hc))
    c.hfrm hcallH hprintH (fun _ _ _ h => h)

/-- **`main`'s call after the setup block from the placement check, its
paths held** (`mainCallWSF_ofHeld` at `c := fnCode2OfP … j d hd`): the
return address's phase (`raOk_main`), the prologue inside `W2`
(`hpro_main_ofPlaceOK`) and its edge (`proEdge2_ofUNM` at the entry control
`cP`), the held tails by `heldTailCX_of` (the
instance `instOk_ofPlaceOK`, the print and abort code from the check,
`main`'s code `CdCLE.toCdCL`, `scc_rt_main`'s return point off the write
abort `posOff_mainRetS`). Left: the setup call's and `main`'s facts
(`hint`, `hc`, `hfn`, `hL`, `hdT`, `hfd`, `hna`, `hnl`, `hZU`, `hsT`, `hw`, `hsw`,
`hc0t`, `hmeL`, `hmeN`, `hmeV`, `hme`, `hfo`, `hmr`, `hun`, `hsub`, `hfit`, `hpN`),
`main`'s body held (`hok`), and per context the rest of `CalleePre2`
(`CalleePre2R`), the construct premises in the callee's region, the held
calls' (`CallC2H`, `PrintCallCH`) and the aborts never ending. -/
theorem mainCallWSF_ofPlaceOKH {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    {Λw : Scc.Sem.Layout} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {rS : Range} {ar : Arena} {J : InvS}
    {Dt : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ms : List TermRun.Frame → MemSide isaLSE2}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop}
    (hint : d.retTy = .int) (hok : Scc.Lower.heldRetOk d.body = true) {sw : Nat}
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
      (SetupArgs (SPostC p lbl ty c0) sw x0) (UPostRF p lbl) ((LY).lab (setupMC sw).sp1).toBitVec tp :=
  mainCallWSF_ofPlaceOKHC h hd (fnCode2OfP hp h j d hd) (fnCode2OfP_spec hp h j d hd).2.2 hint hok hc hfn hL
    hdT hfd hna hnl hZU hsT hw hsw hc0t hmeL hmeN hmeV hme hfo hmr hun hsub hfit hpN hpre

end Place

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.CalleePre2.segH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.CalleePre2.segH

/-- info: 'Spike.Lib.LowerA64.mainCallWSF_ofHeld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.mainCallWSF_ofHeld

/-- info: 'Spike.Lib.LowerA64.mainCallWSF_ofPlaceOKH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.mainCallWSF_ofPlaceOKH

/-- info: 'Spike.Lib.LowerA64.mainCallWSF_ofPlaceOKHC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.mainCallWSF_ofPlaceOKHC
