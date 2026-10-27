/-
**`main`'s function segment to its held exits** (x86-64): a compiled
block whose paths all end in a held return tail (`heldRetOk`), from its
label at a context's premises (`CalleePre2`) to `ExitC2SLF`, and `main`'s
call after the setup block from it (`MainCallWSF` at `UPostRF`).

- `CalleePre2.segH`: the prologue (`proSeg2`) then the body's segment
  (`body2_segS_ofXH`) at the context's construct premises in the rebased
  region and a `HeldTailCX` instance (e.g. `heldTailCX_main`);
- `mainCallWSF_ofHeld`: `MainCallWSF … UPostRF` from `CalleePre2.segH` at
  every frame condition, ghost and entry control of the interface
  (`mainCallWSF_of_exitC2SLF` under `MainCallWSF.ofCtl`);
- `mainCallWSF_ofPlaceOKH`: `mainCallWSF_ofHeld` at `main`'s compiled block
  from the placement check (`fnCode2OfP`): the return address and the
  prologue (`raOk_main`, `hpro_main_ofPlaceOK`), the held tails by
  `heldTailCX_main` (the instance `instOk_ofPlaceOK`, `main`'s code
  `CdCLE.toCdCL`, `scc_rt_main`'s return point off the write abort by
  `posOff_mainRetS`);
- `mainCallWSF_ofPlaceOKHC`: the same at any code facts `c` of the check's
  output with `fnCode2OfP`'s return-address phase and code predicate and
  any immediates (e.g. `fnCode2OfPMe`), its prologue's facts given;
  `mainCallWSF_ofPlaceOKH` is it at `fnCode2OfP`.
-/
import Spike.Lib.LowerX64.ProgC2
import Spike.Lib.LowerX64.Body2SegHF
import Spike.Lib.LowerX64.SetupCallC2
import Spike.Lib.LowerX64.MainCallOf
import Spike.Lib.LowerX64.MainTailX
import Spike.Lib.LowerX64.MainRetPos
import Spike.Lib.Src.ContNR

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Lower.InvX64
open Spike.Lib.LowerNode
open Spike.Lib.X64.Flow.Ret0 (WcG CallerCells)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)}
  {endPc : Int64} {W : FragS isa} {K : State → State → Prop}

/-- **A held function's segment at a context** (`CalleePre2.seg` for a
body whose paths all end in a held return tail, `hok`): the prologue
(`proSeg2`), then the body's segment from its entry node
(`body2_segS_ofXH`) at the context's construct premises in `rbR R`
(`hcall`, `hlane`, `hbuf`, `hprint`) and the held tails' (`hheld`), to the
exits held at pending frames (`ExitC2SLF`) in `rbR R`. -/
theorem CalleePre2.segH {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    {c : FnCode2 exe cells endPc RaOk Cd i T d} {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame}
    {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isa} {J : AS → Ctl → Prop} {c0 : Ctl}
    (h : CalleePre2 W K p lbl lsize ms CxOk c R F fs fp ra tp G0 Ab J c0)
    (hcall : CallC2 p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR R) F W K ms fp ra tp fs G0 i T Ab
      (RetLk d.retTy))
    (hlane : LaneC p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR R) F W K ms fp ra tp fs G0 i T Ab)
    (hbuf : NewBufC p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR R) F W K ms fp ra tp fs G0 i T Ab
      (RetLk d.retTy))
    (hprint : PrintCallC p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR R) F W K ms fp ra tp fs G0 i T Ab)
    (hheld : HeldTailCX p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR R) F W K ms fp ra tp fs G0 i T
      (fun _ => True) (RetLk d.retTy) (fun c0 => ExitC2SLF p lbl exe endPc (rbR R) F fp ra tp c0 fs d.retTy Ab))
    (hok : Scc.Lower.heldRetOk d.body = true) (hT : ∀ t, T t → ContNR t) :
    SegWS W K p lbl ms ((At exe endPc R F ⟨(_root_.Executable.labels exe).label c.fn, ⟨0, []⟩, J⟩).at fs)
      (ExitC2SLF p lbl exe endPc (rbR R) F fp ra tp c0 fs d.retTy Ab) := by
  obtain ⟨hF', hR', hlo', hhi'⟩ := rbR_facts h.hF h.hR h.hlo h.hhi
  have hCd := c.hCd ra h.hra
  have hW₀ : ∀ s c', (fun s c => W s c fs) s c' → W s c' fs := fun _ _ h => h
  exact (SegWS.liftS fs (proSeg2 c h.hF h.hR h.hlo (by have := h.hhi; omega) h.hpro h.hedge) hW₀).seq
    (body2_segS_ofXH h.hG0 c.hfrm (fun _ _ hr => ExitC2SLF.trans hr) (fun _ _ _ _ h => .inr h) hcall hlane hbuf
      hprint (addC2_ofQ (Q := fun t => fs = [] → ∀ a, t ≠ .ret a)
        c.hf c.h1 hF' hR' hlo' hhi' hCd hW₀
        h.hW h.hWp (ContNR.qAdd hT) h.hab c.lcx tp)
      (subC2_ofQ (Q := fun t => fs = [] → ∀ a, t ≠ .ret a)
        c.hf c.h1 hF' hR' hlo' hhi' hCd hW₀
        h.hW h.hWp (ContNR.qSub hT) c.lcx tp)
      (pureMv2_of c.lcx tp) (splitMv2_of c.lcx tp) (unpackMv2_of c.lcx tp)
      (ifC2_ofQ (Q := fun t => fs = [] → ∀ a, t ≠ .ret a)
        c.hf c.h1 hF' hR' hlo' hhi' hCd hW₀
        h.hW (ContNR.qIf hT) c.lcx tp) hheld
      d.body c.env 0 "entry" 0 c.r c.kk _ c.lits [] [] c.hr c.hfr (c.hcode ra h.hra) (c.hbl ra h.hra)
      (fun q hq => have h := c.hWk q hq; ⟨h.1, h.2.1, trivial, h.2.2⟩)
      (fun q hq => ⟨c.hlit q hq, c.hcallL q hq, fun a ha => c.hretL a q.2 (by rw [← ha]; exact hq)⟩)
      c.hcnt c.hxchg hok c0 h.hg0)

/-- **The user `main` after the setup block, its paths held**
(`main`'s call for a body whose paths all end in a held return tail,
`hok`): at every frame condition `F'`, ghost `g` and entry control
`cP` of the interface, a context's premises at the entry invariant of
`uNM` (`CalleePre2`), the construct premises in the rebased region and the
held tails' (`HeldTailCX`, e.g. `heldTailCX_main`), its aborts never
ending; `main`'s return type `int` (`hint`). -/
theorem mainCallWSF_ofHeld {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    (c : FnCode2 exe cells endPc RaOk Cd i T d) (hint : d.retTy = .int) (hok : Scc.Lower.heldRetOk d.body = true)
    (hT : ∀ t, T t → ContNR t)
    {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int} {ZU : Int64}
    {Pre : Ctl → Reg64s → Prop} {ra : BitVec 64} {tp : UInt64} (hfn : fn = c.fn)
    (hpre : ∀ F' : MachineData → Prop, (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).OK →
      FStable (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' →
      (∀ m, F' m → F m ∧ CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m) →
      ∀ g : WcG, g.ra = ra → g.tp = tp → (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).base = g.sp → ∀ cP : Ctl,
      (∃ rs, Pre cP rs) →
      ∃ (G0 : Ctl → Prop) (Ab : FragS isa) (c0' : Ctl),
        CalleePre2 W K p lbl lsize ms CxOk c (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' [] g.fp g.ra tp G0 Ab
          (Spike.Lib.X64.Rt.uNM (_root_.Executable.labels exe).label (ms []) F fn ZU
            (fun c rs => Pre c rs ∧ c = cP) g).J c0' ∧
        CallC2 p lbl lsize c.lcx c.fr (Cd g.ra) (c.Bl g.ra) exe endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8))
          F' W K ms g.fp g.ra tp [] G0 i T Ab (RetLk d.retTy) ∧
        LaneC p lbl lsize c.lcx c.fr (Cd g.ra) (c.Bl g.ra) exe endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8))
          F' W K ms g.fp g.ra tp [] G0 i T Ab ∧
        NewBufC p lbl lsize c.lcx c.fr (Cd g.ra) (c.Bl g.ra) exe endPc
          (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F' W K ms g.fp g.ra tp [] G0 i T Ab (RetLk d.retTy) ∧
        PrintCallC p lbl lsize c.lcx c.fr (Cd g.ra) (c.Bl g.ra) exe endPc
          (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F' W K ms g.fp g.ra tp [] G0 i T Ab ∧
        HeldTailCX p lbl lsize c.lcx c.fr (Cd g.ra) (c.Bl g.ra) exe endPc
          (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F' W K ms g.fp g.ra tp [] G0 i T (fun _ => True)
          (RetLk d.retTy) (fun c0 => ExitC2SLF p lbl exe endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F'
            g.fp g.ra tp c0 [] d.retTy Ab) ∧
        SegWS W K p lbl ms Ab (fun _ _ _ => False)) :
    Spike.Lib.X64.Rt.MainCallWSF W K p lbl ms exe endPc R F fn Z D ZU Pre (UPostRF p lbl) ra tp :=
  MainCallWSF.ofCtl fun cP hcP => mainCallWSF_of_exitC2SLF fun F' hR0 hF' hFF g hra htp hbase => by
    obtain ⟨G0, Ab, c0', hP, hcall, hlane, hbuf, hprint, hheld, hAb⟩ := hpre F' hR0 hF' hFF g hra htp hbase cP hcP
    have H := hP.segH hcall hlane hbuf hprint hheld hok hT
    rw [hint] at H
    subst hfn
    exact ⟨Ab, c0', H, hAb⟩

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

/-- **`main`'s call after the setup block from the placement check, its
paths held, at any code facts of the check's output** (the body of
`mainCallWSF_ofPlaceOKH` at `c` with the return address's phase and
`main`'s code as `fnCode2OfP`'s, any immediates `im`, e.g.
`fnCode2OfPMe`'s `imms2Me`): its prologue's facts `hcPro`; the rest as
`mainCallWSF_ofPlaceOKH`. -/
theorem mainCallWSF_ofPlaceOKHC {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    {im : Expr → String → Nat → Option Nat}
    (c : FnCode2 (LY).exe (LY).prog (LY).endPc
      (fun ra => Spike.Lib.X64.PhRec.ph LY (Int64.ofBitVec ra).toBitVec.toNat =
        Spike.Lib.X64.PhRec.ph LY ((LY).lab raL).toBitVec.toNat)
      (fun ra => CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab
        (Int64.ofBitVec ra))
      im (TailAt2 p j) d)
    (hcPro : ProOK LY d c)
    {Λw : Scc.Sem.Layout} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {rS : Range} {ar : Arena} {J : InvS}
    {Dt : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ms : List TermRun.Frame → MemSide isa}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    (hint : d.retTy = .int) (hok : Scc.Lower.heldRetOk d.body = true) {sw : Nat}
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
      (SetupArgs (SPostC p lbl ty c0) sw x0) (UPostRF p lbl) ((LY).lab (setupMC sw).sp1).toBitVec tp := by
  refine mainCallWSF_ofHeld (lsize := lsize) (CxOk := CxOk) c hint hok
    (fun _ ht => contNR_tailAt2 hd hok ht) hfn
    fun F' hR0 hF' hFF g hra htp hbase cP hcP => ?_
  obtain ⟨G0, Ab, c0', hP, hcall, hlane, hbuf, hprint, hcallH, hprintH, hAb⟩ :=
    hpre F' hR0 hF' hFF g hra htp hbase cP (hfo _ _ hcP.choose_spec)
  have hP2 := hP.toPre (by rw [hra]; exact RaMain.raOk_main h _ hc)
    (hpro_main_ofPlaceOK h c hcPro hL (fun _ _ h => h)
      hP.hR hP.hR8 hP.hlo (by have := hP.hhi; omega) hP.hl hP.hh (htp ▸ hmr)
      (fun m hm => htp ▸ hun m (hFF m hm).1) hsub hfit hP.hFO hpN
      (fun c regs hc' => hPl_setupArgs hsT hw hsw hme Λw c regs hc'.1)
      (fun c regs hc' => hnr_setupArgs hE c regs hc'.1) (fun c regs hc' => hfo c regs hc'.1))
  refine ⟨G0, Ab, c0', hP2, hcall, hlane, hbuf, hprint, ?_, hAb⟩
  have hlo := hP.hlo
  have hhi := hP.hhi
  obtain ⟨hF2, hR2, hlo2, hhi2⟩ := rbR_facts hP.hF hP.hR hlo hhi
  have hb := rbR_base hP.hR (by omega) (by omega)
  have hR8 := hP.hR8
  have hl := hP.hl
  have hh := hP.hh
  have hR8' : (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)).base.toNat % 8 = 0 := by omega
  exact heldTailCX_main hpN (Spike.Lib.X64.PhRec.instOk_ofPlaceOK h _) (printIn_of_placeOKAt h)
    (abortIn_of_placeOKAt h) c.hf c.h1 hF2 hR2 hR8' hlo2
    hhi2 (by have e : (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)).lo
          = (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).lo + 8 := rfl; omega)
    (by have e : (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)).hi
          = (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).hi + 8 := rfl; omega) hsub hfit
    (fun m hm => stackOff_rbR hP.hR (by omega) (by omega) (hP.hFO m hm)) (fun _ _ h => CdCLE.toCdCL h)
    (by rw [hra]; exact posOff_mainRetS (Spike.Lib.X64.Rt.mainSIn_of_okS hc))
    c.hfrm hcallH hprintH (fun _ _ _ h => h)

/-- **`main`'s call after the setup block from the placement check, its
paths held** (`mainCallWSF_ofHeld` at `c := fnCode2OfP … j d hd`):
the return address's phase (`raOk_main`) and the prologue inside `W2`
(`hpro_main_ofPlaceOK`), the held tails by
`heldTailCX_main` in the rebased region (its facts from `CalleePre2R`'s
by `rbR_facts`, `rbR_base`, `stackOff_rbR`; the instance
`instOk_ofPlaceOK`, the print and abort code from the check, `main`'s
code `CdCLE.toCdCL`, `scc_rt_main`'s return point off the write abort
`posOff_mainRetS`). Left: the setup call's and `main`'s facts the
theorem takes (all its premises but `hok` and `hpre`),
`main`'s body held (`hok`), and per context the rest of `CalleePre2`, the
construct premises in the rebased region, the held calls' (`CallC2H`,
`PrintCallCH`) and the aborts never ending. -/
theorem mainCallWSF_ofPlaceOKH {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    {Λw : Scc.Sem.Layout} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {rS : Range} {ar : Arena} {J : InvS}
    {Dt : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ms : List TermRun.Frame → MemSide isa}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    (hint : d.retTy = .int) (hok : Scc.Lower.heldRetOk d.body = true) {sw : Nat}
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
      (SetupArgs (SPostC p lbl ty c0) sw x0) (UPostRF p lbl) ((LY).lab (setupMC sw).sp1).toBitVec tp :=
  mainCallWSF_ofPlaceOKHC h hd (fnCode2OfP hp h j d hd) (fnCode2OfP_spec hp h j d hd).2.2 hint hok hc hfn hL
    hsT hw hsw hme hE hfo hmr hun hsub hfit hpN hpre

end Place

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.CalleePre2.segH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.CalleePre2.segH

/-- info: 'Spike.Lib.LowerX64.mainCallWSF_ofHeld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainCallWSF_ofHeld

/-- info: 'Spike.Lib.LowerX64.mainCallWSF_ofPlaceOKH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainCallWSF_ofPlaceOKH

/-- info: 'Spike.Lib.LowerX64.mainCallWSF_ofPlaceOKHC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainCallWSF_ofPlaceOKHC
