/-
**`SetupCxLB` at the contexts free of the frame invariant** (x86-64; the
setup frame's contexts `CxOkH` (`Spike/Test/X64Hello1CxOkH.lean`) as base
contexts `SetupCxLB` (`Spike/Test/X64Hello1HsOf.lean`) at any family `J`,
by `setupCxLB_ofPre` at the context's witnesses.

- `nbX_abort_fam`: a heap abort exit read at one family is one at any other;
- `setupBot_fam`: a setup frame's bottom key at one family is one at any
  other;
- `cxLB_ofCxOkH`: `SetupCxLB` at `J` from `CxOkH` and the allocator's `W2`
  instance at `J` (`SetupPreF.hAW`).
-/
import Spike.Test.X64Hello1CxLBOf
import Spike.Test.X64Hello1CxOkH


namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (swR FStable At)
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Flow.Ret0 (WcG CallerCells limA)
open Spike.Lib.X64.Flow.NewBuf (nbX)
open Spike.Lib.X64.Rt (setupMC rS0 arOf swFSL)
open Spike.Lib.X64.WriteAb (Ab)
open Spike.Lib.LowerNode (FrOk2 ZBad setupWords2 compiled2 TailAt2 imms2Me)
open Spike.Lib.AllocReach (IN)

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates (`fnCode2OfP`'s). -/
local notation "LY0" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)

set_option hygiene false in
/-- The canonical load's memory of the output. -/
local notation "M0" => Spike.Lib.X64.PhRec.m0Of (Ly).Λ OP
  (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).secs

set_option hygiene false in
/-- `MSAt` at `Closed2At`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max =>
  MSAt h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The program's start control (`S0X`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).env, none⟩ : Ctl)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => tpOf (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The switch region at depth `L`, below the top `v`. -/
local notation "RS" v:max => ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)

set_option hygiene false in
/-- The switch region's frame condition with `WordsNone`, below the top `v`
(`HSBVF`'s). -/
local notation "FS" v:max => (fun m => (Spike.Lib.DmemPriv.WordsNone (Ly).Λ m.dmem ∧
  swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) v m) ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)

set_option hygiene false in
/-- The setup call's callee region. -/
local notation "RC" => (RS v).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8

set_option hygiene false in
set_option linter.unusedVariables false in
/-- The ghosts at the setup frame. -/
local notation "GR" g:max fr:max => fun c => Spike.Lib.FrameRunM p (g.c0, [fr]) (c, [fr])

set_option hygiene false in
set_option linter.unusedVariables false in
/-- The setup call's segment's premises at the callee's frame condition
`F'`, ghost `g` and frame `fr` (`SetupPreF`'s `PREF`). -/
local notation "PREF" F':max g:max fr:max => (RC).OK ∧ FStable (RC) F' ∧
  (∀ m, F' m → (FS v) m ∧ CallerCells (RS v) (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8 m) ∧
  g.ra = ((Ly).lab (setupMC (setupWords2 p)).sp0).toBitVec ∧ g.tp = TP0 ∧
  Spike.Lib.X64.Flow.CallTo p C0 g.c0 fr ∧ (RC).base = g.sp

/-- **A heap abort exit read at one family is one at any other**: `nbX`'s
abort exit reads the memory side `msOfAX` only through the call's `OK`
and `Jfull`, which do not read the family (`msOfAX` differs between
families only in `xa`). -/
theorem nbX_abort_fam {Λ' : Scc.Sem.Layout} {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop}
    {G : Loc → Val → Prop} {own' : OwnS} {ar : Arena} {I0 I1 : InvS} {ab : Option (State → Prop)}
    {L : Lbl} {ls : Lsize} {fs : List TermRun.Frame} {lab : Label → Int64}
    {lbl : WeakMem.AllocLabel → Option Nat} {R : Region} {fz : Int} {pcR : Int64}
    {Jc : Spike.Lib.X64.AS → Ctl → Prop} {exe : _root_.Executable} {endPc : Int64}
    {F : MachineData → Prop} {s : State} {c : Ctl}
    (hA : At exe endPc R F (nbX (msOfAX Λ' μ p rd G own' ar I0 ab L ls fs) lab lbl R fz pcR Jc .abort) s c) :
    At exe endPc R F (nbX (msOfAX Λ' μ p rd G own' ar I1 ab L ls fs) lab lbl R fz pcR Jc .abort) s c := by
  obtain ⟨h1, h2, h3, h4, σ, hAbs, hF, hx, q, hJf, σC, hJc, hsl⟩ := hA
  have hq1 : q.1.OK (msOfAX Λ' μ p rd G own' ar I1 ab L ls fs) lab := by
    have h := q.2
    cases ab <;>
      exact ⟨h.term, h.ev, h.num, h.hold, h.n_lt, h.ctr, h.heap, h.room, h.cells, h.units, h.off, h.accs, h.rt,
        h.mp, h.grow, h.hdr⟩
  refine ⟨h1, h2, h3, h4, σ, hAbs, hF, hx, ⟨q.1, hq1⟩, ?_, σC, hJc, hsl⟩
  cases ab <;> exact hJf

set_option linter.unusedVariables false in
/-- **A setup frame's bottom key at one family is one at any other**:
`SetupBot` reads the memory side `msOfAX` only through the limit word's
`LimOk` (`rt`, `mp`, `G`), which do not read the family. -/
theorem setupBot_fam {Λ' : Scc.Sem.Layout} {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop}
    {G : Loc → Val → Prop} {own' : OwnS} {ar : Arena} {I0 I1 : InvS} {ab : Option (State → Prop)}
    {L : Lbl} {ls : Lsize} {fs0 : List TermRun.Frame} {lab : Label → Int64} {R : Region}
    {F : MachineData → Prop} {sc : Spike.Lib.X64.Rt.SetupCode} {D1 : Int} {ZU1 : Int64}
    {g0 : MainG} {x0 : BitVec 64} {k : StkKey} {fs : List TermRun.Frame}
    (hB : SetupBot p lab (msOfAX Λ' μ p rd G own' ar I0 ab L ls fs0) R F sc D1 ZU1 g0 x0 k fs) :
    SetupBot p lab (msOfAX Λ' μ p rd G own' ar I1 ab L ls fs0) R F sc D1 ZU1 g0 x0 k fs := by
  have hL : ∀ F' a Z, LimOk (msOfAX Λ' μ p rd G own' ar I0 ab L ls fs0) F' a Z =
      LimOk (msOfAX Λ' μ p rd G own' ar I1 ab L ls fs0) F' a Z := by
    intro F' a Z
    apply propext
    cases ab <;>
      exact ⟨fun h => ⟨h.rt, h.mp, h.unmapped, h.room⟩, fun h => ⟨h.rt, h.mp, h.unmapped, h.room⟩⟩
  have hU : Spike.Lib.X64.Rt.uN0 lab (msOfAX Λ' μ p rd G own' ar I0 ab L ls fs0) F sc.setup ZU1 =
      Spike.Lib.X64.Rt.uN0 lab (msOfAX Λ' μ p rd G own' ar I1 ab L ls fs0) F sc.setup ZU1 := by
    funext g
    simp only [Spike.Lib.X64.Rt.uN0, hL]
  obtain ⟨Gh, h1, h2, h3, h4, h5, h6, h7⟩ := hB
  refine ⟨Gh, h1, h2, ?_, h4, h5, h6, h7⟩
  rw [← hU]
  exact h3

/-- **`SetupCxLB` at a context `CxOkH`**: at any family `J` and the `j`th
compiled block `d`, a context `CxOkH` (at its own bounds, top, ghost,
frame and abort family) is a base context `SetupCxLB` at `J`
(`setupCxLB_ofPre` at the context's witnesses; its aborts' heap exits read
at `J` are ones at the context's family, `nbX_abort_fam`; its bottom key
read at `J`, `setupBot_fam`), given the allocator's `W2` instance at `J` at
every bound and bottom key (`hAW`, `SetupPreF.hAW`). -/
theorem cxLB_ofCxOkH (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {Dt : State → Prop} (J : InvS) {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    (hAW : ∀ (L D1 : Int) (fS : Nat) (v : BitVec 64) (F' : MachineData → Prop) (g : WcG)
      (fr : TermRun.Frame), PREF F' g fr →
      SetupBot p (Ly).lab ((MSS J) []) (RS v) (FS v) (setupMC (setupWords2 p)) D1 (Int64.ofInt fS)
        ⟨TOP - 8#64, TP0, C0⟩ (TP0).toBitVec ⟨j, RC, F', g.fp, g.ra, TP0, GR g fr⟩ [fr] →
      AllocW2At p (fun _ => none) (fun _ => 0) (fnCode2OfPMe hp h Λ j d hd).lcx (fnCode2OfPMe hp h Λ j d hd).fr
        (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec g.ra))
        ((fnCode2OfPMe hp h Λ j d hd).Bl g.ra)
        (fun lbl lsize s c => W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum
          (Spike.Lib.X64.PhRec.GOf Ly M0) (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly))
          (arOf (Ly).Λ) (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) Dt (Ab (Ly).lab) lbl lsize s c [fr])
        (KT) (Ly).exe (Ly).endPc (rbR (RC)) F' ((MSS J) [fr]) g.fp g.ra (TP0) (GR g fr) (imms2Me Λ p)
        (TailAt2 p j) (RetLk d.retTy))
    {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64}
    {G0 : Ctl → Prop} {Ab' : FragS isa} (hc : CxOkH h hp j R F fs fp ra tp G0 Ab') :
    SetupCxLB h hp Dt J hd j R F fs fp ra tp G0 Ab' := by
  obtain ⟨d', hd', L, D1, fS, nS, v, g, fr, J', hn, hfS, hnS, hL0, hLm, hL8, hD18, hL1, hrow,
    ⟨hR0, hR8, hF, hFF, hra, htp, hct, hbase⟩, hwn, hSB, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hc
  obtain rfl : d' = d := Option.some.inj (hd'.symm.trans hd)
  exact setupCxLB_ofPre h hp hty J v hfS hnS hL0 hLm hL8 hD18 hL1 hrow hd hn hR0 hR8 hF
    (fun m hm => ⟨⟨(hFF m hm).1.1.2, (hFF m hm).1.2⟩, (hFF m hm).2⟩) hct hwn
    (hAW L D1 fS v F g fr ⟨hR0, hF, hFF, hra, htp, hct, hbase⟩ (setupBot_fam hSB))
    fun Jc pcR _ _ hJ _ hA => Or.inr ⟨rfl, Jc, pcR, hJ, nbX_abort_fam hA⟩

end Assembled

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.nbX_abort_fam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nbX_abort_fam

/-- info: 'Spike.Lib.LowerX64.cxLB_ofCxOkH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cxLB_ofCxOkH

/-- info: 'Spike.Lib.LowerX64.setupBot_fam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms setupBot_fam

end Spike.Lib.LowerX64
