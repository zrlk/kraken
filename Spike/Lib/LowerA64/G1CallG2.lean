/-
**The plain calls at a base context** (AArch64): `CallC2` at the `j`th
compiled block of an `Accepted2` program under the generic base context
`CxG2` with its stack records (`CxOkS`), from `CallC2FW` (the plain call
with its blocks asked at placed nodes), the callee's `FnSpecC2` at its own
earlier index and its context premises (`calleePre2_callG2`).

- `ProCallG2`: a callee's prologue inside `W2` at a plain call (the
  remaining field of `calleePre2_callG2`);
- `WCallG2`: the call's blocks inside `W2` at a base context (`CallC2FW`'s
  `hWB`, `hWR`, `hWBl`, `hWC`);
- `callC2R_ofCxG2MS`: `CallC2R` at a base context at any frames
  (`CxG2M`), the callee's records from its base context;
  `callC2R_ofCxG2M`: the callee's records at the bottom (`main`'s calls);
- `callC2_ofCxG2`: `CallC2` at a base context with its records.
-/
import Spike.Lib.LowerA64.G1CalleePre
import Spike.Lib.LowerA64.G1CallWStmt

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
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2 imms2Me IsNum SlotRepAt)

section G1CallG2

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
/-- `W2At` at `Closed2AtA`'s instance. -/
local notation "W2S" J:max => W2At h (imms2Me Λ p) p IsNum (rS0 (Ly)) J Dt (fun _ => 0)

set_option hygiene false in
/-- `MSAt` at `Closed2AtA`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max => MSAt h (imms2Me Λ p) p IsNum J (ab2 p (Ly).lab) (fun _ => 0)

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
/-- The contexts with their records over the base context. -/
local notation "CXS" => CxOkS (p := p) (lbl := fun _ => none) (lsize := fun _ => 0) (fnCode2OfPMe hp h Λ)
  (CxG2 h hp Dt J) Bot

set_option hygiene false in
/-- The code facts' return address condition. -/
local notation "RAOK" ra:max => Spike.Lib.A64.PhRec.ph LY0 (Int64.ofBitVec ra).toBitVec.toNat =
  Spike.Lib.A64.PhRec.ph LY0 (Int64.ofBitVec ((LY0).lab Spike.Lib.A64.Rt.bareMC.e0 + 4).toBitVec).toBitVec.toNat

set_option linter.unusedVariables false in
/-- **A callee's prologue inside `W2` at a plain call** (`calleePre2_callG2`'s
`hpro`): at a plain call of `g` in the `j`th compiled block under a base
context at any frames (`CxG2M`), at the caller's depth `D`, the callee `dg` found
for `g` the `j'`th compiled block, its prologue at the entry invariant
`calleeJSO` in its region below the caller's frame. -/
def ProCallG2 (hp : Scc.Lower.Accepted2 p = true) : Prop :=
  ∀ (Dt : State → Prop) (J : InvS) (j : Nat) (d : Decl)
    (hd : (compiled2 p)[j]? = some d) (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame)
    (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop) (Ab : FragS isaLSE2),
    CxG2M h hp Dt J j R F fs fp ra tp G0 Ab → RAOK ra →
    ∀ (D : Int), R.lo = -((FC j d hd).cx.frame : Int) - D →
    ∀ (g : String) (q : CallG) (frm : TermRun.Frame) (F' : MachineData → Prop),
    FStable (R.callee (-((FC j d hd).cx.frame : Int)) (-D) 0) F' →
    CalleeF2 p (fun _ => none) (fun _ => 0) (FC j d hd).cx R F D fp ra (imms2Me Λ p) (TailAt2 p j) q frm F' →
    (∃ c x a e, G0 c ∧ TailAt2 p j (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
      CallTo p c q.cE frm) →
    ArgV (fun _ => none) q →
    (∃ pcB k, (FC j d hd).Bl ra pcB (Scc.Lower.Names.user g) k ∧ q.ra = (pcB + 4).toBitVec) →
    CallSite2F p (fun _ => none) (fun _ => 0) (FC j d hd).lcx (FC j d hd).cx (CD ra) ((FC j d hd).Bl ra) G0
      (TailAt2 p j) (_root_.Executable.labels (LY0).exe).label (imms2Me Λ p) (RetLk d.retTy) g q R D fp ra frm F' →
    ∀ (j' : Nat) (dg : Decl) (hd' : (compiled2 p)[j']? = some dg), p.find? (·.name == g) = some dg →
    ProW (fun s c => (W2S J) s c (frm :: fs)) (KT) (LY0).exe (LY0).endPc
      (R.callee (-((FC j d hd).cx.frame : Int)) (-D) 0) F' ((MSS J) (frm :: fs))
      ((_root_.Executable.labels (LY0).exe).label (FC j' dg hd').fn) (Int64.ofInt (FC j' dg hd').cx.frame)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL (FC j' dg hd').cx) (FC j' dg hd').ps
      (calleeJSO (R.callee (-((FC j d hd).cx.frame : Int)) (-D) 0) F' (_root_.Executable.labels (LY0).exe).label
        g tp q)

set_option linter.unusedVariables false in
/-- **A plain call's blocks inside `W2` at a base context** (`CallC2FW`'s
`hWB`, `hWR`, `hWBl`, `hWC` at the `j`th compiled block's code facts, under
a base context at any frames, `CxG2M`): the argument's load, the result's store,
the `bl` and the callee's entry, at nodes whose controls are in `G0` with
the saved pair and placed in the slot file. -/
def WCallG2 (hp : Scc.Lower.Accepted2 p = true) : Prop :=
  ∀ (Dt : State → Prop) (J : InvS) (j : Nat) (d : Decl)
    (hd : (compiled2 p)[j]? = some d) (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame)
    (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop) (Ab : FragS isaLSE2),
    CxG2M h hp Dt J j R F fs fp ra tp G0 Ab → RAOK ra →
    (∀ (n : ND) blk, SubCd (CD ra) n.pc blk → n.o = oF (FC j d hd).cx →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧
        SlotRepAt (imms2Me Λ p) (fun _ => none) (rsOf (FC j d hd).cx) σ.slot c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      CallBlk (FC j d hd).cx blk → BlkW (fun s c => (W2S J) s c fs) (KT) (LY0).exe (LY0).endPc R F n blk) ∧
    (∀ (n : ND) blk (k0 : Int), SubCd (CD ra) n.pc blk → n.o = oF (FC j d hd).cx → blk.length ≤ 1 →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧
        SlotRepAt (imms2Me Λ p) (fun _ => none) (rsOf (FC j d hd).cx) (Spike.Lib.upd σ.slot k0 σ.regs.X0.toBitVec) c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      CallBlk (FC j d hd).cx blk → BlkW (fun s c => (W2S J) s c fs) (KT) (LY0).exe (LY0).endPc R F n blk) ∧
    (∀ (n : ND) (g : String) k, (FC j d hd).Bl ra n.pc (Scc.Lower.Names.user g) k →
      Spike.Lib.LowerCall.Callee (FC j d hd).lcx g → (∃ x a e, TailAt2 p j (.let_ x (.call g [] a []) e)) →
      n.o = oF (FC j d hd).cx →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧
        SlotRepAt (imms2Me Λ p) (fun _ => none) (rsOf (FC j d hd).cx) σ.slot c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      BlkW (fun s c => (W2S J) s c fs) (KT) (LY0).exe (LY0).endPc R F n [blD (Scc.Lower.Names.user g)]) ∧
    (∀ (g : String) (dg : Decl), p.find? (·.name == g) = some dg → Spike.Lib.LowerCall.Callee (FC j d hd).lcx g →
      (∃ x a e, TailAt2 p j (.let_ x (.call g [] a []) e)) → ∀ (n : ND),
      n.pc = (_root_.Executable.labels (LY0).exe).label (Scc.Lower.Names.user g) → n.o = oF (FC j d hd).cx →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧
        SlotRepAt (imms2Me Λ p) (fun _ => none) (rsOf (FC j d hd).cx) σ.slot c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      ∀ s c, Spike.Lib.A64.Flow.At (LY0).exe (LY0).endPc R F n s c → (W2S J) s c fs)

/-- **The plain calls at a base context at any frames** (`bodySpecC2_of`'s
`hcon`, its `CallC2` conjunct, as `CallC2R`): from `CallC2FW` at the
caller's depth `D = -R.lo - frame` (at least the room's slack,
`Room2OwnStmt`), the call's blocks inside `W2` (`WCallG2`), each callee's
segment from its `FnSpecC2` at its earlier index (`hIH`, at the contexts
with records over bottom keys `Bot`) and its context premises
(`calleePre2_callG2M`, its prologue from `ProCallG2`, its records from
its base context `hS`) at the entry invariant `calleeJSO` (`hcal_ofSO`). -/
theorem callC2R_ofCxG2MS (hFW : CallC2FW) (hp : Scc.Lower.Accepted2 p = true) (hown : Room2OwnStmt h hp)
    (hrc : Room2CalleeStmt h hp) (hlc : Lim2CalleeStmt h hp) (hlok : LimOk2Stmt h hp)
    (htg : tgOkB OP = true) (hpc : ProCallG2 h hp) (hwc : WCallG2 h hp)
    {Dt : State → Prop} {J : InvS} {Bot : StkKey → List TermRun.Frame → Prop}
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) {R : Region} {F : MachineData → Prop}
    {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isaLSE2}
    (hcx : CxG2M h hp Dt J j R F fs fp ra tp G0 Ab) (hra : RAOK ra)
    (hS : ∀ (D : Int), R.lo = -((FC j d hd).cx.frame : Int) - D →
      ∀ (g : String) (q : CallG) (frm : TermRun.Frame) (F' : MachineData → Prop),
      FStable (R.callee (-((FC j d hd).cx.frame : Int)) (-D) 0) F' →
      CalleeF2 p (fun _ => none) (fun _ => 0) (FC j d hd).cx R F D fp ra (imms2Me Λ p) (TailAt2 p j) q frm F' →
      (∃ c x a e, G0 c ∧ TailAt2 p j (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
        CallTo p c q.cE frm) →
      (∃ pcB k, (FC j d hd).Bl ra pcB (Scc.Lower.Names.user g) k ∧ q.ra = (pcB + 4).toBitVec) →
      CallSite2F p (fun _ => none) (fun _ => 0) (FC j d hd).lcx (FC j d hd).cx (CD ra) ((FC j d hd).Bl ra) G0
        (TailAt2 p j) (_root_.Executable.labels (LY0).exe).label (imms2Me Λ p) (RetLk d.retTy) g q R D fp ra
        frm F' →
      ∀ (j' : Nat) (dg : Decl), (compiled2 p)[j']? = some dg → p.find? (·.name == g) = some dg →
      CxG2 h hp Dt J j' (R.callee (-((FC j d hd).cx.frame : Int)) (-D) 0) F' (frm :: fs) q.fp q.ra tp
        (fun c => FrameRunM p (q.cE, frm :: fs) (c, frm :: fs)) Ab →
      CXS j' (R.callee (-((FC j d hd).cx.frame : Int)) (-D) 0) F' (frm :: fs) q.fp q.ra tp
        (fun c => FrameRunM p (q.cE, frm :: fs) (c, frm :: fs)) Ab)
    (hIH : ∀ g dg, CallIn2 (FC j d hd).lcx d.body g → p.find? (·.name == g) = some dg →
      ∃ j' : Nat, j' < j ∧ ∃ hd' : (compiled2 p)[j']? = some dg,
        FnSpecC2 (W2S J) (KT) p (fun _ => none) (fun _ => 0) (MSS J) (CXS j') (FC j' dg hd')) :
    CallC2R p (fun _ => none) (fun _ => 0) (FC j d hd).lcx (FC j d hd).cx (CD ra) ((FC j d hd).Bl ra) (LY0).exe
      (LY0).endPc R F (W2S J) (KT) (MSS J) fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j) Ab (RetLk d.retTy) := by
  have hc := hcx.1
  have hR := hc.hR
  have hl := hc.hl
  have h16 := (FC j d hd).h16
  have hrow := hown j d hd 256 R.lo (hc.room d hd)
  have he1 := (fnCode2OfPMe_spec hp h Λ j d hd).1
  obtain ⟨hWB, hWR, hWBl, hWC⟩ := hwc Dt J j d hd R F fs fp ra tp G0 Ab hcx hra
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (imms2Me Λ p) (rS := rS0 (Ly))
  have hx : ∀ g, Spike.Lib.LowerCall.Callee (FC j d hd).lcx g →
      (Scc.Frontend.externs p).find? (·.1 == g) = none := by
    intro g hcl
    have := hcl.1
    rw [he1] at this
    exact this
  refine hFW (FC j d hd).hf (FC j d hd).h1 (FC j d hd).h16 (by rw [he1]) hc.hFS hR hc.hal
    (D := -R.lo - ((FC j d hd).cx.frame : Int)) (by omega) (by omega) (by omega) hc.hhi
    ((FC j d hd).hCd ra hra) ?_ hc.hG0 hWB hWR hWBl hWC
    (fun x g is a ts e hT hcl => Spike.Lib.LowerNode.callee_nilIdx hp hd (hT d hd) (hx g hcl)) ?_
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
    have hpre := calleePre2_callG2M h hp hown hlok htg hd hcx hra hF' hex hav hbl hsite hd' hfd
      (hpc Dt J j d hd R F fs fp ra tp G0 Ab hcx hra _ hDe g q frm F' hF' hCF hex hav hbl hsite j' dg hd' hfd)
      (hS _ hDe g q frm F' hF' hCF hex hbl hsite j' dg hd' hfd
        (CxG2M.callG2 h hp hown hrc hlc hd hcx hDe hF' hCF hex hsite hd' hfd))
    subst hfr
    exact hcal_ofSO hgn hint rfl hpre hs

/-- **The plain calls at a base context at any frames, the callee's
records at the bottom** (`callC2R_ofCxG2MS`, the callee's context
`CxOkS.bot`): at bottom keys `Bot` holding at every frame pushed on `fs`
(`main`'s calls at no frames, under a `Bot` admitting the call's frame). -/
theorem callC2R_ofCxG2M (hFW : CallC2FW) (hp : Scc.Lower.Accepted2 p = true) (hown : Room2OwnStmt h hp)
    (hrc : Room2CalleeStmt h hp) (hlc : Lim2CalleeStmt h hp) (hlok : LimOk2Stmt h hp)
    (htg : tgOkB OP = true) (hpc : ProCallG2 h hp) (hwc : WCallG2 h hp)
    {Dt : State → Prop} {J : InvS} {Bot : StkKey → List TermRun.Frame → Prop}
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) {R : Region} {F : MachineData → Prop}
    {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isaLSE2}
    (hcx : CxG2M h hp Dt J j R F fs fp ra tp G0 Ab) (hra : RAOK ra)
    (hB : ∀ k f, Bot k (f :: fs))
    (hIH : ∀ g dg, CallIn2 (FC j d hd).lcx d.body g → p.find? (·.name == g) = some dg →
      ∃ j' : Nat, j' < j ∧ ∃ hd' : (compiled2 p)[j']? = some dg,
        FnSpecC2 (W2S J) (KT) p (fun _ => none) (fun _ => 0) (MSS J) (CXS j') (FC j' dg hd')) :
    CallC2R p (fun _ => none) (fun _ => 0) (FC j d hd).lcx (FC j d hd).cx (CD ra) ((FC j d hd).Bl ra) (LY0).exe
      (LY0).endPc R F (W2S J) (KT) (MSS J) fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j) Ab (RetLk d.retTy) :=
  callC2R_ofCxG2MS h hFW hp hown hrc hlc hlok htg hpc hwc hd hcx hra
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc' => CxOkS.bot hc' (hB _ _)) hIH

/-- **The plain calls at a base context** (`bodySpecC2_of`'s `hcon`, its
`CallC2` conjunct): `callC2R_ofCxG2MS` at the context's base context, the
callee's records the caller's record pushed (`CxOkS.callG2`), at the
context's suspended frame (`CallC2R.ofCons`). -/
theorem callC2_ofCxG2 (hFW : CallC2FW) (hp : Scc.Lower.Accepted2 p = true) (hown : Room2OwnStmt h hp)
    (hrc : Room2CalleeStmt h hp) (hlc : Lim2CalleeStmt h hp) (hlok : LimOk2Stmt h hp)
    (htg : tgOkB OP = true) (hpc : ProCallG2 h hp) (hwc : WCallG2 h hp)
    {Dt : State → Prop} {J : InvS} {Bot : StkKey → List TermRun.Frame → Prop}
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) {R : Region} {F : MachineData → Prop}
    {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isaLSE2}
    (hcx : CXS j R F fs fp ra tp G0 Ab) (hra : RAOK ra)
    (hIH : ∀ g dg, CallIn2 (FC j d hd).lcx d.body g → p.find? (·.name == g) = some dg →
      ∃ j' : Nat, j' < j ∧ ∃ hd' : (compiled2 p)[j']? = some dg,
        FnSpecC2 (W2S J) (KT) p (fun _ => none) (fun _ => 0) (MSS J) (CXS j') (FC j' dg hd')) :
    CallC2 p (fun _ => none) (fun _ => 0) (FC j d hd).lcx (FC j d hd).cx (CD ra) ((FC j d hd).Bl ra) (LY0).exe
      (LY0).endPc R F (W2S J) (KT) (MSS J) fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j) Ab (RetLk d.retTy) :=
  CallC2R.ofCons hcx.1.2 <| callC2R_ofCxG2MS h hFW hp hown hrc hlc hlok htg hpc hwc hd hcx.1.1 hra
    (fun _ hDe _ _ _ _ hF' hCF hex hbl hsite _ _ hd' hf _ =>
      CxOkS.callG2 h hp hown hrc hlc hd hcx hra hDe hF' hCF hex hbl hsite hd' hf) hIH

end G1CallG2

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.callC2R_ofCxG2M' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.callC2R_ofCxG2M

/-- info: 'Spike.Lib.LowerA64.callC2_ofCxG2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.callC2_ofCxG2
