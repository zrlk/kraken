/-
**A plain call's callee premises at a base context** (x86-64; the twin of
`Spike/Lib/LowerA64/G1CalleePre.lean`): at a plain call of `g` in the `j`th
compiled block of an `Accepted2` program, under the generic base context
`CxG2` with its stack records (`CxOkS`), the callee `g`, the `j'`th compiled
block, has its context premises (`CalleePre2`) in its region below the
caller's frame, its saved `%rbp` and the return address at the caller's
depth `D` (`calleeR (rbR R) size D`).

- `CxG2M.callG2`: the callee's base context from the caller's at any
  frames (`CxCore2.call`), its rows from the room and limit statements;
- `CxOkS.callG2`: the callee's context with the caller's record pushed
  (`CxOkS.callSite` at `CxG2M.callG2`);
- `calleePre2_callG2M`: the callee's `CalleePre2` at the entry invariant
  `calleeJSO` from the caller's base context at any frames, given the
  callee's context and its prologue inside `W2`;
- `calleePre2_callG2`: the same under a context with its records.
-/
import Spike.Lib.LowerX64.G1CalleeFacts
import Spike.Lib.LowerX64.CxBlk2Of
import Spike.Lib.LowerX64.ProEdge2Callee

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region FrameRunM)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (FStable AS SORel)
open Spike.Lib.X64.Flow (CallTo XProW)
open Spike.Lib.X64.Flow.Ret0 (StackOff limA pinA tpOf)
open Spike.Lib.X64.Rt (rS0)
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2 imms2Me IsNum)

section G1Pre

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
/-- The output. -/
local notation "OUT" => Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)

set_option hygiene false in
/-- `MSAt` at `Closed2At`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max => MSAt h (imms2Me Λ p) p IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- `W2At` at `Closed2At`'s instance. -/
local notation "W2S" J:max => W2At h (imms2Me Λ p) p IsNum (rS0 (Ly)) J Dt (fun _ => 0)

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => Spike.Lib.X64.Flow.Ret0.TakeK ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => tpOf (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The `j`th compiled block's code facts at the theorem's immediates. -/
local notation "FC" j:max d:max hd:max => fnCode2OfPMe hp h Λ j d hd

set_option hygiene false in
/-- The code predicate at the return address `ra`. -/
local notation "CD" ra:max => CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab
  (Int64.ofBitVec ra)

set_option hygiene false in
/-- The contexts with their records over the base context. -/
local notation "CXS" => CxOkS (p := p) (lbl := fun _ => none) (lsize := fun _ => 0) (fnCode2OfPMe hp h Λ)
  (CxG2 h hp Dt J) Bot

/-- **The callee's base context at a plain call** (`CxCore2.call`): from
the caller's base context at any frames (`CxG2M`) at the `j`th compiled
block (region `R`, its rebased region `rbR R`), the call site of
`g` (`CallSite2F`, its source call `hex`) at the caller's depth `D` (the
room below the caller's frame and its saved `%rbp`,
`(rbR R).lo = -size - 8 - D`), the callee's frame condition stable in its
region and the caller's at the call (`CalleeF2`), and the callee `dg` found
for `g`, the `j'`th compiled block: the callee's base context `CxG2` at the call's
frame pushed in the callee's region `calleeR (rbR R) size D`, its ghosts
the frame runs from the call's entry control. The rows: the callee's room
at `-D` and its limit room at the callee's entry `%rsp` from the caller's
(`Room2CalleeStmt`, `Lim2CalleeStmt`), its room covering its frame and
saved `%rbp` (`Room2OwnStmt`); no buffer allocation in a plain callee. -/
theorem CxG2M.callG2 (hp : Scc.Lower.Accepted2 p = true) (hown : Room2OwnStmt h hp)
    (hrc : Room2CalleeStmt h hp) (hlc : Lim2CalleeStmt h hp)
    {Dt : State → Prop} {J : InvS}
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) {R : Region} {F : MachineData → Prop}
    {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isa}
    (hcx : CxG2M h hp Dt J j R F fs fp ra tp G0 Ab)
    {D : Int} (hDe : (rbR R).lo = -((FC j d hd).fr.size : Int) - 8 - D)
    {g : String} {q : CallG} {frm : TermRun.Frame} {F' : MachineData → Prop}
    (hF' : FStable (calleeR (rbR R) (FC j d hd).fr.size D) F')
    (hCF : CalleeF2 p (fun _ => none) (fun _ => 0) (FC j d hd).fr (rbR R) F D fp ra (imms2Me Λ p) (TailAt2 p j)
      q frm F')
    (hex : ∃ c x a e, G0 c ∧ TailAt2 p j (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
      CallTo p c q.cE frm)
    (hsite : CallSite2F p (fun _ => none) (fun _ => 0) (FC j d hd).lcx (FC j d hd).fr (CD ra)
      ((FC j d hd).Bl ra) G0 (TailAt2 p j) (_root_.Executable.labels (LY0).exe).label (imms2Me Λ p)
      (RetLk d.retTy) g q (rbR R) D fp ra frm F')
    {j' : Nat} {dg : Decl} (hd' : (compiled2 p)[j']? = some dg) (hf : p.find? (·.name == g) = some dg) :
    CxG2 h hp Dt J j' (calleeR (rbR R) (FC j d hd).fr.size D) F' (frm :: fs) q.fp q.ra tp
      (fun c => FrameRunM p (q.cE, frm :: fs) (c, frm :: fs)) Ab := by
  have hc := hcx.1
  have hR := hc.hR
  have hl := hc.hl
  have h16 := (FC j d hd).h16
  have hgn : dg.name = g := by simpa using List.find?_some hf
  obtain ⟨-, -, -, -, -, -, -, x, a, e, -, -, -, -, -, -, -, -, -, hT, -, -, -, -, -, hcl, -⟩ := id hsite
  have hx : (Scc.Frontend.externs p).find? (·.1 == g) = none := by
    have e1 := (fnCode2OfPMe_spec hp h Λ j d hd).1
    have := hcl.1
    rw [e1] at this
    exact this
  have hrow := hown j d hd 256 ((rbR R).lo - 8) (hc.room d hd)
  have hD0 : 0 ≤ D := by omega
  have hD8 : D % 8 = 0 := by omega
  have hlo : (rbR R).lo ≤ -((FC j d hd).fr.size : Int) - 8 - D := by omega
  have hcall : ∃ c, G0 c ∧ CallTo p c q.cE frm := by
    obtain ⟨c, -, -, -, hc0, -, -, hct⟩ := hex
    exact ⟨c, hc0, hct⟩
  have hnb : ¬ HasNewBuf2 p j' := by
    rintro ⟨y, cn, τ, e', hn⟩
    exact Spike.Lib.LowerNode.callee_noNewBuf hp hd (hT d hd) hx hf (hn dg hd')
  have hroom : ∀ dg', (compiled2 p)[j']? = some dg' →
      NeedRoomX (OUT).place.need (Scc.Lower.Names.user dg'.name) 256 (-D) := by
    intro dg' hdg'
    rw [hd'] at hdg'
    cases hdg'
    obtain ⟨-, -, -, -, -, hr⟩ := hrc j d hd x g a e 256 ((rbR R).lo - 8) hT hcl (hc.room d hd)
    have e2 : (rbR R).lo - 8 + ((FC j d hd).fr.size : Int) + 16 = -D := by omega
    rw [e2] at hr
    rw [hgn]
    exact hr
  have hD : 8 ≤ D := by
    have := hown j' dg hd' 256 (-D) (hroom dg hd')
    omega
  have hlim : ∀ m, F' m → ∀ dg', (compiled2 p)[j']? = some dg' →
      LimRoomX (OUT).place.need (Scc.Lower.Names.user dg'.name) (((MSS J) []).G ⟨limA tp, 8⟩)
        ((rbR R).base.toNat - (FC j d hd).fr.size - 8) := by
    intro m hm dg' hdg'
    rw [hd'] at hdg'
    cases hdg'
    have hb := hR.lo
    rw [hgn]
    exact hlc j d hd x g a e _ ((rbR R).base.toNat + 8) ((rbR R).base.toNat - (FC j d hd).fr.size - 8) hT hcl
      (by omega) (hc.lim m (hCF m hm).1 d hd)
  have core := CxCore2.call h hp hc hd hD hD8 hlo hF' hCF hcall hroom hlim
    (fun dg' hdg' s lo hr => hown j' dg' hdg' s lo hr) hnb
  exact ⟨⟨core, hcx.2⟩, List.cons_ne_nil _ _⟩

/-- **The callee's context at a plain call** (`CxOkS.callSite` at
`CxG2M.callG2`): from the caller's context with its records at the `j`th
compiled block, the same call site and the call's `callq` returning to
`q.ra`: the callee's context with the caller's record pushed. -/
theorem CxOkS.callG2 (hp : Scc.Lower.Accepted2 p = true) (hown : Room2OwnStmt h hp)
    (hrc : Room2CalleeStmt h hp) (hlc : Lim2CalleeStmt h hp)
    {Dt : State → Prop} {J : InvS} {Bot : StkKey → List TermRun.Frame → Prop}
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) {R : Region} {F : MachineData → Prop}
    {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isa}
    (hcx : CXS j R F fs fp ra tp G0 Ab)
    (hra : Spike.Lib.X64.PhRec.ph LY0 (Int64.ofBitVec ra).toBitVec.toNat =
      Spike.Lib.X64.PhRec.ph LY0 ((LY0).lab raL).toBitVec.toNat)
    {D : Int} (hDe : (rbR R).lo = -((FC j d hd).fr.size : Int) - 8 - D)
    {g : String} {q : CallG} {frm : TermRun.Frame} {F' : MachineData → Prop}
    (hF' : FStable (calleeR (rbR R) (FC j d hd).fr.size D) F')
    (hCF : CalleeF2 p (fun _ => none) (fun _ => 0) (FC j d hd).fr (rbR R) F D fp ra (imms2Me Λ p) (TailAt2 p j)
      q frm F')
    (hex : ∃ c x a e, G0 c ∧ TailAt2 p j (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
      CallTo p c q.cE frm)
    (hbl : ∃ pcB zc k, (FC j d hd).Bl ra pcB zc (Scc.Lower.Names.user g) k ∧
      q.ra = (pcB + Int64.ofNat zc).toBitVec)
    (hsite : CallSite2F p (fun _ => none) (fun _ => 0) (FC j d hd).lcx (FC j d hd).fr (CD ra)
      ((FC j d hd).Bl ra) G0 (TailAt2 p j) (_root_.Executable.labels (LY0).exe).label (imms2Me Λ p)
      (RetLk d.retTy) g q (rbR R) D fp ra frm F')
    {j' : Nat} {dg : Decl} (hd' : (compiled2 p)[j']? = some dg) (hf : p.find? (·.name == g) = some dg) :
    CXS j' (calleeR (rbR R) (FC j d hd).fr.size D) F' (frm :: fs) q.fp q.ra tp
      (fun c => FrameRunM p (q.cE, frm :: fs) (c, frm :: fs)) Ab := by
  have hc := hcx.1.1.1
  have hl := hc.hl
  have h16 := (FC j d hd).h16
  obtain ⟨-, -, -, -, -, -, -, x, a, e, -, -, -, -, -, -, -, -, -, hT, -, -, -, -, -, hcl, -⟩ := id hsite
  have hx : (Scc.Frontend.externs p).find? (·.1 == g) = none := by
    have e1 := (fnCode2OfPMe_spec hp h Λ j d hd).1
    have := hcl.1
    rw [e1] at this
    exact this
  have hint : dg.retTy = .int := Spike.Lib.LowerNode.callee_int hp hd (hT d hd) hx hf
  have hfty : frm.ty = .int := by
    obtain ⟨c, x1, a1, e1, -, -, hterm, x', f', a', e', d', t', ws', hct, hfd, -, -, hfr⟩ := hex
    subst hfr
    rw [hterm] at hct
    cases hct
    rw [hf] at hfd
    cases hfd
    exact hint
  have hrow := hown j d hd 256 ((rbR R).lo - 8) (hc.room d hd)
  have hD0 : 0 ≤ D := by omega
  have hD8 : D % 8 = 0 := by omega
  have hlo : (rbR R).lo ≤ -((FC j d hd).fr.size : Int) - 8 - D := by omega
  exact CxOkS.callSite hd hcx hra hsite hD0 hD8 hlo hF' hCF hbl
    (CxG2M.callG2 h hp hown hrc hlc hd hcx.1.1 hDe hF' hCF hex hsite hd' hf) rfl rfl rfl (fun _ h => h)
    ⟨dg, hd', hint⟩ hfty

/-- **The callee's context premises at a plain call** (`CalleePre2` at the
callee's block `j'`, region `calleeR (rbR R) size D` below the caller's
frame and saved `%rbp` at the caller's depth `D`, the call's frame pushed,
saved pair, entry control and the entry invariant `calleeJSO`), from the
caller's base context at any frames (`CxG2M`): its context `hcx'` (with
some records), the return address in the caller's return address's
phase (`raOk_of_blC2L`), the blocks inside `W2` in the callee's rebased
region (`cxBlk2_ofW2`, the return address a position off the write abort,
`posOff_ra_of_blC2L`, the branch targets from `tgOkB`), its abort node's
states the base context's aborts (`AbG2`), the prologue's edge
(`proEdge2_ofCallee`, the limit bound from the callee's limit room covering
its frame and saved `%rbp`, 16-aligned at an entry `%rsp` `8` past a
16-aligned address, `LimOk2Stmt`); the prologue inside `W2` a premise
(`hpro`). -/
theorem calleePre2_callG2M (hp : Scc.Lower.Accepted2 p = true) (hown : Room2OwnStmt h hp)
    (hlok : LimOk2Stmt h hp)
    (htg : tgOkB OP = true)
    {Dt : State → Prop} {J : InvS} {Bot : StkKey → List TermRun.Frame → Prop}
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) {R : Region} {F : MachineData → Prop}
    {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isa}
    (hcx : CxG2M h hp Dt J j R F fs fp ra tp G0 Ab)
    (hra : Spike.Lib.X64.PhRec.ph LY0 (Int64.ofBitVec ra).toBitVec.toNat =
      Spike.Lib.X64.PhRec.ph LY0 ((LY0).lab raL).toBitVec.toNat)
    {D : Int} (hDe : (rbR R).lo = -((FC j d hd).fr.size : Int) - 8 - D)
    {g : String} {q : CallG} {frm : TermRun.Frame} {F' : MachineData → Prop}
    (hF' : FStable (calleeR (rbR R) (FC j d hd).fr.size D) F')
    (hex : ∃ c x a e, G0 c ∧ TailAt2 p j (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
      CallTo p c q.cE frm)
    (hav : ArgV (fun _ => none) q)
    (hbl : ∃ pcB zc k, (FC j d hd).Bl ra pcB zc (Scc.Lower.Names.user g) k ∧
      q.ra = (pcB + Int64.ofNat zc).toBitVec)
    (hsite : CallSite2F p (fun _ => none) (fun _ => 0) (FC j d hd).lcx (FC j d hd).fr (CD ra)
      ((FC j d hd).Bl ra) G0 (TailAt2 p j) (_root_.Executable.labels (LY0).exe).label (imms2Me Λ p)
      (RetLk d.retTy) g q (rbR R) D fp ra frm F')
    {j' : Nat} {dg : Decl} (hd' : (compiled2 p)[j']? = some dg) (hf : p.find? (·.name == g) = some dg)
    (hpro : XProW (fun s c => (W2S J) s c (frm :: fs)) (KT) (LY0).exe (LY0).endPc
      (calleeR (rbR R) (FC j d hd).fr.size D) F' ((MSS J) (frm :: fs))
      ((_root_.Executable.labels (LY0).exe).label (FC j' dg hd').fn) (Int64.ofInt (FC j' dg hd').fr.size)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL (FC j' dg hd').fr) (FC j' dg hd').zl (FC j' dg hd').zf
      (FC j' dg hd').z1 (FC j' dg hd').z2 (FC j' dg hd').zs (FC j' dg hd').ps
      (calleeJSO (calleeR (rbR R) (FC j d hd).fr.size D) F' (_root_.Executable.labels (LY0).exe).label
        g tp q))
    (hcx' : CXS j' (calleeR (rbR R) (FC j d hd).fr.size D) F' (frm :: fs) q.fp q.ra tp
      (fun c => FrameRunM p (q.cE, frm :: fs) (c, frm :: fs)) Ab) :
    CalleePre2 (W2S J) (KT) p (fun _ => none) (fun _ => 0) (MSS J) (CXS j') (FC j' dg hd')
      (calleeR (rbR R) (FC j d hd).fr.size D) F' (frm :: fs) q.fp q.ra tp
      (fun c => FrameRunM p (q.cE, frm :: fs) (c, frm :: fs)) Ab
      (calleeJSO (calleeR (rbR R) (FC j d hd).fr.size D) F' (_root_.Executable.labels (LY0).exe).label
        g tp q) q.cE := by
  haveI := (LY0).valid
  have hc' := hcx'.1.1.1
  have hc := hcx.1
  have hR := hc.hR
  have hl := hc.hl
  have hhi := hc.hhi
  have h16 := (FC j d hd).h16
  have h16' := (FC j' dg hd').h16
  obtain ⟨pcB, zcB, kB, hB, hqB⟩ := hbl
  rw [(fnCode2OfPMe_spec hp h Λ j d hd).2.1] at hB
  obtain ⟨c, x1, a1, e1, -, hT1, hterm, hct⟩ := hex
  obtain ⟨ws, hcE⟩ := cE_of_callTo hct hterm hf
  obtain ⟨-, -, -, -, -, -, -, x, a, e, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcl, -⟩ := id hsite
  have hx : (Scc.Frontend.externs p).find? (·.1 == g) = none := by
    have e1 := (fnCode2OfPMe_spec hp h Λ j d hd).1
    have := hcl.1
    rw [e1] at this
    exact this
  have hint : dg.argTy = .int := Spike.Lib.LowerNode.callee_argInt hp hd (hT1 d hd) hx hf
  have hna : (FC j' dg hd').na = 1 := by
    obtain ⟨w, hlow, hna, -, -⟩ := fnCode2OfPMe_spec2 hp h Λ j' dg hd'
    have hv := hlow.1
    rw [hint] at hv
    have hv1 : Scc.Obj.valWords .int = some 1 := rfl
    rw [hv1] at hv
    rw [hna]
    exact (Option.some.inj hv).symm
  -- the callee's region and its rebased one
  have hrow := hown j d hd 256 ((rbR R).lo - 8) (hc.room d hd)
  have hD0 : 0 ≤ D := by omega
  have hRc : (calleeR (rbR R) (FC j d hd).fr.size D).OK := calleeR_ok hR hD0 (by omega) (by omega)
  have hloD : (calleeR (rbR R) (FC j d hd).fr.size D).lo = -D := by simp only [calleeR, Region.callee]
  have hhiD : (calleeR (rbR R) (FC j d hd).fr.size D).hi = 8 := by simp only [calleeR, Region.callee]
  have hown' := hown j' dg hd' 256 _ (hc'.room dg hd')
  have hloR : (rbR (calleeR (rbR R) (FC j d hd).fr.size D)).lo = -D + 8 := by
    simp only [rbR, calleeR, Region.callee]
  rw [hloR] at hown'
  have hb := rbR_base hRc (by omega) (by omega)
  have hal' := hc'.hal
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (imms2Me Λ p) (rS := rS0 (Ly))
  have hraP : PosOff OP (_root_.Executable.labels (LY0).exe).label (Int64.ofBitVec q.ra) :=
    posOff_ra_of_blC2L (FC j d hd).hp hB hqB
  have hWs := cxBlk2_ofW2 (rd := IsNum)
    (G := Spike.Lib.X64.PhRec.GOf (Ly) (Spike.Lib.X64.PhRec.m0Of (Ly).Λ OP (OUT).secs))
    (ar := Spike.Lib.X64.Rt.arOf (Ly).Λ)
    (J := Spike.Lib.AllocReach.IN (Spike.Lib.X64.Rt.arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) (Dt := Dt)
    (lbl := fun _ => none) (lsize := fun _ => 0) (fs := frm :: fs) (fp := q.fp) (ra := q.ra)
    hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h)
    (Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp) (FC j' dg hd').hf (FC j' dg hd').h1
    hc'.hFS hc'.hR hc'.hR8 (by rw [hloR]; omega) hc'.hhi hc'.hl hc'.hh (Spike.Lib.X64.Rt.rS0_sub (Ly))
    (Spike.Lib.X64.Rt.fitS_of_sub (Ly) (Spike.Lib.X64.Rt.rS0_sub (Ly))) hc'.hFO hc'.hfp hc'.hG0F
    (Cd := CD q.ra) (fun _ _ h => h) hraP
    (hTg_of_tgOkB htg (fun _ _ h => h) _)
  refine
    { hcx := hcx'
      hra := raOk_of_blC2L hB hra hqB
      hF := hF'
      hR := hRc
      hlo := by rw [hloD]; omega
      hhi := by rw [hhiD]; omega
      hG0 := hc'.hG0
      hW := hWs.1
      hWp := hWs.2
      hab := fun c0 hg s c' hAt => hcx.2 s c' (frm :: fs)
        ⟨j', dg, hd', _, F', frm :: fs, q.fp, q.ra, tp, _, hc', .inl ⟨rfl, c0, hg, hAt⟩⟩
      hg0 := .refl _
      hpro := hpro
      hedge := ?_ }
  have henv : (FC j' dg hd').env = Spike.Lib.LowerShape.env2 dg 1 := by rw [(FC j' dg hd').henv, hna]
  obtain ⟨zs, hs⟩ := (FC j' dg hd').hsp
  rw [hna] at hs
  refine proEdge2_ofCallee (FC j' dg hd') hint henv (FC j' dg hd').hlits hs hav hcE (fun σ c' hJ => hJ.1) ?_
  rintro σ c' ⟨hJ, hso, m, hm⟩
  have htpσ : σ.regs.fsBase = TP0 := by rw [hJ.2.2.2.2, hc'.htp]
  have hun : ∀ m, F' m → Mem.loadInt m.dmem (limA (TP0)) 8 = none := by
    have := hc'.hun
    rw [hc'.htp] at this
    exact this
  have hsp : σ.regs.rsp.toBitVec = (calleeR (rbR R) (FC j d hd).fr.size D).base := by
    have := hso .rsp 0 rfl
    simpa [Region.addr, Reg64s.get64] using this
  have hL := LimRoomX.frame (hc'.lim m hm dg hd') (fun s lo h => hown j' dg hd' s lo h)
  rw [hc'.htp] at hL
  refine hlok J F' (frm :: fs) σ (FC j' dg hd').fr.size htpσ hun fun v hv => ?_
  have hv16 := Spike.Lib.X64.PhRec.g16_ofPlaceOK h (imms2Me Λ p) v (by
    revert hv
    rw [Spike.Lib.X64.Rt.pinA_lab0]
    dsimp only [MSAt]; generalize ab2 p _ = ab; cases ab <;> exact fun h' => h')
  have hLv := hL v hv
  rw [hsp]
  refine limRoom_sub_frame (FC j' dg hd').h1 ?_
  omega

/-- **The callee's context premises at a plain call under a context with
its records** (`calleePre2_callG2M` at `CxOkS.callG2`). -/
theorem calleePre2_callG2 (hp : Scc.Lower.Accepted2 p = true) (hown : Room2OwnStmt h hp)
    (hrc : Room2CalleeStmt h hp) (hlc : Lim2CalleeStmt h hp) (hlok : LimOk2Stmt h hp)
    (htg : tgOkB OP = true)
    {Dt : State → Prop} {J : InvS} {Bot : StkKey → List TermRun.Frame → Prop}
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) {R : Region} {F : MachineData → Prop}
    {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isa}
    (hcx : CXS j R F fs fp ra tp G0 Ab)
    (hra : Spike.Lib.X64.PhRec.ph LY0 (Int64.ofBitVec ra).toBitVec.toNat =
      Spike.Lib.X64.PhRec.ph LY0 ((LY0).lab raL).toBitVec.toNat)
    {D : Int} (hDe : (rbR R).lo = -((FC j d hd).fr.size : Int) - 8 - D)
    {g : String} {q : CallG} {frm : TermRun.Frame} {F' : MachineData → Prop}
    (hF' : FStable (calleeR (rbR R) (FC j d hd).fr.size D) F')
    (hCF : CalleeF2 p (fun _ => none) (fun _ => 0) (FC j d hd).fr (rbR R) F D fp ra (imms2Me Λ p) (TailAt2 p j)
      q frm F')
    (hex : ∃ c x a e, G0 c ∧ TailAt2 p j (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
      CallTo p c q.cE frm)
    (hav : ArgV (fun _ => none) q)
    (hbl : ∃ pcB zc k, (FC j d hd).Bl ra pcB zc (Scc.Lower.Names.user g) k ∧
      q.ra = (pcB + Int64.ofNat zc).toBitVec)
    (hsite : CallSite2F p (fun _ => none) (fun _ => 0) (FC j d hd).lcx (FC j d hd).fr (CD ra)
      ((FC j d hd).Bl ra) G0 (TailAt2 p j) (_root_.Executable.labels (LY0).exe).label (imms2Me Λ p)
      (RetLk d.retTy) g q (rbR R) D fp ra frm F')
    {j' : Nat} {dg : Decl} (hd' : (compiled2 p)[j']? = some dg) (hf : p.find? (·.name == g) = some dg)
    (hpro : XProW (fun s c => (W2S J) s c (frm :: fs)) (KT) (LY0).exe (LY0).endPc
      (calleeR (rbR R) (FC j d hd).fr.size D) F' ((MSS J) (frm :: fs))
      ((_root_.Executable.labels (LY0).exe).label (FC j' dg hd').fn) (Int64.ofInt (FC j' dg hd').fr.size)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL (FC j' dg hd').fr) (FC j' dg hd').zl (FC j' dg hd').zf
      (FC j' dg hd').z1 (FC j' dg hd').z2 (FC j' dg hd').zs (FC j' dg hd').ps
      (calleeJSO (calleeR (rbR R) (FC j d hd).fr.size D) F' (_root_.Executable.labels (LY0).exe).label
        g tp q)) :
    CalleePre2 (W2S J) (KT) p (fun _ => none) (fun _ => 0) (MSS J) (CXS j') (FC j' dg hd')
      (calleeR (rbR R) (FC j d hd).fr.size D) F' (frm :: fs) q.fp q.ra tp
      (fun c => FrameRunM p (q.cE, frm :: fs) (c, frm :: fs)) Ab
      (calleeJSO (calleeR (rbR R) (FC j d hd).fr.size D) F' (_root_.Executable.labels (LY0).exe).label
        g tp q) q.cE :=
  calleePre2_callG2M h hp hown hlok htg hd hcx.1.1 hra hDe hF' hex hav hbl hsite hd' hf hpro
    (CxOkS.callG2 h hp hown hrc hlc hd hcx hra hDe hF' hCF hex hbl hsite hd' hf)

end G1Pre

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.CxG2M.callG2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.CxG2M.callG2

/-- info: 'Spike.Lib.LowerX64.CxOkS.callG2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.CxOkS.callG2

/-- info: 'Spike.Lib.LowerX64.calleePre2_callG2M' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.calleePre2_callG2M

/-- info: 'Spike.Lib.LowerX64.calleePre2_callG2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.calleePre2_callG2
