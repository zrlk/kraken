/-
**`main`'s call at the bare start from `main`'s segment** (AArch64): for
an `Accepted2` program without a setup block, `scc_rt_main` is `bareMC`
and calls `main` (a unit parameter, an `Int` result) directly, the ghost
control the source's start `c0` (`main`'s tail call on the unit), one
local step before `main`'s body. The producer is the setup call's
(`mainCallWSF_ofPlaceOKHVC`, `Spike/Lib/LowerA64/HeldPostA.lean`) at the
entry `uN0`: `uN0` is `uNM` at the arguments `fun c _ => c = c0`, so
`main`'s call is a `MainCallWSF` there, with `main`'s held exits
(`heldTailCX_ofV`) returning to `bareMC.e0 + 4` (`sp0`, off the write
abort).

- `mainSig_bare2`: without a setup block `main` takes the unit and
  returns `Int`;
- `frOk2_c0`, `placedS_c0`, `slotRepAt_c0`: the start control `c0` is free
  of `ZBad`, placed at no place, and placed in any slot file;
- `proEdge2_ofMain0`: the prologue's edge into `main`'s body at `uNM`'s
  invariant at the ghost `c0` (`start_step_main` before `entry2U_njB`);
- `posOff_bareRa`: the return address `bareMC.e0 + 4` off the write abort;
- `mainCallWSF_ofPlaceOKHVC0`: `main`'s call at `UPostRF ∧ Q` from the
  placement check at any code facts, the arguments `fun c _ => c = c0`;
- `limS_bare`, `mainCx2_bare`: `main`'s limit room and context facts
  `MainCx2` at its callee region below the first stack's top;
- `mainCallWSF_bareSeg`: `main`'s call at `WordsNone ∧ swFSL` from
  `MainSeg2`.
-/
import Spike.Lib.LowerA64.G1MainStmt
import Spike.Lib.LowerA64.G1NoSetupBounds
import Spike.Lib.LowerA64.ProEdge2UN0
import Spike.Lib.LowerA64.UserCall
import Spike.Lib.LowerA64.StkOfA
import Spike.Lib.Src.HeldLit2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.LowerNode
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow.Ret0
open Scc.Sem (Range ValRep)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.A64ConsumerS (InvS)
open Spike.Lib.A64.Rt (RuntimeLayout bareMC MainCallWSF rS0 arOf swFSL rtF)

/-! ## `main` and the start control -/

/-- **Without a setup block `main` takes the unit and returns `Int`**
(`main2` at `setupOf p = none`). -/
theorem mainSig_bare2 {p : Prog} (hp : Scc.Lower.Accepted2 p = true) (hs : Scc.Lower.setupOf p = none) {d : Decl}
    (hfd : p.find? (·.name == "main") = some d) : d.argTy = .unit ∧ d.retTy = .int := by
  have hds : Scc.Lower.decls2 [] (Scc.Lower.setupOf p) (Scc.Lower.hasPrint p) p = true := by
    simp only [Scc.Lower.Accepted2, Bool.and_eq_true] at hp; exact hp.1.1.1.1.1.1.1.2
  have hn : d.name = "main" := by simpa using List.find?_some hfd
  obtain ⟨E', hE'⟩ := decl2_of_decls2 hds d (List.mem_of_find?_eq_some hfd)
  have hpe : Scc.Lower.isPrintExt d = false := by simp [Scc.Lower.isPrintExt, hn]
  have hnl : (Scc.Lower.hasPrint p && "main" == "printL") = false := by
    rw [show ("main" == "printL") = false by decide, Bool.and_false]
  simp only [Scc.Lower.decl2, hpe, hn, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true] at hE'
  rw [hnl] at hE'
  simp only [Bool.false_eq_true, ↓reduceIte] at hE'
  unfold Scc.Lower.main2 at hE'
  rw [hs] at hE'
  simp only [Bool.and_eq_true, beq_iff_eq] at hE'
  exact ⟨hE'.1.2, hE'.1.1.2⟩

/-- **The start control is free of `ZBad`** (a tail call), at no frame. -/
theorem frOk2_c0 : FrOk2 Spike.Lib.A64Consumer.c0 [] :=
  ⟨trivial, fun _ h => nomatch h⟩

/-- Every word list of the start control's environment is empty. -/
theorem c0_words {x : String} {ty : Ty} {ws : List TermRun.Word}
    (h : TermRun.lookupE Spike.Lib.A64Consumer.c0.env x = some (ty, ws)) : ws = [] := by
  by_cases hx : x = "a"
  · subst hx
    simp [Spike.Lib.A64Consumer.c0, TermRun.lookupE] at h
    exact h.2
  · have hx' : ("a" == x) = false := by simp; exact Ne.symm hx
    simp [Spike.Lib.A64Consumer.c0, TermRun.lookupE, List.find?, hx'] at h

/-- **The start control is placed at depth 0**, at no place (its one
variable binds no word). -/
theorem placedS_c0 {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} :
    PlacedS Λ lbl s Spike.Lib.A64Consumer.c0 [] := by
  refine ⟨fun _ _ _ => none, fun _ _ _ _ _ _ _ _ _ _ _ he => by simp at he, fun d env xs hd _ x _ ty ws hl k hk => ?_,
    fun _ _ _ _ _ _ he => by simp at he⟩
  cases d with
  | zero =>
    simp only [envsOf, List.getElem?_cons_zero, Option.some.injEq] at hd
    subst hd
    rw [c0_words hl] at hk
    cases hk
  | succ d => simp [envsOf] at hd

/-- **The start control placed in any slot file** (`SlotRepAt` at the
symbolic environment binding `a` to the unit at no place). -/
theorem slotRepAt_c0 {i : Expr → String → Nat → Option Nat} {lbl : WeakMem.AllocLabel → Option Nat}
    {rs : Scc.IR.Reg → Option Int} {sl : Int → BitVec 64} :
    SlotRepAt i lbl rs sl Spike.Lib.A64Consumer.c0 := by
  have hl : ∀ x, Spike.Lib.Form.lookupS [("a", .unit, [])] x = if x = "a" then some (.unit, []) else none := by
    intro x
    by_cases hx : x = "a"
    · subst hx; rfl
    · have hx' : ("a" == x) = false := by simp; exact Ne.symm hx
      simp [Spike.Lib.Form.lookupS, List.find?, hx', hx]
  refine ⟨[("a", .unit, [])], fun x t pls hx => ?_, fun y hy => ?_, fun y _ ty pls hy b o hb => ?_,
    fun x k v hx => ?_⟩
  · rw [hl] at hx
    split at hx
    · next he =>
      subst he
      cases hx
      exact ⟨[], rfl, trivial⟩
    · cases hx
  · have : y = "a" := by simpa [Spike.Lib.A64Consumer.c0, Scc.Sem.exprFv, atVars] using hy
    subst this
    rfl
  · rw [hl] at hy
    split at hy
    · cases hy; cases hb
    · cases hy
  · rw [hl] at hx
    split at hx <;> simp at hx

/-! ## The prologue's edge at the start control -/

section Edge

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {exe : _root_.Executable} {prog : List Directive} {endPc : Int64}

/-- **The prologue's edge into `main`'s body at the start control**
(`ProEdge2` at `uNM`'s invariant at the arguments `c = c0`, one entry
control `cP`, any `J` within it): for `main`'s code block `d` (`hfd`) with a
unit parameter (`hu`) of no words (`hna`), the room `ZU` the frame
(`hZU`), the limit word's facts `uNM` holds at its memory side `ms0` and
frame condition `F` carried to the edge's `ms1` and `F'` (`hms`, `hFF`):
the ghost `c0` steps once (`start_step_main`) to `main`'s body at its
entry node (`entry2U_njB`), and is placed in any slot file
(`slotRepAt_c0`). -/
theorem proEdge2_ofMain0 {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (c : FnCode2 exe prog endPc RaOk Cd i T d) (hu : d.argTy = .unit)
    (hfd : p.find? (·.name == "main") = some d) (hna : c.na = 0)
    {g : WcG} {lab : Label → Int64} {ms0 ms1 : MemSide isaLSE2} {F F' : MachineData → Prop} {fn : Label}
    {ZU : Int64} (hZU : ZU = Int64.ofInt c.cx.frame)
    (hms : ∀ a Z, LimOk ms0 F exe endPc a Z → LimOk ms1 F exe endPc a Z) (hFF : ∀ m, F' m → F m)
    {cP : Ctl} {J : AS → Ctl → Prop}
    (hJ : ∀ σ c', J σ c' → (Spike.Lib.A64.Rt.uNM lab ms0 F exe endPc fn ZU
      (fun c _ => c = Spike.Lib.A64Consumer.c0 ∧ c = cP) g).J σ c') :
    ProEdge2 p lbl lsize ms1 F' c g.fp g.ra g.tp cP J := by
  have hs := c.hsp
  rw [hna] at hs
  refine proEdge2_ofSpills (na := 0) c hs fun σ c' hJσ => ?_
  obtain ⟨⟨⟨rfl, hcP⟩, hfp, hra, hsp, htp⟩, hlim⟩ := hJ σ c' hJσ
  subst hcP
  have hl := (hms _ _ hlim).mono hFF
  have hl' := limOk_tpidr (σ := σ) htp hl
  rw [← hsp, hZU] at hl'
  refine ⟨⟨hl'.rt, hl'.mp, hl'.unmapped, hl'.room⟩, hfp, hra, htp, .refl _, fun sl _ _ => ?_⟩
  have henv0 : ([(d.arg, TermRun.close [] d.argTy, [])] : TermRun.Env) = [(d.arg, d.argTy, [])] := by
    rw [hu]; rfl
  have hst := start_step_main (p := p) hfd
  rw [henv0] at hst
  rw [c.henv, hna, c.hlits]
  exact ⟨⟨fun _ => False, #[], 0, NJB.pre (.single hst) (entry2U_njB (B := 0) hu rfl rfl rfl)⟩, slotRepAt_c0⟩

end Edge

/-- **The bare return address is off the write abort**: `bareMC.e0 + 4` is
`sp0` (`mainRetU_eq`), off the write abort (`posOff_mainRetU`). -/
theorem posOff_bareRa (Lr : RuntimeLayout) (hin : Spike.Lib.A64.Rt.mainUIn Lr.prog bareMC = true) :
    PosOff Lr.prog Lr.lab (Int64.ofBitVec (Lr.lab bareMC.e0 + 4).toBitVec) := by
  have he := mainRetU_eq Lr.lays hin
  have h4 : Int64.ofNat (4 * 1) = 4 := rfl
  rw [h4] at he
  rw [Int64.ofBitVec_toBitVec, ← he]
  exact posOff_mainRetU hin

/-! ## `main`'s call from the placement check -/

section Place

open Spike.Lib.A64Consumer (K0)
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

include hp in
/-- **`main`'s call without a setup block from the placement check, its
paths held, at `UPostRF ∧ Q`, at any code facts of the check's output**
(the bare twin of `mainCallWSF_ofPlaceOKHVC`): `MainCallWSF` at the
arguments `fun c _ => c = c0` (the entry `uN0` at the ghost `c0`), the
return address `bareMC.e0 + 4`. `main` takes the unit (`hu`, no
parameter words `hna`); the prologue by `hpro_main_ofPlaceOK` (`c0`
placed at no place, a tail call, free of `ZBad`), its edge by
`proEdge2_ofMain0`, the held exits by `heldTailCX_ofV` at the return
address off the write abort (`posOff_bareRa`, A11's `mainUIn` at `bareMC`,
`hin`). -/
theorem mainCallWSF_ofPlaceOKHVC0 {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    {im : Expr → String → Nat → Option Nat}
    (c : FnCode2 (LY).exe (LY).prog (LY).endPc
      (fun ra => Spike.Lib.A64.PhRec.ph LY (Int64.ofBitVec ra).toBitVec.toNat =
        Spike.Lib.A64.PhRec.ph LY (Int64.ofBitVec ((LY).lab bareMC.e0 + 4).toBitVec).toBitVec.toNat)
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
    {Q : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hQ : ∀ c fs v, HeldTail c fs → HeldRd c fs → UPostRF p lbl c fs v → Q c fs v)
    (hin : Spike.Lib.A64.Rt.mainUIn OP bareMC = true)
    {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int} {ZU : Int64} {tp : UInt64}
    (hfn : fn = c.fn)
    (hL : PosOff OP (LY).lab ((LY).lab (proL c.cx)))
    (hu : d.argTy = .unit) (hfd : p.find? (·.name == "main") = some d) (hna : c.na = 0)
    (hZU : ZU = Int64.ofInt c.cx.frame)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λw) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λw.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hpN : ProgNoS ZBad p)
    (hpre : ∀ F' : MachineData → Prop, (R.callee (-Z.toInt) (-D) 0).OK →
      (R.callee (-Z.toInt) (-D) 0).base.toNat % 16 = 0 → FStable (R.callee (-Z.toInt) (-D) 0) F' →
      (∀ m, F' m → F m ∧ CallerCells R (-Z.toInt) (-D) 0 m) →
      ∀ g : WcG, g.ra = ((LY).lab bareMC.e0 + 4).toBitVec → g.tp = tp → ∀ cP : Ctl,
      FrOk2 cP [] →
      ∃ (G0 : Ctl → Prop) (Ab : FragS isaLSE2),
        CalleePre2R (WW) (Spike.Lib.A64.PhRec.K LY rS) p lbl lsize ms CxOk c rS
          (R.callee (-Z.toInt) (-D) 0) F' [] g.fp g.ra tp G0 Ab cP ∧
        CallC2R p lbl lsize c.lcx c.cx (CD g.ra)
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
    MainCallWSF (WW) (Spike.Lib.A64.PhRec.K LY rS) p lbl ms (LY).exe (LY).endPc R F fn Z D ZU
      (fun c _ => c = Spike.Lib.A64Consumer.c0) (fun c fs v => UPostRF p lbl c fs v ∧ Q c fs v)
      ((LY).lab bareMC.e0 + 4).toBitVec tp := by
  refine mainCallWSF_ofHeldV (lsize := lsize) (CxOk := CxOk) c hint hok
    (fun _ ht => contNR_tailAt2 hd hok ht) hfn hQ
    fun F' hR0 hal hF' hFF g hra htp cP hcP => ?_
  obtain ⟨-, rfl⟩ := hcP
  obtain ⟨G0, Ab, hP, hcall, hlane, hbuf, hprint, hcallH, hprintH, hAb⟩ :=
    hpre F' hR0 hal hF' hFF g hra htp _ frOk2_c0
  refine ⟨G0, Ab, Spike.Lib.A64Consumer.c0, hP.toPre ?_ ?_ ?_, hcall, hlane, hbuf, hprint, ?_, hAb⟩
  · show _ = _
    rw [hra]
  · exact hpro_main_ofPlaceOK h c hcPro hL (fun _ _ h => h)
      hP.hR hP.hal hP.hlo hP.hhi hP.hl hP.hh (htp ▸ hmr)
      (fun m hm => htp ▸ hun m (hFF m hm).1) hsub hfit hP.hFO hpN
      (fun c regs hc' s _ => by obtain ⟨rfl, -⟩ := hc'; exact placedS_c0)
      (fun c regs hc' a he => by obtain ⟨rfl, -⟩ := hc'; cases he)
      (fun c regs hc' => by obtain ⟨rfl, -⟩ := hc'; exact frOk2_c0)
  · have he := proEdge2_ofMain0 (lbl := lbl) (lsize := lsize) c hu hfd hna (g := g)
      (lab := (_root_.Executable.labels (LY).exe).label) (ms0 := ms []) (ms1 := ms [])
      (F := F) (F' := F') (fn := fn) hZU (fun _ _ h => h)
      (fun m hm => (hFF m hm).1) (cP := Spike.Lib.A64Consumer.c0) (fun _ _ h => h)
    rwa [htp] at he
  exact heldTailCX_ofV hpN (Spike.Lib.A64.PhRec.instOk_ofPlaceOK h _) (printIn_of_placeOKAt h)
    (abortIn_of_placeOKAt h) c.hf c.h1
    c.h16 hP.hF hP.hR hP.hal hP.hlo hP.hhi hP.hl hP.hh hsub hfit hP.hFO
    (fun _ _ h => CdCLE.toCdCL h)
    (by rw [hra]; exact posOff_bareRa LY hin)
    c.hfrm hcallH hprintH (fun _ _ _ h => h) fun x g is a ts k hT hn => by
      obtain ⟨rfl, his⟩ := hlitP x g is a ts k (hT d hd)
      rw [hlcx] at hn
      rw [heldLit_print hp hd (hT d hd) hn] at his
      cases his

end Place

/-! ## `main`'s call from `main`'s segment -/

section Generic

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))

set_option hygiene false in
/-- The record's static memory. -/
local notation "M0" => Spike.Lib.A64.PhRec.m0Of (Ly).Λ OP (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).secs

set_option hygiene false in
/-- `W2At` at `Closed2AtA`'s instance. -/
local notation "W2S" J:max => W2At h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum (rS0 (Ly)) J Dt (fun _ => 0)

set_option hygiene false in
/-- `MSAt` at `Closed2AtA`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max => MSAt h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The first TCB's address. -/
local notation "X0" => pinA (Ly).lab + 0#64 + 8#64

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => UInt64.ofBitVec (X0)

set_option hygiene false in
/-- The switch region's frame condition, below the top `v`. -/
local notation "FS" v:max => swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) v

set_option hygiene false in
/-- The switch region's frame condition with `WordsNone`, below the top `v`
(`Closed2AtWA`'s start frame carried to `scc_rt_main`). -/
local notation "FWS" v:max => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧ (FS v) m

set_option hygiene false in
/-- `main`'s code (`fnCode2OfPMe`'s choice, at the theorem's immediates). -/
local notation "FC" => fnCode2OfPMe hp h Λ j d hd

set_option hygiene false in
/-- `main`'s callee region below the first stack's top, at the room `D`. -/
local notation "RCT" D:max => (swR (TOP) (-L) 0).callee (-bareMC.Z.toInt) (-D) 0

set_option hygiene false in
/-- The ghosts at `main`'s frame: the controls a frame run reaches from the entry control `cP` at no frame. -/
local notation "GM" cP:max => fun c => Spike.Lib.FrameRunM p (cP, []) (c, [])

/-- **`main`'s limit room at `main`'s callee region without a setup block**
(`MainCx2.lim`, the twin of `limS_main`): `main`'s need `n` is at most
`12240` (`mainRowBareA`), so above the limit `stacksA + 4096` or the limit
word's initial `0` the need fits below the callee region's base
`TOP - 48`. -/
theorem limS_bare (hp : Scc.Lower.Accepted2 p = true) (hs : Scc.Lower.setupOf p = none)
    (hcfg : CfgNeedOkA pcfg = true) {L D : Int} (hL0 : 0 ≤ L) (hLm : L ≤ 16384) (hD0 : 0 ≤ D)
    (hLZ : bareMC.Z.toInt + D ≤ L) (J : InvS) :
    LimRoomA (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need (Scc.Lower.Names.user "main")
      (((MSS J) []).G ⟨limA (TP0), 8⟩) (RCT D).base.toNat := by
  have hZ := bareZ_toInt
  obtain ⟨l, f, n, hr, -, hn⟩ := mainRowBareA h hp hs hcfg
  refine ⟨l, f, n, hr, fun w hw => ?_⟩
  -- the callee region's base: `TOP - 48`
  have hok : (swR (TOP) (-L) 0).OK := by
    rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hLm
  have hb := Region.callee_base (kc := -bareMC.Z.toInt) (lo' := -D) (hi' := 0) hok
    (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
  have htop : ((swR (TOP) (-L) 0).base.toNat : Int) = (Ly).stacksA.toNat + 16384 := by
    show ((TOP).toNat : Int) = _
    rw [show stacksA (Ly).lab = (Ly).stacksA from (Ly).lab_stacks, Spike.Lib.A64.Rt.top0_toNat]; rfl
  have hw' : Spike.Lib.A64.PhRec.GOf Ly M0 ⟨(Ly).pinA + 16#64, 8⟩ w := by
    revert hw
    rw [(Ly).lab_pin, Spike.Lib.A64.Rt.limA_tcb0]
    dsimp only [MSAt]; generalize ab2 p _ = ab; cases ab <;> exact fun h' => h'
  have := (Ly).pool_fit
  obtain ⟨h1, h2⟩ := (Ly).stacks_sub
  simp only at h1 h2
  rcases Spike.Lib.A64.PhRec.gOf_lim hw' with rfl | rfl
  · have hv : ((Spike.Lib.A64.PhRec.limV (Ly)).setWidth 64).toNat = (Ly).stacksA.toNat + 4096 := by
      simp only [Spike.Lib.A64.PhRec.limV, BitVec.setWidth_setWidth_of_le _ (by decide : 64 ≤ 128),
        BitVec.setWidth_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    rw [hv]
    omega
  · have hv : (((M0).initVal ⟨(Ly).pinA + 16#64, 8⟩).setWidth 64).toNat = 0 := by
      rw [Spike.Lib.A64.PhRec.limInit_ofPlaceOK h (imms2Me Λ p)]
      rfl
    rw [hv]
    omega

/-- **`main`'s context facts at its callee region without a setup block**
(`MainCx2` at the bare start's `main` call, below the first stack's top;
the twin of `mainCx2_setup`): the region's facts from the call's premises
(`stackOff_callee`), `WordsNone` and the limit word's freedom from the frame
condition, the return address `bareMC.e0 + 4` off the write abort
(`posOff_bareRa`, `mainUIn_bare2A`), the room from `nM + 48 + 208 ≤ D` and
the limit room by `limS_bare`. -/
theorem mainCx2_bare (hp : Scc.Lower.Accepted2 p = true) (hs : Scc.Lower.setupOf p = none)
    (hcfg : CfgNeedOkA pcfg = true) {L D : Int} {lM : String} {nM fM : Nat}
    (hrM : Scc.Cert.NeedA64.row? (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need
      (Scc.Lower.Names.user "main") = some (lM, fM, nM)) (hnM : (nM : Int) + 48 + 208 ≤ D)
    (hL0 : 0 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0) (hD0 : 0 ≤ D) (hD8 : D % 8 = 0)
    (hLZ : bareMC.Z.toInt + D ≤ L) {F' : MachineData → Prop} {g : WcG}
    (hok' : (RCT D).OK) (h16 : (RCT D).base.toNat % 16 = 0) (hst : FStable (RCT D) F')
    (hFF : ∀ m, F' m → (FWS (TOP)) m ∧ CallerCells (swR (TOP) (-L) 0) (-bareMC.Z.toInt) (-D) 0 m)
    (hra : g.ra = ((Ly).lab bareMC.e0 + 4).toBitVec) (htp : g.tp = TP0) :
    MainCx2 h (RCT D) F' g.ra g.tp := by
  have hZ := bareZ_toInt
  refine
    { hR := hok'
      hal := h16
      hl := by show (-D) % 8 = 0; omega
      hh := by show (0 : Int) % 8 = 0; rfl
      hhi := Int.le_refl _
      hFS := hst
      hFO := fun m hm => ?_
      hwn := fun m hm => (hFF m hm).1.1
      hraP := by rw [hra]; exact posOff_bareRa (Ly) (mainUIn_bare2A h hp hs)
      hraK := by rw [hra]; rfl
      htp := htp
      hun := fun m hm => by rw [htp]; exact (hFF m hm).1.2.1.2
      room := ⟨lM, fM, nM, hrM, by show -D ≤ _; omega⟩
      lim := fun m hm J => ?_ }
  · obtain ⟨⟨-, -, hoff⟩, hcc⟩ := hFF m hm
    have hok : (swR (TOP) (-L) 0).OK := by
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hLm
    have h8 : (swR (TOP) (-L) 0).base.toNat % 8 = 0 := by
      show (TOP).toNat % 8 = 0
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; have := Spike.Lib.A64.Rt.rt_h16 (Ly); omega
    exact Spike.Lib.A64.Flow.Ret0.Inst.stackOff_callee hok h8 (by show (-L) % 8 = 0; omega)
      (by show (0 : Int) % 8 = 0; rfl)
      (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega) (by omega) hoff hcc
  · rw [htp]
    exact limS_bare h hp hs hcfg hL0 hLm hD0 hLZ J

/-- **`main`'s call at `WordsNone ∧ swFSL` from `main`'s segment without a
setup block** (the bare twin of `mainCallWSF_ofMainSeg2F`): off the first
stack's top no state is in the frame condition; at it,
`mainCallWSF_ofPlaceOKHVC0` at `main`'s code facts from the placement check
and `Accepted2` (`main` takes the unit and returns `Int`, held returns from
`mainRetOk`), the callee frame's context facts `MainCx2` by
`mainCx2_bare`, and `CalleePre2R` and the constructs' segments from
`MainSeg2` at the ghosts `GM cP`. The bounds are `Bounds0A`'s. -/
theorem mainCallWSF_bareSeg {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true)
    (hs : Scc.Lower.setupOf p = none) (hm : Scc.Lower.mainRetOk p = true) (hcfg : CfgNeedOkA pcfg = true)
    {L D : Int} {lM : String} {fM nM : Nat}
    (hrM : Scc.Cert.NeedA64.row? (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need
      (Scc.Lower.Names.user "main") = some (lM, fM, nM)) (hnM : (nM : Int) + 48 + 208 ≤ D)
    (hrowM : ∀ f fi, (f, fi) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx → f.checkStack = true →
      f.name = Scc.Lower.Names.user "main" →
        (Scc.Cert.Code1A64.ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi f).frame = fM)
    (hL0 : 0 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0) (hD0 : 0 ≤ D) (hD8 : D % 8 = 0)
    (hLZ : bareMC.Z.toInt + D ≤ L) (J : InvS) (HM : MainSeg2 h hp Dt J) (v : BitVec 64) :
    MainCallWSF (W2S J) (KT) p (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (swR v (-L) 0) (FWS v)
      bareMC.fn bareMC.Z D (Int64.ofInt (fM : Int)) (fun c _ => c = Spike.Lib.A64Consumer.c0)
      (fun c fs v => UPostRF p (fun _ => none) c fs v ∧ MainCtlV (lay2 Λ p) (fun _ => none) c fs v)
      ((Ly).lab bareMC.e0 + 4).toBitVec TP0 := by
  -- off the first stack's top, no state is in the switch region's frame condition (`swF`)
  refine (Classical.em (v = TOP)).elim (fun hv => ?pos) (fun hv => ?neg)
  case neg =>
    intro F' _ _ _ hFF _ _ _
    refine ⟨fun _ _ _ => False, fun s c fs hP => ?_, fun _ _ _ h => h.elim, fun _ _ _ h => h.elim⟩
    obtain ⟨⟨-, -, -, -, σ, -, hF, -⟩, -⟩ := hP
    exact hv (hFF _ hF).1.2.1.1
  subst hv
  obtain ⟨d, hfd⟩ : ∃ d, p.find? (·.name == "main") = some d := by
    obtain ⟨jm, dm, hdm, hnm⟩ := Spike.Lib.LowerNode.main_compiled2_ofAccepted2 hp
    have hm' : p.any (·.name == "main") = true := by
      simp only [Scc.Lower.Accepted2, Bool.and_eq_true] at hp; exact hp.1.1.1.1.1.1.1.1.2
    exact Option.isSome_iff_exists.mp
      (List.find?_isSome.mpr (List.any_eq_true.mp hm') : (p.find? (·.name == "main")).isSome)
  obtain ⟨hu, hint⟩ := mainSig_bare2 hp hs hfd
  obtain ⟨j, hd, hdn⟩ := Spike.Lib.LowerNode.main_compiled2 hfd
  have hok : Scc.Lower.heldRetOk d.body = true := by simpa [Scc.Lower.mainRetOk, hfd] using hm
  have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
  obtain ⟨w, fi, hLw, hna, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  have hna0 : (FC).na = 0 := by
    rw [hna]
    have := hLw.1
    rw [hu] at this
    exact (Option.some.inj this).symm
  have hZU : Int64.ofInt (fM : Int) = Int64.ofInt (FC).cx.frame := by
    rw [hcx, hrowM _ _ hmem rfl (by show Scc.Lower.Names.user d.name = _; rw [hdn])]
  have hpos : PosOff OP (Ly).lab ((Ly).lab (proL (FC).cx)) := by
    obtain ⟨w, fi, -, -, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
    have hok := Scc.Cert.Code1A64.fnOk1_of_fnCode1Ok (fnCode1_of_placeOKAt h (lowerAll_place_ir cfg p)) hmem rfl
    have hab : proL (FC).cx ∉ Spike.Lib.A64.AllocG.abLabs := by
      unfold proL; exact local_not_abLabs (fnCode2OfPMe_spec hp h Λ j d hd).2.2.1 _
    rw [hcx] at hab ⊢
    exact posOff_proL_of_fnOk1 hok hab _
  refine mainCallWSF_ofPlaceOKHVC0 (CxOk := fun _ _ _ _ _ _ _ _ => True) hp h hd (FC)
    (fnCode2OfPMe_spec hp h Λ j d hd).2.2 (fnCode2OfPMe_spec hp h Λ j d hd).1 hint
    hok (hlitP_of_mainRetOk hm hfd) (fun _ _ _ => mainCtlV_held) (mainUIn_bare2A h hp hs)
    (by rw [(FC).hfn, hdn]; rfl) hpos hu hfd hna0 hZU ?_
    (fun m hm => hm.2.1.2) hsub (Spike.Lib.A64.Rt.fitS_of_sub _ hsub) (progNoS_zbad_of_accepted2 hp) ?_
  · rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.limA_tcb0]
    exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1
  · intro F' hok' h16 hst hF g hra htp cP hcP
    have hC := mainCx2_bare h hp hs hcfg hrM hnM hL0 hLm hL8 hD0 hD8 hLZ hok' h16 hst hF hra htp
    obtain ⟨Ab, hab, hC2, hL, hN, hP, hCH, hPH, hA⟩ := HM j d hd hdn _ F' g cP hC hcP
    rw [htp] at hab hC2 hL hN hP hCH hPH
    exact ⟨GM cP, Ab, hab, hC2, hL, hN, hP, hCH, hPH, hA⟩

end Generic

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.mainSig_bare2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.mainSig_bare2

/-- info: 'Spike.Lib.LowerA64.frOk2_c0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.frOk2_c0

/-- info: 'Spike.Lib.LowerA64.c0_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.c0_words

/-- info: 'Spike.Lib.LowerA64.placedS_c0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.placedS_c0

/-- info: 'Spike.Lib.LowerA64.slotRepAt_c0' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.slotRepAt_c0

/-- info: 'Spike.Lib.LowerA64.proEdge2_ofMain0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.proEdge2_ofMain0

/-- info: 'Spike.Lib.LowerA64.posOff_bareRa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.posOff_bareRa

/-- info: 'Spike.Lib.LowerA64.mainCallWSF_ofPlaceOKHVC0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.mainCallWSF_ofPlaceOKHVC0

/-- info: 'Spike.Lib.LowerA64.limS_bare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.limS_bare

/-- info: 'Spike.Lib.LowerA64.mainCx2_bare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.mainCx2_bare

/-- info: 'Spike.Lib.LowerA64.mainCallWSF_bareSeg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.mainCallWSF_bareSeg
