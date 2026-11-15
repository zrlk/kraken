/-
**`main`'s call at the bare start from the placement check** (x86-64): for
an `Accepted2` program without a setup block, `scc_rt_main` is `bareMC`
and calls `main` (a unit parameter, an `Int` result) directly, the ghost
control the source's start `c0` (`main`'s tail call on the unit), one
local step before `main`'s body. The producer is the setup call's
(`mainCallWSF_ofPlaceOKHMVCR`, `Spike/Lib/LowerX64/HeldPostXV.lean`) at
the arguments `fun c _ => c = c0`, the prologue's edge discharged here
(`proEdge2_ofMain0`), `main`'s held exits (`heldTailCX_mainV`) returning to
`bareMC.sp0`, the return point of `call fn`, off the write abort
(`posOff_mainRetU`).

- `frOk2_c0`, `placedS_c0`, `slotRepAt_c0`: the start control `c0` is free
  of `ZBad`, placed at no place, and placed in any slot file;
- `proEdge2_ofMain0`: the prologue's edge into `main`'s body at `uNM`'s
  invariant at the ghost `c0` (`start_step_main` before `entry2U_njB`);
- `mainCallWSF_ofPlaceOKHMVCR0`: `main`'s call at `UPostRF ∧ MainCtlV` from
  the placement check at any code facts, the arguments `fun c _ => c = c0`,
  its context premises given every edge.
-/
import Spike.Lib.LowerX64.HeldPostXV
import Spike.Lib.LowerX64.ProEdge2Of
import Spike.Lib.LowerX64.LimOk0
import Spike.Lib.LowerX64.UserCall
import Spike.Lib.LowerX64.MainRetPos
import Spike.Lib.Src.Entry2U

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64
open Scc.Lower.InvX64
open Spike.Lib.LowerNode
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64.Flow.Ret0 (StackOff WcG CallerCells LimOk limA)

/-! ## The start control -/

/-- **The start control is free of `ZBad`** (a tail call), at no frame. -/
theorem frOk2_c0 : FrOk2 Spike.Lib.X64Consumer.c0 [] :=
  ⟨trivial, fun _ h => nomatch h⟩

/-- Every word list of the start control's environment is empty. -/
theorem c0_words {x : String} {ty : Ty} {ws : List TermRun.Word}
    (h : TermRun.lookupE Spike.Lib.X64Consumer.c0.env x = some (ty, ws)) : ws = [] := by
  by_cases hx : x = "a"
  · subst hx
    simp [Spike.Lib.X64Consumer.c0, TermRun.lookupE] at h
    exact h.2
  · have hx' : ("a" == x) = false := by simp; exact Ne.symm hx
    simp [Spike.Lib.X64Consumer.c0, TermRun.lookupE, List.find?, hx'] at h

/-- **The start control is placed at depth 0**, at no place (its one
variable binds no word). -/
theorem placedS_c0 {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} :
    PlacedS Λ lbl s Spike.Lib.X64Consumer.c0 [] := by
  refine ⟨fun _ _ _ => none, fun _ _ _ _ _ _ _ _ _ _ _ he => by simp at he,
    fun d env xs hd _ x _ ty ws hl k hk => ?_, fun _ _ _ _ _ _ he => by simp at he⟩
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
    SlotRepAt i lbl rs sl Spike.Lib.X64Consumer.c0 := by
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
  · have : y = "a" := by simpa [Spike.Lib.X64Consumer.c0, Scc.Sem.exprFv, atVars] using hy
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
  {exe : _root_.Executable} {cells : List (Directive × Nat)} {endPc : Int64}

/-- **The prologue's edge into `main`'s body at the start control**
(`ProEdge2` at `uNM`'s invariant at the arguments `c = c0`, one entry
control `cP`, any `J` within it): for `main`'s code block `d` (`hfd`) with a
unit parameter (`hu`) of no words (`hna`), the room `ZU` the frame
(`hZU`), the limit word's facts `uNM` holds at its memory side `ms0` and
frame condition `F` carried to the edge's `ms1` and `F'` (`hms`, `hFF`):
the ghost `c0` steps once (`start_step_main`) to `main`'s body at its
entry node (`entry2U_njB`), and is placed in any slot file
(`slotRepAt_c0`). -/
theorem proEdge2_ofMain0 {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (c : FnCode2 exe cells endPc RaOk Cd i T d) (hu : d.argTy = .unit)
    (hfd : p.find? (·.name == "main") = some d) (hna : c.na = 0)
    {g : WcG} {lab : Label → Int64} {ms0 ms1 : MemSide isa} {F F' : MachineData → Prop} {fn : Label}
    {ZU : Int64} (hZU : ZU = Int64.ofInt c.fr.size)
    (hms : ∀ a Z, LimOk ms0 F a Z → LimOk ms1 F a Z) (hFF : ∀ m, F' m → F m)
    {cP : Ctl} {J : AS → Ctl → Prop}
    (hJ : ∀ σ c', J σ c' → (Spike.Lib.X64.Rt.uNM lab ms0 F fn ZU
      (fun c _ => c = Spike.Lib.X64Consumer.c0 ∧ c = cP) g).J σ c') :
    ProEdge2 p lbl lsize ms1 F' c g.fp g.ra g.tp cP J := by
  obtain ⟨zs, hsp⟩ := c.hsp
  refine proEdge2_ofSpills c hsp fun σ c' hJσ => ?_
  obtain ⟨⟨⟨rfl, hcP⟩, hfp, hra, hsp', htp⟩, hlim⟩ := hJ σ c' hJσ
  subst hcP
  have hl := (hms _ _ hlim).mono hFF
  have hl' := limOk_fsBase (σ := σ) htp hl
  rw [← hsp', hZU] at hl'
  refine ⟨⟨hl'.rt, hl'.mp, hl'.unmapped, hl'.room⟩, hfp, hra, htp, .refl _, fun sl _ _ => ?_⟩
  have henv0 : ([(d.arg, TermRun.close [] d.argTy, [])] : TermRun.Env) = [(d.arg, d.argTy, [])] := by
    rw [hu]; rfl
  have hst := start_step_main (p := p) hfd
  rw [henv0] at hst
  rw [c.henv, hna, c.hlits]
  exact ⟨⟨fun _ => False, #[], 0, NJB.pre (.single hst) (entry2U_njB (B := 0) hu rfl rfl rfl)⟩, slotRepAt_c0⟩

end Edge

/-! ## `main`'s call from the placement check -/

section Place

open Scc.Sem (Range ValRep)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64Consumer (K0)
open Spike.Lib.X64ConsumerS (InvS)
open Spike.Lib.X64.Rt (RuntimeLayout bareMC)

variable {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
  {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

local notation "LY" => RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)

set_option hygiene false in
/-- `W2` at the record's instance (`mainCallWSF_ofPlaceOKHMVCR`'s). -/
local notation "WW" => fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
  (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs

set_option hygiene false in
/-- `main`'s code at the return address `ra` (`fnCode2OfP`'s code predicate). -/
local notation "CD" ra:max => CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab
  (Int64.ofBitVec ra)

set_option hygiene false in
/-- `main`'s callee region below `scc_rt_main`'s frame `Z` at the room `D`. -/
local notation "RC" => R.callee (-8 - Z.toInt - 8 - 0) (-D) 8

include hp in
/-- **`main`'s call without a setup block from the placement check, its
paths held, at `UPostRF ∧ MainCtlV`, at any code facts of the check's
output** (the bare twin of `mainCallWSF_ofPlaceOKHMVCR`): `MainCallWSF` at
the arguments `fun c _ => c = c0`, the return address `bareMC.sp0` (the
phase anchor `raL`). `main` takes the unit (`hu`, no parameter words
`hna`); the context premises are asked given each edge (`hpre`'s first
conjunct), the edge by `proEdge2_ofMain0`; the prologue by
`hpro_main_ofPlaceOK` (`c0` placed at no place, a tail call, free of
`ZBad`); the held exits by `heldTailCX_mainV` at the return address off the
write abort (`posOff_mainRetU`, `mainUIn` at `bareMC`, `hin`). -/
theorem mainCallWSF_ofPlaceOKHMVCR0 {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
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
    {Λv : Scc.Sem.Layout}
    (hin : Spike.Lib.X64.Rt.mainUIn OP bareMC = true)
    {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int} {ZU : Int64} {tp : UInt64}
    (hfn : fn = c.fn)
    (hL : PosOff OP (LY).lab ((LY).lab (proL c.fr)))
    (hu : d.argTy = .unit) (hfd : p.find? (·.name == "main") = some d) (hna : c.na = 0)
    (hZU : ZU = Int64.ofInt c.fr.size)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λw) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λw.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hpN : ProgNoS ZBad p)
    (hpre : ∀ F' : MachineData → Prop, (RC).OK → FStable (RC) F' →
      (∀ m, F' m → F m ∧ CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m) →
      ∀ g : WcG, g.ra = ((LY).lab bareMC.sp0).toBitVec → g.tp = tp → (RC).base = g.sp →
      ∃ (G0 : Ctl → Prop) (Ab : FragS isa),
        (∀ JE : AS → Ctl → Prop, ProEdge2 p lbl lsize (ms []) F' c g.fp g.ra tp Spike.Lib.X64Consumer.c0 JE →
          CalleePre2R (WW) (Spike.Lib.X64.PhRec.K LY rS) p lbl lsize ms CxOk c rS (RC) F' [] g.fp g.ra tp G0 Ab
            JE Spike.Lib.X64Consumer.c0) ∧
        CallC2R p lbl lsize c.lcx c.fr (CD g.ra) (c.Bl g.ra) (LY).exe (LY).endPc (rbR (RC)) F' (WW)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 im (TailAt2 p j) Ab (RetLk d.retTy) ∧
        LaneC p lbl lsize c.lcx c.fr (CD g.ra) (c.Bl g.ra) (LY).exe (LY).endPc (rbR (RC)) F' (WW)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 im (TailAt2 p j) Ab ∧
        NewBufC p lbl lsize c.lcx c.fr (CD g.ra) (c.Bl g.ra) (LY).exe (LY).endPc (rbR (RC)) F' (WW)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 im (TailAt2 p j) Ab (RetLk d.retTy) ∧
        PrintCallC p lbl lsize c.lcx c.fr (CD g.ra) (c.Bl g.ra) (LY).exe (LY).endPc (rbR (RC)) F' (WW)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 im (TailAt2 p j) Ab ∧
        CallC2H p lbl lsize c.lcx c.fr (CD g.ra) (c.Bl g.ra) (LY).exe (LY).endPc (rbR (RC)) F' (WW)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 im (TailAt2 p j) Ab (RetLk d.retTy) ∧
        PrintCallCH p lbl lsize c.lcx c.fr (CD g.ra) (c.Bl g.ra) (LY).exe (LY).endPc (rbR (RC)) F' (WW)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 im (TailAt2 p j) Ab ∧
        SegWS (WW) (Spike.Lib.X64.PhRec.K LY rS) p lbl ms Ab (fun _ _ _ => False)) :
    Spike.Lib.X64.Rt.MainCallWSF (WW) (Spike.Lib.X64.PhRec.K LY rS) p lbl ms (LY).exe (LY).endPc R F fn Z D ZU
      (fun c _ => c = Spike.Lib.X64Consumer.c0) (fun c fs v => UPostRF p lbl c fs v ∧ MainCtlV Λv lbl c fs v)
      ((LY).lab bareMC.sp0).toBitVec tp := by
  refine mainCallWSF_ofHeldV (lsize := lsize) (CxOk := CxOk) c hint hok
    (fun _ ht => contNR_tailAt2 hd hok ht) hfn (fun _ _ _ => mainCtlV_held)
    fun F' hR0 hF' hFF g hra htp hbase cP hcP => ?_
  obtain ⟨_, rfl⟩ := hcP
  obtain ⟨G0, Ab, hP, hcall, hlane, hbuf, hprint, hcallH, hprintH, hAb⟩ := hpre F' hR0 hF' hFF g hra htp hbase
  have he := proEdge2_ofMain0 (lbl := lbl) (lsize := lsize) c hu hfd hna (g := g)
    (lab := (_root_.Executable.labels (LY).exe).label) (ms0 := ms []) (ms1 := ms [])
    (F := F) (F' := F') (fn := fn) hZU (fun _ _ h => h)
    (fun m hm => (hFF m hm).1) (cP := Spike.Lib.X64Consumer.c0) (fun _ _ h => h)
  rw [htp] at he
  have hP1 := hP _ he
  have hP2 := hP1.toPre (by rw [hra, Int64.ofBitVec_toBitVec]; rfl)
    (hpro_main_ofPlaceOK h c hcPro hL (fun _ _ h => h)
      hP1.hR hP1.hR8 hP1.hlo (by have := hP1.hhi; omega) hP1.hl hP1.hh (htp ▸ hmr)
      (fun m hm => htp ▸ hun m (hFF m hm).1) hsub hfit hP1.hFO hpN
      (fun c regs hc' s _ => by obtain ⟨rfl, -⟩ := hc'; exact placedS_c0)
      (fun c regs hc' a he => by obtain ⟨rfl, -⟩ := hc'; cases he)
      (fun c regs hc' => by obtain ⟨rfl, -⟩ := hc'; exact frOk2_c0))
  refine ⟨G0, Ab, Spike.Lib.X64Consumer.c0, hP2, hcall, hlane, hbuf, hprint, ?_, hAb⟩
  have hlo := hP1.hlo
  have hhi := hP1.hhi
  obtain ⟨hF2, hR2, hlo2, hhi2⟩ := rbR_facts hP1.hF hP1.hR hlo hhi
  have hb := rbR_base hP1.hR (by omega) (by omega)
  have hR8 := hP1.hR8
  have hl := hP1.hl
  have hh := hP1.hh
  have hR8' : (rbR (RC)).base.toNat % 8 = 0 := by omega
  exact heldTailCX_mainV hpN (Spike.Lib.X64.PhRec.instOk_ofPlaceOK h _) (printIn_of_placeOKAt h)
    (abortIn_of_placeOKAt h) c.hf c.h1 hF2 hR2 hR8' hlo2
    hhi2 (by have e : (rbR (RC)).lo = (RC).lo + 8 := rfl; omega)
    (by have e : (rbR (RC)).hi = (RC).hi + 8 := rfl; omega) hsub hfit
    (fun m hm => stackOff_rbR hP1.hR (by omega) (by omega) (hP1.hFO m hm)) (fun _ _ h => CdCLE.toCdCL h)
    (by rw [hra]; exact posOff_mainRetU hin)
    c.hfrm hcallH hprintH (fun _ _ _ h => h) fun x g is a ts k hT hn => by
      obtain ⟨rfl, his⟩ := hlitP x g is a ts k (hT d hd)
      rw [hlcx] at hn
      rw [heldLit_print hp hd (hT d hd) hn] at his
      cases his

end Place

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.slotRepAt_c0' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.slotRepAt_c0

/-- info: 'Spike.Lib.LowerX64.proEdge2_ofMain0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.proEdge2_ofMain0

/--
info: 'Spike.Lib.LowerX64.mainCallWSF_ofPlaceOKHMVCR0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainCallWSF_ofPlaceOKHMVCR0
