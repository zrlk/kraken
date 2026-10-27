/-
**The premises at the contexts from the placement check** (AArch64, H7a
calls): `fnSpecC_all_ofPre`'s (`Spike/Lib/LowerA64/ProgCB.lean`) `CallPre`
and `CalleePre` at the code blocks' contexts `CxOkC`
(`Spike/Lib/LowerA64/CtxC.lean`) for an `Accepted1` program passing
`placeOKAt`, at the runtime layout `RuntimeLayout.ofPlaceOK h (imms1Of p)`,
for code facts with no frames limit (`CodeFactsS`, plain calls); the twin of
`Spike/Lib/LowerX64/PreC.lean`.

- `limBv_of_le`: a limit room in the prologue's form;
- `argTy_callee`: a callee's argument is an `Int`;
- `callPre_of`: a code block's `CallPre` at a context, at the callee room
  `D := -R.lo - frame` (all of the region below the frame), from the plain
  calls (`callPreC_of`) with the call's blocks inside `BodyWS0`
  (`CallBlkW`);
- `calleePre_of`: a callee's `CalleePre` at a call from a context;
- `fnSpecC_all_ofPlaceOK`: every code block's `FnSpecC` at its contexts.

Where AArch64 differs from x86-64: no return address or saved frame
pointer between the caller's frame and the callee's entry `sp` (no rebased
region), the callee's region `R.callee (-frame) (-D) 0` starts at the
frame's bottom, and the frame is `ctxOf`'s at the code block's index past
the runtime's `rt` (so `CodeFactsS` takes `rt`).
-/
import Spike.Lib.LowerA64.MainC
import Spike.Lib.LowerA64.CallC

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Cert.Code1A64 (ctxOf)
open Scc.Lower.Inv (Res1 func1 params1R env1)
open Spike.Lib.LowerNode (Pairwise2 LowC funcs1)
open Spike.Lib.A64ConsumerS (msOfS)
open Spike.Lib.A64.Rt (RuntimeLayout bareMC)
open Spike.Lib.A64.PhRec (μ K)
open Spike.Lib.A64Consumer (noRetBlk)

/-- **A limit room in the prologue's form**: with `x + f` at most `sp`
(`f` small), `x` is at most `sp - f`. -/
theorem limBv_of_le {f : Nat} (hf : f < 2 ^ 63) {sp : BitVec 64} {x : Nat} (h : x + f ≤ sp.toNat) :
    x ≤ (sp - (Int64.ofInt f).toBitVec).toNat := by
  have hf' : (Int64.ofInt f).toBitVec.toNat = f := by
    rw [Int64.toBitVec_ofInt, BitVec.toNat_ofInt]
    omega
  have := sp.isLt
  simp only [BitVec.toNat_sub, hf']
  omega

/-- **A called code block's argument is an `Int`**: the callee `g` of a
call at a point of an `Accepted1` code block's walk is not `main`
(`body1_call_walkC`), so its declared argument is an `Int` (`decl1`). -/
theorem argTy_callee {p : Prog} (hp : Scc.Lower.Accepted1 p = true) {j : Nat} {d : Decl} (hd : p[j]? = some d)
    {frames : Option Nat} {e : Expr} (hT : InWalkD frames d e) {x g : String} {a : At} {e' : Expr}
    (he : e = .let_ x (.call g [] a []) e') {j' : Nat} {dg : Decl} (hd' : p[j']? = some dg)
    (hname : dg.name = g) : dg.argTy = .int := by
  obtain ⟨q, hq, hqe⟩ := hT
  have hp' := hp
  simp only [Scc.Lower.Accepted1, Bool.and_eq_true, decide_eq_true_eq] at hp'
  have hd1 := Spike.Lib.LowerCallOrder.decl1_of_decls1 hp'.1.2 hd
  simp only [Scc.Lower.decl1, Bool.and_eq_true, beq_iff_eq] at hd1
  have hc := (Spike.Lib.LowerCallOrder.body1_call_walkC _ _ _ _ _ hd1.2 q hq x g [] a [] e' (hqe.trans he)).1
  simp only [Scc.Lower.callee1, Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
  have hg1 := Spike.Lib.LowerCallOrder.decl1_of_decls1 hp'.1.2 hd'
  simp only [Scc.Lower.decl1, Bool.and_eq_true, beq_iff_eq] at hg1
  have := hg1.1.2
  simpa [hname, hc.2] using this

section Pre

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog}

set_option quotPrecheck false

/-- The lowering's output. -/
local notation "O" => Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)

/-- The runtime's layout of the output, at the lowering's immediates. -/
local notation "Ly" h => RuntimeLayout.ofPlaceOK h (Scc.Lower.imms1Of p)

/-- The value invariant: the first TCB's limit word holds its loaded value or the limit. -/
local notation "G0" h:max => Spike.Lib.A64.PhRec.GOf (Ly h) (Spike.Lib.A64.PhRec.m0Of (Ly h).Λ (O).prog (O).secs)

/-- The placement's memory side at the frames. -/
local notation "MSS" h:max => msOfS (Ly h).Λ (μ (Ly h)) (fun _ => True) (G0 h)
  (fun s _ => Spike.Lib.A64.PhRec.own (Ly h) s) (Ly h).Λ.static (fun _ => 0)

/-- The body's facts at the frames, the consumer's start held back. -/
local notation "WS" h:max cells:max => BodyWS0 (Ly h).Λ (μ (Ly h)) p (Spike.Lib.A64.PhRec.own (Ly h))
  (Spike.Lib.A64.Rt.rS0 (Ly h)) (Spike.Lib.A64.PhRec.Tk (Ly h)) (Ly h).Λ.static cells 0 Spike.Lib.A64Consumer.c0

/-- The outside move: the take of the first stack. -/
local notation "KS" h => K (Ly h) (Spike.Lib.A64.Rt.rS0 (Ly h))

/-- The aborts of the code blocks at their contexts. -/
local notation "AbS" h:max hcode:max => AbC p (O).place.need (Ly h).Λ (Ly h).Λ.static (MSS h)
  (Spike.Lib.A64.Rt.rS0 (Ly h)) hcode

/-- The return addresses in the phase of the one after `scc_rt_main`'s `bl`. -/
local notation "RaOkS" h => fun ra : BitVec 64 => Spike.Lib.A64.PhRec.ph (Ly h) (Int64.ofBitVec ra).toBitVec.toNat =
  Spike.Lib.A64.PhRec.ph (Ly h) (Int64.ofBitVec ((Ly h).lab bareMC.e0 + 4).toBitVec).toBitVec.toNat

/-- The code predicate at a return address. -/
local notation "CdS" h => fun ra : BitVec 64 => CdC (O).prog (Spike.Lib.A64.PhRec.okPc (Ly h))
  (Spike.Lib.A64.PhRec.ph (Ly h)) (Ly h).lab (Int64.ofBitVec ra)

/-- **A code block's `CallPre` at a context**: for the `j`th code block
`d` of an `Accepted1` program with code facts with no frames limit
(`CodeFactsS`, its closed form `rs[j]`), at a context of `CtxB` with a
return address with `RaOk`, at the `Good1` ghosts with no hold, the callee
room `D := -R.lo - frame` (the region below the frame; the region's room
from the code block's, `ownRoom_of_placeOK`): `callPreC_of` with the calls'
code (`cdOf_blC`), the call's blocks inside `BodyWS0` (the argument's load
and the result's store, `blkW_bodySC`; the `bl`, `blkW_bl`; the callee's
entry from its code facts, `nodeW_calleeEntry_ofCode`) and the calls
without index or type arguments (`body1_call_walkC`). -/
theorem callPre_of (hp : Scc.Lower.Accepted1 p = true) {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true)
    {rs : List Res1} {rt : List Scc.IR.Func} (hrs : Pairwise2 (LowC p cfg.layout.obj none) p rs)
    (hir : (Scc.Lower.A64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    {cells : Nat} {T : Nat → Expr → Prop} (hT : ∀ j d, p[j]? = some d → ∀ e, T j e → InWalkD none d e)
    (hcode : ∀ j d, p[j]? = some d →
      FnCode (Ly h).exe (Ly h).prog (Ly h).endPc (RaOkS h) (CdS h) (Scc.Lower.imms1Of p) (T j) d)
    (hok : ∀ j d (hd : p[j]? = some d), CodeFactsS h rs rt (hcode j d hd) j)
    {j : Nat} {d : Decl} (hd : p[j]? = some d) {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame}
    {tp : UInt64} {fp ra : BitVec 64} {Ab : FragS isaLSE2}
    (hc : CtxB p (O).place.need (Ly h).Λ (Ly h).Λ.static (MSS h) (Spike.Lib.A64.Rt.rS0 (Ly h)) j R F fs tp)
    (hra : (RaOkS h) ra) :
    CallPre (WS h cells) (KS h) p (Ly h).Λ.static (MSS h) (hcode j d hd) R F fs fp ra tp
      (fun c => Good1 p (c, fs) ∧ c.hold = none) Ab (-R.lo - ((hcode j d hd).cx.frame : Int)) := by
  obtain ⟨r, hr, hprog, hfrm, -, -, -, -, hcxe, hBl, -, -⟩ := hok j d hd
  have hown := ownRoom_of_placeOK h hrs hir hd hr (hc.room d hd)
  rw [← hcxe] at hown
  have hl8 := hc.hl8
  have hhi := hc.hhi
  have hR := hc.hR
  have hb16 := hc.hb16
  have hf := (hcode j d hd).hf
  have h1 := (hcode j d hd).h1
  have h16 := (hcode j d hd).h16
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms1Of p) (rS := Spike.Lib.A64.Rt.rS0 (Ly h))
  have hsub : (Spike.Lib.A64.Rt.rS0 (Ly h)).Sub (Ly h).Λ.stackPool := Spike.Lib.A64.Rt.rS0_sub (Ly h)
  have hfit := Spike.Lib.A64.Rt.fitS_of_sub (Ly h) hsub
  have hh8 : R.hi % 8 = 0 := by rw [hhi]; rfl
  refine callPreC_of (hcode j d hd) hfrm hprog hra (by omega) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_
  · rw [hBl]
    intro pc g k hb
    exact cdOf_blC hI.lays hI.endOk pc g k (by rw [hI.labOk]; exact hb)
  · intro n blk hcd hno hJ hcb
    have hok' : okBlk (-((hcode j d hd).cx.frame : Int)) 0 n.o blk = true := by
      rw [hno]
      rcases hcb with ⟨w, lw, hw, rfl⟩ | ⟨d', ls, hs, rfl⟩
      · exact okBlk_argLoad hf h1 h16 hw
      · exact okBlk_resStore hf h1 h16 hs
    have hnr : noRetBlk blk = true := by
      rcases hcb with ⟨w, lw, hw, rfl⟩ | ⟨d', ls, hs, rfl⟩
      · exact noRet_argLoad hf h1 hw
      · exact noRet_resStore hf h1 hs
    exact blkW_bodySC hI hR hb16 (by omega) (by omega) hl8 hh8 hsub hfit hc.hFO
      Spike.Lib.A64.Flow.Ret0.Inst.cfacts_c0 hp (good1_tail rfl) (fun σ c h => (hJ σ c h).1) hcd hok' hnr
  · intro n g k hb hno hJ
    rw [hBl] at hb
    exact blkW_bl hI hR hb16 (by omega) (by omega) hl8 hh8 hsub hfit hc.hFO
      Spike.Lib.A64.Flow.Ret0.Inst.cfacts_c0 hp (good1_tail rfl) (fun σ c h => (hJ σ c h).1) hb
  · intro g dg hfd n hpc hno hJ
    obtain ⟨j', hj', hpj⟩ := Spike.Lib.LowerNode.find_index hfd
    have hd' : p[j']? = some dg := by rw [List.getElem?_eq_getElem hj', hpj]
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hph⟩ := hok j' dg hd'
    exact nodeW_calleeEntry_ofCode hI hR hb16 (by omega) (by omega) hl8 hh8 hsub hfit hc.hFO
      Spike.Lib.A64.Flow.Ret0.Inst.cfacts_c0 hp (good1_tail rfl) hfd (hcode j' dg hd') hph hpc hno
      (fun σ c h => (hJ σ c h).1)
  · intro x g is a ts e hTe
    obtain ⟨q, hq, hqe⟩ := hT j d hd _ hTe
    have hp' := hp
    simp only [Scc.Lower.Accepted1, Bool.and_eq_true, decide_eq_true_eq] at hp'
    have hd1 := Spike.Lib.LowerCallOrder.decl1_of_decls1 hp'.1.2 hd
    simp only [Scc.Lower.decl1, Bool.and_eq_true, beq_iff_eq] at hd1
    exact (Spike.Lib.LowerCallOrder.body1_call_walkC _ _ _ _ _ hd1.2 q hq x g is a ts e hqe).2

/-- **A callee's `CalleePre` at a call from a context**: at a call of `g`
(the `j'`th code block `dg`) from the `j`th code block's context
(`CxOkC`, a return address with `RaOk`), in the callee's region below the
caller's frame at the room `D := -R.lo - frame` with the callee's frame
condition `F'` (`CalleeF`, stable): the callee's context (`CtxB.callF`, its
rooms from the call site's, `calleeRoom_of_placeOK`, `calleeLim_of_placeOK`),
the return address after the call in the phase of `ra` (`blC_ph`), the
body's blocks (`hWbS_of`, `hWsS_of`), the aborts (`CxOkC.hab`), the ghost
the entry control after the call (`good1_step`), the prologue from its code
facts (`proW_bodyS`), and the entry's facts: the limit word's from the
context (its room, `ownLim_of_placeOK`), `calleeN`'s registers, the entry
node `nj_callee` at the parameter's slot (`rsOf_param`). -/
theorem calleePre_of (hp : Scc.Lower.Accepted1 p = true) {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true)
    {rs : List Res1} {rt : List Scc.IR.Func} (hrs : Pairwise2 (LowC p cfg.layout.obj none) p rs)
    (hir : (Scc.Lower.A64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    {cells : Nat} {T : Nat → Expr → Prop} (hT : ∀ j d, p[j]? = some d → ∀ e, T j e → InWalkD none d e)
    (hcode : ∀ j d, p[j]? = some d →
      FnCode (Ly h).exe (Ly h).prog (Ly h).endPc (RaOkS h) (CdS h) (Scc.Lower.imms1Of p) (T j) d)
    (hok : ∀ j d (hd : p[j]? = some d), CodeFactsS h rs rt (hcode j d hd) j)
    {j : Nat} {d : Decl} (hd : p[j]? = some d) {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame}
    {fp ra : BitVec 64} {tp : UInt64} {Gc : Ctl → Prop} {Ab : FragS isaLSE2}
    (hcx : CxOkC p (O).place.need (Ly h).Λ (Ly h).Λ.static (MSS h) (Spike.Lib.A64.Rt.rS0 (Ly h))
      (AbS h hcode) j R F fs fp ra tp Gc Ab)
    (hra : (RaOkS h) ra) {g : String} {q : CallG} {frm : TermRun.Frame} {F' : MachineData → Prop} {j' : Nat}
    {dg : Decl} (hd' : p[j']? = some dg) (hname : dg.name = g)
    (hfd : p.find? (·.name == g) = some dg)
    (hFS : FStable (R.callee (-((hcode j d hd).cx.frame : Int)) (-(-R.lo - ((hcode j d hd).cx.frame : Int))) 0)
      F')
    (hCF : CalleeF p (Ly h).Λ.static (hcode j d hd).cx R F (-R.lo - ((hcode j d hd).cx.frame : Int)) fp ra
      (Scc.Lower.imms1Of p) (T j) q frm F')
    (hc3 : ∃ c x a e, Gc c ∧ T j (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
      CallTo p c q.cE frm)
    (harg : ArgV (Ly h).Λ.static q)
    (hbl : ∃ pcB k, (hcode j d hd).Bl ra pcB (Scc.Lower.Names.user g) k ∧ q.ra = (pcB + 4).toBitVec) :
    CalleePre (WS h cells) (KS h) p (Ly h).Λ.static (MSS h)
      (CxOkC p (O).place.need (Ly h).Λ (Ly h).Λ.static (MSS h) (Spike.Lib.A64.Rt.rS0 (Ly h))
        (AbS h hcode) j')
      (hcode j' dg hd')
      (R.callee (-((hcode j d hd).cx.frame : Int)) (-(-R.lo - ((hcode j d hd).cx.frame : Int))) 0) F'
      (frm :: fs) q.fp q.ra tp (fun c => Good1 p (c, frm :: fs) ∧ c.hold = none) Ab
      (fun σ c => (calleeN (_root_.Executable.labels (Ly h).exe).label g tp q).J σ c ∧
        σ.regs.SP.toBitVec =
          (R.callee (-((hcode j d hd).cx.frame : Int)) (-(-R.lo - ((hcode j d hd).cx.frame : Int))) 0).base)
      q.cE := by
  obtain ⟨hc, rfl, rfl⟩ := hcx
  obtain ⟨r, hr, -, hfrm, henv, hn, hrr, -, hcxe, hBl, -, -⟩ := hok j d hd
  obtain ⟨r', hr', -, -, henv', -, -, hprs', hcxe', -, -, hphP'⟩ := hok j' dg hd'
  obtain ⟨c0, x, a, e, hg0c, hTc, hct, hcall⟩ := hc3
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms1Of p) (rS := Spike.Lib.A64.Rt.rS0 (Ly h))
  -- the call's instruction and the callee's name
  obtain ⟨qw, hqw, hqe⟩ := hT j d hd _ hTc
  obtain ⟨ds, ws, hmem⟩ := Spike.Lib.LowerShape.lowerC_callMem (hcode j d hd).lcx d.body (hcode j d hd).env
    (hcode j d hd).n (hcode j d hd).l (hcode j d hd).k (hcode j d hd).r (hcode j d hd).hr qw
    (by rw [hfrm, henv, hn]; exact hqw) x g [] a [] e hqe
  rw [hrr] at hmem
  have hgp : g ∈ p.map (·.name) := by
    rw [← hname]; exact List.mem_map_of_mem (List.mem_of_find?_eq_some hfd)
  have hint : dg.argTy = .int := argTy_callee hp hd (hT j d hd _ hTc) rfl hd' hname
  -- the caller's room and the callee's
  have hown := ownRoom_of_placeOK h hrs hir hd hr (hc.room d hd)
  obtain ⟨-, -, -, -, -, -, -, D0, -, -, hlo0, hroom0⟩ :=
    calleeRoom_of_placeOK hp h hrs hir hd hr hmem hgp hc.hl8 (hc.room d hd)
  rw [← hcxe] at hown hlo0
  have hroomg := hroom0.mono (lo' := -(-R.lo - ((hcode j d hd).cx.frame : Int))) (by omega)
  have hhi := hc.hhi
  have hl8 := hc.hl8
  have hb16 := hc.hb16
  have hR := hc.hR
  have h16 := (hcode j d hd).h16
  have hRlo := hR.lo
  obtain ⟨-, -, -, -, -, -, -, hlimg⟩ := calleeLim_of_placeOK hp h hrs hir hd hr hmem hgp
    (G := ((MSS h) []).G ⟨Spike.Lib.A64.Flow.Ret0.limA tp, 8⟩) (sp := R.base.toNat)
    (sp' := R.base.toNat - (hcode j d hd).cx.frame) (by rw [← hcxe]; omega) (hc.lim d hd)
  -- the callee's context
  have hcx' := hc.callF (hcode j d hd).hf h16 (D := -R.lo - ((hcode j d hd).cx.frame : Int)) (by omega)
    (by omega) (by omega) hFS hCF
    (fun d' hd'' => by rw [hd'] at hd''; cases hd''; rw [hname]; exact hroomg)
    (fun d' hd'' => by rw [hd'] at hd''; cases hd''; rw [hname]; exact hlimg)
  have hR' := hcx'.hR
  have hl8' := hcx'.hl8
  have hhi' := hcx'.hhi
  have hb16' := hcx'.hb16
  have hown' := ownRoom_of_placeOK h hrs hir hd' hr' (hcx'.room dg hd')
  rw [← hcxe'] at hown'
  have hh8' : (R.callee (-((hcode j d hd).cx.frame : Int)) (-(-R.lo - ((hcode j d hd).cx.frame : Int))) 0).hi % 8
      = 0 := by rw [hhi']; rfl
  -- the return address
  have hra' : (RaOkS h) q.ra := by
    obtain ⟨pcB, k, hb, hq⟩ := hbl
    rw [hBl] at hb
    show _ = _
    rw [hq, Int64.ofBitVec_toBitVec]
    exact (blC_ph hb).trans hra
  -- the callee's entry control
  obtain ⟨x', f, a', e', d0, t, ws0, ht, hfd0, -, hcE, -⟩ := id hcall
  rw [hct] at ht
  cases ht
  rw [hfd] at hfd0
  cases hfd0
  have hg0 : Good1 p (q.cE, frm :: fs) ∧ q.cE.hold = none :=
    ⟨good1_step hp (hcall.step fs) hg0c.1, by rw [hcE]⟩
  have hsub : (Spike.Lib.A64.Rt.rS0 (Ly h)).Sub (Ly h).Λ.stackPool := Spike.Lib.A64.Rt.rS0_sub (Ly h)
  have hfit := Spike.Lib.A64.Rt.fitS_of_sub (Ly h) hsub
  have hG0' : ∀ c c', Good1 p (c, frm :: fs) ∧ c.hold = none → FrameRun p (c, frm :: fs) (c', frm :: fs) →
      Good1 p (c', frm :: fs) ∧ c'.hold = none :=
    fun c c' hg hr'' => ⟨good1_run hp hr'' hg.1, FrameRun.hold_none hr'' hg.2⟩
  refine ⟨⟨hcx', rfl, rfl⟩, hra', hFS, hR', hb16', by omega, by omega, hG0', ?_, ?_,
    CxOkC.hab hd' ⟨hcx', rfl, rfl⟩ hra', hg0, ?_, ?_⟩
  · exact hWbS_of (hcode j' dg hd').hf (hcode j' dg hd').h1 (hcode j' dg hd').h16 hI hR' hb16' (by omega)
      (by omega) hl8' hh8' hsub hfit hcx'.hFO Spike.Lib.A64.Flow.Ret0.Inst.cfacts_c0 hp (good1_tail rfl) rfl hG0'
      fun _ h => h
  · exact hWsS_of (hcode j' dg hd').hf (hcode j' dg hd').h1 (hcode j' dg hd').h16 hI hR' hb16' (by omega)
      (by omega) hl8' hh8' hsub hfit hcx'.hFO Spike.Lib.A64.Flow.Ret0.Inst.cfacts_c0 hp (good1_tail rfl) rfl hG0'
      fun _ h => h
  · exact proW_bodyS hI (hcode j' dg hd').hf (hcode j' dg hd').h1 (hcode j' dg hd').h16 (hcode j' dg hd').hpro
      (spillsOk_of_paramSpill (hcode j' dg hd').hf (hcode j' dg hd').h1 (hcode j' dg hd').hsp) hphP'
      Spike.Lib.A64.Flow.Ret0.Inst.cfacts_c0 hp (good1_tail rfl)
      (fun σ c ⟨⟨hc0, _, _, _, htp⟩, _⟩ => ⟨htp, by rw [hc0]; exact hg0.1, by rw [hc0]; exact hg0.2⟩)
      hR' hb16' (by omega) (by omega) hl8' hh8' hcx'.limMp.1 hcx'.limUn hsub hfit hcx'.hFO
  · rintro σ c ⟨⟨rfl, hfp, hsl, hx0, htp⟩, hsp⟩
    rw [show tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit) = Spike.Lib.A64.Flow.Ret0.limA tp from
      Spike.Lib.A64.Flow.Ret0.tcbA_limA htp]
    refine ⟨⟨hcx'.limRt, hcx'.limMp, hcx'.limUn, fun v hv => ?_⟩, hfp, hsl, fun sl hsl' => ?_, .refl _⟩
    · have := ownLim_of_placeOK h hrs hir hd' hr' (hcx'.lim dg hd') v hv
      rw [← hcxe'] at this
      rw [hsp]
      exact limBv_of_le (by have := (hcode j' dg hd').h1; omega) this
    · rw [henv']
      obtain ⟨k, hk⟩ := rsOf_param (Scc.Lower.A64.lowerAll cfg p).low.ir.abortFn
        (Scc.Lower.A64.lowerAll cfg p).low.ir.growth
        (Scc.IR.StackMap.argAreas (Scc.Lower.A64.lowerAll cfg p).low.ir Scc.Emit.A64.argRegs.length)
        (rt.length + j') (Scc.Lower.Names.user dg.name) hint r'
      have hk' : rsOf (hcode j' dg hd').cx s!"{dg.arg}.{0}" = some k := by rw [hcxe']; exact hk
      exact nj_callee hint harg hcE hk' ((hsl' _ (by rw [hprs']; simp [params1R, hint]) k hk').trans hx0)

/-- **Every code block's `FnSpecC` at its contexts from the placement
check**: `fnSpecC_all_ofPre` at the contexts `CxOkC` (the aborts `AbC`),
each code block's `CallPre` from `callPre_of` and each callee's
`CalleePre` from `calleePre_of`, at the callee room `-R.lo - frame`, for
code facts `hcode` with their fields (`hok`, no frames limit) and walk
predicates in the code blocks' walks (`hT`). -/
theorem fnSpecC_all_ofPlaceOK (hp : Scc.Lower.Accepted1 p = true) {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (O) = true)
    {rs : List Res1} {rt : List Scc.IR.Func} (hrs : Pairwise2 (LowC p cfg.layout.obj none) p rs)
    (hir : (Scc.Lower.A64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    {cells : Nat} {T : Nat → Expr → Prop} (hT : ∀ j d, p[j]? = some d → ∀ e, T j e → InWalkD none d e)
    (hcode : ∀ j d, p[j]? = some d →
      FnCode (Ly h).exe (Ly h).prog (Ly h).endPc (RaOkS h) (CdS h) (Scc.Lower.imms1Of p) (T j) d)
    (hok : ∀ j d (hd : p[j]? = some d), CodeFactsS h rs rt (hcode j d hd) j) :
    ∀ j d (hd : p[j]? = some d), FnSpecC (WS h cells) (KS h) p (Ly h).Λ.static (MSS h)
      (CxOkC p (O).place.need (Ly h).Λ (Ly h).Λ.static (MSS h) (Spike.Lib.A64.Rt.rS0 (Ly h))
        (AbS h hcode) j)
      (hcode j d hd) := by
  refine fnSpecC_all_ofPre hp hcode ?_ ?_
  · intro j d hd e he
    obtain ⟨r, -, -, hfrm, henv, hn, -⟩ := hok j d hd
    rw [hfrm, henv, hn]
    exact hT j d hd e he
  · intro j d hd R F fs fp ra tp Gc Ab hcx hra
    refine ⟨-R.lo - ((hcode j d hd).cx.frame : Int), ?_,
      fun g q frm F' j' dg hd' _ hname hfd hFS hCF hc3 harg hbl =>
        ⟨_, calleePre_of hp h hrs hir hT hcode hok hd hcx hra hd' hname hfd hFS hCF hc3 harg hbl⟩⟩
    obtain ⟨hc, rfl, rfl⟩ := hcx
    exact callPre_of hp h hrs hir hT hcode hok hd hc hra

end Pre

end Spike.Lib.LowerA64
