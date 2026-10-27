/-
**The premises at the contexts from the placement check** (x86-64, H7a
calls): `fnSpecC_all_ofPre`'s (`Spike/Lib/LowerX64/ProgCB.lean`) `CallPre`
and `CalleePre` at the code blocks' contexts `CxOkC`
(`Spike/Lib/LowerX64/CtxC.lean`) for an `Accepted1` program passing
`placeOKAt`, at the runtime layout `RuntimeLayout.ofPlaceOK h (imms1Of p)`,
for code facts lowered with no frames limit (plain calls); the call blocks
from the code's placement and phase facts (`Spike/Lib/LowerX64/CallBlkW.lean`),
the prologues from the code facts (`proW_bodyS`).

- `callPre_of`: a code block's `CallPre` at a context, at the callee room
  `D := -R.lo - size - 16`.
- `CodeFactsS`: the code facts' fields (`fnCode_ofPlaceOKR`'s);
  `argTy_callee`: a callee's argument is an `Int`.
- `calleePre_of`: a callee's `CalleePre` at a call from a context.
- `fnSpecC_all_ofPlaceOK`: every code block's `FnSpecC` at its contexts.
-/
import Spike.Lib.LowerX64.CtxC
import Spike.Lib.LowerX64.FnCodeOf
import Spike.Lib.LowerX64.BodyWSC
import Spike.Lib.LowerX64.CallBlkW
import Spike.Lib.X64StartOfPlaceOK
import Spike.Lib.LowerCallMem
import Spike.Lib.LowerX64.ProWS

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Lower.InvX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Lower.Inv (Res1 func1 params1R env1)
open Spike.Lib.LowerNode (Pairwise2 LowC funcs1)
open Spike.Lib.X64ConsumerS (msOfS)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.PhRec (μ K)
open Spike.Lib.X64.Flow (CallTo)

/-- `Pairwise2` at an index, from the two lookups. -/
theorem Pairwise2.get? {α γ : Type} {P : α → γ → Prop} {ds : List α} {rs : List γ} (h : Pairwise2 P ds rs)
    {i : Nat} {d : α} {r : γ} (hd : ds[i]? = some d) (hr : rs[i]? = some r) : P d r := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hd
  obtain ⟨hir, rfl⟩ := List.getElem?_eq_some_iff.mp hr
  exact h.get i hi

section Pre

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog} {sizes : List Nat}
  {labelOffs : List (String × Nat)}

set_option quotPrecheck false

/-- The lowering's output. -/
local notation "O" => Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs

/-- The runtime's layout of the output, at the lowering's immediates. -/
local notation "Ly" h => RuntimeLayout.ofPlaceOK h (Scc.Lower.imms1Of p)

/-- The value invariant: the first TCB's limit word holds its loaded value or the limit. -/
local notation "G0" h:max => Spike.Lib.X64.PhRec.GOf (Ly h) (Spike.Lib.X64.PhRec.m0Of (Ly h).Λ (O).prog (O).secs)

/-- The placement's memory side at the frames. -/
local notation "MSS" h:max => msOfS (Ly h).Λ (μ (Ly h)) (fun _ => True) (G0 h)
  (fun s _ => Spike.Lib.X64.PhRec.own (Ly h) s) (Ly h).Λ.static (fun _ => 0)

/-- The body's facts at the frames, the consumer's start held back. -/
local notation "WS" h:max cells:max => BodyWS0 (Ly h).Λ (μ (Ly h)) p (Spike.Lib.X64.PhRec.own (Ly h))
  (Spike.Lib.X64.Rt.rS0 (Ly h)) (Spike.Lib.X64.PhRec.Tk (Ly h)) (Ly h).Λ.static cells 0 Spike.Lib.X64Consumer.c0

/-- The outside move: the take of the first stack. -/
local notation "KS" h => K (Ly h) (Spike.Lib.X64.Rt.rS0 (Ly h))

/-- The return addresses in the phase of `raL`. -/
local notation "RaOkS" h => fun ra : BitVec 64 => Spike.Lib.X64.PhRec.ph (Ly h) (Int64.ofBitVec ra).toBitVec.toNat =
  Spike.Lib.X64.PhRec.ph (Ly h) ((Ly h).lab raL).toBitVec.toNat

/-- The code predicate at a return address. -/
local notation "CdS" h => fun ra : BitVec 64 => CdC (O).prog (Spike.Lib.X64.PhRec.okPc (Ly h))
  (Spike.Lib.X64.PhRec.ph (Ly h)) (Ly h).lab (Int64.ofBitVec ra)

/-- The block predicate at a frame and return address. -/
local notation "BlS" h => fun (fr : Scc.Emit.X64.Frame) (ra : BitVec 64) => BlC (O).prog
  (Spike.Lib.X64.PhRec.okPc (Ly h)) (Spike.Lib.X64.PhRec.ph (Ly h)) (Ly h).lab fr (Int64.ofBitVec ra)

/-- **A code block's code facts' fields** (`fnCode_ofPlaceOKR`'s): the
`j`th code block `d`'s closed form `r` (`rs[j]`), its context's program and
no frames limit, its entry environment and counter, its parameter
registers, its frame and block predicate, with a checked `+` the
overflow block's code and phase facts, and the prologue's phase facts. -/
def CodeFactsS {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true) (rs : List Res1) {T : Expr → Prop}
    {d : Decl} (c : FnCode (Ly h).exe (Ly h).prog (Ly h).endPc (RaOkS h) (CdS h) (Scc.Lower.imms1Of p) T d)
    (j : Nat) : Prop :=
  ∃ r, rs[j]? = some r ∧ c.lcx.prog = p ∧ c.lcx.frames = none ∧ c.env = env1 d ∧ c.n = 0 ∧ c.r = r ∧
    c.prs = params1R d ∧
    c.fr = frOf (Scc.Lower.X64.lowerAll cfg p).low.ir (func1 (Scc.Lower.Names.user d.name) (params1R d) r) ∧
    c.Bl = (BlS h) c.fr ∧
    (Scc.Cert.Code1X64.hasAddChk (func1 (Scc.Lower.Names.user d.name) (params1R d) r) = true →
      Scc.Cert.Rt.X64.blockAtB (O).prog (ovfL c.fr) 0 ovfBlk = true ∧
      Spike.Lib.X64Consumer.blkPh (Spike.Lib.X64.PhRec.okPc (Ly h)) (Spike.Lib.X64.PhRec.ph (Ly h)) (fun _ => false)
        (Ly h).lab ((Ly h).lab (ovfL c.fr) + Int64.ofNat 0) 0 Spike.Lib.X64.Abort.Local.lb = true) ∧
    ProPh (Spike.Lib.X64.PhRec.okPc (Ly h)) (Spike.Lib.X64.PhRec.ph (Ly h)) (Ly h).lab c.fn
      (Scc.Emit.X64.labelOf c.fr.fn "chk") (Int64.ofInt c.fr.size) (proL c.fr) c.zl c.zf c.z1 c.z2 c.zs c.ps

/-- **A code block's `CallPre` at a context**: for the `j`th code block
`d` of an `Accepted1` program (code facts `hcode` with their fields `hok`,
closed forms `hrs` at no frames limit, walk predicates `hT`), at a context
of `CtxB`, at the `Good1` ghosts with no hold, the callee room
`D := -R.lo - size - 16`: the region's room from the code block's
(`ownRoom_of_placeOK`), the calls' code (`cdOf_blC`), the calls without
index or type arguments (`body1_call_walkC`), the body's covered `ret`-free
blocks (`blkW_bodySC`), the calls' `callq` (`blkW_callq`) and the callee's
entry at its prologue head (`nodeW_calleeEntry`, the callee's code facts'
prologue and its phase facts) inside `W`. -/
theorem callPre_of (hp : Scc.Lower.Accepted1 p = true) {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true)
    {rs : List Res1} {rt : List Scc.IR.Func} (hrs : Pairwise2 (LowC p cfg.layout.obj none) p rs)
    (hir : (Scc.Lower.X64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    {cells : Nat} {T : Nat → Expr → Prop} (hT : ∀ j d, p[j]? = some d → ∀ e, T j e → InWalkD none d e)
    (hcode : ∀ j d, p[j]? = some d →
      FnCode (Ly h).exe (Ly h).prog (Ly h).endPc (RaOkS h) (CdS h) (Scc.Lower.imms1Of p) (T j) d)
    (hok : ∀ j d (hd : p[j]? = some d), CodeFactsS h rs (hcode j d hd) j)
    {j : Nat} {d : Decl} (hd : p[j]? = some d)
    {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {tp : UInt64} {fp ra : BitVec 64}
    (hc : CtxB p (O).place.need (Ly h).Λ (Ly h).Λ.static (MSS h) (Spike.Lib.X64.Rt.rS0 (Ly h)) j R F fs tp) :
    CallPre p (Ly h).exe (Ly h).endPc (rbR R) F (WS h cells) (KS h) (hcode j d hd).fr ((CdS h) ra)
      ((hcode j d hd).Bl ra) fp ra fs (fun c => Good1 p (c, fs) ∧ c.hold = none) (T j)
      (-R.lo - (hcode j d hd).fr.size - 16) := by
  obtain ⟨r, hr, -, -, -, -, -, -, hfr, hBl, -⟩ := hok j d hd
  have hown := ownRoom_of_placeOK h hrs hir hd hr (hc.room d hd)
  have h16 := frame16_of_fnPh1 h hrs hir hd hr
  rw [← hfr] at hown h16
  have hl8 := hc.hl8
  have hhi := hc.hhi
  have hb16 := hc.hb16
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms1Of p) (rS := Spike.Lib.X64.Rt.rS0 (Ly h))
  have hsub : (Spike.Lib.X64.Rt.rS0 (Ly h)).Sub (Ly h).Λ.stackPool := Spike.Lib.X64.Rt.rS0_sub (Ly h)
  have hfit : (Spike.Lib.X64.Rt.rS0 (Ly h)).lo + (Spike.Lib.X64.Rt.rS0 (Ly h)).size ≤ 2 ^ 64 := by
    have := (Ly h).pool_fit; obtain ⟨-, h2⟩ := hsub; omega
  have e1 : (rbR R).lo = R.lo + 8 := rfl
  have e2 : (rbR R).hi = R.hi + 8 := rfl
  have hrbOK := rbR_ok hc.hR (by omega) (by omega)
  have hrb := rbR_base hc.hR (by omega) (by omega)
  have hFOb := fun m hm => stackOff_rbR hc.hR (by omega) (by omega) (hc.hFO m hm)
  have h8 : ((hcode j d hd).fr.size : Int) % 8 = 0 := by omega
  refine ⟨rbR_fstable hc.hR (by omega) (by omega) hc.hF, hrbOK, by omega, by omega, by rw [e1]; omega,
    by rw [e2]; omega, ?_, fun c c' hg hr' => ⟨good1_run hp hr' hg.1, FrameRun.hold_none hr' hg.2⟩, ?_, ?_, ?_, ?_⟩
  · rw [hBl]
    intro pc zc g k hb
    exact cdOf_blC hI.lays hI.endOk pc zc g k (by rw [hI.labOk]; exact hb)
  · intro n blk hcd hno hokb hnr hJ
    exact blkW_bodySC hI hrbOK (by omega) (lo := -((hcode j d hd).fr.size : Int)) (hi := 16) (by rw [e1]; omega)
      (by rw [e2]; omega) (by rw [e1]; omega) (by rw [e2]; omega) hsub hfit hFOb
      Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0 hp (good1_tail rfl) (fun σ c h => (hJ σ c h).1) hcd
      (by rw [hno]; exact hokb) hnr
  · intro n zc g k hb hno hJ
    rw [hBl] at hb
    exact blkW_callq hI h8 hrbOK (by omega) (by rw [e1]; omega) (by rw [e2]; omega) (by rw [e1]; omega)
      (by rw [e2]; omega) hsub hfit hFOb Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0 hp (good1_tail rfl) hno
      (fun σ c h => (hJ σ c h).1) hb
  · intro n g dg hfd hpc hno hJ
    obtain ⟨j', hj', hpj'⟩ := Spike.Lib.LowerNode.find_index hfd
    have hd' : p[j']? = some dg := by rw [List.getElem?_eq_getElem hj', hpj']
    have hname : dg.name = g := by simpa using List.find?_some hfd
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hphP'⟩ := hok j' dg hd'
    have hpro := (hcode j' dg hd').hpro
    simp only [Spike.Lib.X64.Flow.prologueIn, Bool.and_eq_true] at hpro
    obtain ⟨⟨⟨⟨⟨⟨-, hxh⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hpro
    have hfn : (hcode j' dg hd').fn = Scc.Lower.Names.user g := by rw [(hcode j' dg hd').hfn, hname]
    have hph := hphP'.hd
    rw [hfn] at hxh hph
    exact nodeW_calleeEntry hI h8 hrbOK (by omega) (by rw [e1]; omega) (by rw [e2]; omega) (by rw [e1]; omega)
      (by rw [e2]; omega) hsub hfit hFOb Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0 hp (good1_tail rfl) hxh hph hpc hno
      (fun σ c h => (hJ σ c h).1)
  · intro x g is a ts e hTe
    obtain ⟨q, hq, hqe⟩ := hT j d hd _ hTe
    have hp' := hp
    simp only [Scc.Lower.Accepted1, Bool.and_eq_true, decide_eq_true_eq] at hp'
    have hd1 := Spike.Lib.LowerCallOrder.decl1_of_decls1 hp'.1.2 hd
    simp only [Scc.Lower.decl1, Bool.and_eq_true, beq_iff_eq] at hd1
    exact (Spike.Lib.LowerCallOrder.body1_call_walkC _ _ _ _ _ hd1.2 q hq x g is a ts e hqe).2

/-- **A called code block's argument is an `Int`**: the callee `g` of a
call at a point of an `Accepted1` code block's walk is not `main`
(`body1_call_walkC`), so its declared argument is an `Int` (`decl1`). -/
theorem argTy_callee (hp : Scc.Lower.Accepted1 p = true) {j : Nat} {d : Decl} (hd : p[j]? = some d)
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

/-- **A callee's `CalleePre` at a call from a context**: at a call of `g`
(the `j'`th code block `dg`) from the `j`th code block's context
(`CxOkC`, a return address with `RaOk`), in the callee's region below the
caller's frame at the room `D := -R.lo - size - 16` with the callee's frame
condition `F'` (`CalleeF`, stable): the callee's context (`CtxB.callF`, its
rooms from the call site's, `calleeRoom_of_placeOK`, `calleeLim_of_placeOK`),
the return address after the call in `raL`'s phase (`blC_ph`), the body's
blocks (`hWbS_of`, `hWsS_of`), the aborts (`CxOkC.hab`), the ghost the
entry control after the call (`good1_step`), the prologue from its code facts (`proW_bodyS`), and
the entry's facts: the limit word's from the context (its room,
`ownLimBv_of_placeOK`), `calleeN`'s registers, the entry node `nj_callee`
at the parameter's slot (`rsOf_param`). -/
theorem calleePre_of (hp : Scc.Lower.Accepted1 p = true) {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true)
    {rs : List Res1} {rt : List Scc.IR.Func}
    (hrs : Pairwise2 (LowC p cfg.layout.obj none) p rs)
    (hir : (Scc.Lower.X64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    {cells : Nat} {T : Nat → Expr → Prop} (hT : ∀ j d, p[j]? = some d → ∀ e, T j e → InWalkD none d e)
    (hcode : ∀ j d, p[j]? = some d →
      FnCode (Ly h).exe (Ly h).prog (Ly h).endPc (RaOkS h) (CdS h) (Scc.Lower.imms1Of p) (T j) d)
    (hok : ∀ j d (hd : p[j]? = some d), CodeFactsS h rs (hcode j d hd) j)
    {j : Nat} {d : Decl} (hd : p[j]? = some d) {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame}
    {fp ra : BitVec 64} {tp : UInt64} {Gc : Ctl → Prop} {Ab : FragS isa}
    (hcx : CxOkC p (O).place.need (Ly h).Λ (Ly h).Λ.static (MSS h) (Spike.Lib.X64.Rt.rS0 (Ly h))
      (AbC p (O).place.need (Ly h).Λ (Ly h).Λ.static (MSS h) (Spike.Lib.X64.Rt.rS0 (Ly h)) hcode)
      j R F fs fp ra tp Gc Ab)
    (hra : (RaOkS h) ra) {g : String} {q : CallG} {frm : TermRun.Frame} {F' : MachineData → Prop} {j' : Nat}
    {dg : Decl} (hd' : p[j']? = some dg) (hname : dg.name = g)
    (hfd : p.find? (·.name == g) = some dg)
    (hFS : FStable (calleeR (rbR R) (hcode j d hd).fr.size (-R.lo - (hcode j d hd).fr.size - 16)) F')
    (hCF : CalleeF p (Ly h).Λ.static (hcode j d hd).fr (rbR R) F (-R.lo - (hcode j d hd).fr.size - 16) fp ra
      (Scc.Lower.imms1Of p) (T j) q frm F')
    (hc3 : ∃ c x a e, Gc c ∧ T j (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
      CallTo p c q.cE frm)
    (harg : ArgV (Ly h).Λ.static q)
    (hbl : ∃ pcB zc k, (hcode j d hd).Bl ra pcB zc (Scc.Lower.Names.user g) k ∧
      q.ra = (pcB + Int64.ofNat zc).toBitVec) :
    CalleePre (WS h cells) (KS h) p (Ly h).Λ.static (MSS h)
      (CxOkC p (O).place.need (Ly h).Λ (Ly h).Λ.static (MSS h) (Spike.Lib.X64.Rt.rS0 (Ly h))
        (AbC p (O).place.need (Ly h).Λ (Ly h).Λ.static (MSS h) (Spike.Lib.X64.Rt.rS0 (Ly h)) hcode) j')
      (hcode j' dg hd') (calleeR (rbR R) (hcode j d hd).fr.size (-R.lo - (hcode j d hd).fr.size - 16)) F'
      (frm :: fs) q.fp q.ra tp (fun c => Good1 p (c, frm :: fs) ∧ c.hold = none) Ab
      (fun σ c => (calleeN (_root_.Executable.labels (Ly h).exe).label g tp q).J σ c ∧
        σ.regs.rsp.toBitVec = (calleeR (rbR R) (hcode j d hd).fr.size (-R.lo - (hcode j d hd).fr.size - 16)).base)
      q.cE := by
  obtain ⟨hc, rfl, rfl⟩ := hcx
  obtain ⟨r, hr, -, hfrm, henv, hn, hrr, -, hfr, hBl, -⟩ := hok j d hd
  obtain ⟨r', hr', -, -, henv', -, -, hprs', hfr', -, -, hphP'⟩ := hok j' dg hd'
  obtain ⟨c0, x, a, e, hg0c, hTc, hct, hcall⟩ := hc3
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms1Of p) (rS := Spike.Lib.X64.Rt.rS0 (Ly h))
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
  have h16 := frame16_of_fnPh1 h hrs hir hd hr
  obtain ⟨-, -, -, -, -, -, -, hroomg⟩ := calleeRoom_of_placeOK hp h hrs hir hd hr hmem hgp (hc.room d hd)
  rw [← hfr] at hown h16 hroomg
  have hhi := hc.hhi
  have hl8 := hc.hl8
  have hb16 := hc.hb16
  have hcb := calleeR_base hc.hR hhi (size := (hcode j d hd).fr.size) (by omega)
  obtain ⟨-, -, -, -, -, -, -, -, hlimg⟩ := calleeLim_of_placeOK hp h hrs hir hd hr hmem hgp
    (G := ((MSS h) []).G ⟨Spike.Lib.X64.Flow.Ret0.limA tp, 8⟩) (rsp := R.base.toNat)
    (rsp' := R.base.toNat - (hcode j d hd).fr.size - 16) hb16 (by rw [← hfr]; omega) (hc.lim d hd)
  -- the callee's context
  have hcx' := hc.callF (hcode j d hd).hf h16 hown hFS hCF
    (fun d' hd'' => by rw [hd'] at hd''; cases hd''; rw [hname]; exact hroomg)
    (fun d' hd'' => by rw [hd'] at hd''; cases hd''; rw [hname]; exact hlimg)
  have hR' := hcx'.hR
  have hl8' := hcx'.hl8
  have hhi' := hcx'.hhi
  have hb16' := hcx'.hb16
  have hown' := ownRoom_of_placeOK h hrs hir hd' hr' (hcx'.room dg hd')
  rw [← hfr'] at hown'
  -- the return address
  have hra' : (RaOkS h) q.ra := by
    obtain ⟨pcB, zc, k, hb, hq⟩ := hbl
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
  -- the rebased region
  have hsub : (Spike.Lib.X64.Rt.rS0 (Ly h)).Sub (Ly h).Λ.stackPool := Spike.Lib.X64.Rt.rS0_sub (Ly h)
  have hfit : (Spike.Lib.X64.Rt.rS0 (Ly h)).lo + (Spike.Lib.X64.Rt.rS0 (Ly h)).size ≤ 2 ^ 64 := by
    have := (Ly h).pool_fit; obtain ⟨-, h2⟩ := hsub; omega
  have e1 : ∀ R'' : Region, (rbR R'').lo = R''.lo + 8 := fun _ => rfl
  have e2 : ∀ R'' : Region, (rbR R'').hi = R''.hi + 8 := fun _ => rfl
  have hrbOK := rbR_ok hR' (by omega) (by omega)
  have hrb := rbR_base hR' (by omega) (by omega)
  have hFOb := fun m hm => stackOff_rbR hR' (by omega) (by omega) (hcx'.hFO m hm)
  have hG0' : ∀ c c', Good1 p (c, frm :: fs) ∧ c.hold = none → FrameRun p (c, frm :: fs) (c', frm :: fs) →
      Good1 p (c', frm :: fs) ∧ c'.hold = none :=
    fun c c' hg hr'' => ⟨good1_run hp hr'' hg.1, FrameRun.hold_none hr'' hg.2⟩
  refine ⟨⟨hcx', rfl, rfl⟩, hra', hFS, hR', by omega, by omega, hG0', ?_, ?_, CxOkC.hab hd' ⟨hcx', rfl, rfl⟩ hra',
    hg0, ?_, ?_⟩
  · exact hWbS_of (hcode j' dg hd').hf (hcode j' dg hd').h1 hI hrbOK (by omega)
      (by rw [e1]; omega) (by rw [e2]; omega) (by rw [e1]; omega) (by rw [e2]; omega) hsub hfit hFOb
      Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0 hp (good1_tail rfl) rfl hG0' fun _ h => h
  · exact hWsS_of (hcode j' dg hd').hf (hcode j' dg hd').h1 hI hrbOK (by omega)
      (by rw [e1]; omega) (by rw [e2]; omega) (by rw [e1]; omega) (by rw [e2]; omega) hsub hfit hFOb
      Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0 hp (good1_tail rfl) rfl hG0' fun _ h => h
  · exact proW_bodyS hI (hcode j' dg hd').h1 (hcode j' dg hd').hpro
      (spillsOk_of_hps (hcode j' dg hd').h1 (hcode j' dg hd').hps) hphP'
      Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0 hp (good1_tail rfl)
      (fun σ c ⟨⟨hc, _, _, _, htp⟩, _⟩ => ⟨htp, by rw [hc]; exact hg0.1, by rw [hc]; exact hg0.2⟩)
      hR' (by omega) (by omega) (by omega) hl8' (by omega) hcx'.limMp.1 hcx'.limUn hsub hfit hcx'.hFO
  · rintro σ c ⟨⟨rfl, hfp, hsl, hrdi, htp⟩, hsp⟩
    have ha : σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec =
        Spike.Lib.X64.Flow.Ret0.limA tp := by
      rw [Spike.Lib.X64.Flow.Ret0.limA, htp]; rfl
    rw [ha]
    refine ⟨⟨hcx'.limRt, hcx'.limMp, hcx'.limUn, ?_⟩, hfp, hsl, ?_, .refl _⟩
    · have := ownLimBv_of_placeOK h hrs hir hd' hr' (rsp := σ.regs.rsp.toBitVec) (by rw [hsp]; exact hb16')
        hcx'.g16 (by rw [hsp]; exact hcx'.lim dg hd')
      rw [← hfr'] at this
      exact this
    · intro sl hsl'
      rw [henv']
      obtain ⟨k, hk⟩ := rsOf_param (Scc.Lower.X64.lowerAll cfg p).low.ir (Scc.Lower.Names.user dg.name) hint r'
      rw [← hfr'] at hk
      exact nj_callee hint harg hcE hk ((hsl' _ (by rw [hprs']; simp [params1R, hint]) k hk).trans hrdi)

/-- **Every code block's `FnSpecC` at its contexts from the placement
check**: `fnSpecC_all_ofPre` at the contexts `CxOkC` (the aborts `AbC`),
each code block's `CallPre` from `callPre_of` and each callee's
`CalleePre` from `calleePre_of`, for code facts `hcode` with their fields
(`hok`, no frames limit) and walk predicates in the code blocks' walks
(`hT`). -/
theorem fnSpecC_all_ofPlaceOK (hp : Scc.Lower.Accepted1 p = true) {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (O) = true)
    {rs : List Res1} {rt : List Scc.IR.Func} (hrs : Pairwise2 (LowC p cfg.layout.obj none) p rs)
    (hir : (Scc.Lower.X64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    {cells : Nat} {T : Nat → Expr → Prop} (hT : ∀ j d, p[j]? = some d → ∀ e, T j e → InWalkD none d e)
    (hcode : ∀ j d, p[j]? = some d →
      FnCode (Ly h).exe (Ly h).prog (Ly h).endPc (RaOkS h) (CdS h) (Scc.Lower.imms1Of p) (T j) d)
    (hok : ∀ j d (hd : p[j]? = some d), CodeFactsS h rs (hcode j d hd) j) :
    ∀ j d (hd : p[j]? = some d), FnSpecC (WS h cells) (KS h) p (Ly h).Λ.static (MSS h)
      (CxOkC p (O).place.need (Ly h).Λ (Ly h).Λ.static (MSS h) (Spike.Lib.X64.Rt.rS0 (Ly h))
        (AbC p (O).place.need (Ly h).Λ (Ly h).Λ.static (MSS h) (Spike.Lib.X64.Rt.rS0 (Ly h)) hcode) j)
      (hcode j d hd) := by
  refine fnSpecC_all_ofPre hp hcode (fun j d hd => (hok j d hd).choose_spec.2.1)
    (fun j d hd => (hok j d hd).choose_spec.2.2.1) ?_ ?_
  · intro j d hd e he
    obtain ⟨r, -, -, hfrm, henv, hn, -⟩ := hok j d hd
    rw [hfrm, henv, hn]
    exact hT j d hd e he
  · intro j d hd R F fs fp ra tp Gc Ab hcx hra
    refine ⟨-R.lo - (hcode j d hd).fr.size - 16, ?_, fun g q frm F' j' dg hd' _ hname hfd hFS hCF hc3 harg hbl =>
      ⟨_, calleePre_of hp h hrs hir hT hcode hok hd hcx hra hd' hname hfd hFS hCF hc3 harg hbl⟩⟩
    obtain ⟨hc, rfl, rfl⟩ := hcx
    exact callPre_of hp h hrs hir hT hcode hok hd hc

end Pre

end Spike.Lib.LowerX64
