/-
**The aborts of an `Accepted1` program's code blocks at their contexts,
held back, never end** (AArch64, H7a calls): the twin of
`Spike/Lib/LowerX64/MainC.lean`'s `abC_lag`, for `CxOkC`'s aborts `AbC`
(`Spike/Lib/LowerA64/CtxC.lean`).

- `hasAddChk_func1`: a checked `+` among a closed form's instructions is
  one of its function's (`Code1A64.hasAddChk`);
- `OvfFactsS`: the code facts' fields `abC_lag` reads (a part of the x86-64
  `CodeFactsS`): the `j`th code block's closed form `r` (`rs[j]`), its
  context with no frames limit, its entry environment and counter, its frame
  `ctxOf`'s, with a checked `+` the overflow block's code and phase facts;
- `abC_lag`: the aborts `AbC` held back at the consumer's start, inside
  `SFactsS … OvfDt`, never end (`hab_ofS` at each context).
- `CodeFactsS`: the code facts' fields (`fnCode_ofPlaceOKR`'s);
  `CodeFactsS.ovfFacts`: they give `OvfFactsS`.
- `LowerNoneS`: every code block's code facts with no frames limit;
  `lowerNoneS_ofPlaceOK`: from the placement check (the lowering's calls
  are plain).
- `mainCtxB`: `main`'s context `CtxB` at `scc_rt_main`'s call, below
  `scc_rt_main`'s frame after the switch, at the depth `needDA n`;
  `g16_ofPlaceOK`: the limit word's values 16-aligned.
- `argTy_main`, `spillsOk_of_paramSpill`; `mainPre_of`: `main`'s
  `CalleePre` at its context, from the interface's entry `uN0`.
- `uPostS_ret`: `main`'s return node is the interface's return at
  `UPostS`.

Where AArch64 differs from x86-64: the region is the context's own (no
rebased region), the code predicate and return addresses are any (`abC_lag`
reads neither, and takes the fields `OvfFactsS` that `CodeFactsS` gives),
the frame is `ctxOf`'s at the code block's index past the runtime's `rt`,
and the return addresses are those of the phase of `bareMC.e0 + 4`.
-/
import Spike.Lib.LowerA64.CtxC
import Spike.Lib.LowerA64.FnCodeOf
import Spike.Lib.LowerA64.AbortCallS
import Spike.Lib.LowerA64.AbortOfPlaceOK
import Spike.Lib.LowerA64.OvfDt
import Spike.Lib.LowerCallMem
import Spike.Lib.SegLagS
import Spike.Lib.A64StartOfPlaceOK
import Spike.Lib.LowerA64.BodyWSC
import Spike.Lib.LowerA64.ProWS
import Spike.Lib.LowerA64.CalleeRoom
import Spike.Lib.LowerA64.UPostS
import Spike.Lib.Rt.A64StartArith

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Cert.Code1A64 (ctxOf hasAddChk)
open Scc.Lower.Inv (Res1 func1 params1R env1)
open Spike.Lib.LowerNode (Pairwise2 LowC funcs1)
open Spike.Lib.LowerShape (allInsts)
open Spike.Lib.A64ConsumerS (SFactsS msOfS)
open Spike.Lib.A64.Rt (RuntimeLayout bareMC)
open Spike.Lib.A64.PhRec (μ K)

/-- **A checked `+` of a closed form is its function's** (`hasAddChk`). -/
theorem hasAddChk_func1 {name : Scc.IR.Sym} {ps : List Scc.IR.Reg} {r : Res1} {i : Scc.IR.Inst}
    (hi : i ∈ allInsts r) {d : Scc.IR.Reg} {u v : Scc.IR.Operand} (he : i = .addChk d u v) :
    hasAddChk (func1 name ps r) = true := by
  subst he
  simp only [allInsts, List.mem_append, List.mem_flatMap] at hi
  simp only [hasAddChk, func1, List.any_cons, List.any_eq_true, Bool.or_eq_true]
  rcases hi with hi | ⟨b, hb, hi⟩
  · exact .inl ⟨_, hi, rfl⟩
  · exact .inr ⟨b, hb, _, hi, rfl⟩

section Main

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

/-- The facts every pair of the run carries at its frames, at the arena's
`cells` and the overflow stub's write tail. -/
local notation "WSS" h:max cells:max => fun s c fs => SFactsS (Ly h).Λ (μ (Ly h)) p
  (fun s _ => Spike.Lib.A64.PhRec.own (Ly h) s) (Spike.Lib.A64.Rt.rS0 (Ly h)) (Spike.Lib.A64.PhRec.Tk (Ly h))
  (Ly h).Λ.static cells 0 s c fs (OvfDt (Ly h).exe (Ly h).endPc (Ly h).lab)

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

/-- The block predicate at a frame and return address. -/
local notation "BlS" h => fun (cx : FnCtx) (ra : BitVec 64) => BlC (O).prog
  (Spike.Lib.A64.PhRec.okPc (Ly h)) (Spike.Lib.A64.PhRec.ph (Ly h)) (Ly h).lab cx (Int64.ofBitVec ra)

/-- **A code block's code facts' fields that its aborts read** (a part of
the x86-64 `CodeFactsS`): the `j`th code block `d`'s closed form `r`
(`rs[j]`), its context with no frames limit, its entry environment and
counter, its frame (`ctxOf` at its index past the runtime's `rt`), with a
checked `+` the overflow block's code and phase facts. -/
def OvfFactsS {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true) (rs : List Res1)
    (rt : List Scc.IR.Func) {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {T : Expr → Prop} {d : Decl}
    (c : FnCode (Ly h).exe (Ly h).prog (Ly h).endPc RaOk Cd (Scc.Lower.imms1Of p) T d) (j : Nat) : Prop :=
  ∃ r, rs[j]? = some r ∧ c.lcx.frames = none ∧ c.env = env1 d ∧ c.n = 0 ∧ c.r = r ∧
    c.cx = ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir (rt.length + j)
      (func1 (Scc.Lower.Names.user d.name) (params1R d) r) ∧
    (hasAddChk (func1 (Scc.Lower.Names.user d.name) (params1R d) r) = true →
      Scc.Cert.Rt.A64.blockAt (O).prog (c.cx.local "abort_overflow") 0 ovfBlk = true ∧
      Spike.Lib.A64Consumer.blkPh (Spike.Lib.A64.PhRec.okPc (Ly h)) (Spike.Lib.A64.PhRec.ph (Ly h))
        (fun _ => false) (Ly h).lab ((Ly h).lab (c.cx.local "abort_overflow") + Int64.ofNat (4 * 0)) 0
        A64.Abort.Local.lb = true)

/-- **The aborts of the code blocks at their contexts, held back at the
consumer's start, never end** (inside `SFactsS … OvfDt`): at each context
(`CtxB`, a `Good1` ghost with no hold) `hab_ofS` at the code block's
overflow abort label, its block's facts with a checked `+` in the walk
(`lowerC_addMem`, `hasAddChk_func1`, `OvfFactsS`), the abort path's facts
from the placement check, the frames placed and small from the context
(vacuous at an empty frame condition). -/
theorem abC_lag (hp : Scc.Lower.Accepted1 p = true) {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true)
    {rs : List Res1} {rt : List Scc.IR.Func}
    (hrs : Pairwise2 (LowC p cfg.layout.obj none) p rs)
    (hir : (Scc.Lower.A64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {T : Nat → Expr → Prop} (hT : ∀ j d, p[j]? = some d → ∀ e, T j e → InWalkD none d e)
    (hcode : ∀ j d, p[j]? = some d →
      FnCode (Ly h).exe (Ly h).prog (Ly h).endPc RaOk Cd (Scc.Lower.imms1Of p) (T j) d)
    (hok : ∀ j d (hd : p[j]? = some d), OvfFactsS h rs rt (hcode j d hd) j) {cells : Nat} :
    SegWS (WSS h cells) (KS h) p (Ly h).Λ.static (MSS h)
      (LagS p (· = Spike.Lib.A64Consumer.c0) (AbS h hcode)) (fun _ _ _ => False) := by
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms1Of p) (rS := Spike.Lib.A64.Rt.rS0 (Ly h))
  have hsub : (Spike.Lib.A64.Rt.rS0 (Ly h)).Sub (Ly h).Λ.stackPool := Spike.Lib.A64.Rt.rS0_sub (Ly h)
  have hfit : (Spike.Lib.A64.Rt.rS0 (Ly h)).lo + (Spike.Lib.A64.Rt.rS0 (Ly h)).size ≤ 2 ^ 64 := by
    have := (Ly h).pool_fit; obtain ⟨-, h2⟩ := hsub; omega
  have hsd := hprog_ofPlaceOK h (Scc.Lower.imms1Of p)
  have key : ∀ j d (hd : p[j]? = some d) R F tp fp ra c0 fs', SegWS (WSS h cells) (KS h) p (Ly h).Λ.static (MSS h)
      (fun s c fs => (CtxB p (O).place.need (Ly h).Λ (Ly h).Λ.static (MSS h) (Spike.Lib.A64.Rt.rS0 (Ly h))
          j R F fs' tp ∧ Good1 p (c0, fs')) ∧
        LagS p (· = Spike.Lib.A64Consumer.c0) ((At (Ly h).exe (Ly h).endPc R F
          (abortN (Scc.Lower.imms1Of p) (T j) p (Ly h).Λ.static (hcode j d hd).cx
            (_root_.Executable.labels (Ly h).exe).label fp ra c0)).at fs') s c fs) (fun _ _ _ => False) := by
    intro j d hd R F tp fp ra c0 fs'
    by_cases hcond : CtxB p (O).place.need (Ly h).Λ (Ly h).Λ.static (MSS h) (Spike.Lib.A64.Rt.rS0 (Ly h))
          j R F fs' tp ∧ Good1 p (c0, fs')
    case neg => exact SegWS.empty fun _ _ _ hx => hcond hx.1
    obtain ⟨hc, hg⟩ := hcond
    by_cases hne : ∃ m, F m
    case neg =>
      refine SegWS.empty fun _ _ _ hx => ?_
      obtain ⟨-, -, -, -, -, ⟨⟨-, -, -, -, σ, -, hD, -⟩, -⟩, -⟩ := hx
      exact hne ⟨_, hD⟩
    obtain ⟨m0, hm0⟩ := hne
    obtain ⟨r, hr, hfrm, henv, hn, hrr, hfr, hovf⟩ := hok j d hd
    have hown := ownRoom_of_placeOK h hrs hir hd hr (hc.room d hd)
    rw [← hfr] at hown
    have hl8 := hc.hl8
    have hhi := hc.hhi
    refine (hab_ofS (hcode j d hd).hf (hcode j d hd).h16 hI (Dt := OvfDt (Ly h).exe (Ly h).endPc (Ly h).lab) ?_
      hsd (Spike.Lib.A64.PhRec.abortPhOk_ofPlaceOK h (Scc.Lower.imms1Of p))
      Spike.Lib.A64.Flow.Ret0.Inst.cfacts_c0
      rfl (hrel_ofPlaceOK h (Scc.Lower.imms1Of p)) (htk_ofPlaceOK h (Scc.Lower.imms1Of p))
      (hk_ofPlaceOK h (Scc.Lower.imms1Of p)) (hKex_ofPlaceOK h (Scc.Lower.imms1Of p))
      (hms_ofPlaceOK h (Scc.Lower.imms1Of p) (rd := fun _ => True) (G := G0 h)
        (own := Spike.Lib.A64.PhRec.own (Ly h)) (lbl := (Ly h).Λ.static) (lsize := fun _ => 0))
      rfl (fun _ _ hal hlo hhi _ _ _ hA => ovfDt_of_at hal hlo hhi hA) hp (good1_tail rfl) hg
      (fun s hF => (Classical.choose_spec (hc.hFP s hF)).toFramesPlaced) (hc.hes m0 hm0)
      hc.hR hc.hb16 (by omega) (by omega) hl8 (by omega) hc.hF hsub hfit hc.hFO).mono_pre fun _ _ _ hx => hx.2
    rintro ⟨x, a, b, e, hTe⟩
    obtain ⟨q, hq, hqe⟩ := hT j d hd _ hTe
    obtain ⟨i, hi, d', u, v, he⟩ := Spike.Lib.LowerShape.lowerC_addMem (hcode j d hd).lcx d.body
      (hcode j d hd).env (hcode j d hd).n (hcode j d hd).l (hcode j d hd).k (hcode j d hd).r (hcode j d hd).hr q
      (by rw [hfrm, henv, hn]; exact hq) x a b e hqe
    rw [hrr] at hi
    exact hovf (hasAddChk_func1 hi he)
  refine SegWS.mono_pre (SegWS.exists_pre fun j => SegWS.exists_pre fun d => SegWS.exists_pre fun hd =>
    SegWS.exists_pre fun R => SegWS.exists_pre fun F => SegWS.exists_pre fun tp => SegWS.exists_pre fun fp =>
    SegWS.exists_pre fun ra => SegWS.exists_pre fun c0 => SegWS.exists_pre fun fs' =>
      key j d hd R F tp fp ra c0 fs') ?_
  rintro s c fs ⟨rfl, hC, c', fs', ⟨j, d, hd, R, F, tp, fp, ra, c0, hc, -, hg, -, hA⟩, hr⟩
  exact ⟨j, d, hd, R, F, tp, fp, ra, c0, fs', ⟨hc, hg⟩, rfl, hC, c', fs', ⟨hA, rfl⟩, hr⟩

/-- **A code block's code facts' fields** (`fnCode_ofPlaceOKR`'s): the
`j`th code block `d`'s closed form `r` (`rs[j]`), its context's program and
no frames limit (plain calls), its entry environment and counter, its parameter
registers, its frame (`ctxOf` at its index past the runtime's `rt`) and
block predicate, with a checked `+` the overflow block's code and phase
facts, and the prologue's phase facts at its spills. -/
def CodeFactsS {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true) (rs : List Res1)
    (rt : List Scc.IR.Func) {T : Expr → Prop} {d : Decl}
    (c : FnCode (Ly h).exe (Ly h).prog (Ly h).endPc (RaOkS h) (CdS h) (Scc.Lower.imms1Of p) T d) (j : Nat) : Prop :=
  ∃ r, rs[j]? = some r ∧ c.lcx.prog = p ∧ c.lcx.frames = none ∧ c.env = env1 d ∧ c.n = 0 ∧ c.r = r ∧
    c.prs = params1R d ∧
    c.cx = ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir (rt.length + j)
      (func1 (Scc.Lower.Names.user d.name) (params1R d) r) ∧
    c.Bl = (BlS h) c.cx ∧
    (hasAddChk (func1 (Scc.Lower.Names.user d.name) (params1R d) r) = true →
      Scc.Cert.Rt.A64.blockAt (O).prog (c.cx.local "abort_overflow") 0 ovfBlk = true ∧
      Spike.Lib.A64Consumer.blkPh (Spike.Lib.A64.PhRec.okPc (Ly h)) (Spike.Lib.A64.PhRec.ph (Ly h))
        (fun _ => false) (Ly h).lab ((Ly h).lab (c.cx.local "abort_overflow") + Int64.ofNat (4 * 0)) 0
        A64.Abort.Local.lb = true) ∧
    ProPh (Spike.Lib.A64.PhRec.okPc (Ly h)) (Spike.Lib.A64.PhRec.ph (Ly h)) (Ly h).lab
      (c.cx.local "stack_check") (Int64.ofInt c.cx.frame) (proL c.cx) c.ps

/-- **The code facts' fields give the aborts' fields** (`abC_lag`'s
`hok`). -/
theorem CodeFactsS.ovfFacts {Λ : Scc.Sem.Layout} {h : placeOKAt pcfg Λ (O) = true} {rs : List Res1}
    {rt : List Scc.IR.Func} {T : Expr → Prop} {d : Decl}
    {c : FnCode (Ly h).exe (Ly h).prog (Ly h).endPc (RaOkS h) (CdS h) (Scc.Lower.imms1Of p) T d} {j : Nat}
    (hc : CodeFactsS h rs rt c j) : OvfFactsS h rs rt c j :=
  let ⟨r, hr, _, hfrm, henv, hn, hrr, _, hcx, _, hovf, _⟩ := hc
  ⟨r, hr, hfrm, henv, hn, hrr, hcx, hovf⟩

/-- **Every code block's code facts with no frames limit, indexed by
position** (`fnCode_ofPlaceOKR`'s conclusion, the lowering's calls plain,
`lowerNoneS_ofPlaceOK`): the closed forms
`rs` with no frames limit and the runtime's functions `rt`, the walk
predicates `T j` (the `j`th code block's walk), the code facts `hcode` and
their fields `CodeFactsS`. -/
def LowerNoneS {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true) : Prop :=
  ∃ (rs : List Res1) (rt : List Scc.IR.Func), Pairwise2 (LowC p cfg.layout.obj none) p rs ∧
    (Scc.Lower.A64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs) ∧
    ∃ (T : Nat → Expr → Prop), (∀ j d, p[j]? = some d → ∀ e, T j e → InWalkD none d e) ∧
      ∃ hcode : (∀ j d, p[j]? = some d →
        FnCode (Ly h).exe (Ly h).prog (Ly h).endPc (RaOkS h) (CdS h) (Scc.Lower.imms1Of p) (T j) d),
        ∀ j d (hd : p[j]? = some d), CodeFactsS h rs rt (hcode j d hd) j

/-- **`LowerNoneS` from the placement check**: the lowering lowers calls
plain (no frames limit), so `fnCode_ofPlaceOKR`'s code facts are at no
frames limit; the `j`th code block's walk `T j` is its declaration's
`InWalkD none`. -/
theorem lowerNoneS_ofPlaceOK (hp : Scc.Lower.Accepted1 p = true) {em : Scc.Lower.A64.Emitted}
    (hlow : Scc.Lower.A64.lowerAll? cfg p = .ok em) {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true) :
    LowerNoneS h := by
  obtain ⟨rs, rt, hrs, hir, H⟩ := fnCode_ofPlaceOKR hp hlow h
  refine ⟨rs, rt, hrs, hir, fun j e => ∃ d, p[j]? = some d ∧ InWalkD none d e, ?_,
    fun j d hd => (Classical.choose_spec (H j d hd)).choose.monoT fun e he => ⟨d, hd, he⟩, fun j d hd => ?_⟩
  · rintro j d hd e ⟨d', hd', he⟩
    rw [hd] at hd'
    cases hd'
    exact he
  · obtain ⟨hr, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := (Classical.choose_spec (H j d hd)).choose_spec
    exact ⟨_, hr, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- The body's facts at the frames, the consumer's start held back. -/
local notation "WS" h:max cells:max => BodyWS0 (Ly h).Λ (μ (Ly h)) p (Spike.Lib.A64.PhRec.own (Ly h))
  (Spike.Lib.A64.Rt.rS0 (Ly h)) (Spike.Lib.A64.PhRec.Tk (Ly h)) (Ly h).Λ.static cells 0 Spike.Lib.A64Consumer.c0

/-- The first stack's top. -/
local notation "TOP" h:max => Ret0.stacksA (Ly h).lab + 0#64 + 16384#64

/-- The first thread's pointer. -/
local notation "TP0" h:max => UInt64.ofBitVec (Ret0.pinA (Ly h).lab + 0#64 + 8#64)

/-- `scc_rt_main`'s region after the switch, at `main`'s depth `D`. -/
local notation "RS1" h:max D:max => swR (TOP h) (-(D + 48)) 0

/-- `main`'s region, below `scc_rt_main`'s frame. -/
local notation "RM" h:max D:max => (RS1 h D).callee (-bareMC.Z.toInt) (-D) 0

/-- **The limit word's values are 16-aligned** (the limit `scc_rt_stacks +
4096`, `scc_rt_stacks` 16-aligned, or the initial `0`). -/
theorem g16_ofPlaceOK {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true) :
    ∀ v : Val, (G0 h) ⟨Ret0.limA (UInt64.ofBitVec ((Ly h).pinA + 0#64 + 8#64)), 8⟩ v →
      (v.setWidth 64).toNat % 16 = 0 := by
  intro v hv
  rw [Spike.Lib.A64.Rt.limA_tcb0 (RuntimeLayout.ofPlaceOK h (Scc.Lower.imms1Of p))] at hv
  rcases Spike.Lib.A64.PhRec.gOf_lim (show Spike.Lib.A64.PhRec.GOf (Ly h)
      (Spike.Lib.A64.PhRec.m0Of (Ly h).Λ (O).prog (O).secs) ⟨(Ly h).pinA + 16#64, 8⟩ v from hv) with rfl | rfl
  · have := (Ly h).pool_fit
    have := (Ly h).stacks_al
    obtain ⟨h1, h2⟩ := (Ly h).stacks_sub
    simp only at h1 h2
    simp only [Spike.Lib.A64.PhRec.limV, BitVec.setWidth_setWidth_of_le _ (by decide : 64 ≤ 128),
      BitVec.setWidth_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · rw [Spike.Lib.A64.PhRec.limInit_ofPlaceOK h (Scc.Lower.imms1Of p)]
    simp

/-- **`main`'s context at `scc_rt_main`'s call** (`CtxB` at depth `0`): in
`main`'s region below `scc_rt_main`'s frame, after the switch to the first
stack's top, at `main`'s depth `D := needDA n` (its row's need `n` within
`12240`), the first thread's pointer; the limit word's facts from the
entry's (`hL`). -/
theorem mainCtxB {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true) {jm : Nat} {dm : Decl}
    (hdm : p[jm]? = some dm) (hnm : dm.name = "main") {l : String} {f n : Nat}
    (hrow : Scc.Cert.NeedA64.row? (O).place.need (Scc.Lower.Names.user "main") = some (l, f, n))
    (hn : n ≤ 12240) {a : BitVec 64} {F F' : MachineData → Prop} {Z : BitVec 64}
    (hF : ∀ m, F m → Spike.Lib.A64.Rt.swFSL (needDA n + 48) (Spike.Lib.A64.Rt.rS0 (Ly h)) (TOP h) a (TOP h) m)
    (hR0 : (RM h (needDA n)).OK) (hF' : FStable (RM h (needDA n)) F')
    (hFF : ∀ m, F' m → F m ∧ Ret0.CallerCells (RS1 h (needDA n)) (-bareMC.Z.toInt) (-needDA n) 0 m)
    (hL : Ret0.LimOk ((MSS h) []) F (Ly h).exe (Ly h).endPc (Ret0.limA (TP0 h)) Z) :
    CtxB p (O).place.need (Ly h).Λ (Ly h).Λ.static (MSS h) (Spike.Lib.A64.Rt.rS0 (Ly h)) jm
      (RM h (needDA n)) F' [] (TP0 h) := by
  have hZ : bareMC.Z.toInt = 48 := by decide
  have hD : needDA n = 8 * (((n : Int) + 48 + 7) / 8) := rfl
  have htop : (TOP h).toNat = (Ly h).stacksA.toNat + 16384 := by
    rw [Spike.Lib.A64.PhRec.stacksA_lab h (Scc.Lower.imms1Of p)]
    exact Spike.Lib.A64.Rt.top0_toNat _
  have hfit := (Ly h).pool_fit
  have hal := (Ly h).stacks_al
  obtain ⟨hs1, hs2⟩ := (Ly h).stacks_sub
  simp only at hs1 hs2
  have hok : (RS1 h (needDA n)).OK :=
    ⟨by simp only [swR]; omega, by simp only [swR]; omega⟩
  have hbm : ((RM h (needDA n)).base.toNat : Int) = (TOP h).toNat - 48 := by
    have : ((RM h (needDA n)).base.toNat : Int) = (TOP h).toNat + -bareMC.Z.toInt :=
      Region.callee_base (hi' := 0) (kc := -bareMC.Z.toInt) (lo' := -needDA n) hok
        (by show -(needDA n + 48) ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
    omega
  have htop8 : (TOP h).toNat % 8 = 0 := by omega
  refine ⟨hF', hR0, by omega,
    by show (-needDA n) % 8 = 0; omega, rfl, ?_, ?_, ?_, hL.rt, hL.mp, fun m hm => hL.unmapped m (hFF m hm).1, ?_,
    fun _ _ => ⟨fun _ => False, Spike.Lib.A64ConsumerS.FramesPlacedInI.nil _⟩, fun _ _ f hf => by simp at hf⟩
  · intro d hd
    rw [hdm] at hd
    cases hd
    rw [hnm]
    exact mainRoom_of_row hrow
  · intro d hd
    rw [hdm] at hd
    cases hd
    rw [hnm]
    refine ⟨l, f, n, hrow, fun v hv => ?_⟩
    have := Spike.Lib.A64.PhRec.room_of_le h (Scc.Lower.imms1Of p) (b := (Ly h).stacksA.toNat + 4096) (by omega) v
      (by rw [(Ly h).lab_pin] at hv; exact hv)
    omega
  · intro m hm
    exact Spike.Lib.A64.Flow.Ret0.Inst.stackOff_callee hok htop8 (by show (-(needDA n + 48)) % 8 = 0; omega)
      (by show (0 : Int) % 8 = 0; rfl) (by show -(needDA n + 48) ≤ _; omega) (by omega)
      (by show _ < (0 : Int); omega) (by rw [hZ]; decide) (hF _ (hFF m hm).1).2 (hFF m hm).2
  · intro v hv
    exact g16_ofPlaceOK h v (by rw [(Ly h).lab_pin] at hv; exact hv)

/-- **`main`'s argument is the unit** (`decl1` at `main`). -/
theorem argTy_main (hp : Scc.Lower.Accepted1 p = true) {j : Nat} {d : Decl} (hd : p[j]? = some d)
    (hnm : d.name = "main") : d.argTy = .unit := by
  have hp' := hp
  simp only [Scc.Lower.Accepted1, Bool.and_eq_true, decide_eq_true_eq] at hp'
  have hd1 := Spike.Lib.LowerCallOrder.decl1_of_decls1 hp'.1.2 hd
  simp only [Scc.Lower.decl1, Bool.and_eq_true, beq_iff_eq] at hd1
  have := hd1.1.2
  simpa [hnm] using this

/-- **A parameter spill's stores are at cells of the frame** (`proW_bodyS`'s
`hps`), at the frame's `Int64` size. -/
theorem spillsOk_of_paramSpill {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095)
    {ps : List (XReg × Int64)} {prs : List Scc.IR.Reg} (hsp : ParamSpill cx ps prs) :
    ∀ q ∈ ps, offOk (-(Int64.ofInt cx.frame).toInt) 0 (-(Int64.ofInt cx.frame).toInt + q.2.toInt) = true := by
  have hge := frame_ge16 hf
  have hF64 : (Int64.ofInt cx.frame).toInt = cx.frame := toInt_ofInt_small (by omega) (by omega)
  rw [hF64]
  rcases hsp with ⟨rfl, -⟩ | ⟨pr, o, rfl, -, -, -, hok⟩
  · intro q hq; cases hq
  · intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    exact hok

/-- **`main`'s `CalleePre` at `scc_rt_main`'s call**: at `main`'s context
(`mainCtxB`, the aborts `AbC`), from `scc_rt_main`'s return address (that
of `bareMC.e0 + 4`, `RaOk`), the interface's entry `uN0` with `sp` at the
region's base: the body's blocks (`hWbS_of`, `hWsS_of`), the aborts
(`CxOkC.hab`), the start's ghost (`good1_tail`), the prologue from its code
facts (`proW_bodyS`), and the entry's facts: the limit word's from `uN0`'s
(`LimOk`), its registers, the start's step into `main`'s body
(`nj_start`). The call premise `CallPre` is not part of `CalleePre`; it
stays the caller's. -/
theorem mainPre_of (hp : Scc.Lower.Accepted1 p = true) {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true)
    {rs : List Res1} {rt : List Scc.IR.Func} {cells : Nat} {T : Nat → Expr → Prop}
    (hcode : ∀ j d, p[j]? = some d →
      FnCode (Ly h).exe (Ly h).prog (Ly h).endPc (RaOkS h) (CdS h) (Scc.Lower.imms1Of p) (T j) d)
    (hok : ∀ j d (hd : p[j]? = some d), CodeFactsS h rs rt (hcode j d hd) j)
    {jm : Nat} {dm : Decl} (hdm : p[jm]? = some dm) (hfd : p.find? (·.name == "main") = some dm)
    {R : Region} {F F' : MachineData → Prop} {ZU : Int64} {g : Ret0.WcG}
    (hc : CtxB p (O).place.need (Ly h).Λ (Ly h).Λ.static (MSS h) (Spike.Lib.A64.Rt.rS0 (Ly h)) jm R F' []
      (TP0 h))
    (hFF : ∀ m, F' m → F m) (hlo : R.lo ≤ -((hcode jm dm hdm).cx.frame : Int))
    (hZU : ZU = Int64.ofInt (hcode jm dm hdm).cx.frame)
    (hra : g.ra = ((Ly h).lab bareMC.e0 + 4).toBitVec)
    (hcg : g.c0 = Spike.Lib.A64Consumer.c0) (htp : g.tp = TP0 h) :
    CalleePre (WS h cells) (KS h) p (Ly h).Λ.static (MSS h)
      (CxOkC p (O).place.need (Ly h).Λ (Ly h).Λ.static (MSS h) (Spike.Lib.A64.Rt.rS0 (Ly h))
        (AbS h hcode) jm)
      (hcode jm dm hdm) R F' [] g.fp g.ra (TP0 h) (fun c => Good1 p (c, []) ∧ c.hold = none) (AbS h hcode)
      (fun σ c => (Spike.Lib.A64.Rt.uN0 (Ly h).lab ((MSS h) []) F (Ly h).exe (Ly h).endPc bareMC.fn ZU g).J σ c ∧
        σ.regs.SP.toBitVec = R.base)
      Spike.Lib.A64Consumer.c0 := by
  have hnm : dm.name = "main" := by simpa using List.find?_some hfd
  have hu := argTy_main hp hdm hnm
  obtain ⟨r, hr, -, -, henv, -, -, hprs, -, -, -, hphP⟩ := hok jm dm hdm
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms1Of p) (rS := Spike.Lib.A64.Rt.rS0 (Ly h))
  have hR := hc.hR
  have hl8 := hc.hl8
  have hhi := hc.hhi
  have hb16 := hc.hb16
  have hra' : (RaOkS h) g.ra := by
    show _ = _
    rw [hra]
  have hg0 : Good1 p (Spike.Lib.A64Consumer.c0, []) ∧ Spike.Lib.A64Consumer.c0.hold = none := ⟨good1_tail rfl, rfl⟩
  have hsub : (Spike.Lib.A64.Rt.rS0 (Ly h)).Sub (Ly h).Λ.stackPool := Spike.Lib.A64.Rt.rS0_sub (Ly h)
  have hfit := Spike.Lib.A64.Rt.fitS_of_sub (Ly h) hsub
  have hG0' : ∀ c c', Good1 p (c, []) ∧ c.hold = none → FrameRun p (c, []) (c', []) →
      Good1 p (c', []) ∧ c'.hold = none :=
    fun c c' hg hr'' => ⟨good1_run hp hr'' hg.1, FrameRun.hold_none hr'' hg.2⟩
  have hh8 : R.hi % 8 = 0 := by rw [hhi]; rfl
  have hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (Ly h).Λ) false ⟨Ret0.limA (TP0 h), 8⟩ = true := by
    rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.limA_tcb0]
    exact ((Ly h).words_mapped _ ((Ly h).fld_mem (by decide))).2.1
  refine ⟨⟨hc, rfl, rfl⟩, hra', hc.hF, hR, hb16, hlo, by omega, hG0', ?_, ?_, CxOkC.hab hdm ⟨hc, rfl, rfl⟩ hra',
    hg0, ?_, ?_⟩
  · exact hWbS_of (hcode jm dm hdm).hf (hcode jm dm hdm).h1 (hcode jm dm hdm).h16 hI hR hb16 hlo (by omega) hl8 hh8
      hsub hfit hc.hFO Spike.Lib.A64.Flow.Ret0.Inst.cfacts_c0 hp (good1_tail rfl) rfl hG0' fun _ h => h
  · exact hWsS_of (hcode jm dm hdm).hf (hcode jm dm hdm).h1 (hcode jm dm hdm).h16 hI hR hb16 hlo (by omega) hl8 hh8
      hsub hfit hc.hFO Spike.Lib.A64.Flow.Ret0.Inst.cfacts_c0 hp (good1_tail rfl) rfl hG0' fun _ h => h
  · exact proW_bodyS hI (hcode jm dm hdm).hf (hcode jm dm hdm).h1 (hcode jm dm hdm).h16 (hcode jm dm hdm).hpro
      (spillsOk_of_paramSpill (hcode jm dm hdm).hf (hcode jm dm hdm).h1 (hcode jm dm hdm).hsp) hphP
      Spike.Lib.A64.Flow.Ret0.Inst.cfacts_c0 hp (good1_tail rfl)
      (fun σ c ⟨⟨⟨hc0, _, _, _, htp0⟩, _⟩, _⟩ =>
        ⟨htp0.trans htp, by rw [hc0, hcg]; exact hg0.1, by rw [hc0, hcg]; exact hg0.2⟩)
      hR hb16 hlo (by omega) hl8 hh8 hmr hc.limUn hsub hfit hc.hFO
  · rintro σ c ⟨⟨⟨hc0, hfp, hsl, hsp0, htp0⟩, hlim⟩, -⟩
    rw [hcg] at hc0
    subst hc0
    have hlim' := hlim.mono hFF
    rw [htp] at hlim'
    rw [show tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit) = Ret0.limA (TP0 h) from
      Spike.Lib.A64.Flow.Ret0.tcbA_limA (htp0.trans htp)]
    refine ⟨⟨hlim'.rt, hlim'.mp, hlim'.unmapped, fun v hv => ?_⟩, hfp, hsl, fun sl _ => ?_, .refl _⟩
    · rw [hsp0, ← hZU]; exact hlim'.room v hv
    · rw [henv]
      simp only [env1, params1R, hu]
      exact nj_start hfd hu

/-- **`main`'s return at the interface's post** (`userCallWS_of_exitCL`'s
`hret`): the return's exit, after a frame run from the held-back start
`c0` to its control, is the interface's return `uNx` at `UPostS` from
`c0`, in the same region (AArch64: no return address on the stack, no
rebasing). -/
theorem uPostS_ret {exe : _root_.Executable} {endPc : Int64} {lbl : WeakMem.AllocLabel → Option Nat}
    {R : Region} {F : MachineData → Prop} {g : Ret0.WcG} {c0 c1 c : Ctl} {s : State} {tp : UInt64}
    (hr : FrameRun p (c0, []) (c, []))
    (hA : At exe endPc R F ((retN p lbl g.fp g.ra c1).withTp tp) s c) :
    At exe endPc R F (Spike.Lib.A64.Rt.uNx (UPostS p lbl c0) g) s c0 := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨⟨a, t, w, hta, hho, hev, hnm, hv, hfp, hra⟩, -⟩, -⟩ := hA
  exact ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨rfl, c, hr, a, t, w, hta, hho, hev, hnm, hv⟩, hfp, hra⟩

end Main

end Spike.Lib.LowerA64
