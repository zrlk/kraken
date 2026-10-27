/-
**The user `main` of an `Accepted1` program with calls as `scc_rt_main`'s
user function from the placement check** (x86-64, H7a calls): the aborts
of the code blocks at their contexts held back never end, `main`'s context
and premises at `scc_rt_main`'s call, and `x64_lower_correctES_of_user`'s
`hU` from the code facts (the lowering's closed forms with no frames
limit: plain calls).

- `abC_lag`: the aborts `AbC` held back at the consumer's start, inside
  `SFactsS`, never end (`hab_ofS` at each context).
- `mainCtxB`: `main`'s context `CtxB` at `scc_rt_main`'s call, below its
  frame after the switch to the first stack's top.
- `argTy_main`: `main`'s argument is the unit.
- `mainPre_of`: `main`'s `CalleePre` at the interface's entry `uN0`.
- `uPostS_ret`: `main`'s return is the interface's return `uNx` at
  `UPostS`.
- `userMainSW_of`: `x64_lower_correctES_of_user`'s `hU` from
  `userCallWS_of_exitCL`.
- `fnCodes_ofPlaceOK`: every function's code at its placement, lowered with
  no frames limit (plain calls), from `fnCode_ofPlaceOKR`.
- `userMainSW_ofPlaceOK`: `userMainSW_of`'s conclusion from the placement
  check.
-/
import Spike.Lib.LowerX64.PreC
import Spike.Lib.LowerX64.AbortCallS
import Spike.Lib.LowerX64.AbortOfPlaceOK
import Spike.Lib.LowerX64.UserLag
import Spike.Lib.LowerX64.OvfDt
import Spike.Lib.LowerX64.MainD
import Spike.Lib.LowerX64.MainRoomU
import Spike.Lib.LowerX64.UPostS

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (limA tpOf)
open Scc.Lower.InvX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Lower.Inv (Res1 func1 params1R env1)
open Spike.Lib.LowerNode (Pairwise2 LowC funcs1)
open Spike.Lib.X64ConsumerS (SFactsS msOfS)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.PhRec (μ K)

section Main

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

/-- The facts every pair of the run carries at its frames, at the arena's
`cells` and the overflow stub's write tail. -/
local notation "WSS" h:max cells:max => fun s c fs => SFactsS (Ly h).Λ (μ (Ly h)) p
  (fun s _ => Spike.Lib.X64.PhRec.own (Ly h) s) (Spike.Lib.X64.Rt.rS0 (Ly h)) (Spike.Lib.X64.PhRec.Tk (Ly h))
  (Ly h).Λ.static cells 0 s c fs (OvfDt (Ly h).exe (Ly h).endPc (Ly h).lab)

/-- The outside move: the take of the first stack. -/
local notation "KS" h => K (Ly h) (Spike.Lib.X64.Rt.rS0 (Ly h))

/-- The return addresses in the phase of `raL`. -/
local notation "RaOkS" h => fun ra : BitVec 64 => Spike.Lib.X64.PhRec.ph (Ly h) (Int64.ofBitVec ra).toBitVec.toNat =
  Spike.Lib.X64.PhRec.ph (Ly h) ((Ly h).lab raL).toBitVec.toNat

/-- The code predicate at a return address. -/
local notation "CdS" h => fun ra : BitVec 64 => CdC (O).prog (Spike.Lib.X64.PhRec.okPc (Ly h))
  (Spike.Lib.X64.PhRec.ph (Ly h)) (Ly h).lab (Int64.ofBitVec ra)

/-- The aborts of the code blocks at their contexts. -/
local notation "AbS" h:max hcode:max => AbC p (O).place.need (Ly h).Λ (Ly h).Λ.static (MSS h)
  (Spike.Lib.X64.Rt.rS0 (Ly h)) hcode

/-- The body's facts at the frames, the consumer's start held back. -/
local notation "WS" h:max cells:max => BodyWS0 (Ly h).Λ (μ (Ly h)) p (Spike.Lib.X64.PhRec.own (Ly h))
  (Spike.Lib.X64.Rt.rS0 (Ly h)) (Spike.Lib.X64.PhRec.Tk (Ly h)) (Ly h).Λ.static cells 0 Spike.Lib.X64Consumer.c0

/-- **The aborts of the code blocks at their contexts, held back at the
consumer's start, never end** (inside `SFactsS … OvfDt`): at each context
(`CtxB`, a `Good1` ghost with no hold) `hab_ofS` at the code block's
overflow abort label, its block's facts with a checked `+` in the walk
(`lowerC_addMem`, `hasAddChk_func1`, `CodeFactsS`), the abort path's facts
from the placement check, the frames placed and small from the context
(vacuous at an empty frame condition). -/
theorem abC_lag (hp : Scc.Lower.Accepted1 p = true) {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true)
    {rs : List Res1} {rt : List Scc.IR.Func}
    (hrs : Pairwise2 (LowC p cfg.layout.obj none) p rs)
    (hir : (Scc.Lower.X64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    {T : Nat → Expr → Prop} (hT : ∀ j d, p[j]? = some d → ∀ e, T j e → InWalkD none d e)
    (hcode : ∀ j d, p[j]? = some d →
      FnCode (Ly h).exe (Ly h).prog (Ly h).endPc (RaOkS h) (CdS h) (Scc.Lower.imms1Of p) (T j) d)
    (hok : ∀ j d (hd : p[j]? = some d), CodeFactsS h rs (hcode j d hd) j) {cells : Nat} :
    SegWS (WSS h cells) (KS h) p (Ly h).Λ.static (MSS h)
      (LagS p (· = Spike.Lib.X64Consumer.c0) (AbS h hcode)) (fun _ _ _ => False) := by
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms1Of p) (rS := Spike.Lib.X64.Rt.rS0 (Ly h))
  have hsub : (Spike.Lib.X64.Rt.rS0 (Ly h)).Sub (Ly h).Λ.stackPool := Spike.Lib.X64.Rt.rS0_sub (Ly h)
  have hfit : (Spike.Lib.X64.Rt.rS0 (Ly h)).lo + (Spike.Lib.X64.Rt.rS0 (Ly h)).size ≤ 2 ^ 64 := by
    have := (Ly h).pool_fit; obtain ⟨-, h2⟩ := hsub; omega
  have hsd := hprog_ofPlaceOK h (Scc.Lower.imms1Of p)
  have key : ∀ j d (hd : p[j]? = some d) R F tp fp ra c0 fs', SegWS (WSS h cells) (KS h) p (Ly h).Λ.static (MSS h)
      (fun s c fs => (CtxB p (O).place.need (Ly h).Λ (Ly h).Λ.static (MSS h) (Spike.Lib.X64.Rt.rS0 (Ly h))
          j R F fs' tp ∧ Good1 p (c0, fs')) ∧
        LagS p (· = Spike.Lib.X64Consumer.c0) ((At (Ly h).exe (Ly h).endPc (rbR R) F
          (abortN (Scc.Lower.imms1Of p) (T j) p (Ly h).Λ.static (hcode j d hd).fr
            (_root_.Executable.labels (Ly h).exe).label fp ra c0)).at fs') s c fs) (fun _ _ _ => False) := by
    intro j d hd R F tp fp ra c0 fs'
    by_cases hcond : CtxB p (O).place.need (Ly h).Λ (Ly h).Λ.static (MSS h) (Spike.Lib.X64.Rt.rS0 (Ly h))
          j R F fs' tp ∧ Good1 p (c0, fs')
    case neg => exact SegWS.empty fun _ _ _ hx => hcond hx.1
    obtain ⟨hc, hg⟩ := hcond
    by_cases hne : ∃ m, F m
    case neg =>
      refine SegWS.empty fun _ _ _ hx => ?_
      obtain ⟨-, -, -, -, -, ⟨⟨-, -, -, -, σ, -, hD, -⟩, -⟩, -⟩ := hx
      exact hne ⟨_, hD⟩
    obtain ⟨m0, hm0⟩ := hne
    obtain ⟨r, hr, -, hfrm, henv, hn, hrr, -, hfr, -, hovf, -⟩ := hok j d hd
    have hown := ownRoom_of_placeOK h hrs hir hd hr (hc.room d hd)
    rw [← hfr] at hown
    have hR := hc.hR
    have hl8 := hc.hl8
    have hhi := hc.hhi
    have hb16 := hc.hb16
    have hrb := rbR_base hR (by omega) (by omega)
    refine (hab_ofS (hcode j d hd).hf hI (Dt := OvfDt (Ly h).exe (Ly h).endPc (Ly h).lab) ?_ hsd
      (hsysIn_ofPlaceOK h (Scc.Lower.imms1Of p)) (Spike.Lib.X64.PhRec.abortPhOk_ofPlaceOK h (Scc.Lower.imms1Of p))
      Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0
      rfl (hrel_ofPlaceOK h (Scc.Lower.imms1Of p)) (htk_ofPlaceOK h (Scc.Lower.imms1Of p))
      (hk_ofPlaceOK h (Scc.Lower.imms1Of p)) (hKex_ofPlaceOK h (Scc.Lower.imms1Of p))
        (hms_ofPlaceOK h (Scc.Lower.imms1Of p) (rd := fun _ => True) (G := G0 h) (own := Spike.Lib.X64.PhRec.own (Ly h))
          (lbl := (Ly h).Λ.static) (lsize := fun _ => 0))
      rfl (fun _ _ hlo hhi _ _ _ hA => ovfDt_of_at hlo hhi hA) hp (good1_tail rfl) hg
      (fun s hF => (Classical.choose_spec (hc.hFP s hF)).toFramesPlaced) (hc.hes m0 hm0)
      (rbR_ok hR (by omega) (by omega)) (by omega) (by show R.lo + 8 ≤ _; omega)
      (by show (0 : Int) ≤ R.hi + 8; omega) (by show (R.lo + 8) % 8 = 0; omega)
      (by show (R.hi + 8) % 8 = 0; omega) (rbR_fstable hR (by omega) (by omega) hc.hF) hsub hfit
      (fun m hm => stackOff_rbR hR (by omega) (by omega) (hc.hFO m hm))).mono_pre fun _ _ _ hx => hx.2
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

/-- The first stack's top. -/
local notation "TOP" h:max => Ret0.stacksA (Ly h).lab + 0#64 + 16384#64

/-- The first thread's pointer. -/
local notation "TP0" h:max => tpOf (Ret0.pinA (_root_.Executable.labels (Ly h).exe).label + 0#64 + 8#64)

/-- `scc_rt_main`'s region after the switch, at `main`'s depth `D`. -/
local notation "RS1" h:max D:max => (swR (TOP h) (-(D + 56)) 0).callee (-8 - 0) (8 - (D + 56)) 8

/-- `main`'s region, below `scc_rt_main`'s frame. -/
local notation "RM" h:max D:max => (RS1 h D).callee (-8 - Spike.Lib.X64.Rt.bareMC.Z.toInt - 8 - 0) (-D) 8

/-- **`main`'s context at `scc_rt_main`'s call** (`CtxB` at depth `0`): in
`main`'s region below `scc_rt_main`'s frame, after the switch to the first
stack's top, at `main`'s depth `D := needD fr n` (its row's need `n` within
`12240`), the first thread's pointer; the limit word's facts from the
entry's (`hL`). -/
theorem mainCtxB {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true) {jm : Nat} {dm : Decl}
    (hdm : p[jm]? = some dm) (hnm : dm.name = "main") {fr : Scc.Emit.X64.Frame} {l : String} {g n : Nat}
    (hrow : Scc.Cert.NeedX64.row? (O).place.need (Scc.Lower.Names.user "main") = some (l, g, n))
    (hn : n ≤ 12240) (hD0 : 0 ≤ needD fr n) (hD8 : needD fr n % 8 = 0) (hD : needD fr n + 56 ≤ 16384)
    {a : BitVec 64} {F F' : MachineData → Prop} {Z : BitVec 64}
    (hF : ∀ m, F m → Spike.Lib.X64.Rt.swFSL (needD fr n + 56) (Spike.Lib.X64.Rt.rS0 (Ly h)) (TOP h) a (TOP h) m ∧
      Ret0.CallerCells (swR (TOP h) (-(needD fr n + 56)) 0) (-8 - 0) (8 - (needD fr n + 56)) 8 m)
    (hR0 : (RM h (needD fr n)).OK) (hF' : FStable (RM h (needD fr n)) F')
    (hFF : ∀ m, F' m → F m ∧
      Ret0.CallerCells (RS1 h (needD fr n)) (-8 - Spike.Lib.X64.Rt.bareMC.Z.toInt - 8 - 0) (-needD fr n) 8 m)
    (hL : Ret0.LimOk ((MSS h) []) F (limA (TP0 h)) Z) :
    CtxB p (O).place.need (Ly h).Λ (Ly h).Λ.static (MSS h) (Spike.Lib.X64.Rt.rS0 (Ly h)) jm
      (RM h (needD fr n)) F' [] (TP0 h) := by
  have hZ : Spike.Lib.X64.Rt.bareMC.Z.toInt = 32 := by decide
  have htop : (TOP h).toNat = (Ly h).stacksA.toNat + 16384 := by
    rw [Spike.Lib.X64.PhRec.stacksA_lab h (Scc.Lower.imms1Of p)]
    exact Spike.Lib.X64.Rt.top0_toNat _
  have hfit := (Ly h).pool_fit
  have hal := (Ly h).stacks_al
  obtain ⟨hs1, hs2⟩ := (Ly h).stacks_sub
  simp only at hs1 hs2
  have hok : (swR (TOP h) (-(needD fr n + 56)) 0).OK :=
    ⟨by simp only [swR]; omega, by simp only [swR]; omega⟩
  have hR1 : (RS1 h (needD fr n)).OK :=
    Region.callee_ok hok (by show -(needD fr n + 56) ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
      (by show _ ≤ (0 : Int); omega)
  have hb1 : ((RS1 h (needD fr n)).base.toNat : Int) = (TOP h).toNat - 8 :=
    Region.callee_base hok (by show -(needD fr n + 56) ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
  have hbm : ((RM h (needD fr n)).base.toNat : Int) = (TOP h).toNat - 56 := by
    have := Region.callee_base (hi' := 8) (kc := -8 - Spike.Lib.X64.Rt.bareMC.Z.toInt - 8 - 0)
      (lo' := -needD fr n) hR1 (by show 8 - (needD fr n + 56) ≤ _; omega) (by omega) (by show _ < (8 : Int); omega)
    omega
  have htop8 : (TOP h).toNat % 8 = 0 := by omega
  have hb8 : (RS1 h (needD fr n)).base.toNat % 8 = 0 := by omega
  refine ⟨hF', hR0, by omega, by show (-needD fr n) % 8 = 0; omega,
    rfl, ?_, ?_, ?_, hL.rt, hL.mp, fun m hm => hL.unmapped m (hFF m hm).1, ?_,
    fun _ _ => ⟨fun _ => False, Spike.Lib.X64ConsumerS.FramesPlacedInI.nil _⟩, fun _ _ f hf => by simp at hf⟩
  · intro d hd
    rw [hdm] at hd
    cases hd
    rw [hnm]
    exact mainRoom_of_row fr hrow
  · intro d hd
    rw [hdm] at hd
    cases hd
    rw [hnm]
    refine ⟨l, g, n, hrow, fun v hv => ?_⟩
    have := Spike.Lib.X64.PhRec.room_of_le h (Scc.Lower.imms1Of p) (b := (Ly h).stacksA.toNat + 4096) (by omega) v
      (by rw [(Ly h).lab_pin] at hv; exact hv)
    omega
  · intro m hm
    exact Spike.Lib.X64.Rt.stackOff_callee hR1 hb8 (by show (8 - (needD fr n + 56)) % 8 = 0; omega)
      (by show (8 : Int) % 8 = 0; decide) (by show 8 - (needD fr n + 56) ≤ _; omega) (by omega)
      (by show _ < (8 : Int); omega) (by omega)
      (Spike.Lib.X64.Rt.stackOff_callee hok htop8 (by show (-(needD fr n + 56)) % 8 = 0; omega)
        (by show (0 : Int) % 8 = 0; rfl) (by show -(needD fr n + 56) ≤ _; omega) (by omega)
        (by show _ < (0 : Int); omega) (by decide) (hF _ (hFF m hm).1).1.2 (hF _ (hFF m hm).1).2)
      (hFF m hm).2
  · intro v hv
    have := Spike.Lib.X64.PhRec.g16_ofPlaceOK h (Scc.Lower.imms1Of p) v (by rw [(Ly h).lab_pin] at hv; exact hv)
    exact this

/-- **`main`'s argument is the unit** (`decl1` at `main`). -/
theorem argTy_main (hp : Scc.Lower.Accepted1 p = true) {j : Nat} {d : Decl} (hd : p[j]? = some d)
    (hnm : d.name = "main") : d.argTy = .unit := by
  have hp' := hp
  simp only [Scc.Lower.Accepted1, Bool.and_eq_true, decide_eq_true_eq] at hp'
  have hd1 := Spike.Lib.LowerCallOrder.decl1_of_decls1 hp'.1.2 hd
  simp only [Scc.Lower.decl1, Bool.and_eq_true, beq_iff_eq] at hd1
  have := hd1.1.2
  simpa [hnm] using this

/-- **`main`'s `CalleePre` at `scc_rt_main`'s call**: at `main`'s context
(`mainCtxB`, the aborts `AbC`), from `scc_rt_main`'s return address
(`raL`'s, `RaOk`), the interface's entry `uN0` with `%rsp` at the region's
base: the body's blocks (`hWbS_of`, `hWsS_of`), the aborts (`CxOkC.hab`),
the start's ghost (`good1_tail`), the prologue from its code facts
(`proW_bodyS`), and the entry's facts: the limit word's from `uN0`'s
(`LimOk`), its registers, the start's step into `main`'s body
(`nj_start`). -/
theorem mainPre_of (hp : Scc.Lower.Accepted1 p = true) {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true)
    {rs : List Res1} {cells : Nat} {T : Nat → Expr → Prop}
    (hcode : ∀ j d, p[j]? = some d →
      FnCode (Ly h).exe (Ly h).prog (Ly h).endPc (RaOkS h) (CdS h) (Scc.Lower.imms1Of p) (T j) d)
    (hok : ∀ j d (hd : p[j]? = some d), CodeFactsS h rs (hcode j d hd) j)
    {jm : Nat} {dm : Decl} (hdm : p[jm]? = some dm) (hfd : p.find? (·.name == "main") = some dm)
    {R : Region} {F F' : MachineData → Prop} {ZU : Int64} {g : Ret0.WcG}
    (hc : CtxB p (O).place.need (Ly h).Λ (Ly h).Λ.static (MSS h) (Spike.Lib.X64.Rt.rS0 (Ly h)) jm R F' []
      (TP0 h))
    (hFF : ∀ m, F' m → F m) (hlo : R.lo ≤ -8 - ((hcode jm dm hdm).fr.size : Int))
    (hZU : ZU = Int64.ofInt (hcode jm dm hdm).fr.size)
    (hra : g.ra = ((_root_.Executable.labels (Ly h).exe).label Spike.Lib.X64.Rt.bareMC.sp0).toBitVec)
    (hcg : g.c0 = Spike.Lib.X64Consumer.c0) (htp : g.tp = TP0 h) :
    CalleePre (WS h cells) (KS h) p (Ly h).Λ.static (MSS h)
      (CxOkC p (O).place.need (Ly h).Λ (Ly h).Λ.static (MSS h) (Spike.Lib.X64.Rt.rS0 (Ly h))
        (AbS h hcode) jm)
      (hcode jm dm hdm) R F' [] g.fp g.ra (TP0 h) (fun c => Good1 p (c, []) ∧ c.hold = none) (AbS h hcode)
      (fun σ c => (Spike.Lib.X64.Rt.uN0 (_root_.Executable.labels (Ly h).exe).label ((MSS h) []) F
          Spike.Lib.X64.Rt.bareMC.fn ZU g).J σ c ∧ σ.regs.rsp.toBitVec = R.base)
      Spike.Lib.X64Consumer.c0 := by
  have hnm : dm.name = "main" := by simpa using List.find?_some hfd
  have hu := argTy_main hp hdm hnm
  obtain ⟨r, hr, -, -, henv, -, -, -, hfr, -, -, hphP⟩ := hok jm dm hdm
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms1Of p) (rS := Spike.Lib.X64.Rt.rS0 (Ly h))
  have hR := hc.hR
  have hl8 := hc.hl8
  have hhi := hc.hhi
  have hb16 := hc.hb16
  have hra' : (RaOkS h) g.ra := by
    show _ = _
    rw [hra, Int64.ofBitVec_toBitVec]
    rfl
  have hg0 : Good1 p (Spike.Lib.X64Consumer.c0, []) ∧ Spike.Lib.X64Consumer.c0.hold = none := ⟨good1_tail rfl, rfl⟩
  have hsub : (Spike.Lib.X64.Rt.rS0 (Ly h)).Sub (Ly h).Λ.stackPool := Spike.Lib.X64.Rt.rS0_sub (Ly h)
  have hfit : (Spike.Lib.X64.Rt.rS0 (Ly h)).lo + (Spike.Lib.X64.Rt.rS0 (Ly h)).size ≤ 2 ^ 64 := by
    have := (Ly h).pool_fit; obtain ⟨-, h2⟩ := hsub; omega
  have e1 : ∀ R'' : Region, (rbR R'').lo = R''.lo + 8 := fun _ => rfl
  have e2 : ∀ R'' : Region, (rbR R'').hi = R''.hi + 8 := fun _ => rfl
  have hrbOK := rbR_ok hR (by omega) (by omega)
  have hrb := rbR_base hR (by omega) (by omega)
  have hFOb := fun m hm => stackOff_rbR hR (by omega) (by omega) (hc.hFO m hm)
  have hG0' : ∀ c c', Good1 p (c, []) ∧ c.hold = none → FrameRun p (c, []) (c', []) →
      Good1 p (c', []) ∧ c'.hold = none :=
    fun c c' hg hr'' => ⟨good1_run hp hr'' hg.1, FrameRun.hold_none hr'' hg.2⟩
  refine ⟨⟨hc, rfl, rfl⟩, hra', hc.hF, hR, hlo, by omega, hG0', ?_, ?_, CxOkC.hab hdm ⟨hc, rfl, rfl⟩ hra',
    hg0, ?_, ?_⟩
  · exact hWbS_of (hcode jm dm hdm).hf (hcode jm dm hdm).h1 hI hrbOK (by omega)
      (by rw [e1]; omega) (by rw [e2]; omega) (by rw [e1]; omega) (by rw [e2]; omega) hsub hfit hFOb
      Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0 hp (good1_tail rfl) rfl hG0' fun _ h => h
  · exact hWsS_of (hcode jm dm hdm).hf (hcode jm dm hdm).h1 hI hrbOK (by omega)
      (by rw [e1]; omega) (by rw [e2]; omega) (by rw [e1]; omega) (by rw [e2]; omega) hsub hfit hFOb
      Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0 hp (good1_tail rfl) rfl hG0' fun _ h => h
  · exact proW_bodyS hI (hcode jm dm hdm).h1 (hcode jm dm hdm).hpro
      (spillsOk_of_hps (hcode jm dm hdm).h1 (hcode jm dm hdm).hps) hphP
      Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0 hp (good1_tail rfl)
      (fun σ c ⟨⟨⟨hc0, _, _, _, htp0⟩, _⟩, _⟩ =>
        ⟨htp0.trans htp, by rw [hc0, hcg]; exact hg0.1, by rw [hc0, hcg]; exact hg0.2⟩)
      hR (by omega) (by omega) (by omega) hl8 (by omega) hc.limMp.1 hc.limUn hsub hfit hc.hFO
  · rintro σ c ⟨⟨⟨hc0, hfp, hsl, hsp0, htp0⟩, hlim⟩, -⟩
    rw [hcg] at hc0
    subst hc0
    have hlim' := hlim.mono hFF
    rw [htp] at hlim'
    have ha : σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec = limA (TP0 h) := by
      rw [limA, htp0, htp]; rfl
    rw [ha]
    refine ⟨⟨hlim'.rt, hlim'.mp, hlim'.unmapped, fun v hv => ?_⟩, hfp, hsl, fun sl _ => ?_, .refl _⟩
    · rw [hsp0, ← hZU]; exact hlim'.room v hv
    · rw [henv]
      simp only [env1, params1R, hu]
      exact nj_start hfd hu

/-- **`main`'s return at the interface's post** (`userCallWS_of_exitCL`'s
`hret`): the return's exit past `ret` in the rebased region, after a frame
run from the held-back start `c0` to its control, is the interface's
return `uNx` at `UPostS` from `c0`, `%rsp` past the return address at the
entry's `%rsp` the region's base (`hbase`, `at_of_rbR`). -/
theorem uPostS_ret {exe : _root_.Executable} {endPc : Int64} {lbl : WeakMem.AllocLabel → Option Nat}
    {R : Region} {F : MachineData → Prop} {g : Ret0.WcG} {c0 c1 c : Ctl} {s : State} {tp : UInt64}
    (hbase : R.base = g.sp) (hr : FrameRun p (c0, []) (c, []))
    (hA : At exe endPc (rbR R) F ((retN p lbl g.fp g.ra c1).withTp tp) s c) :
    At exe endPc R F (Spike.Lib.X64.Rt.uNx (UPostS p lbl c0) g) s c0 := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD', ⟨⟨a, t, w, hta, hho, hev, hnm, hv, hbp⟩, -⟩, -⟩ := hA
  have h' : At exe endPc (rbR R) F ⟨Int64.ofBitVec g.ra, ⟨16, []⟩, fun σ (_ : Ctl) =>
      σ.regs.get64 .rbp = g.fp ∧ Scc.Sem.ValRep lbl w.val (σ.regs.get64 .rax).toNat⟩ s c :=
    ⟨he, hn, hdc, hpc, σ, hA, hD', hbp, hv⟩
  obtain ⟨he, hn, hdc, hpc, σ', hA', hD'', hbp', hv'⟩ :=
    at_of_rbR (J' := fun σ (_ : Ctl) => σ.regs.get64 .rbp = g.fp ∧ Scc.Sem.ValRep lbl w.val (σ.regs.get64 .rax).toNat)
      (fun _ _ h => h) h'
  have hsp := hA'.so .rsp (16 - 8) (by simp [SO.get])
  refine ⟨he, hn, hdc, hpc, σ', hA', hD'', ⟨rfl, c, hr, a, t, w, hta, hho, hev, hnm, hv'⟩, hbp', ?_⟩
  rw [show σ'.regs.rsp.toBitVec = σ'.regs.get64 .rsp from rfl, hsp, Region.addr, hbase]
  rfl

/-- `main`'s frame at its closed form `r`. -/
local notation "FRM" dm:max r:max =>
  frOf (Scc.Lower.X64.lowerAll cfg p).low.ir (func1 (Scc.Lower.Names.user (Decl.name dm)) (params1R dm) r)

/-- **The user `main` as `scc_rt_main`'s user function at depth, from
the placement check and the code facts** (`x64_lower_correctES_of_user`'s
`hU`): for
`main` (the `jm`th code block `dm`, closed form `r`, row need `n`) at its
depth `D := needD fr n` and limit room its frame `fr`, at every switch value
(vacuous off the first stack's top) and frame condition, `UserCallWS` inside
`SFactsS` from `userCallWS_of_exitCL`: the segment from `main`'s
`FnSpecC` (`fnSpecC_all_ofPlaceOK`) at its `CalleePre` (`mainPre_of`,
`mainCtxB`; vacuous where the entry's limit word facts fail), the held-back
aborts never ending (`abC_lag`), the return at `UPostS` (`uPostS_ret`). -/
theorem userMainSW_of (hp : Scc.Lower.Accepted1 p = true) {em : Scc.Lower.X64.Emitted}
    (hlow : Scc.Lower.X64.lowerAll? cfg p = .ok em) {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true)
    (hcfg : CfgNeedOk pcfg = true) {rs : List Res1}
    {rt : List Scc.IR.Func} (hrs : Pairwise2 (LowC p cfg.layout.obj none) p rs)
    (hir : (Scc.Lower.X64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    {cells : Nat} {T : Nat → Expr → Prop} (hT : ∀ j d, p[j]? = some d → ∀ e, T j e → InWalkD none d e)
    (hcode : ∀ j d, p[j]? = some d →
      FnCode (Ly h).exe (Ly h).prog (Ly h).endPc (RaOkS h) (CdS h) (Scc.Lower.imms1Of p) (T j) d)
    (hok : ∀ j d (hd : p[j]? = some d), CodeFactsS h rs (hcode j d hd) j)
    {jm : Nat} {dm : Decl} (hdm : p[jm]? = some dm) (hfd : p.find? (·.name == "main") = some dm) {r : Res1}
    (hr : rs[jm]? = some r) {l : String} {g n : Nat}
    (hrow : Scc.Cert.NeedX64.row? (O).place.need (Scc.Lower.Names.user "main") = some (l, g, n)) :
    ∀ v (F' : MachineData → Prop),
      (∀ m, F' m → Spike.Lib.X64.Rt.swFSL (needD (FRM dm r) n + 56) (Spike.Lib.X64.Rt.rS0 (Ly h)) (TOP h)
          (limA (tpOf (Ret0.pinA (Ly h).lab + 0#64 + 8#64))) v m ∧
          Ret0.CallerCells (swR v (-(needD (FRM dm r) n + 56)) 0) (-8 - 0) (8 - (needD (FRM dm r) n + 56)) 8 m) →
      Spike.Lib.X64.Rt.UserCallWS (WSS h cells) (KS h) p (Ly h).Λ.static (MSS h) (Ly h).exe (Ly h).endPc
        ((swR v (-(needD (FRM dm r) n + 56)) 0).callee (-8 - 0) (8 - (needD (FRM dm r) n + 56)) 8) F'
        Spike.Lib.X64.Rt.bareMC.fn Spike.Lib.X64.Rt.bareMC.Z (needD (FRM dm r) n) (Int64.ofInt (FRM dm r).size)
        (UPostS p (Ly h).Λ.static Spike.Lib.X64Consumer.c0)
        (((_root_.Executable.labels (Ly h).exe).label Spike.Lib.X64.Rt.bareMC.sp0).toBitVec)
        Spike.Lib.X64Consumer.c0 (TP0 h) := by
  intro v F' hF'
  have hnm : dm.name = "main" := by simpa using List.find?_some hfd
  obtain ⟨r', hr', -, -, -, -, -, -, hfr, -, -⟩ := hok jm dm hdm
  -- `main`'s IR function and its row
  obtain ⟨hjm, hpj⟩ := List.getElem?_eq_some_iff.mp hdm
  obtain ⟨hjr, hrj⟩ := List.getElem?_eq_some_iff.mp hr
  have hmem := Spike.Lib.LowerNode.mem_progOf_funcs1 cfg.layout rt hrs jm hjm
  rw [List.mem_zipIdx_iff_getElem?] at hmem
  have hf := List.mem_of_getElem? hmem
  rw [← hir] at hf
  simp only [hpj, hrj] at hf
  have hname : (func1 (Scc.Lower.Names.user dm.name) (params1R dm) r).name = Scc.Lower.Names.user "main" := by
    show Scc.Lower.Names.user dm.name = _; rw [hnm]
  obtain ⟨l', g', n', hr1, -, -, hD0, hD8, hD, hfrD, -⟩ := mainD_of_placeOKAt hp hlow h hcfg hf hname rfl
  rw [hname, hrow] at hr1
  cases hr1
  have hcfg' := hcfg
  simp only [CfgNeedOk, Bool.and_eq_true, decide_eq_true_eq] at hcfg'
  obtain ⟨a, n'', hr2, hb⟩ := mainRow_of_placeOKAt hp hlow h hcfg'.1 hf hname rfl
  rw [hname, hrow] at hr2
  cases hr2
  have hn : n ≤ 12240 := by
    have := mainThread0_frame (Scc.Lower.X64.lowerAll cfg p).low.ir
    omega
  by_cases hv : v = TOP h
  case neg =>
    intro F'' _ _ hFF _ _ _ _
    exact SegWS.empty fun s c fs ⟨⟨_, _, _, _, _, _, hD', _⟩, _⟩ => hv (hF' _ (hFF _ hD').1).1.1.1
  subst hv
  refine userCallWS_of_exitCL hp rfl Spike.Lib.X64ConsumerS.msAgree_msOfS (ownIncl_of_indep fun _ => rfl) ?_
  intro F'' hR0 hF'' hFF g hra hc htp hbase
  refine ⟨AbS h hcode, g.fp, g.ra, Spike.Lib.X64Consumer.c0, ?_, abC_lag hp h hrs hir hT hcode hok,
    fun c1 s c hr0 _ hA => uPostS_ret hbase hr0 hA⟩
  by_cases hL : ∃ Z, Ret0.LimOk ((MSS h) []) F' (limA (TP0 h)) Z
  case neg =>
    exact SegWS.empty fun s c fs ⟨⟨_, _, _, _, σ, _, _, _, hlim⟩, _⟩ => hL ⟨_, by rw [← htp]; exact hlim⟩
  obtain ⟨Z, hL⟩ := hL
  have hcx := mainCtxB h hdm hnm hrow hn hD0 hD8 hD hF' hR0 hF'' hFF hL
  have hrr : r' = r := Option.some.inj (hr'.symm.trans hr)
  subst hrr
  have hpre := mainPre_of (cells := cells) hp h hcode hok hdm hfd hcx (fun m hm => (hFF m hm).1)
    (by show -needD (FRM dm r') n ≤ _; rw [hfr]; omega) (by rw [hfr]) hra hc htp
  have H := hpre.seg (fnSpecC_all_ofPlaceOK hp h hrs hir hT hcode hok jm dm hdm)
    fun σ c hJ => hJ.1.1.2.2.2.2.trans htp
  have hfn : (hcode jm dm hdm).fn = Spike.Lib.X64.Rt.bareMC.fn := by rw [(hcode jm dm hdm).hfn, hnm]; rfl
  rw [hfn] at H
  exact H.mono_pre fun s c fs ⟨hA, hfs⟩ => ⟨at_rsp0 hA, hfs⟩

/-- **Every code block's code facts with no frames limit, indexed by
position** (`fnCode_ofPlaceOKR`): the closed forms `rs` with no frames limit
(plain calls), the walk predicates `T j` (the `j`th code block's walk), the
code facts `hcode` and their fields `CodeFactsS`. -/
theorem fnCodes_ofPlaceOK (hp : Scc.Lower.Accepted1 p = true) {em : Scc.Lower.X64.Emitted}
    (hlow : Scc.Lower.X64.lowerAll? cfg p = .ok em) {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true) :
    ∃ (rs : List Res1) (rt : List Scc.IR.Func), Pairwise2 (LowC p cfg.layout.obj none) p rs ∧
      (Scc.Lower.X64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs) ∧
      ∃ (T : Nat → Expr → Prop), (∀ j d, p[j]? = some d → ∀ e, T j e → InWalkD none d e) ∧
        ∃ hcode : (∀ j d, p[j]? = some d →
          FnCode (Ly h).exe (Ly h).prog (Ly h).endPc (RaOkS h) (CdS h) (Scc.Lower.imms1Of p) (T j) d),
          ∀ j d (hd : p[j]? = some d), CodeFactsS h rs (hcode j d hd) j := by
  obtain ⟨rs, rt, hrs, hir, H⟩ := fnCode_ofPlaceOKR hp hlow h
  let T : Nat → Expr → Prop := fun j e => ∃ d, p[j]? = some d ∧ InWalkD none d e
  have hTe : ∀ j d, p[j]? = some d → InWalkD none d = T j := fun j d hd =>
    funext fun e => propext ⟨fun h => ⟨d, hd, h⟩, fun ⟨d', hd', h⟩ => by rw [hd] at hd'; cases hd'; exact h⟩
  refine ⟨rs, rt, hrs, hir, T, fun j d hd e he => by rw [← hTe j d hd] at he; exact he,
    fun j d hd => hTe j d hd ▸ (H j d hd).choose_spec.choose, fun j d hd => ?_⟩
  have key : ∀ (T' : Expr → Prop) (e : InWalkD none d = T'),
      CodeFactsS h rs (e ▸ (H j d hd).choose_spec.choose) j := by
    intro T' e
    subst e
    obtain ⟨hr, hprog, hfrm, henv, hn, hrr, hprs, hfr, hBl, hovf, hph⟩ := (H j d hd).choose_spec.choose_spec
    exact ⟨_, hr, hprog, hfrm, henv, hn, hrr, hprs, hfr, hBl, hovf, hph⟩
  exact key (T j) (hTe j d hd)

/-- **The user `main`'s interface at depth from the placement check and
the code facts with no frames limit** (`userMainSW_of` at the code facts of
`fnCodes_ofPlaceOK`): `main`'s depth `D` and limit room `ZU` (its
frame, within `12224`, `mainFrameU_of_placeOKAt`) with their bounds
(`mainD_of_placeOKAt`), and `x64_lower_correctES_of_user`'s `hU` there. -/
theorem userMainSW_ofPlaceOK (hp : Scc.Lower.Accepted1 p = true) {em : Scc.Lower.X64.Emitted}
    (hlow : Scc.Lower.X64.lowerAll? cfg p = .ok em) {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true)
    (hcfg : CfgNeedOk pcfg = true) {cells : Nat} :
    ∃ (D : Int) (fsz : Nat), 0 ≤ D ∧ D % 8 = 0 ∧ D + 56 ≤ 16384 ∧ fsz ≤ 12224 ∧
      ∀ v (F' : MachineData → Prop),
        (∀ m, F' m → Spike.Lib.X64.Rt.swFSL (D + 56) (Spike.Lib.X64.Rt.rS0 (Ly h)) (TOP h)
            (limA (tpOf (Ret0.pinA (Ly h).lab + 0#64 + 8#64))) v m ∧
            Ret0.CallerCells (swR v (-(D + 56)) 0) (-8 - 0) (8 - (D + 56)) 8 m) →
        Spike.Lib.X64.Rt.UserCallWS (WSS h cells) (KS h) p (Ly h).Λ.static (MSS h) (Ly h).exe (Ly h).endPc
          ((swR v (-(D + 56)) 0).callee (-8 - 0) (8 - (D + 56)) 8) F'
          Spike.Lib.X64.Rt.bareMC.fn Spike.Lib.X64.Rt.bareMC.Z D (Int64.ofInt fsz)
          (UPostS p (Ly h).Λ.static Spike.Lib.X64Consumer.c0)
          (((_root_.Executable.labels (Ly h).exe).label Spike.Lib.X64.Rt.bareMC.sp0).toBitVec)
          Spike.Lib.X64Consumer.c0 (TP0 h) := by
  obtain ⟨rs, rt, hrs, hir, T, hT, hcode, hok⟩ := fnCodes_ofPlaceOK hp hlow h
  -- `main`'s code block
  have hm : p.any (·.name == "main") = true := by
    simp only [Scc.Lower.Accepted1, Bool.and_eq_true] at hp
    exact hp.1.1.2
  obtain ⟨dm, hfd⟩ := Option.isSome_iff_exists.mp
    (List.find?_isSome.mpr (List.any_eq_true.mp hm) : (p.find? (·.name == "main")).isSome)
  have hnm : dm.name = "main" := by simpa using List.find?_some hfd
  obtain ⟨jm, hjm, hpj⟩ := Spike.Lib.LowerNode.find_index hfd
  have hdm : p[jm]? = some dm := by rw [List.getElem?_eq_getElem hjm, hpj]
  have hjr : jm < rs.length := hrs.1 ▸ hjm
  have hr : rs[jm]? = some rs[jm] := List.getElem?_eq_getElem hjr
  -- its IR function and row
  have hmem := Spike.Lib.LowerNode.mem_progOf_funcs1 cfg.layout rt hrs jm hjm
  rw [List.mem_zipIdx_iff_getElem?] at hmem
  have hf := List.mem_of_getElem? hmem
  rw [← hir] at hf
  simp only [hpj] at hf
  have hname : (func1 (Scc.Lower.Names.user dm.name) (params1R dm) rs[jm]).name = Scc.Lower.Names.user "main" := by
    show Scc.Lower.Names.user dm.name = _; rw [hnm]
  obtain ⟨l, g, n, hrow, -, -, hD0, hD8, hD, -, -⟩ := mainD_of_placeOKAt hp hlow h hcfg hf hname rfl
  rw [hname] at hrow
  exact ⟨_, _, hD0, hD8, hD, mainFrameU_of_placeOKAt hp hlow h hcfg hf hname rfl,
    userMainSW_of hp hlow h hcfg hrs hir hT hcode hok hdm hfd hr hrow⟩

end Main

end Spike.Lib.LowerX64
