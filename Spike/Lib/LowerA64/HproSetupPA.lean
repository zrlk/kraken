/-
**The setup call's prologue with the caller's words placed** (AArch64; the
twin of `Spike/Lib/LowerX64/HproSetupP.lean`):
`hpro_setup_ofPlaceOK` with the callee's states placed by a premise
(`hpl`) in place of the caller's environment binding no word, and that
premise at the program's start: while `rodata` runs, the pending frame is
`setupK` over the start's environment, whose one word, `me`'s, is placed
at the immediate `imms2Me` keys at `setupK`.

- `hpro_setup_ofPlaceOKP`: `hpro_setup_ofPlaceOK` at `hpl`;
- `placedS_setupCall`: the setup call's callee control and frame placed at
  every state;
- `setupCallWS_ofPlaceOK`: `SetupCallWS` at `SRetR` from the setup
  function's `FnSpecC2`, its return address (`raOk_setup`) and prologue
  (`hpro_setup_ofPlaceOKP` at `placedS_setupCall`) discharged.
-/
import Spike.Lib.LowerA64.MainCallOf
import Spike.Lib.LowerA64.CalleeRgn2
import Spike.Lib.Src.ImmsMe

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (Range ValRep)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64Consumer (K0 Lbl Lsize)
open Spike.Lib.A64ConsumerS (PlacedS InvS envsOf fvOf termsOf)
open Spike.Lib.A64.Rt (RuntimeLayout setupMC bareMC)
open Spike.Lib.A64.Flow.Ret0 (StackOff limA LimOk WcG CallerCells)
open Spike.Lib.LowerNode (FrOk2 ZBad setupK compiled2)

/-- **The setup call's callee and frame are placed at every state**: at the
start's control `⟨setupTerm, [me ↦ [meW], u ↦ []]⟩`, the call of `rodata`
(`hct`) binds its unit parameter to no word and leaves the frame `setupK`
over the start's environment; `me`'s word is placed at the immediate `n`
the table keys at `setupK` (`himm`), which represents it (`hv`). -/
theorem placedS_setupCall {Λ : Scc.Sem.Layout} {lbl : Lbl} {p : Prog} {meW : TermRun.Word} {n : Nat}
    {cE : Ctl} {fr : TermRun.Frame}
    (hct : CallTo p ⟨Scc.Sem.SrcSem.setupTerm, [("me", .ptr .pub .void, [meW]), ("u", .unit, [])], none⟩ cE fr)
    (himm : Λ.imms setupK "me" 0 = some n) (hv : ValRep lbl meW.val n) (s : State) :
    PlacedS Λ lbl s cE [fr] := by
  obtain ⟨x, f, a, e, d, t, ws, ht, -, ha, rfl, rfl⟩ := hct
  simp only [Scc.Sem.SrcSem.setupTerm, Expr.let_.injEq, Op.call.injEq] at ht
  obtain ⟨rfl, ⟨rfl, -, rfl, -⟩, rfl⟩ := ht
  have hws : ws = [] := by
    simp [TermRun.evalAt, TermRun.lookupE] at ha
    exact ha.2
  subst hws
  refine ⟨fun d y k => if d = 1 ∧ y = "me" ∧ k = 0 then some (.imm n) else none, ?_, ?_, ?_⟩
  · intro d env hd y ty ws hl k wd wp hwd hwp
    dsimp only at hwp
    split at hwp
    · obtain ⟨rfl, rfl, rfl⟩ := ‹_ ∧ _ ∧ _›
      cases hwp
      simp [envsOf] at hd
      subst hd
      simp [TermRun.lookupE] at hl
      obtain ⟨-, rfl⟩ := hl
      simp at hwd
      subst hwd
      exact hv
    · cases hwp
  · intro d env xs hd hxs y hy ty ws hl k hk
    match d, hd, hxs with
    | 0, hd, _ =>
      simp [envsOf] at hd
      subst hd
      rw [lookupE_nil_words hl] at hk
      exact absurd hk (Nat.not_lt_zero _)
    | 1, hd, hxs =>
      simp [envsOf] at hd
      subst hd
      simp only [fvOf, List.map_cons, List.map_nil, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hxs
      subst hxs
      have hL : (Scc.Sem.exprFv setupK).filter (· != "r") = ["me"] := by decide +kernel
      change y ∈ (Scc.Sem.exprFv setupK).filter (· != "r") at hy
      rw [hL] at hy
      have hy' : y = "me" := by simpa using hy
      subst hy'
      simp [TermRun.lookupE] at hl
      obtain ⟨-, rfl⟩ := hl
      have hk0 : k = 0 := by simpa using hk
      exact ⟨_, ite_eq_left ⟨rfl, rfl, hk0⟩⟩
    | d + 2, hd, _ => simp [envsOf] at hd
  · intro d e' y k m hd hm
    dsimp only at hm
    split at hm
    · obtain ⟨rfl, rfl, rfl⟩ := ‹_ ∧ _ ∧ _›
      cases hm
      simp [termsOf] at hd
      subst hd
      exact himm
    · cases hm

section Place

variable {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
  {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

local notation "LY" => RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))

variable {im : Expr → String → Nat → Option Nat}
variable {d : Decl} {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
  {T : Expr → Prop} {rS : Range} {Λw : Scc.Sem.Layout} {lbl : Lbl} {rd : TermRun.Word → Prop}
  {G : Loc → Val → Prop} {ar : Arena} {J : InvS} {Dt : State → Prop} {lsize : Lsize}

/-- **The setup function's prologue inside `W2` from the placement check,
the callee's states placed by a premise** (`hpro_setup_ofPlaceOK` with
`hpl`, e.g. `placedS_setupCall`, in place of `hct`, `hcE`, `hW0`). -/
theorem hpro_setup_ofPlaceOKP (c : FnCode2 (LY).exe (LY).prog (LY).endPc RaOk Cd im T d)
    (hc : ProOK LY c) (hL : PosOff OP (LY).lab ((LY).lab (proL c.cx))) {ms : MemSide isaLSE2}
    {ms0 : MemSide isaLSE2} {F0 : MachineData → Prop} {fn : Label} {ZU : Int64} {g : WcG}
    {fr : TermRun.Frame}
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -(c.cx.frame : Int)) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λw) false ⟨limA g.tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA g.tp) 8 = none)
    (hsub : rS.Sub Λw.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hpN : ProgNoS ZBad p) (hpl : ∀ s, PlacedS Λw lbl s g.c0 [fr]) (hfo : FrOk2 g.c0 [fr]) :
    ProW (fun s c => W2 Λw (Spike.Lib.A64.PhRec.μ LY) p rd G (Spike.Lib.A64.PhRec.own LY) rS
        (Spike.Lib.A64.PhRec.Tk LY) ar J Dt (A64.WriteAb.Ab (LY).lab) lbl lsize s c [fr])
      (Spike.Lib.A64.PhRec.K LY rS) (LY).exe (LY).endPc R F ms
      ((_root_.Executable.labels (LY).exe).label c.fn) (Int64.ofInt c.cx.frame)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL c.cx) c.ps
      (Spike.Lib.A64.Rt.uN0 (_root_.Executable.labels (LY).exe).label ms0 F0 (LY).exe (LY).endPc fn ZU g).J := by
  obtain ⟨hfi, hph, hent⟩ := hc
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms2Of p) (rS := rS)
  refine proW_w2C c hI (fun _ _ h => h.1.2.2.2.2) hph hR hal hlo hhi hl hh hmr hun hsub hfit hFO hpN
    (proW_abStC c hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hph hfi hL hent
      (fun _ _ h => h.1.2.2.2.2) hR hal hlo hhi hun)
    (fun _ _ h s _ => h.1.1 ▸ hpl s) fun _ _ h => ⟨fun h' => (List.cons_ne_nil _ _ h').elim, h.1.1 ▸ hfo⟩

/-- **The setup call from the placement check** (`setupCallWS_ofFnSpec` at
`c := fnCode2OfP … j d hd`, the setup function's compiled block, from the
start's control `c0` before the setup block, `hc0`): the return address
past `setupMC sw`'s `e0` has the anchor's phase (`raOk_setup`), and the
prologue is inside `W2` (`hpro_setup_ofPlaceOKP`, the callee and the frame
placed by `placedS_setupCall` at `me`'s immediate `n`, `himm`, `hv`); the
edge is `setupCallWS_ofFnSpec`'s. Left: the setup function's `FnSpecC2`
(`hs`) and shape (`hu`, `hna`, `hfn`, `hZU`, `hcE`, `hms`), the overflow
stub's position (`hL`), the limit word (`hmr`, `hun`), the stack (`hsub`,
`hfit`), `hpN`, and per context the rest of `CalleePre2` with `FrOk2` at
the call (`hpre`). -/
theorem setupCallWS_ofPlaceOK {j : Nat} (hd : (compiled2 p)[j]? = some d)
    {ms : List TermRun.Frame → MemSide isaLSE2}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop}
    (hs : FnSpecC2 (fun s c fs => W2 Λw (Spike.Lib.A64.PhRec.μ LY) p rd G (Spike.Lib.A64.PhRec.own LY) rS
        (Spike.Lib.A64.PhRec.Tk LY) ar J Dt (A64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
      (Spike.Lib.A64.PhRec.K LY rS) p lbl lsize ms CxOk (fnCode2OfP hp h j d hd))
    (hu : d.argTy = .unit) (hna : (fnCode2OfP hp h j d hd).na = 0)
    {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int} {ZU : Int64} {sw : Nat}
    {tp : UInt64} {c0 : Ctl} {meW : TermRun.Word} {n : Nat}
    (hfn : fn = (fnCode2OfP hp h j d hd).fn) (hZU : ZU = Int64.ofInt (fnCode2OfP hp h j d hd).cx.frame)
    (hc0 : c0 = ⟨Scc.Sem.SrcSem.setupTerm, [("me", .ptr .pub .void, [meW]), ("u", .unit, [])], none⟩)
    (hcE : ∀ cE fr, CallTo p c0 cE fr → cE = ⟨d.body, [(d.arg, d.argTy, [])], none⟩)
    (hms : ∀ fr a Z', LimOk (ms []) F (LY).exe (LY).endPc a Z' → LimOk (ms [fr]) F (LY).exe (LY).endPc a Z')
    (hL : PosOff OP (LY).lab ((LY).lab (proL (fnCode2OfP hp h j d hd).cx)))
    (himm : Λw.imms setupK "me" 0 = some n) (hv : ValRep lbl meW.val n)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λw) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λw.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hpN : ProgNoS ZBad p)
    (hpre : ∀ F' : MachineData → Prop, (R.callee (-Z.toInt) (-D) 0).OK →
      (R.callee (-Z.toInt) (-D) 0).base.toNat % 16 = 0 → FStable (R.callee (-Z.toInt) (-D) 0) F' →
      (∀ m, F' m → F m ∧ CallerCells R (-Z.toInt) (-D) 0 m) →
      ∀ (g : WcG) (fr : TermRun.Frame), g.ra = ((LY).lab (setupMC sw).e0 + 4).toBitVec → g.tp = tp →
      CallTo p c0 g.c0 fr → (R.callee (-Z.toInt) (-D) 0).base = g.sp →
      ∃ (G0 : Ctl → Prop) (Ab : FragS isaLSE2),
        CalleePre2R (fun s c fs => W2 Λw (Spike.Lib.A64.PhRec.μ LY) p rd G (Spike.Lib.A64.PhRec.own LY) rS
            (Spike.Lib.A64.PhRec.Tk LY) ar J Dt (A64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.A64.PhRec.K LY rS) p lbl lsize ms CxOk (fnCode2OfP hp h j d hd) rS
          (R.callee (-Z.toInt) (-D) 0) F' [fr] g.fp g.ra tp G0 Ab g.c0 ∧
        FrOk2 g.c0 [fr] ∧
        SegWS (fun s c fs => W2 Λw (Spike.Lib.A64.PhRec.μ LY) p rd G (Spike.Lib.A64.PhRec.own LY) rS
            (Spike.Lib.A64.PhRec.Tk LY) ar J Dt (A64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.A64.PhRec.K LY rS) p lbl ms Ab (fun _ _ _ => False)) :
    Spike.Lib.A64.Rt.SetupCallWS
      (fun s c fs => W2 Λw (Spike.Lib.A64.PhRec.μ LY) p rd G (Spike.Lib.A64.PhRec.own LY) rS
        (Spike.Lib.A64.PhRec.Tk LY) ar J Dt (A64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
      (Spike.Lib.A64.PhRec.K LY rS) p lbl ms (LY).exe (LY).endPc R F fn Z D ZU (SRetR lbl d.retTy)
      ((LY).lab (setupMC sw).e0 + 4).toBitVec c0 tp := by
  refine setupCallWS_ofFnSpec (fnCode2OfP hp h j d hd) hs hu hna hfn hZU hcE hms
    fun F' hR0 hal hF' hFF g fr hra htp hct hbase => ?_
  obtain ⟨G0, Ab, hP, hfo, hAb⟩ := hpre F' hR0 hal hF' hFF g fr hra htp hct hbase
  refine ⟨G0, Ab, fun he => hP.toPre ?_ ?_ he, hAb⟩
  · rw [hra]; exact raOk_setup LY sw
  · subst hc0
    exact hpro_setup_ofPlaceOKP h (fnCode2OfP hp h j d hd) (fnCode2OfP_spec hp h j d hd).2.2 hL
      hP.hR hP.hal hP.hlo hP.hhi hP.hl hP.hh (htp ▸ hmr)
      (fun m hm => htp ▸ hun m (hFF m hm).1) hsub hfit hP.hFO hpN (placedS_setupCall hct himm hv) hfo

end Place

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.placedS_setupCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms placedS_setupCall

/-- info: 'Spike.Lib.LowerA64.hpro_setup_ofPlaceOKP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hpro_setup_ofPlaceOKP

/-- info: 'Spike.Lib.LowerA64.setupCallWS_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms setupCallWS_ofPlaceOK

end Spike.Lib.LowerA64
