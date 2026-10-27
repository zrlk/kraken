/-
**The consumer's `h0` with a setup block, the placement of the source
controls after it per state** (AArch64, option (b)): `mainSW_ofPlaceOK`,
`hWx_ofPlaceOK` and `h0_ofPlaceOK_setupF` (`Spike/Lib/LowerA64/RtMainX.lean`,
`Spike/Lib/LowerA64/RtMainXF.lean`) asked the controls back from the setup
block (`PostS`) and at `main`'s return (`Post`) placed at *every* state
(`CFacts.place`, `MainCtl`'s `PlacedS`), which only a control of immediates
meets. Here they give the controls' shape facts (`CFactsC`, `MainCtlC`)
and the placement at the states of the marshalling block (`hPlS`) and of
the `exit_group` tail (`hPlX`) only, as `BlkW`/`ExitW` of `Placed` and
`PlacedS` with no outside move (`mainSW_sfactsR`,
`Spike/Lib/Rt/A64RtWR.lean`).

- `MainCtlC`: `MainCtlF` without the placement (`FrOk2`, not at an
  overflow); `rtM_w2R`: `rtM_w2F` with the placement at the state;
- `mainSW_ofPlaceOKR`, `hWx_ofPlaceOKR`, `h0_ofPlaceOK_setupFR`: the three
  at the controls' shape facts and the per-state placement.
-/
import Spike.Lib.LowerA64.RtMainXF
import Spike.Lib.Rt.A64RtWR

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Rt (InstOk SetupCode setupMC MainSW mainSIn)
open Spike.Lib.A64.Rt.MainS (MainPhS)
open Spike.Lib.A64.WriteAb (Ab)
open Spike.Lib.A64.AllocG (abLabs)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Spike.Lib.AllocReach (IN)
open Scc.Sem.A64 (abi pcOf)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {ar : Arena} {lbl : Lbl} {lab : Label → Int64}

/-- **A source control's facts `W2` asks at the frames `fs` beyond
`SFacts` and the placement** (`MainCtlF` without `PlacedS`): its frame
runs free of `ZBad`, not at an overflow. -/
def MainCtlC (c : Ctl) (fs : List TermRun.Frame) : Prop :=
  FrOk2 c fs ∧ ¬ OvfReady c

/-- `MainCtlF` gives `MainCtlC`. -/
theorem MainCtlF.toC {L0 : Lbl} {c : Ctl} {fs : List TermRun.Frame} (h : MainCtlF Λ L0 c fs) : MainCtlC c fs :=
  ⟨h.1, h.2.1⟩

/-- **`W2` at a runtime state at the frames `fs`, at a source control,
placed at the state** (`rtM_w2F` with the placement at `s`, `hPl`). -/
theorem rtM_w2R {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : Own} {rS : Range}
    {Tk : State → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl} {lsize : Lsize} (hp : ProgNoS ZBad p)
    {s : State} {c : Ctl} {fs : List TermRun.Frame} (hS : SFacts Λ μ own rS Tk lbl0 s c) (hM : RtM μ ar lab s c)
    (hQ : MainCtlC c fs) (hPl : PlacedS Λ lbl s c fs) :
    W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c fs := by
  have hP := w2Part_of_wrOff (J := J) (rd := rd) (G := G) (p := p) (lsize := lsize) hM.1 hPl hM.2 hS
  exact w2_of hp hQ.1 (hS.toSt.dt_mono fun _ h => h.elim) hP.1 (fun _ => hS.noRet) (.of_placedS hP.2.1) hP.2.2.1
    (abortOkA_of_ne (noAbort_of_sfacts hQ.2 hS)) hP.2.2.2

/-! ## At a placed output -/

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.A64.placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h i

open Spike.Lib.A64.Flow.Ret0 in
open Spike.Lib.A64.Rt (swFSL rS0) in
/-- **`scc_rt_main`'s own states after a setup block inside `W2At`, the
placement per state** (`mainSW_ofPlaceOK`): `mainSW_sfactsR` and
`mainSW_rtM` at the record, joined by `rtM_w2R` with the controls'
`MainCtlC` (`MainSW.ofCtl`) and their `PlacedS` (`MainSW.ofPl`); the
controls after the setup block and at the return point by their shape
facts (`hCS`, `hCP`, `hQS`, `hQP`), placed at the marshalling block's
states (`hPlS`) and the tail's (`hPlX`), at the stacks' top. -/
theorem mainSW_ofPlaceOKR {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {ab : Option (State → Prop)} {c0 : Ctl} {L : Int} (hp : ProgNoS ZBad p)
    (hL0 : 0 ≤ L) (hL : L ≤ 16384) (hL8 : L % 8 = 0)
    {sw : Nat} (hsw : sw < 8) (hc : Spike.Lib.A64.Rt.rtCodeOkS (Ly).prog (setupMC sw) = true)
    (hph : MainPhS (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (Ly).lab (setupMC sw))
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).grow))
    (hset : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).setup))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).fn))
    (hLZ : (setupMC sw).Z.toInt ≤ L)
    {PostS : Ctl → Reg64s → Prop} {Post : Ctl → BitVec 64 → Prop}
    (hC0 : CFacts (Ly).Λ lbl0 c0) (hCS : ∀ c rs, PostS c rs → CFactsC c) (hCP : ∀ c v, Post c v → CFactsC c)
    (hQ0 : MainCtl (Ly).Λ (fun _ => none) c0) (hQS : ∀ c rs, PostS c rs → MainCtlC c [])
    (hQP : ∀ c v, Post c v → MainCtlC c [])
    (hPlS : BlkW (fun s c => Placed (Ly).Λ lbl0 s c ∧ PlacedS (Ly).Λ (fun _ => none) s c []) (fun _ _ => False)
      (Ly).exe (Ly).endPc (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0)
      (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64))
      (Spike.Lib.A64.Rt.mainS0 (Ly).lab (setupMC sw) PostS
        ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩
        (pinA (Ly).lab + 0#64 + 8#64))
      (Spike.Lib.A64.Rt.marshal (setupMC sw).sw (setupMC sw).fn))
    (hPlX : ExitW (fun s c => Placed (Ly).Λ lbl0 s c ∧ PlacedS (Ly).Λ (fun _ => none) s c []) (fun _ _ => False)
      (Ly).exe (Ly).endPc (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0)
      (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64))
      (Spike.Lib.A64.Rt.mainSR (Ly).lab (setupMC sw) Post) (setupMC sw).k) :
    ∀ v, MainSW (Spike.Lib.A64.Rt.nilW (W2At h i p rd (rS0 (Ly)) J Dt ls0))
      (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) (Ly).exe (Ly).endPc
      (swR v (-L) 0) (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v) (MSAt h i p rd J ab ls0 [])
      (setupMC sw) PostS Post
      ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩
      (pinA (Ly).lab + 0#64 + 8#64) := by
  intro v
  by_cases hv : v = stacksA (Ly).lab + 0#64 + 16384#64
  · subst hv
    have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h i (rS := rS0 (Ly))
    have hin := Spike.Lib.A64.Rt.mainSIn_of_okS hc
    have hZ := setupMC_Z sw hsw
    have hok : (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).OK := by
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hL
    have h16 : (stacksA (Ly).lab + 0#64 + 16384#64).toNat % 16 = 0 := by
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_h16 _
    have hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (Ly).Λ) false
        ⟨limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)), 8⟩ = true := by
      rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.limA_tcb0]
      exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1
    have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
    have H1 := Spike.Lib.A64.Rt.mainSW_sfactsR (lbl := lbl0) (ms := MSAt h i p rd J ab ls0 []) hI hin hC0 hCS hCP
      hph (Spike.Lib.A64.AllocG.BlkW.imp hPlS BlkW.triv fun _ _ h _ => h.1)
      (ExitW.imp hPlX ExitW.triv fun _ _ h _ => h.1)
      hok h16 (by show -L ≤ _; omega) (Int.le_refl _) (by show (-L) % 8 = 0; omega)
      (by show (0 : Int) % 8 = 0; rfl) (by rw [hZ]; omega) (by rw [hZ]; omega) (show sw ≤ 7 by omega)
      (by show 8 * (sw : Int) + 8 ≤ _; rw [hZ]; omega)
      (by simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ, setupMC_k sw hsw]; refine ⟨?_, ?_, ?_⟩ <;> omega)
      hmr (fun _ hm => hm.1.2) hsub (Spike.Lib.A64.Rt.fitS_of_sub _ hsub) (fun _ hm => hm.2)
    have H2 := mainSW_rtM (ar := Spike.Lib.A64.Rt.arOf (Ly).Λ) (PostS := PostS) (Post := Post)
      (g := ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩)
      (x0 := pinA (Ly).lab + 0#64 + 8#64)
      (F := swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64))
      (ms := MSAt h i p rd J ab ls0 []) hI (Scc.Cert.PlaceOK.A64.printIn_of_placeOKAt h)
      (Scc.Cert.PlaceOK.A64.abortIn_of_placeOKAt h) hsw hin hph hgrow hset hfn hok h16
      (by show -L ≤ _; omega) (Int.le_refl _) (fun _ hm => hm.1.2)
    have H3 := MainSW.ofCtl (Q := fun c => MainCtlC c []) (exe := (Ly).exe) (endPc := (Ly).endPc)
      (R := swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0)
      (F := swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64))
      (ms := MSAt h i p rd J ab ls0 []) (sc := setupMC sw)
      (g := ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩)
      (x0 := pinA (Ly).lab + 0#64 + 8#64) ⟨hQ0.1, hQ0.2.1⟩ hQS hQP
    have H4 := Spike.Lib.A64.Rt.MainSW.ofPl (P := fun s c => PlacedS (Ly).Λ (fun _ => none) s c [])
      (ms := MSAt h i p rd J ab ls0 []) (sc := setupMC sw)
      (g := ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩)
      (x0 := pinA (Ly).lab + 0#64 + 8#64) hQ0.2.2
      (Spike.Lib.A64.AllocG.BlkW.imp hPlS BlkW.triv fun _ _ h _ => h.2)
      (ExitW.imp hPlX ExitW.triv fun _ _ h _ => h.2)
    exact MainSW.imp H1 (MainSW.imp (W := fun s c => RtM (Spike.Lib.A64.PhRec.μ (Ly))
        (Spike.Lib.A64.Rt.arOf (Ly).Λ) (Ly).lab s c ∧ MainCtlC c [] ∧ PlacedS (Ly).Λ (fun _ => none) s c [])
        H2 (MainSW.imp H3 H4 fun _ _ h1 h2 => ⟨h1, h2⟩) fun _ _ h1 h2 => ⟨h1, h2⟩)
      fun s c hS ⟨hM, hQ, hPl⟩ => rtM_w2R hp hS hM hQ hPl
  · exact Spike.Lib.A64.Rt.mainSW_ofFalse fun m hm => hv hm.1.1

open Spike.Lib.A64.Flow.Ret0 in
open Spike.Lib.A64.Rt (swFSL rS0) in
/-- **The exit tail's states inside `W2At` at every frames, the placement
per state** (`hWx_ofPlaceOK`): `mainSW_sfactsR`'s and `mainSW_rtM`'s exit
parts at the post at the frames `fs`, joined by `rtM_w2R` with the post's
controls' `MainCtlC` at `fs` (`hQP`) and their placement at the tail's
states (`hPlX`, at the stacks' top). -/
theorem hWx_ofPlaceOKR {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {c0 : Ctl} {L : Int} (hp : ProgNoS ZBad p)
    (hL0 : 0 ≤ L) (hL : L ≤ 16384) (hL8 : L % 8 = 0)
    {sw : Nat} (hsw : sw < 8) (hc : Spike.Lib.A64.Rt.rtCodeOkS (Ly).prog (setupMC sw) = true)
    (hph : MainPhS (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (Ly).lab (setupMC sw))
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).grow))
    (hset : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).setup))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).fn))
    (hLZ : (setupMC sw).Z.toInt ≤ L) {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hC0 : CFacts (Ly).Λ lbl0 c0) (hCP : ∀ c fs v, Post c fs v → CFactsC c)
    (hQP : ∀ c fs v, Post c fs v → MainCtlC c fs)
    (hPlX : ∀ fs, ExitW (fun s c => Placed (Ly).Λ lbl0 s c ∧ PlacedS (Ly).Λ (fun _ => none) s c fs)
      (fun _ _ => False) (Ly).exe (Ly).endPc (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0)
      (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64))
      (Spike.Lib.A64.Rt.mainSR (Ly).lab (setupMC sw) (fun c v => Post c fs v)) (setupMC sw).k) :
    ∀ v fs, ExitW (fun s c => W2At h i p rd (rS0 (Ly)) J Dt ls0 s c fs)
      (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) (Ly).exe (Ly).endPc
      (swR v (-L) 0) (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v)
      (Spike.Lib.A64.Rt.mainSR (Ly).lab (setupMC sw) (fun c v => Post c fs v)) (setupMC sw).k := by
  intro v fs
  by_cases hv : v = stacksA (Ly).lab + 0#64 + 16384#64
  · subst hv
    have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h i (rS := rS0 (Ly))
    have hin := Spike.Lib.A64.Rt.mainSIn_of_okS hc
    have hZ := setupMC_Z sw hsw
    have hok : (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).OK := by
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hL
    have h16 : (stacksA (Ly).lab + 0#64 + 16384#64).toNat % 16 = 0 := by
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_h16 _
    have hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (Ly).Λ) false
        ⟨limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)), 8⟩ = true := by
      rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.limA_tcb0]
      exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1
    have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
    have H1 := (Spike.Lib.A64.Rt.mainSW_sfactsR (lbl := lbl0) (PostS := fun _ _ => False)
      (Post := fun c v => Post c fs v)
      (g := ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩)
      (x0 := pinA (Ly).lab + 0#64 + 8#64) (ms := MSAt h i p rd J none ls0 [])
      (F := swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64)) hI hin hC0
      (fun _ _ h => h.elim) (fun c v h => hCP c fs v h) hph
      (fun _ _ _ _ _ _ _ _ _ hJ => hJ.1.elim) (ExitW.imp (hPlX fs) ExitW.triv fun _ _ h _ => h.1)
      hok h16 (by show -L ≤ _; omega) (Int.le_refl _) (by show (-L) % 8 = 0; omega)
      (by show (0 : Int) % 8 = 0; rfl) (by rw [hZ]; omega) (by rw [hZ]; omega) (show sw ≤ 7 by omega)
      (by show 8 * (sw : Int) + 8 ≤ _; rw [hZ]; omega)
      (by simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ, setupMC_k sw hsw]; refine ⟨?_, ?_, ?_⟩ <;> omega)
      hmr (fun _ hm => hm.1.2) hsub (Spike.Lib.A64.Rt.fitS_of_sub _ hsub) (fun _ hm => hm.2)).exit
    have H2 := (mainSW_rtM (ar := Spike.Lib.A64.Rt.arOf (Ly).Λ) (PostS := fun _ _ => False)
      (Post := fun c v => Post c fs v)
      (g := ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩)
      (x0 := pinA (Ly).lab + 0#64 + 8#64) (ms := MSAt h i p rd J none ls0 [])
      (F := swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64)) hI
      (Scc.Cert.PlaceOK.A64.printIn_of_placeOKAt h) (Scc.Cert.PlaceOK.A64.abortIn_of_placeOKAt h) hsw hin hph
      hgrow hset hfn hok h16 (by show -L ≤ _; omega) (Int.le_refl _) (fun _ hm => hm.1.2)).exit
    have H3 : ExitW (fun s c => MainCtlC c fs ∧ PlacedS (Ly).Λ (fun _ => none) s c fs) (fun _ _ => False)
        (Ly).exe (Ly).endPc (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0)
        (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64))
        (Spike.Lib.A64.Rt.mainSR (Ly).lab (setupMC sw) (fun c v => Post c fs v)) (setupMC sw).k :=
      ExitW.imp (W1 := fun _ c => MainCtlC c fs)
        ⟨BlkW.ofCtl fun _ _ hJ => hQP _ _ _ hJ, NodeW.ofCtl fun _ _ ⟨_, _, hJ, _⟩ => hQP _ _ _ hJ⟩ (hPlX fs)
        fun _ _ h1 h2 => ⟨h1, h2.2⟩
    exact ExitW.imp H1 (ExitW.imp (W := fun s c => RtM (Spike.Lib.A64.PhRec.μ (Ly)) (Spike.Lib.A64.Rt.arOf (Ly).Λ)
        (Ly).lab s c ∧ MainCtlC c fs ∧ PlacedS (Ly).Λ (fun _ => none) s c fs) H2 H3 fun _ _ h1 h2 => ⟨h1, h2⟩)
      fun s c hS ⟨hM, hQ, hPl⟩ => rtM_w2R hp hS hM hQ hPl
  · exact (Spike.Lib.A64.Rt.mainSW_ofFalse (PostS := fun _ _ => False) (Post := fun c v => Post c fs v)
      (ms := MSAt h i p rd J none ls0 []) (sc := setupMC sw)
      (g := ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩)
      (x0 := pinA (Ly).lab + 0#64 + 8#64) fun m hm => hv hm.1.1).exit

open Spike.Lib.A64.Flow.Ret0 in
open Spike.Lib.A64.Rt (SetupCallWS MainCallWSF SetupArgs swFSL rS0 entryR rtF) in
/-- **The consumer's `h0` at a placed output with a setup block, `main`
returning at pending frames, the placement per state**
(`h0_ofPlaceOK_setupF`): `hW` from `mainSW_ofPlaceOKR` at the post at
`[]`, `hWx` from `hWx_ofPlaceOKR`. Left beyond `h0_ofPlaceOK_setupF`'s, in
place of its controls' `CFacts` and `MainCtl(F)` after the setup block and
at the post: their shape facts (`hPostS`, `hPost`: `CFactsC`, `MainCtlC`)
and their placement at the marshalling block's states (`hPlS`) and the
tail's at every frames (`hPlX`), at the stacks' top. -/
theorem h0_ofPlaceOK_setupFR {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {ab : Option (State → Prop)} {c0 : Ctl} {L : Int} {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ)
    {FE : MachineData → Prop} (hFE : ∀ m, FE m → rtF (Ly) m) (hFEs : FStable (entryR E) FE)
    (hFEk : ∀ m pm, FE m → FE (takeMem pm (rS0 (Ly)) m))
    (hp : ProgNoS ZBad p) (hf0 : FrOk2 c0 []) (hov : ¬ OvfReady c0) (hC0 : CFacts (Ly).Λ lbl0 c0)
    (hpl0 : ∀ s, PlacedS (Ly).Λ (fun _ => none) s c0 [])
    (hL0 : 0 ≤ L) (hL : L ≤ 16384) (hL8 : L % 8 = 0)
    {sw : Nat} (hsw : sw < 8) (hc : Spike.Lib.A64.Rt.rtCodeOkS (Ly).prog (setupMC sw) = true)
    (hph : MainPhS (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (Ly).lab (setupMC sw))
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).grow))
    (hset : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).setup))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).fn))
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    {PostR PostS : Ctl → Reg64s → Prop} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hL1 : (setupMC sw).Z.toInt + D1 ≤ L) (hL2 : (setupMC sw).Z.toInt + D2 ≤ L)
    (hZM : (Ly).stacksA.toNat + 4096 ≤ (stacksA (Ly).lab + 0#64 + 16384#64 - (setupMC sw).Z.toBitVec).toNat)
    (hZS : (Ly).stacksA.toNat + 4096 ≤
      (stacksA (Ly).lab + 0#64 + 16384#64 - (setupMC sw).Z.toBitVec - ZU1.toBitVec).toNat)
    (hZU : (Ly).stacksA.toNat + 4096 ≤
      (stacksA (Ly).lab + 0#64 + 16384#64 - (setupMC sw).Z.toBitVec - ZU2.toBitVec).toNat)
    (hPostS : ∀ c rs, PostS c rs → CFactsC c ∧ MainCtlC c [])
    (hPU : ∀ c fs v, Post c fs v → UPostRF p (fun _ => none) c fs v)
    (hPost : ∀ c fs v, Post c fs v → CFactsC c ∧ MainCtlC c fs)
    (hPlS : BlkW (fun s c => Placed (Ly).Λ lbl0 s c ∧ PlacedS (Ly).Λ (fun _ => none) s c []) (fun _ _ => False)
      (Ly).exe (Ly).endPc (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0)
      (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64))
      (Spike.Lib.A64.Rt.mainS0 (Ly).lab (setupMC sw) PostS
        ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩
        (pinA (Ly).lab + 0#64 + 8#64))
      (Spike.Lib.A64.Rt.marshal (setupMC sw).sw (setupMC sw).fn))
    (hPlX : ∀ fs, ExitW (fun s c => Placed (Ly).Λ lbl0 s c ∧ PlacedS (Ly).Λ (fun _ => none) s c fs)
      (fun _ _ => False) (Ly).exe (Ly).endPc (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0)
      (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64))
      (Spike.Lib.A64.Rt.mainSR (Ly).lab (setupMC sw) (fun c v => Post c fs v)) (setupMC sw).k)
    (hS : ∀ v, SetupCallWS (W2At h i p rd (rS0 (Ly)) J Dt ls0) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSAt h i p rd J ab ls0) (Ly).exe (Ly).endPc
      (swR v (-L) 0) (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v)
      (setupMC sw).setup (setupMC sw).Z D1 ZU1 PostR ((Ly).lab (setupMC sw).e0 + 4).toBitVec c0
      (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)))
    (hcall : ∃ cE fr, Spike.Lib.A64.Flow.CallTo p c0 cE fr)
    (hPS : ∀ cE fr c rs, Spike.Lib.A64.Flow.CallTo p c0 cE fr → PostR c rs →
      ∃ c'', Spike.Lib.FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    {chk entry : Label} {Zs lim : Int64} {Lg : Label} {ps : List (XReg × Int64)}
    (hproS : prologueIn (Ly).prog (setupMC sw).setup chk entry Zs lim Lg ps = true)
    (hphS : blkPh (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (fun _ => false) (Ly).lab
      ((Ly).lab chk + Int64.ofNat (4 * 0)) 0 (chkHead Zs) = true)
    (hlS : chk ∉ abLabs)
    (hU : ∀ v, MainCallWSF (W2At h i p rd (rS0 (Ly)) J Dt ls0) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSAt h i p rd J ab ls0) (Ly).exe (Ly).endPc
      (swR v (-L) 0) (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v)
      (setupMC sw).fn (setupMC sw).Z D2 ZU2 (SetupArgs PostS (setupMC sw).sw (pinA (Ly).lab + 0#64 + 8#64)) Post
      ((Ly).lab (setupMC sw).sp1).toBitVec (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) :
    SegWS (W2At h i p rd (rS0 (Ly)) J Dt ls0) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p (fun _ => none)
      (MSAt h i p rd J ab ls0)
      ((Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc (entryR E) FE (entryN (Ly).lab c0)).at [])
      fun _ _ _ => False := by
  have hZ := setupMC_Z sw hsw
  have hW := mainSW_ofPlaceOKR h i (rd := rd) (J := J) (Dt := Dt) (ls0 := ls0) (ab := ab) hp hL0 hL hL8 hsw hc
    hph hgrow hset hfn (by omega) hC0 (fun c rs h => (hPostS c rs h).1) (fun c v h => (hPost c [] v h).1)
    ⟨hf0, hov, hpl0⟩ (fun c rs h => (hPostS c rs h).2) (fun c v h => (hPost c [] v h).2) hPlS (hPlX [])
  have hWx := hWx_ofPlaceOKR h i (rd := rd) (J := J) (Dt := Dt) (ls0 := ls0) hp hL0 hL hL8 hsw hc hph
    hgrow hset hfn (by omega) hC0 (fun c fs v h => (hPost c fs v h).1) (fun c fs v h => (hPost c fs v h).2) hPlX
  have h16 : (setupMC sw).Z.toInt % 16 = 0 := by rw [hZ]; omega
  have hZ16 : 16 ≤ (setupMC sw).Z.toInt := by rw [hZ]; omega
  have hZw : 8 * ((setupMC sw).sw : Int) + 8 ≤ (setupMC sw).Z.toInt := by
    show 8 * (sw : Int) + 8 ≤ _; rw [hZ]; omega
  have hk : Spike.Lib.offOk (-(setupMC sw).Z.toInt) 0 (-(setupMC sw).Z.toInt + (setupMC sw).k.toInt) = true := by
    simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ, setupMC_k sw hsw]; refine ⟨?_, ?_, ?_⟩ <;> omega
  have hsw7 : (setupMC sw).sw ≤ 7 := show sw ≤ 7 by omega
  have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
  have hSM := stackM_rS0 (Ly) hE
  obtain ⟨hhdr, htcb, hfld, htk⟩ := rows_ofPlaceOK h i (p := p) (rd := rd) (ar := Spike.Lib.A64.Rt.arOf (Ly).Λ)
    (J := IN (Spike.Lib.A64.Rt.arOf (Ly).Λ) (fun _ => none) ls0 J) (ab := ab) (lsize := ls0) hFE
  have h16t : (stacksA (Ly).lab + 0#64 + 16384#64).toNat % 16 = 0 := by
    rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_h16 _
  have hok : (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).OK := by
    rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hL
  exact Spike.Lib.A64.Rt.startS_segWSF (Ly).lays rfl (Spike.Lib.A64.Rt.rtCode0_of_placeOKAt h) msOfAX_K_abi hFEs
    (Spike.Lib.A64.Rt.entryR_ok hE) (Spike.Lib.A64.Rt.entryR_al hE) (by show (-65536 : Int) ≤ -304; decide)
    (by show (0 : Int) ≤ 0; decide) 0#64 0#64 c0 (by decide) hhdr htcb (by simp) hfld htk h16t hok
    (by rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rS0_subRD _ hL0 hL)
    (by rw [Spike.Lib.A64.Rt.pinA_lab0]; exact Spike.Lib.A64.Rt.rt_hfit _)
    (by rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_houtD _ hL0 hL)
    (hun_ofPlaceOK h i hFE) (Spike.Lib.A64.Rt.rS_of_sub _ hE hsub) (Spike.Lib.A64.Rt.fitS_of_sub _ hsub)
    (Spike.Lib.A64.Rt.outS_of_sub _ hE hsub) hFEk
    (startEW_w2G h i (lbl0 := lbl0) (J := IN (Spike.Lib.A64.Rt.arOf (Ly).Λ) (fun _ => none) ls0 J)
      (Dt := Dt) (lsize := ls0) (L := L) hp hf0 hov hC0 (Spike.Lib.A64.Rt.entryR_ok hE)
      (Spike.Lib.A64.Rt.entryR_al hE) (by show (-65536 : Int) ≤ -304; decide) (by show (0 : Int) ≤ 0; decide) hFE
      (rS0_eq_lab _) hsub hSM.1 hSM.2.1 hSM.2.2 (Spike.Lib.A64.Rt.fitS_of_sub _ hsub) h16t hok hL8 (by simp)
      hpl0)
    (Spike.Lib.A64.Rt.mainSIn_of_okS hc) h16 hZ16 hsw7 hZw hk
    hD10 hD18 hD20 hD28 hL1 hL2 (limOk_ofPlaceOK h i hZM) (limOk_ofPlaceOK h i hZS) (limOk_ofPlaceOK h i hZU) hS
    hcall hPS (hWC_ofPlaceOK h i (sc := setupMC sw) hp hL0 hL hL8 hproS hphS hlS hC0 ⟨hf0, hov, hpl0⟩) hU
    (fun R' F' s c fs v hP hAt => uPostRF_exit R' F' s c fs v (hPU c fs v hP) hAt) hW hWx

end Place

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.rtM_w2R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rtM_w2R

/-- info: 'Spike.Lib.LowerA64.mainSW_ofPlaceOKR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainSW_ofPlaceOKR

/-- info: 'Spike.Lib.LowerA64.hWx_ofPlaceOKR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hWx_ofPlaceOKR

/-- info: 'Spike.Lib.LowerA64.h0_ofPlaceOK_setupFR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h0_ofPlaceOK_setupFR

end Spike.Lib.LowerA64
