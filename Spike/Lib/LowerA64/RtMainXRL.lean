/-
**`scc_rt_main`'s own states inside `W2` at any current placement**
(AArch64): `W2At` / `MSAt` (`Spike/Lib/LowerA64/Start2W2.lean`) fix the
current placement at the start's, no label placed (`fun _ => none`, `ls0`);
a landing's segment (`H1InA`) resumes `scc_rt_main` at a placement `L0`,
`ls` some allocations past it. Here the current placement is a parameter;
the family `IN … J` stays rooted at the start's.

- `W2AtL`, `MSAtL`: `W2At`, `MSAt` at the current placement `L0`, `ls`;
  `w2AtL_none`, `msAtL_none`: at the start's they are `W2At`, `MSAt` (`rfl`);
- `mainSW_ofPlaceOKRL`, `hWx_ofPlaceOKRL`: `mainSW_ofPlaceOKR`,
  `hWx_ofPlaceOKR` (`Spike/Lib/LowerA64/RtMainXR.lean`) at `L0`, `ls`
  (the controls' `MainCtl` and placement `PlacedS` at `L0`).
-/
import Spike.Lib.LowerA64.RtMainXR

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Rt (InstOk SetupCode setupMC MainSW mainSIn arOf)
open Spike.Lib.A64.Rt.MainS (MainPhS)
open Spike.Lib.A64.WriteAb (Ab)
open Spike.Lib.A64.AllocG (abLabs)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Spike.Lib.AllocReach (IN)
open Scc.Sem.A64 (abi pcOf)

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.A64.placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h i

set_option hygiene false in
/-- The canonical load's memory of the output. -/
local notation "M0" => Spike.Lib.A64.PhRec.m0Of (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h i).Λ o.prog o.secs

open Spike.Lib.A64.PhRec (GOf) in
/-- **`W2` at a current placement `L0`, `ls`** over `IN … J` rooted at the
start's placement (no label placed, `ls0`): `W2At` with the current
placement a parameter. -/
abbrev W2AtL (p : Prog) (rd : TermRun.Word → Prop) (rS : Range) (J : InvS) (Dt : State → Prop) (ls0 : Lsize)
    (L0 : Lbl) (ls : Lsize) : FragS isaLSE2 := fun s c fs =>
  W2 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p rd (GOf Ly M0) (Spike.Lib.A64.PhRec.own (Ly)) rS
    (Spike.Lib.A64.PhRec.Tk (Ly)) (arOf (Ly).Λ) (IN (arOf (Ly).Λ) (fun _ => none) ls0 J) Dt (Ab (Ly).lab)
    L0 ls s c fs

open Spike.Lib.A64.PhRec (GOf) in
/-- **The rows' memory side at a current placement `L0`, `ls`** (`msOfAX`
as in `W2AtL`, abort `ab`): `MSAt` with the current placement a
parameter. -/
abbrev MSAtL (p : Prog) (rd : TermRun.Word → Prop) (J : InvS) (ab : Option (State → Prop)) (ls0 : Lsize)
    (L0 : Lbl) (ls : Lsize) : List TermRun.Frame → MemSide isaLSE2 :=
  msOfAX (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p rd (GOf Ly M0) (fun s _ => Spike.Lib.A64.PhRec.own (Ly) s)
    (arOf (Ly).Λ) (IN (arOf (Ly).Λ) (fun _ => none) ls0 J) ab L0 ls

/-- `W2AtL` at the start's placement is `W2At`. -/
theorem w2AtL_none {p : Prog} {rd : TermRun.Word → Prop} {rS : Range} {J : InvS} {Dt : State → Prop}
    {ls0 : Lsize} : W2AtL h i p rd rS J Dt ls0 (fun _ => none) ls0 = W2At h i p rd rS J Dt ls0 := rfl

/-- `MSAtL` at the start's placement is `MSAt`. -/
theorem msAtL_none {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {ab : Option (State → Prop)}
    {ls0 : Lsize} : MSAtL h i p rd J ab ls0 (fun _ => none) ls0 = MSAt h i p rd J ab ls0 := rfl

open Spike.Lib.A64.Flow.Ret0 in
open Spike.Lib.A64.Rt (swFSL rS0) in
/-- **`scc_rt_main`'s own states after a setup block inside `W2AtL`, the
placement per state, at any current placement** (`mainSW_ofPlaceOKR` at
`L0`, `ls`): `mainSW_sfactsR` and
`mainSW_rtM` at the record, joined by `rtM_w2R` with the controls'
`MainCtlC` (`MainSW.ofCtl`) and their `PlacedS` (`MainSW.ofPl`); the
controls after the setup block and at the return point by their shape
facts (`hCS`, `hCP`, `hQS`, `hQP`), placed at the marshalling block's
states (`hPlS`) and the tail's (`hPlX`), at the stacks' top. -/
theorem mainSW_ofPlaceOKRL {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {L0 : Lbl} {ls : Lsize} {ab : Option (State → Prop)} {c0 : Ctl} {L : Int} (hp : ProgNoS ZBad p)
    (hL0 : 0 ≤ L) (hL : L ≤ 16384) (hL8 : L % 8 = 0)
    {sw : Nat} (hsw : sw < 8) (hc : Spike.Lib.A64.Rt.rtCodeOkS (Ly).prog (setupMC sw) = true)
    (hph : MainPhS (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (Ly).lab (setupMC sw))
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).grow))
    (hset : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).setup))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).fn))
    (hLZ : (setupMC sw).Z.toInt ≤ L)
    {PostS : Ctl → Reg64s → Prop} {Post : Ctl → BitVec 64 → Prop}
    (hC0 : CFacts (Ly).Λ lbl0 c0) (hCS : ∀ c rs, PostS c rs → CFactsC c) (hCP : ∀ c v, Post c v → CFactsC c)
    (hQ0 : MainCtl (Ly).Λ L0 c0) (hQS : ∀ c rs, PostS c rs → MainCtlC c [])
    (hQP : ∀ c v, Post c v → MainCtlC c [])
    (hPlS : BlkW (fun s c => Placed (Ly).Λ lbl0 s c ∧ PlacedS (Ly).Λ L0 s c []) (fun _ _ => False)
      (Ly).exe (Ly).endPc (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0)
      (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64))
      (Spike.Lib.A64.Rt.mainS0 (Ly).lab (setupMC sw) PostS
        ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩
        (pinA (Ly).lab + 0#64 + 8#64))
      (Spike.Lib.A64.Rt.marshal (setupMC sw).sw (setupMC sw).fn))
    (hPlX : ExitW (fun s c => Placed (Ly).Λ lbl0 s c ∧ PlacedS (Ly).Λ L0 s c []) (fun _ _ => False)
      (Ly).exe (Ly).endPc (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0)
      (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64))
      (Spike.Lib.A64.Rt.mainSR (Ly).lab (setupMC sw) Post) (setupMC sw).k) :
    ∀ v, MainSW (Spike.Lib.A64.Rt.nilW (W2AtL h i p rd (rS0 (Ly)) J Dt ls0 L0 ls))
      (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) (Ly).exe (Ly).endPc
      (swR v (-L) 0) (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v) (MSAtL h i p rd J ab ls0 L0 ls [])
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
    have H1 := Spike.Lib.A64.Rt.mainSW_sfactsR (lbl := lbl0) (ms := MSAtL h i p rd J ab ls0 L0 ls []) hI hin hC0 hCS hCP
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
      (ms := MSAtL h i p rd J ab ls0 L0 ls []) hI (Scc.Cert.PlaceOK.A64.printIn_of_placeOKAt h)
      (Scc.Cert.PlaceOK.A64.abortIn_of_placeOKAt h) hsw hin hph hgrow hset hfn hok h16
      (by show -L ≤ _; omega) (Int.le_refl _) (fun _ hm => hm.1.2)
    have H3 := MainSW.ofCtl (Q := fun c => MainCtlC c []) (exe := (Ly).exe) (endPc := (Ly).endPc)
      (R := swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0)
      (F := swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64))
      (ms := MSAtL h i p rd J ab ls0 L0 ls []) (sc := setupMC sw)
      (g := ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩)
      (x0 := pinA (Ly).lab + 0#64 + 8#64) ⟨hQ0.1, hQ0.2.1⟩ hQS hQP
    have H4 := Spike.Lib.A64.Rt.MainSW.ofPl (P := fun s c => PlacedS (Ly).Λ L0 s c [])
      (ms := MSAtL h i p rd J ab ls0 L0 ls []) (sc := setupMC sw)
      (g := ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩)
      (x0 := pinA (Ly).lab + 0#64 + 8#64) hQ0.2.2
      (Spike.Lib.A64.AllocG.BlkW.imp hPlS BlkW.triv fun _ _ h _ => h.2)
      (ExitW.imp hPlX ExitW.triv fun _ _ h _ => h.2)
    exact MainSW.imp H1 (MainSW.imp (W := fun s c => RtM (Spike.Lib.A64.PhRec.μ (Ly))
        (Spike.Lib.A64.Rt.arOf (Ly).Λ) (Ly).lab s c ∧ MainCtlC c [] ∧ PlacedS (Ly).Λ L0 s c [])
        H2 (MainSW.imp H3 H4 fun _ _ h1 h2 => ⟨h1, h2⟩) fun _ _ h1 h2 => ⟨h1, h2⟩)
      fun s c hS ⟨hM, hQ, hPl⟩ => rtM_w2R hp hS hM hQ hPl
  · exact Spike.Lib.A64.Rt.mainSW_ofFalse fun m hm => hv hm.1.1

open Spike.Lib.A64.Flow.Ret0 in
open Spike.Lib.A64.Rt (swFSL rS0) in
/-- **The exit tail's states inside `W2AtL` at every frames, the
placement per state, at any current placement** (`hWx_ofPlaceOKR` at
`L0`, `ls`): `mainSW_sfactsR`'s and `mainSW_rtM`'s exit
parts at the post at the frames `fs`, joined by `rtM_w2R` with the post's
controls' `MainCtlC` at `fs` (`hQP`) and their placement at the tail's
states (`hPlX`, at the stacks' top). -/
theorem hWx_ofPlaceOKRL {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {L0 : Lbl} {ls : Lsize} {c0 : Ctl} {L : Int} (hp : ProgNoS ZBad p)
    (hL0 : 0 ≤ L) (hL : L ≤ 16384) (hL8 : L % 8 = 0)
    {sw : Nat} (hsw : sw < 8) (hc : Spike.Lib.A64.Rt.rtCodeOkS (Ly).prog (setupMC sw) = true)
    (hph : MainPhS (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (Ly).lab (setupMC sw))
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).grow))
    (hset : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).setup))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).fn))
    (hLZ : (setupMC sw).Z.toInt ≤ L) {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hC0 : CFacts (Ly).Λ lbl0 c0) (hCP : ∀ c fs v, Post c fs v → CFactsC c)
    (hQP : ∀ c fs v, Post c fs v → MainCtlC c fs)
    (hPlX : ∀ fs, ExitW (fun s c => Placed (Ly).Λ lbl0 s c ∧ PlacedS (Ly).Λ L0 s c fs)
      (fun _ _ => False) (Ly).exe (Ly).endPc (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0)
      (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64))
      (Spike.Lib.A64.Rt.mainSR (Ly).lab (setupMC sw) (fun c v => Post c fs v)) (setupMC sw).k) :
    ∀ v fs, ExitW (fun s c => W2AtL h i p rd (rS0 (Ly)) J Dt ls0 L0 ls s c fs)
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
      (x0 := pinA (Ly).lab + 0#64 + 8#64) (ms := MSAtL h i p rd J none ls0 L0 ls [])
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
      (x0 := pinA (Ly).lab + 0#64 + 8#64) (ms := MSAtL h i p rd J none ls0 L0 ls [])
      (F := swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64)) hI
      (Scc.Cert.PlaceOK.A64.printIn_of_placeOKAt h) (Scc.Cert.PlaceOK.A64.abortIn_of_placeOKAt h) hsw hin hph
      hgrow hset hfn hok h16 (by show -L ≤ _; omega) (Int.le_refl _) (fun _ hm => hm.1.2)).exit
    have H3 : ExitW (fun s c => MainCtlC c fs ∧ PlacedS (Ly).Λ L0 s c fs) (fun _ _ => False)
        (Ly).exe (Ly).endPc (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0)
        (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64))
        (Spike.Lib.A64.Rt.mainSR (Ly).lab (setupMC sw) (fun c v => Post c fs v)) (setupMC sw).k :=
      ExitW.imp (W1 := fun _ c => MainCtlC c fs)
        ⟨BlkW.ofCtl fun _ _ hJ => hQP _ _ _ hJ, NodeW.ofCtl fun _ _ ⟨_, _, hJ, _⟩ => hQP _ _ _ hJ⟩ (hPlX fs)
        fun _ _ h1 h2 => ⟨h1, h2.2⟩
    exact ExitW.imp H1 (ExitW.imp (W := fun s c => RtM (Spike.Lib.A64.PhRec.μ (Ly)) (Spike.Lib.A64.Rt.arOf (Ly).Λ)
        (Ly).lab s c ∧ MainCtlC c fs ∧ PlacedS (Ly).Λ L0 s c fs) H2 H3 fun _ _ h1 h2 => ⟨h1, h2⟩)
      fun s c hS ⟨hM, hQ, hPl⟩ => rtM_w2R hp hS hM hQ hPl
  · exact (Spike.Lib.A64.Rt.mainSW_ofFalse (PostS := fun _ _ => False) (Post := fun c v => Post c fs v)
      (ms := MSAtL h i p rd J none ls0 L0 ls []) (sc := setupMC sw)
      (g := ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩)
      (x0 := pinA (Ly).lab + 0#64 + 8#64) fun m hm => hv hm.1.1).exit

end Place

/-- info: 'Spike.Lib.LowerA64.w2AtL_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms w2AtL_none

/-- info: 'Spike.Lib.LowerA64.mainSW_ofPlaceOKRL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainSW_ofPlaceOKRL

/-- info: 'Spike.Lib.LowerA64.hWx_ofPlaceOKRL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hWx_ofPlaceOKRL

end Spike.Lib.LowerA64
