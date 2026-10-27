/-
**The exit tail inside `W2` at any current placement, the post placed by
its value** (AArch64; the twin of `Spike/Lib/LowerX64/RtMainXVL.lean`):
`hWx_ofPlaceOKV` (`Spike/Lib/LowerA64/RtMainXVA.lean`) at `W2AtL` / `MSAtL`
(`Spike/Lib/LowerA64/RtMainXRL.lean`), the current placement `L0`, `ls` a
parameter: a landing's segment resumes `scc_rt_main`'s exit tail at a
placement some allocations past the start's.

- `hWx_ofPlaceOKVL`: `hWx_ofPlaceOKV` at `L0`, `ls` (`MainCtlV` and the
  tail's placement under `L0`).
-/
import Spike.Lib.LowerA64.RtMainXVA
import Spike.Lib.LowerA64.RtMainXRL

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

open Scc.Sem (Place placeVal)
open Spike.Lib.A64.Flow (exitTail ExitW exitNx arun AS SO ND)

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.A64.placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h i

open Spike.Lib.A64.Flow.Ret0 in
open Spike.Lib.A64.Rt (swFSL rS0) in
/-- **The exit tail's states inside `W2AtL` at any current placement `L0`,
`ls`, at every frames, the post at a held pair placed by its value**
(`hWx_ofPlaceOKV` at `L0`, `ls`; `hWx_ofPlaceOKRL`'s placement
generalisation): `SFacts` at the entry's control (`hC0`, not at an overflow
`hov`) at every exit state, the post's controls' `MainCtlV` under `L0` at
the frames (`hQP`), the control placed under `L0` at each tail state by the
value in `x0` (`exitW_placedV`), joined by `rtM_w2V`. -/
theorem hWx_ofPlaceOKVL {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {L0 : Lbl} {ls : Lsize} {c0 : Ctl} {L : Int} (hp : ProgNoS ZBad p)
    (hL0 : 0 ≤ L) (hL : L ≤ 16384) (hL8 : L % 8 = 0)
    {sw : Nat} (hsw : sw < 8) (hc : Spike.Lib.A64.Rt.rtCodeOkS (Ly).prog (setupMC sw) = true)
    (hph : MainPhS (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (Ly).lab (setupMC sw))
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).grow))
    (hset : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).setup))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).fn))
    (hLZ : (setupMC sw).Z.toInt ≤ L) {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hC0 : CFacts (Ly).Λ lbl0 c0) (hov : ¬ OvfReady c0)
    (hQP : ∀ c fs v, Post c fs v → MainCtlV (Ly).Λ L0 c fs v) :
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
    have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
    have H1 := Spike.Lib.A64.Rt.exitW_sfactsAt (lbl := lbl0) (Post := fun c v => Post c fs v)
      (F := swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64)) hI hin hC0
      hph hok h16 (by show -L ≤ _; omega) (Int.le_refl _) (by show (-L) % 8 = 0; omega)
      (by show (0 : Int) % 8 = 0; rfl) (by rw [hZ]; omega)
      (by simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ, setupMC_k sw hsw]; refine ⟨?_, ?_, ?_⟩ <;> omega)
      hsub (Spike.Lib.A64.Rt.fitS_of_sub _ hsub) (fun _ hm => hm.2)
    have H2 := (mainSW_rtM (ar := Spike.Lib.A64.Rt.arOf (Ly).Λ) (PostS := fun _ _ => False)
      (Post := fun c v => Post c fs v)
      (g := ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩)
      (x0 := pinA (Ly).lab + 0#64 + 8#64) (ms := MSAtL h i p rd J none ls0 L0 ls [])
      (F := swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64)) hI
      (Scc.Cert.PlaceOK.A64.printIn_of_placeOKAt h) (Scc.Cert.PlaceOK.A64.abortIn_of_placeOKAt h) hsw hin hph
      hgrow hset hfn hok h16 (by show -L ≤ _; omega) (Int.le_refl _) (fun _ hm => hm.1.2)).exit
    have H3 := exitW_placedV (Λ := (Ly).Λ) (L0 := L0) (fs := fs) (exe := (Ly).exe)
      (endPc := (Ly).endPc) (R := swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0)
      (F := swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64))
      (n := Spike.Lib.A64.Rt.mainSR (Ly).lab (setupMC sw) (fun c v => Post c fs v)) (k := (setupMC sw).k)
      fun _ _ hJ => hQP _ _ _ hJ
    exact ExitW.imp H1 (ExitW.imp (W := fun s c => RtM (Spike.Lib.A64.PhRec.μ (Ly)) (Spike.Lib.A64.Rt.arOf (Ly).Λ)
        (Ly).lab s c ∧ (FrOk2 c fs ∧ (fs = [] → ∀ a, c.term ≠ .ret a) ∧ PlacedS (Ly).Λ L0 s c fs))
        H2 H3 fun _ _ h1 h2 => ⟨h1, h2⟩)
      fun s c hS ⟨hM, hf, hnr, hpl⟩ => rtM_w2V hp hS hov hM hf hnr hpl
  · exact (Spike.Lib.A64.Rt.mainSW_ofFalse (PostS := fun _ _ => False) (Post := fun c v => Post c fs v)
      (ms := MSAtL h i p rd J none ls0 L0 ls []) (sc := setupMC sw)
      (g := ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩)
      (x0 := pinA (Ly).lab + 0#64 + 8#64) fun m hm => hv hm.1.1).exit

end Place

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.hWx_ofPlaceOKVL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hWx_ofPlaceOKVL

end Spike.Lib.LowerA64
