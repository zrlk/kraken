/-
**The exit tail inside `W2` at any current placement, the post placed by
its value** (x86-64): `hWx_ofPlaceOKV` (`Spike/Lib/LowerX64/RtMainXV.lean`)
at `W2AtL` / `MSAtL` (`Spike/Lib/LowerX64/RtMainXRL.lean`), the current
placement `L0`, `ls` a parameter: a landing's segment resumes
`scc_rt_main`'s exit tail at a placement some allocations past the start's.

- `hWx_ofPlaceOKVL`: `hWx_ofPlaceOKV` at `L0`, `ls` (`MainCtlV` and the
  tail's placement under `L0`).
-/
import Spike.Lib.LowerX64.RtMainXV
import Spike.Lib.LowerX64.RtMainXRL

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range Place placeVal ValRep exprFv)
open Scc.Sem.X64 (machine kernel)
open Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS
open Spike.Lib.X64 (NodeW BlkW ND At arun AS)
open Spike.Lib.X64.Flow (ofNat_zero' ofNat_add' xExit xExit_ok prologueIn exitIn XExitW xExitNx)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.X64.Rt (InstOk setupMC MainSW mainSIn marshal blkW_postO nodeW_syscall_postO mainSRR)
open Spike.Lib.LowerNode (FrOk2 ZBad)

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.X64.placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h i

open A9NoSpawn Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (swR FStable)
open Spike.Lib.LowerNode (FrOk2 ZBad)

open Spike.Lib.X64.Flow.Ret0 (stacksA)
open Spike.Lib.X64.Rt (arOf)
open Spike.Lib.X64.AllocG (BlkW.imp NodeW.imp)

open Spike.Lib.X64.Flow.Ret0 in
open Spike.Lib.X64.Rt (swFSL rS0 setupMC rtCodeOkS mainSRR) in
/-- **The exit tail's states inside `W2AtL` at any current placement `L0`,
`ls`, at every frames, the post at a held pair placed by its value**
(`hWx_ofPlaceOKV` at `L0`, `ls`; `hWx_ofPlaceOKRL`'s placement
generalisation): `SFacts` at the entry's control (`hC0`, not at an overflow
`hov`) at every exit state, the post's controls' `MainCtlV` under `L0` at
the frames (`hQP`), the control placed under `L0` at each tail state by the
register holding the value (`xExitW_placedV`). -/
theorem hWx_ofPlaceOKVL {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {L0 : Lbl} {ls : Lsize} {c0 : Ctl} {L : Int} (hp : ProgNoS ZBad p)
    (hL : 8 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0)
    {sw : Nat} (hsw : sw < 6) (hc : rtCodeOkS (Ly).prog (setupMC sw) = true)
    (hph : MainPhS (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (Ly).lab (setupMC sw))
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).grow))
    (hset : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).setup))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).fn))
    (hLZ : 8 + 8 + (setupMC sw).Z.toInt + 8 ≤ L) {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hC0 : CFacts (Ly).Λ lbl0 c0) (hov : ¬ OvfReady c0)
    (hQP : ∀ c fs v, Post c fs v → MainCtlV (Ly).Λ L0 c fs v) :
    ∀ v fs, XExitW (fun s c => W2AtL h i p rd (rS0 (Ly)) J Dt ls0 L0 ls s c fs)
      (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) (Ly).exe (Ly).endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (mainSRR (Ly).lab (setupMC sw) (fun c v => Post c fs v)) (-8 - (setupMC sw).Z.toInt) (-8)
      (setupMC sw).k 4 4 5 := by
  intro v fs
  by_cases hv : v = stacksA (Ly).lab + 0#64 + 16384#64
  · subst hv
    have hin := Spike.Lib.X64.Rt.mainSIn_of_okS hc
    have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h i (rS := rS0 (Ly))
    have hsub := Spike.Lib.X64.Rt.rS0_sub (Ly)
    have hL0 : (0 : Int) ≤ L := by omega
    have h8 : (stacksA (Ly).lab + 0#64 + 16384#64).toNat % 8 = 0 := by
      rw [Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
    have hok : (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).OK := by
      rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ hL0 hLm
    have hfit : (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))).toNat + 8 ≤ 2 ^ 64 := by
      rw [Spike.Lib.X64.Rt.pinA_lab0]; exact Spike.Lib.X64.Rt.rt_hfit _
    have hout : ((limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))).toNat : Int) + 8 ≤
          (stacksA (Ly).lab + 0#64 + 16384#64).toNat + -L ∨
        ((stacksA (Ly).lab + 0#64 + 16384#64).toNat : Int) + 0 ≤
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))).toNat := by
      rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_houtD _ hL0 hLm
    obtain ⟨hR', -⟩ := Spike.Lib.X64.Rt.mainE_ok (rS := rS0 (Ly)) (tcb := pinA (Ly).lab + 0#64 + 8#64)
      (top := stacksA (Ly).lab + 0#64 + 16384#64) hL hL8 hok hfit hout (Spike.Lib.X64.Rt.fitS_of_sub _ hsub)
    have hb0 : ((((swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).callee (-8 - 0) (8 - L) 8).base.toNat : Int) =
        (stacksA (Ly).lab + 0#64 + 16384#64).toNat + (-8 - 0)) :=
      Region.callee_base hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
    have H1 := exitW_sfactsAt (lbl := lbl0) hI hsw hin (Post := fun c v => Post c fs v)
      (F := fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64) m ∧
        CallerCells (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0) (-8 - 0) (8 - L) 8 m)
      hC0 hph hR' (by omega) (by show 8 - L ≤ _; omega)
      (by show (0 : Int) ≤ 8; decide) (by show (8 - L) % 8 = 0; omega) (by show (8 : Int) % 8 = 0; decide)
      hsub (Spike.Lib.X64.Rt.fitS_of_sub _ hsub)
      (fun _ h => Spike.Lib.X64.Rt.stackOff_callee hok h8 (by show (-L) % 8 = 0; omega)
        (by show (0 : Int) % 8 = 0; rfl) (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
        (by decide) h.1.2 h.2)
    have H2 := (mainSW_rtM (ar := arOf (Ly).Λ) (PostS := fun _ _ => False) (Post := fun c v => Post c fs v)
      (g := ⟨stacksA (Ly).lab + 0#64 + 16384#64 - 8#64, tpOf (pinA (Ly).lab + 0#64 + 8#64), c0⟩)
      (x0 := (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec) (ms := MSAtL h i p rd J none ls0 L0 ls [])
      (F := fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64) m ∧
        CallerCells (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0) (-8 - 0) (8 - L) 8 m) hI
      (Scc.Cert.PlaceOK.X64.printIn_of_placeOKAt h) (Scc.Cert.PlaceOK.X64.abortIn_of_placeOKAt h)
      hsw hin hph hgrow hset hfn hR' (by show 8 - L ≤ _; omega) (by show (0 : Int) ≤ 8; decide)).exit
    have H3 := xExitW_placedV (Λ := (Ly).Λ) (L0 := L0) (fs := fs) (exe := (Ly).exe)
      (endPc := (Ly).endPc) (R := (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).callee (-8 - 0) (8 - L) 8)
      (F := fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64) m ∧
        CallerCells (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0) (-8 - 0) (8 - L) 8 m)
      (n := mainSRR (Ly).lab (setupMC sw) (fun c v => Post c fs v)) (k := (setupMC sw).k) (z0 := 4) (z1 := 4)
      (z2 := 5) rfl fun _ _ hJ => hQP _ _ _ hJ.1
    have hw : ∀ s c, SFacts (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly))
        (Spike.Lib.X64.PhRec.Tk (Ly)) lbl0 s c0 →
        (RtM (Spike.Lib.X64.PhRec.μ (Ly)) (arOf (Ly).Λ) (Ly).lab s c ∧
          (FrOk2 c fs ∧ (fs = [] → ∀ a, c.term ≠ .ret a) ∧ PlacedS (Ly).Λ L0 s c fs)) →
        W2AtL h i p rd (rS0 (Ly)) J Dt ls0 L0 ls s c fs :=
      fun _ _ h1 h2 => rtM_w2V hp h1 hov h2.1 h2.2.1 h2.2.2.1 h2.2.2.2
    exact ⟨BlkW.imp H1.w0 (BlkW.imp H2.w0 H3.w0 fun _ _ a b => ⟨a, b⟩) hw,
      NodeW.imp H1.w1 (NodeW.imp H2.w1 H3.w1 fun _ _ a b => ⟨a, b⟩) hw⟩
  · exact ⟨Spike.Lib.X64.Rt.blkW_ofFalse fun m hm => hv hm.1.1.1,
      Spike.Lib.X64.Rt.nodeW_ofFalse fun m hm => hv hm.1.1.1⟩

end Place

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hWx_ofPlaceOKVL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hWx_ofPlaceOKVL

end Spike.Lib.LowerX64
