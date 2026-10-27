/-
**`h0` with the controls back from the setup block and the user function
placed state by state** (x86-64, option (b) of h1 chunk 6; the twin of
`Spike/Lib/LowerA64/RtMainXR.lean`): `CFacts` and `MainCtl` ask a control
placed in every state, which a control back from a call holding a
run-dependent result in registers is not; here those controls carry
`CFactsC` and `MainCtlC`, their placement asked at the states of the nodes
they reach (`Spike/Lib/Rt/X64RtWR.lean`).

- `mainSW_sfactsR`: `mainSW_sfacts` with `CFactsC` back from the setup
  block and the user function, their placement at the marshalling block's
  and the exit tail's states (`hPlS`, `hPlX`);
- `MainCtlC`: `MainCtlF` without the placement; `rtM_w2R`: `rtM_w2F` with
  the placement at the state;
- `mainSW_ofPlaceOKR`, `hWx_ofPlaceOKR`, `h0_ofPlaceOK_setupFR`:
  `mainSW_ofPlaceOK`, `hWx_ofPlaceOK`, `h0_ofPlaceOK_setupF`
  (`Spike/Lib/LowerX64/RtMainXF.lean`) at `CFactsC ∧ MainCtlC` of the
  controls back, the placement at both placements (the source's `lbl0`,
  the rows' none) at the marshalling block's and the exit tail's states
  (`hPlS`, `hPlX`, at the switch region's top).
-/
import Spike.Lib.LowerX64.RtMainXF
import Spike.Lib.Rt.X64RtWR

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS
open Spike.Lib.X64 (NodeW BlkW ND classify okBlk okBlk_callB)
open Spike.Lib.X64.Flow (ofNat_zero' ofNat_add' xHead xLea xCmp xFr xExit xS2 xS1 hdRegs xHead_ok xLea_ok xCmp_ok
  xFr_ok xExit_ok prologueIn exitIn XExitW)
open Spike.Lib.X64.Flow.Ret0 (MainG StackOff limA)
open Spike.Lib.X64.Rt (InstOk SetupCode setupMC marshal MainSW mainSIn okBlk_marshal blkW_postO nodeW_fsld_postO
  nodeW_syscall_postO blkW_postOR nodeW_syscall_postOR CFactsC mainS0R mainSRR)
open Spike.Lib.X64.Rt.MainU (xHead_noRet xLea_noRet xCmp_noRet xFr_noRet callB_noRet xExit_noRet)
open Scc.Cert.Rt.X64 (blockAtB label_labelGapB)

section Main

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {lbl : Lbl}

set_option maxHeartbeats 800000 in
/-- **`scc_rt_main`'s own states after a setup block are inside `SFacts`,
the controls back from the setup block and the user function placed state
by state** (`mainSW_sfacts`): at the entry the control's `CFacts` (`hC0`);
back from the setup block (`hPostS`) and from the user function (`hPost`)
only `CFactsC`, their placement at the marshalling block's and the exit
tail's states as state obligations (`hPlS`, `hPlX`). -/
theorem mainSW_sfactsR {ms : MemSide isa} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    {sw : Nat} (hsw : sw < 6) (hin : mainSIn cells (setupMC sw) = true)
    {PostS : Ctl → Reg64s → Prop} {Post : Ctl → BitVec 64 → Prop} {g : MainG} {x0 : BitVec 64}
    (hC0 : CFacts Λ lbl g.c0) (hPostS : ∀ c rs, PostS c rs → CFactsC c)
    (hPost : ∀ c v, Post c v → CFactsC c) (hph : MainPhS okPc ph lab (setupMC sw))
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hR8 : R.base.toNat % 8 = 0)
    (hlo : R.lo ≤ -8 - (setupMC sw).Z.toInt - 8) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨limA g.tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA g.tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hPlS : BlkW (fun s c => Placed Λ lbl s c) (fun _ _ => False) exe endPc R F
      (mainS0R (_root_.Executable.labels exe).label (setupMC sw) PostS g x0) (marshal (setupMC sw).sw (setupMC sw).fn))
    (hPlX : XExitW (fun s c => Placed Λ lbl s c) (fun _ _ => False) exe endPc R F
      (mainSRR (_root_.Executable.labels exe).label (setupMC sw) Post) (-8 - (setupMC sw).Z.toInt) (-8)
      (setupMC sw).k 4 4 5) :
    MainSW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F ms (setupMC sw) PostS Post g x0 := by
  have hZ := setupMC_Z sw hsw
  have hk := setupMC_k sw hsw
  have hm8 : (-8 : Int64).toInt = -8 := by decide
  have hmf : noRetBlk (marshal (setupMC sw).sw (setupMC sw).fn) = true ∧
      blkLabs (marshal (setupMC sw).sw (setupMC sw).fn) = [(setupMC sw).fn] ∧
      lastFalls (marshal (setupMC sw).sw (setupMC sw).fn) = false := marshal_facts sw hsw
  have h := hin
  simp only [mainSIn, prologueIn, exitIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hgap, bHd⟩, bLea⟩, bLd⟩, bCmp⟩, bFr⟩, -⟩, bCall⟩, -⟩, bMsh⟩, -⟩, bEx, bSvc⟩ := h
  have esc := label_labelGapB hI.lays hgap
  rw [hI.labOk] at esc
  have h4 : lab "scc_rt_main" + 1 + 3 = lab (setupMC sw).sc := by rw [esc, Int64.add_assoc]; rfl
  have hloZ : R.lo ≤ -8 - (setupMC sw).Z.toInt := by omega
  rw [hI.labOk] at hPlS hPlX
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩⟩ <;> rw [hI.labOk]
  · -- the head
    exact blkW_postO hI bHd (ofNat_zero' _) (xHead_ok (lo := -8 - (setupMC sw).Z.toInt) (hi := 0)
      (by omega) (Int.le_refl _)) hR hloZ hhi hR8 hl hh (fun _ _ hJ => hJ.1.1 ▸ hC0) hph.hd
      (fun _ _ _ k hk hr => (noRet_false xHead_noRet k hk hr).elim) (fun _ _ _ => rfl) hsub hfit hFO
  · -- the check's address
    exact blkW_postO hI bLea (by show _ = _ + 1 + 3; rw [h4, ofNat_zero'])
      (xLea_ok (lo := -8 - (setupMC sw).Z.toInt) (hi := 0) _ _) hR hloZ hhi hR8 hl hh
      (fun _ _ ⟨_, hJ, _⟩ => hJ.1.1 ▸ hC0) hph.lea
      (fun _ _ _ k hk hr => (noRet_false (xLea_noRet _ _) k hk hr).elim) (fun _ _ _ => rfl) hsub hfit hFO
  · -- the limit's load
    exact nodeW_fsld_postO (p := lab (setupMC sw).sc + Int64.ofNat 5) hI bLd rfl
      (by show _ + 1 + 3 + _ = _; rw [h4]) (fun _ _ ⟨_, hJ, _⟩ => hJ.1.1 ▸ hC0) hph.ld.1 hph.ld.2
      (fun _ _ ⟨σ0, hJ, he⟩ => by
        rw [he, show (xS2 (setupMC sw).Z σ0).regs.fsBase = σ0.regs.fsBase by simp [xS2, xS1, hdRegs, Reg64s.set64],
          hJ.1.2.2]
        rfl)
      hmr hun hR hR8 hl hh hsub hFO
  · -- the check
    have e : lab (setupMC sw).sc + Int64.ofNat 14 =
        lab "scc_rt_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 := by rw [h4, ← ofNat_add']
    exact blkW_postO hI bCmp e (xCmp_ok (lo := -8 - (setupMC sw).Z.toInt) (hi := 0) _ _ _ _) hR hloZ hhi hR8 hl
      hh (fun _ _ ⟨_, _, hJ, _⟩ => hJ.1.1 ▸ hC0) hph.cmp
      (fun _ _ _ k hk hr => (noRet_false (xCmp_noRet _ _ _) k hk hr).elim) (fun _ _ _ => rfl) hsub hfit
      hFO
  · -- the frame
    have e : lab (setupMC sw).sc + Int64.ofNat 19 =
        lab "scc_rt_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 2 := by
      rw [h4, ← ofNat_add', ← ofNat_add', ← ofNat_add']
    exact blkW_postO hI bFr e (xFr_ok (lo := -8 - (setupMC sw).Z.toInt) (hi := 0) _ _ _
        (fun p hp => by
          simp only [List.mem_singleton] at hp
          subst hp
          simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ, hm8]
          refine ⟨?_, ?_, ?_⟩ <;> omega))
      hR hloZ hhi hR8 hl hh (fun _ _ ⟨_, _, hJ, _⟩ => hJ.1.1 ▸ hC0) hph.fr
      (fun _ _ _ k hk hr => (noRet_false (xFr_noRet _ _ _) k hk hr).elim)
      (fun _ _ _ => rfl) hsub hfit hFO
  · -- the setup call
    exact blkW_postO hI bCall (ofNat_zero' _)
      (okBlk_callB (lo := -8 - (setupMC sw).Z.toInt - 8) (hi := 0) _ (by
        simp only [Spike.Lib.offOk, decide_eq_true_eq, Spike.Lib.X64.Rt.mainS1R, Spike.Lib.X64.Rt.oU, hZ]
        refine ⟨?_, ?_, ?_⟩ <;> omega))
      hR hlo hhi hR8 hl hh (fun _ _ hJ => hJ.1.1 ▸ hC0) hph.call0
      (fun _ _ _ k hk hr => (noRet_false (callB_noRet _) k hk hr).elim) (fun _ _ _ => rfl) hsub
      hfit hFO
  · -- the marshalling block
    exact blkW_postOR hI bMsh (ofNat_zero' _)
      (okBlk_marshal (lo := -8 - (setupMC sw).Z.toInt - 8) (hi := 0) (show sw ≤ 5 by omega) _
        (fun i hi => by
          simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ]
          refine ⟨?_, ?_, ?_⟩ <;> omega)
        (by
          simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ]
          refine ⟨?_, ?_, ?_⟩ <;> omega)
        (by
          simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ]
          refine ⟨?_, ?_, ?_⟩ <;> omega))
      hR hlo hhi hR8 hl hh (fun _ _ hJ => hPostS _ _ hJ.1.1) hPlS hph.sp0
      (fun _ _ _ k hk hr => (noRet_false hmf.1 k hk hr).elim) (fun _ _ _ => rfl) hsub hfit hFO
  · -- the tail's block
    exact blkW_postOR hI bEx (ofNat_zero' _)
      (xExit_ok (lo := -8 - (setupMC sw).Z.toInt) (hi := 0) _ _ _ _ (by
        simp only [Spike.Lib.offOk, decide_eq_true_eq, hk, hZ]
        refine ⟨?_, ?_, ?_⟩ <;> omega))
      hR hloZ hhi hR8 hl hh (fun _ _ hJ => hPost _ _ hJ.1) hPlX.w0 hph.ex
      (fun _ _ _ k hk hr => (noRet_false (xExit_noRet _ _ _ _) k hk hr).elim) (fun _ _ _ => rfl)
      hsub hfit hFO
  · -- the `exit_group`
    exact nodeW_syscall_postOR (p := lab (setupMC sw).sp1 + Int64.ofNat 13) hI bSvc rfl
      (by
        show lab (setupMC sw).sp1 + Int64.ofNat 4 + Int64.ofNat 4 + Int64.ofNat 5 = _
        rw [← ofNat_add', ← ofNat_add'])
      (fun _ _ ⟨_, _, hJ, _⟩ => hPost _ _ hJ.1) hPlX.w1 hph.svc.1 hph.svc.2 hR hR8 hl hh hsub hFO
      (fun _ _ h => by rw [h.1]; decide)

end Main

section RtX

open A9NoSpawn Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1 Spike.Lib.X64ConsumerA
open Spike.Lib.X64.WriteAb (Ab)
open Spike.Lib.LowerNode (FrOk2 ZBad)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {ar : Arena} {lbl : Lbl} {lab : Label → Int64}

/-- **A source control's facts `W2` asks at the frames `fs` beyond `SFacts`,
but its placement** (`MainCtlF` without `PlacedS`): its frame runs free of
`ZBad`, not at an overflow. -/
def MainCtlC (c : Ctl) (fs : List TermRun.Frame) : Prop :=
  FrOk2 c fs ∧ ¬ OvfReady c

/-- **`W2` at a runtime state at the frames `fs`, at a source control placed
there** (`rtM_w2F` with the placement at the state): `SFacts` at the
control, `RtM`, the control's `MainCtlC` at `fs` and its placement at the
state at `fs` (`hPl`). -/
theorem rtM_w2R {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : Own} {rS : Range}
    {Tk : State → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl} {lsize : Lsize} (hp : ProgNoS ZBad p)
    {s : State} {c : Ctl} {fs : List TermRun.Frame} (hS : SFacts Λ μ own rS Tk lbl0 s c) (hM : RtM μ ar lab s c)
    (hQ : MainCtlC c fs) (hPl : PlacedS Λ lbl s c fs) :
    W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c fs := by
  have hP := w2Part_of_wrOff (J := J) (rd := rd) (G := G) (p := p) (lsize := lsize) hM.1 hPl hM.2 hS
  exact w2_of hp hQ.1 (hS.toSt.dt_mono fun _ h => h.elim) hP.1 (fun _ => hS.noRet) (.of_placedS hP.2.1) hP.2.2.1
    (abortOkA_of_ne (noAbort_of_sfacts hQ.2 hS)) hP.2.2.2

end RtX

/-! ## At a placed output -/

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
open Spike.Lib.X64.Rt (MainSW swFSL rS0 setupMC rtCodeOkS mainS0R mainSRR CFactsC) in
/-- **`scc_rt_main`'s own states inside `W2At`, the controls back placed
state by state** (`mainSW_ofPlaceOK` over `mainSW_sfactsR`,
`MainSW.ofPl`, `rtM_w2R`): back from the setup block and the user function
the controls' `CFactsC` (`hCS`, `hCP`) and `MainCtlC` (`hQS`, `hQP`), their
placement at both placements at the marshalling block's and the exit
tail's states at the switch region's top (`hPlS`, `hPlX`). -/
theorem mainSW_ofPlaceOKR {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {ab : Option (State → Prop)} {c0 : Ctl} {L : Int} (hp : ProgNoS ZBad p)
    (hL : 8 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0)
    {sw : Nat} (hsw : sw < 6) (hc : rtCodeOkS (Ly).prog (setupMC sw) = true)
    (hph : MainPhS (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (Ly).lab (setupMC sw))
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).grow))
    (hset : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).setup))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).fn))
    (hLZ : 8 + 8 + (setupMC sw).Z.toInt + 8 ≤ L)
    {PostS : Ctl → Reg64s → Prop} {Post : Ctl → BitVec 64 → Prop}
    (hC0 : CFacts (Ly).Λ lbl0 c0) (hCS : ∀ c rs, PostS c rs → CFactsC c) (hCP : ∀ c v, Post c v → CFactsC c)
    (hQ0 : MainCtl (Ly).Λ (fun _ => none) c0) (hQS : ∀ c rs, PostS c rs → MainCtlC c [])
    (hQP : ∀ c v, Post c v → MainCtlC c [])
    (hPlS : BlkW (fun s c => Placed (Ly).Λ lbl0 s c ∧ PlacedS (Ly).Λ (fun _ => none) s c []) (fun _ _ => False)
      (Ly).exe (Ly).endPc ((swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64) m ∧
        CallerCells (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0) (-8 - 0) (8 - L) 8 m)
      (mainS0R (Ly).lab (setupMC sw) PostS
        ⟨stacksA (Ly).lab + 0#64 + 16384#64 - 8#64, tpOf (pinA (Ly).lab + 0#64 + 8#64), c0⟩
        (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec)
      (marshal (setupMC sw).sw (setupMC sw).fn))
    (hPlX : XExitW (fun s c => Placed (Ly).Λ lbl0 s c ∧ PlacedS (Ly).Λ (fun _ => none) s c []) (fun _ _ => False)
      (Ly).exe (Ly).endPc ((swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64) m ∧
        CallerCells (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0) (-8 - 0) (8 - L) 8 m)
      (mainSRR (Ly).lab (setupMC sw) Post) (-8 - (setupMC sw).Z.toInt) (-8) (setupMC sw).k 4 4 5) :
    ∀ v, MainSW (Spike.Lib.X64.Rt.nilW (W2At h i p rd (rS0 (Ly)) J Dt ls0))
      (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) (Ly).exe (Ly).endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m) (MSAt h i p rd J ab ls0 [])
      (setupMC sw) PostS Post ⟨stacksA (Ly).lab + 0#64 + 16384#64 - 8#64, tpOf (pinA (Ly).lab + 0#64 + 8#64), c0⟩
      (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec := by
  intro v
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
    have hmr : Scc.Sem.Kernel.mapped (K0 (Ly).Λ) false ⟨limA (tpOf (pinA (Ly).lab + 0#64 + 8#64)), 8⟩ = true := by
      rw [(Ly).lab_pin, Spike.Lib.X64.Rt.limA_tcb0]; exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1
    obtain ⟨hR', -⟩ := Spike.Lib.X64.Rt.mainE_ok (rS := rS0 (Ly)) (tcb := pinA (Ly).lab + 0#64 + 8#64)
      (top := stacksA (Ly).lab + 0#64 + 16384#64) hL hL8 hok hfit hout (Spike.Lib.X64.Rt.fitS_of_sub _ hsub)
    have hb0 : ((((swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).callee (-8 - 0) (8 - L) 8).base.toNat : Int) =
        (stacksA (Ly).lab + 0#64 + 16384#64).toNat + (-8 - 0)) :=
      Region.callee_base hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
    have hS1 := mainSW_sfactsR (ms := MSAt h i p rd J ab ls0 []) (lbl := lbl0) hI hsw hin (Post := Post)
      (F := fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64) m ∧
        CallerCells (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0) (-8 - 0) (8 - L) 8 m)
      (g := ⟨stacksA (Ly).lab + 0#64 + 16384#64 - 8#64, tpOf (pinA (Ly).lab + 0#64 + 8#64), c0⟩)
      (x0 := (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec) hC0 hCS hCP hph hR' (by omega)
      (by show 8 - L ≤ _; omega)
      (by show (0 : Int) ≤ 8; decide) (by show (8 - L) % 8 = 0; omega) (by show (8 : Int) % 8 = 0; decide) hmr
      (fun _ h => h.1.1.2) hsub (Spike.Lib.X64.Rt.fitS_of_sub _ hsub)
      (fun _ h => Spike.Lib.X64.Rt.stackOff_callee hok h8 (by show (-L) % 8 = 0; omega)
        (by show (0 : Int) % 8 = 0; rfl) (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
        (by decide) h.1.2 h.2)
      (BlkW.imp hPlS hPlS fun _ _ h _ => h.1)
      ⟨BlkW.imp hPlX.w0 hPlX.w0 fun _ _ h _ => h.1, NodeW.imp hPlX.w1 hPlX.w1 fun _ _ h _ => h.1⟩
    have hS2 := Spike.Lib.X64.Rt.MainSW.ofPl
      (P := fun s c => MainCtlC c [] ∧ PlacedS (Ly).Λ (fun _ => none) s c []) (ms := MSAt h i p rd J ab ls0 [])
      (sc := setupMC sw) (PostS := PostS) (Post := Post)
      (g := ⟨stacksA (Ly).lab + 0#64 + 16384#64 - 8#64, tpOf (pinA (Ly).lab + 0#64 + 8#64), c0⟩)
      (x0 := (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec)
      (fun s => ⟨⟨hQ0.1, hQ0.2.1⟩, hQ0.2.2 s⟩)
      (BlkW.imp (Spike.Lib.X64.Rt.BlkW.ofSt fun _ _ hJ _ => hQS _ _ hJ.1.1) hPlS
        fun _ _ (h1 : MainCtlC _ []) (h2 : _ ∧ PlacedS (Ly).Λ (fun _ => none) _ _ []) => ⟨h1, h2.2⟩)
      ⟨BlkW.imp (Spike.Lib.X64.Rt.BlkW.ofSt fun _ _ hJ _ => hQP _ _ hJ.1) hPlX.w0
        fun _ _ (h1 : MainCtlC _ []) (h2 : _ ∧ PlacedS (Ly).Λ (fun _ => none) _ _ []) => ⟨h1, h2.2⟩,
        NodeW.imp (Spike.Lib.X64.Rt.NodeW.ofSt fun _ _ ⟨_, _, hJ, _⟩ _ => hQP _ _ hJ.1) hPlX.w1
          fun _ _ (h1 : MainCtlC _ []) (h2 : _ ∧ PlacedS (Ly).Λ (fun _ => none) _ _ []) => ⟨h1, h2.2⟩⟩
    exact MainSW.imp hS1
      (MainSW.imp (W := fun s c => RtM (Spike.Lib.X64.PhRec.μ (Ly)) (arOf (Ly).Λ) (Ly).lab s c ∧
          (MainCtlC c [] ∧ PlacedS (Ly).Λ (fun _ => none) s c []))
        (mainSW_rtM hI (Scc.Cert.PlaceOK.X64.printIn_of_placeOKAt h)
        (Scc.Cert.PlaceOK.X64.abortIn_of_placeOKAt h)
        hsw hin hph hgrow hset hfn hR' (by show 8 - L ≤ _; omega) (by show (0 : Int) ≤ 8; decide)) hS2
        fun _ _ h1 h2 => ⟨h1, h2⟩)
      fun s c h1 h2 => rtM_w2R hp h1 h2.1 h2.2.1 h2.2.2
  · exact MainSW.ofFalse fun m hm => hv hm.1.1.1

open Spike.Lib.X64.Flow.Ret0 in
open Spike.Lib.X64.Flow (XExitW) in
open Spike.Lib.X64.Rt (swFSL rS0 setupMC rtCodeOkS mainSRR CFactsC) in
/-- **The exit tail's states inside `W2At` at every frames, the post's
controls placed state by state** (`hWx_ofPlaceOK` over `mainSW_sfactsR`,
`rtM_w2R`): the post's controls' `CFactsC` (`hCP`) and `MainCtlC` at the
frames (`hQP`), their placement at both placements at the exit tail's
states at the switch region's top at every frames (`hPlX`). -/
theorem hWx_ofPlaceOKR {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {c0 : Ctl} {L : Int} (hp : ProgNoS ZBad p)
    (hL : 8 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0)
    {sw : Nat} (hsw : sw < 6) (hc : rtCodeOkS (Ly).prog (setupMC sw) = true)
    (hph : MainPhS (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (Ly).lab (setupMC sw))
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).grow))
    (hset : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).setup))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).fn))
    (hLZ : 8 + 8 + (setupMC sw).Z.toInt + 8 ≤ L) {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hC0 : CFacts (Ly).Λ lbl0 c0) (hCP : ∀ c fs v, Post c fs v → CFactsC c)
    (hQP : ∀ c fs v, Post c fs v → MainCtlC c fs)
    (hPlX : ∀ fs, XExitW (fun s c => Placed (Ly).Λ lbl0 s c ∧ PlacedS (Ly).Λ (fun _ => none) s c fs) (fun _ _ => False)
      (Ly).exe (Ly).endPc ((swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64) m ∧
        CallerCells (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0) (-8 - 0) (8 - L) 8 m)
      (mainSRR (Ly).lab (setupMC sw) (fun c v => Post c fs v)) (-8 - (setupMC sw).Z.toInt) (-8) (setupMC sw).k 4 4 5) :
    ∀ v fs, XExitW (fun s c => W2At h i p rd (rS0 (Ly)) J Dt ls0 s c fs)
      (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) (Ly).exe (Ly).endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (Spike.Lib.X64.Rt.mainSRR (Ly).lab (setupMC sw) (fun c v => Post c fs v)) (-8 - (setupMC sw).Z.toInt) (-8)
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
    have hmr : Scc.Sem.Kernel.mapped (K0 (Ly).Λ) false ⟨limA (tpOf (pinA (Ly).lab + 0#64 + 8#64)), 8⟩ = true := by
      rw [(Ly).lab_pin, Spike.Lib.X64.Rt.limA_tcb0]; exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1
    obtain ⟨hR', -⟩ := Spike.Lib.X64.Rt.mainE_ok (rS := rS0 (Ly)) (tcb := pinA (Ly).lab + 0#64 + 8#64)
      (top := stacksA (Ly).lab + 0#64 + 16384#64) hL hL8 hok hfit hout (Spike.Lib.X64.Rt.fitS_of_sub _ hsub)
    have hb0 : ((((swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).callee (-8 - 0) (8 - L) 8).base.toNat : Int) =
        (stacksA (Ly).lab + 0#64 + 16384#64).toNat + (-8 - 0)) :=
      Region.callee_base hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
    have H1 := (mainSW_sfactsR (ms := MSAt h i p rd J none ls0 []) (lbl := lbl0) hI hsw hin
      (PostS := fun _ _ => False) (Post := fun c v => Post c fs v)
      (F := fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64) m ∧
        CallerCells (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0) (-8 - 0) (8 - L) 8 m)
      (g := ⟨stacksA (Ly).lab + 0#64 + 16384#64 - 8#64, tpOf (pinA (Ly).lab + 0#64 + 8#64), c0⟩)
      (x0 := (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec) hC0 (fun _ _ h => h.elim)
      (fun c v h => hCP c fs v h) hph hR' (by omega) (by show 8 - L ≤ _; omega)
      (by show (0 : Int) ≤ 8; decide) (by show (8 - L) % 8 = 0; omega) (by show (8 : Int) % 8 = 0; decide) hmr
      (fun _ h => h.1.1.2) hsub (Spike.Lib.X64.Rt.fitS_of_sub _ hsub)
      (fun _ h => Spike.Lib.X64.Rt.stackOff_callee hok h8 (by show (-L) % 8 = 0; omega)
        (by show (0 : Int) % 8 = 0; rfl) (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
        (by decide) h.1.2 h.2)
      (Spike.Lib.X64.Rt.BlkW.ofSt fun _ _ hJ => hJ.1.1.elim)
      ⟨BlkW.imp (hPlX fs).w0 (hPlX fs).w0 fun _ _ h _ => h.1,
        NodeW.imp (hPlX fs).w1 (hPlX fs).w1 fun _ _ h _ => h.1⟩).exit
    have H2 := (mainSW_rtM (ar := arOf (Ly).Λ) (PostS := fun _ _ => False) (Post := fun c v => Post c fs v)
      (g := ⟨stacksA (Ly).lab + 0#64 + 16384#64 - 8#64, tpOf (pinA (Ly).lab + 0#64 + 8#64), c0⟩)
      (x0 := (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec) (ms := MSAt h i p rd J none ls0 [])
      (F := fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64) m ∧
        CallerCells (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0) (-8 - 0) (8 - L) 8 m) hI
      (Scc.Cert.PlaceOK.X64.printIn_of_placeOKAt h) (Scc.Cert.PlaceOK.X64.abortIn_of_placeOKAt h)
      hsw hin hph hgrow hset hfn hR' (by show 8 - L ≤ _; omega) (by show (0 : Int) ≤ 8; decide)).exit
    have hw : ∀ s c, SFacts (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly))
        (Spike.Lib.X64.PhRec.Tk (Ly)) lbl0 s c →
        (RtM (Spike.Lib.X64.PhRec.μ (Ly)) (arOf (Ly).Λ) (Ly).lab s c ∧
          (MainCtlC c fs ∧ PlacedS (Ly).Λ (fun _ => none) s c fs)) →
        W2At h i p rd (rS0 (Ly)) J Dt ls0 s c fs :=
      fun _ _ h1 h2 => rtM_w2R hp h1 h2.1 h2.2.1 h2.2.2
    exact ⟨BlkW.imp H1.w0 (BlkW.imp H2.w0 (BlkW.imp (Spike.Lib.X64.Rt.BlkW.ofSt fun _ _ hJ _ => hQP _ _ _ hJ.1)
        (hPlX fs).w0 fun _ _ a b => ⟨a, b.2⟩) fun _ _ a b => ⟨a, b⟩) hw,
      NodeW.imp H1.w1 (NodeW.imp H2.w1 (NodeW.imp
        (Spike.Lib.X64.Rt.NodeW.ofSt fun _ _ ⟨_, _, hJ, _⟩ _ => hQP _ _ _ hJ.1)
        (hPlX fs).w1 fun _ _ a b => ⟨a, b.2⟩) fun _ _ a b => ⟨a, b⟩) hw⟩
  · exact ⟨Spike.Lib.X64.Rt.blkW_ofFalse fun m hm => hv hm.1.1.1,
      Spike.Lib.X64.Rt.nodeW_ofFalse fun m hm => hv hm.1.1.1⟩

open Spike.Lib.X64.Flow.Ret0 in
open Spike.Lib.X64.Rt (SetupCode SetupCallWS MainCallWSF MainSW SetupArgs swFSL mainSIn oU rS0 entryR rtF setupMC
  rtCodeOkS mainS0R mainSRR CFactsC) in
open Spike.Lib.AllocReach (IN) in
/-- **The consumer's `h0` at a placed output, an entry state and a setup
block, `main` returning at pending frames, the controls back placed state
by state** (`h0_ofPlaceOK_setupF` over `mainSW_ofPlaceOKR`,
`hWx_ofPlaceOKR`): back from the setup block and the user function the
controls' `CFactsC ∧ MainCtlC` (`hPostS`, `hPost`), their placement at
both placements at the marshalling block's and the exit tail's states at
the switch region's top (`hPlS`, `hPlX`). -/
theorem h0_ofPlaceOK_setupFR {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {ab : Option (State → Prop)} {c0 : Ctl} {L : Int} {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ)
    {FE : MachineData → Prop} (hFE : ∀ m, FE m → rtF (Ly) m) (hFEs : FStable (entryR E) FE)
    (hFEk : ∀ m pm, FE m → FE (takeMem pm (rS0 (Ly)) m))
    (hp : ProgNoS ZBad p) (hf0 : FrOk2 c0 []) (hov : ¬ OvfReady c0) (hC0 : CFacts (Ly).Λ lbl0 c0)
    (hpl0 : ∀ s, PlacedS (Ly).Λ (fun _ => none) s c0 [])
    (hL : 8 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0)
    {sw : Nat} (hsw : sw < 6) (hc : rtCodeOkS (Ly).prog (setupMC sw) = true)
    (hph : MainPhS (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (Ly).lab (setupMC sw))
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).grow))
    (hset : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).setup))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).fn))
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    {PostR PostS : Ctl → Reg64s → Prop} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hPostS : ∀ c rs, PostS c rs → CFactsC c ∧ MainCtlC c [])
    (hPU : ∀ c fs v, Post c fs v → UPostRF p (fun _ => none) c fs v)
    (hPost : ∀ c fs v, Post c fs v → CFactsC c ∧ MainCtlC c fs)
    (hPlS : BlkW (fun s c => Placed (Ly).Λ lbl0 s c ∧ PlacedS (Ly).Λ (fun _ => none) s c []) (fun _ _ => False)
      (Ly).exe (Ly).endPc ((swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64) m ∧
        CallerCells (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0) (-8 - 0) (8 - L) 8 m)
      (mainS0R (Ly).lab (setupMC sw) PostS
        ⟨stacksA (Ly).lab + 0#64 + 16384#64 - 8#64, tpOf (pinA (Ly).lab + 0#64 + 8#64), c0⟩
        (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec)
      (marshal (setupMC sw).sw (setupMC sw).fn))
    (hPlX : ∀ fs, XExitW (fun s c => Placed (Ly).Λ lbl0 s c ∧ PlacedS (Ly).Λ (fun _ => none) s c fs) (fun _ _ => False)
      (Ly).exe (Ly).endPc ((swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64) m ∧
        CallerCells (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0) (-8 - 0) (8 - L) 8 m)
      (mainSRR (Ly).lab (setupMC sw) (fun c v => Post c fs v)) (-8 - (setupMC sw).Z.toInt) (-8) (setupMC sw).k 4 4 5)
    (hL1 : 8 + 8 + (setupMC sw).Z.toInt + 8 + D1 ≤ L) (hL2 : 8 + 8 + (setupMC sw).Z.toInt + 8 + D2 ≤ L)
    (hZM : (Ly).stacksA.toNat + 4096 ≤
      (stacksA (Ly).lab + 0#64 + 16384#64 - 8#64 - 8#64 - (setupMC sw).Z.toBitVec).toNat)
    (hZS : (Ly).stacksA.toNat + 4096 ≤ (stacksA (Ly).lab + 0#64 + 16384#64 - 8#64 - 8#64 - (setupMC sw).Z.toBitVec -
      8#64 - 8#64 - ZU1.toBitVec).toNat)
    (hZU : (Ly).stacksA.toNat + 4096 ≤ (stacksA (Ly).lab + 0#64 + 16384#64 - 8#64 - 8#64 - (setupMC sw).Z.toBitVec -
      8#64 - 8#64 - ZU2.toBitVec).toNat)
    (hS : ∀ v, SetupCallWS (W2At h i p rd (rS0 (Ly)) J Dt ls0) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSAt h i p rd J ab ls0) (Ly).exe (Ly).endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (setupMC sw).setup (setupMC sw).Z D1 ZU1 PostR ((Ly).lab (setupMC sw).sp0).toBitVec c0
      (tpOf (pinA (Ly).lab + 0#64 + 8#64)))
    (hcall : ∃ cE fr, Spike.Lib.X64.Flow.CallTo p c0 cE fr)
    (hPS : ∀ cE fr c rs, Spike.Lib.X64.Flow.CallTo p c0 cE fr → PostR c rs →
      ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hD8 : 8 ≤ D1) {chk entry : Label} {Zs lim : Int64} {Lg : Label} {zl zf z1 z2 zs : Nat}
    {ps : List (Reg64 × Int64 × Nat)}
    (hproS : Spike.Lib.X64.Flow.prologueIn (Ly).prog (setupMC sw).setup chk entry Zs lim Lg zl zf z1 z2 zs ps = true)
    (hphS : blkPh (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (fun _ => false) (Ly).lab
      ((Ly).lab (setupMC sw).setup + Int64.ofNat 0) 0 Spike.Lib.X64.Flow.xHead = true)
    (hlS : (setupMC sw).setup ∉ Spike.Lib.X64.AllocG.abLabs) (hlcS : chk ∉ Spike.Lib.X64.AllocG.abLabs)
    (hU : ∀ v, MainCallWSF (W2At h i p rd (rS0 (Ly)) J Dt ls0) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSAt h i p rd J ab ls0) (Ly).exe (Ly).endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (setupMC sw).fn (setupMC sw).Z D2 ZU2
      (SetupArgs PostS (setupMC sw).sw (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec) Post
      ((Ly).lab (setupMC sw).sp1).toBitVec (tpOf (pinA (Ly).lab + 0#64 + 8#64))) :
    SegWS (W2At h i p rd (rS0 (Ly)) J Dt ls0) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p (fun _ => none)
      (MSAt h i p rd J ab ls0)
      ((Spike.Lib.X64.At (Ly).exe (Ly).endPc (entryR E) FE (Spike.Lib.X64.Rt.entryN0 (Ly).lab c0)).at [])
      fun _ _ _ => False := by
  have hZ := setupMC_Z sw hsw
  have hk := setupMC_k sw hsw
  have hin := Spike.Lib.X64.Rt.mainSIn_of_okS hc
  have hsub := Spike.Lib.X64.Rt.rS0_sub (Ly)
  have hL0 : (0 : Int) ≤ L := by omega
  have hW := mainSW_ofPlaceOKR h i (rd := rd) (J := J) (Dt := Dt) (ls0 := ls0) (ab := ab) hp hL hLm hL8 hsw hc hph
    hgrow hset hfn (by omega) hC0 (fun c rs h => (hPostS c rs h).1) (fun c v h => (hPost c [] v h).1)
    ⟨hf0, hov, hpl0⟩ (fun c rs h => (hPostS c rs h).2) (fun c v h => (hPost c [] v h).2) hPlS (hPlX [])
  have hWx := hWx_ofPlaceOKR h i (rd := rd) (J := J) (Dt := Dt) (ls0 := ls0) hp hL hLm hL8 hsw hc hph
    hgrow hset hfn (by omega) hC0 (fun c fs v h => (hPost c fs v h).1) (fun c fs v h => (hPost c fs v h).2) hPlX
  have hpl : ∀ s c, Placed (Ly).Λ (fun _ => none) s c → (MSAt h i p rd J ab ls0 []).pl s c := by
    intro s c hP; cases ab <;> exact ⟨rfl, hP⟩
  obtain ⟨hhdr, htcb, hfld, htk⟩ := rows_ofPlaceOK h i (p := p) (rd := rd) (ar := arOf (Ly).Λ)
    (J := IN (arOf (Ly).Λ) (fun _ => none) ls0 J) (ab := ab) (lsize := ls0) hFE
  have h8 : (stacksA (Ly).lab + 0#64 + 16384#64).toNat % 8 = 0 := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
  have hok : (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).OK := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ hL0 hLm
  exact Spike.Lib.X64.Rt.startS_segWSF (Ly).lays rfl (Spike.Lib.X64.Rt.rtCodeTi_of_placeOKAt h) msOfAX_K_abi hFEs
    (Spike.Lib.X64.Rt.entryR_ok hE) (Spike.Lib.X64.Rt.entryR_al hE) (by show (-65536 : Int) ≤ -304; decide)
    (by show (0 : Int) ≤ 0; decide) 0#64 0#64 c0 (by decide) hhdr htcb (by decide) hfld htk hok
    (by rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rS0_subRD _ hL0 hLm)
    (by rw [Spike.Lib.X64.Rt.pinA_lab0]; exact Spike.Lib.X64.Rt.rt_hfit _)
    (by rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_houtD _ hL0 hLm)
    (hun_ofPlaceOK h i hFE) (Spike.Lib.X64.Rt.rS_of_sub _ hE hsub) (Spike.Lib.X64.Rt.fitS_of_sub _ hsub)
    (Spike.Lib.X64.Rt.outS_of_sub _ hE hsub) hFEk
    (startEW_w2G h i (lbl0 := lbl0) (J := IN (arOf (Ly).Λ) (fun _ => none) ls0 J) (Dt := Dt) (lsize := ls0)
      hp hf0 hov hC0 (Spike.Lib.X64.Rt.entryR_ok hE) (by show (-65536 : Int) ≤ -304; decide)
      (by show (0 : Int) ≤ 0; decide) hFE (by rw [Spike.Lib.X64.Rt.stacksA_lab0]) hsub
      (Spike.Lib.X64.Rt.outS_of_sub _ hE hsub) h8 hok hL hL8 (by decide) hpl0)
    hin (by rw [hZ]; omega) (show sw ≤ 5 by omega) (by show 8 * (sw : Int) + 8 ≤ _; rw [hZ]; omega)
    (by simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ, hk]; refine ⟨?_, ?_, ?_⟩ <;> omega)
    hD10 hD18 hD20 hD28 hL1 hL2 hL8 (limOk_ofPlaceOK h i hZM) (limOk_ofPlaceOK h i hZS) (limOk_ofPlaceOK h i hZU)
    hS hcall hPS (hWC_ofPlaceOK h i hp hL hLm hL8 hsw hD8 hL1 hproS hphS hlS hlcS hC0 ⟨hf0, hov, hpl0⟩) hU
    (fun R' F' s c fs v hP hAt => uPostRF_exit (Λ := (Ly).Λ) hpl R' F' s c fs v (hPU c fs v hP) hAt) hW hWx

end Place

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.mainSW_sfactsR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainSW_sfactsR

/-- info: 'Spike.Lib.LowerX64.rtM_w2R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rtM_w2R

/-- info: 'Spike.Lib.LowerX64.mainSW_ofPlaceOKR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainSW_ofPlaceOKR

/-- info: 'Spike.Lib.LowerX64.hWx_ofPlaceOKR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hWx_ofPlaceOKR

/-- info: 'Spike.Lib.LowerX64.h0_ofPlaceOK_setupFR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h0_ofPlaceOK_setupFR

end Spike.Lib.LowerX64
