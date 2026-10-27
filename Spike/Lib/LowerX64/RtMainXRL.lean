/-
**`scc_rt_main`'s own states inside `W2` at any current placement**
(x86-64; the twin of `Spike/Lib/LowerA64/RtMainXRL.lean`): `W2At` / `MSAt`
(`Spike/Lib/LowerX64/Start2W2.lean`) fix the current placement at the
start's, no label placed (`fun _ => none`, `ls0`); a landing's segment
(`H1In`) resumes `scc_rt_main` at a placement `L0`, `ls` some allocations
past it. Here the current placement is a parameter; the family `IN … J`
stays rooted at the start's.

- `W2AtL`, `MSAtL`: `W2At`, `MSAt` at the current placement `L0`, `ls`;
  `w2AtL_none`, `msAtL_none`: at the start's they are `W2At`, `MSAt` (`rfl`);
- `mainSW_ofPlaceOKRL`, `hWx_ofPlaceOKRL`: `mainSW_ofPlaceOKR`,
  `hWx_ofPlaceOKR` (`Spike/Lib/LowerX64/RtMainXR.lean`) at `L0`, `ls`
  (the controls' `MainCtl` and placement `PlacedS` at `L0`).
-/
import Spike.Lib.LowerX64.RtMainXR

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
open Spike.Lib.X64.WriteAb (Ab)

open Spike.Lib.X64.Flow.Ret0 (stacksA)
open Spike.Lib.X64.Rt (arOf)
open Spike.Lib.X64.AllocG (BlkW.imp NodeW.imp)

set_option hygiene false in
/-- The canonical load's memory of the output. -/
local notation "M0" => Spike.Lib.X64.PhRec.m0Of (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h i).Λ o.prog o.secs

open Spike.Lib.AllocReach (IN) in
open Spike.Lib.X64.PhRec (GOf) in
/-- **`W2` at a current placement `L0`, `ls`** over `IN … J` rooted at the
start's placement (no label placed, `ls0`): `W2At` with the current
placement a parameter. -/
abbrev W2AtL (p : Prog) (rd : TermRun.Word → Prop) (rS : Range) (J : InvS) (Dt : State → Prop) (ls0 : Lsize)
    (L0 : Lbl) (ls : Lsize) : FragS isa := fun s c fs =>
  W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p rd (GOf Ly M0) (Spike.Lib.X64.PhRec.own (Ly)) rS
    (Spike.Lib.X64.PhRec.Tk (Ly)) (arOf (Ly).Λ) (IN (arOf (Ly).Λ) (fun _ => none) ls0 J) Dt (Ab (Ly).lab)
    L0 ls s c fs

open Spike.Lib.AllocReach (IN) in
open Spike.Lib.X64.PhRec (GOf) in
/-- **The rows' memory side at a current placement `L0`, `ls`** (`msOfAX`
as in `W2AtL`, abort `ab`): `MSAt` with the current placement a
parameter. -/
abbrev MSAtL (p : Prog) (rd : TermRun.Word → Prop) (J : InvS) (ab : Option (State → Prop)) (ls0 : Lsize)
    (L0 : Lbl) (ls : Lsize) : List TermRun.Frame → MemSide isa :=
  msOfAX (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p rd (GOf Ly M0) (fun s _ => Spike.Lib.X64.PhRec.own (Ly) s)
    (arOf (Ly).Λ) (IN (arOf (Ly).Λ) (fun _ => none) ls0 J) ab L0 ls

/-- `W2AtL` at the start's placement is `W2At`. -/
theorem w2AtL_none {p : Prog} {rd : TermRun.Word → Prop} {rS : Range} {J : InvS} {Dt : State → Prop}
    {ls0 : Lsize} : W2AtL h i p rd rS J Dt ls0 (fun _ => none) ls0 = W2At h i p rd rS J Dt ls0 := rfl

/-- `MSAtL` at the start's placement is `MSAt`. -/
theorem msAtL_none {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {ab : Option (State → Prop)}
    {ls0 : Lsize} : MSAtL h i p rd J ab ls0 (fun _ => none) ls0 = MSAt h i p rd J ab ls0 := rfl

open Spike.Lib.X64.Flow.Ret0 in
open Spike.Lib.X64.Rt (MainSW swFSL rS0 setupMC rtCodeOkS mainS0R mainSRR CFactsC) in
/-- **`scc_rt_main`'s own states inside `W2AtL` at any current placement
`L0`, `ls`, the controls back placed state by state** (`mainSW_ofPlaceOKR`
at `L0`, `ls`; `mainSW_ofPlaceOK` over `mainSW_sfactsR`,
`MainSW.ofPl`, `rtM_w2R`): back from the setup block and the user function
the controls' `CFactsC` (`hCS`, `hCP`) and `MainCtlC` (`hQS`, `hQP`), their
placement at both placements at the marshalling block's and the exit
tail's states at the switch region's top (`hPlS`, `hPlX`). -/
theorem mainSW_ofPlaceOKRL {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {L0 : Lbl} {ls : Lsize} {ab : Option (State → Prop)} {c0 : Ctl} {L : Int} (hp : ProgNoS ZBad p)
    (hL : 8 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0)
    {sw : Nat} (hsw : sw < 6) (hc : rtCodeOkS (Ly).prog (setupMC sw) = true)
    (hph : MainPhS (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (Ly).lab (setupMC sw))
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).grow))
    (hset : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).setup))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).fn))
    (hLZ : 8 + 8 + (setupMC sw).Z.toInt + 8 ≤ L)
    {PostS : Ctl → Reg64s → Prop} {Post : Ctl → BitVec 64 → Prop}
    (hC0 : CFacts (Ly).Λ lbl0 c0) (hCS : ∀ c rs, PostS c rs → CFactsC c) (hCP : ∀ c v, Post c v → CFactsC c)
    (hQ0 : MainCtl (Ly).Λ L0 c0) (hQS : ∀ c rs, PostS c rs → MainCtlC c [])
    (hQP : ∀ c v, Post c v → MainCtlC c [])
    (hPlS : BlkW (fun s c => Placed (Ly).Λ lbl0 s c ∧ PlacedS (Ly).Λ L0 s c []) (fun _ _ => False)
      (Ly).exe (Ly).endPc ((swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64) m ∧
        CallerCells (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0) (-8 - 0) (8 - L) 8 m)
      (mainS0R (Ly).lab (setupMC sw) PostS
        ⟨stacksA (Ly).lab + 0#64 + 16384#64 - 8#64, tpOf (pinA (Ly).lab + 0#64 + 8#64), c0⟩
        (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec)
      (marshal (setupMC sw).sw (setupMC sw).fn))
    (hPlX : XExitW (fun s c => Placed (Ly).Λ lbl0 s c ∧ PlacedS (Ly).Λ L0 s c []) (fun _ _ => False)
      (Ly).exe (Ly).endPc ((swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64) m ∧
        CallerCells (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0) (-8 - 0) (8 - L) 8 m)
      (mainSRR (Ly).lab (setupMC sw) Post) (-8 - (setupMC sw).Z.toInt) (-8) (setupMC sw).k 4 4 5) :
    ∀ v, MainSW (Spike.Lib.X64.Rt.nilW (W2AtL h i p rd (rS0 (Ly)) J Dt ls0 L0 ls))
      (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) (Ly).exe (Ly).endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m) (MSAtL h i p rd J ab ls0 L0 ls [])
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
    have hS1 := mainSW_sfactsR (ms := MSAtL h i p rd J ab ls0 L0 ls []) (lbl := lbl0) hI hsw hin (Post := Post)
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
      (P := fun s c => MainCtlC c [] ∧ PlacedS (Ly).Λ L0 s c []) (ms := MSAtL h i p rd J ab ls0 L0 ls [])
      (sc := setupMC sw) (PostS := PostS) (Post := Post)
      (g := ⟨stacksA (Ly).lab + 0#64 + 16384#64 - 8#64, tpOf (pinA (Ly).lab + 0#64 + 8#64), c0⟩)
      (x0 := (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec)
      (fun s => ⟨⟨hQ0.1, hQ0.2.1⟩, hQ0.2.2 s⟩)
      (BlkW.imp (Spike.Lib.X64.Rt.BlkW.ofSt fun _ _ hJ _ => hQS _ _ hJ.1.1) hPlS
        fun _ _ (h1 : MainCtlC _ []) (h2 : _ ∧ PlacedS (Ly).Λ L0 _ _ []) => ⟨h1, h2.2⟩)
      ⟨BlkW.imp (Spike.Lib.X64.Rt.BlkW.ofSt fun _ _ hJ _ => hQP _ _ hJ.1) hPlX.w0
        fun _ _ (h1 : MainCtlC _ []) (h2 : _ ∧ PlacedS (Ly).Λ L0 _ _ []) => ⟨h1, h2.2⟩,
        NodeW.imp (Spike.Lib.X64.Rt.NodeW.ofSt fun _ _ ⟨_, _, hJ, _⟩ _ => hQP _ _ hJ.1) hPlX.w1
          fun _ _ (h1 : MainCtlC _ []) (h2 : _ ∧ PlacedS (Ly).Λ L0 _ _ []) => ⟨h1, h2.2⟩⟩
    exact MainSW.imp hS1
      (MainSW.imp (W := fun s c => RtM (Spike.Lib.X64.PhRec.μ (Ly)) (arOf (Ly).Λ) (Ly).lab s c ∧
          (MainCtlC c [] ∧ PlacedS (Ly).Λ L0 s c []))
        (mainSW_rtM hI (Scc.Cert.PlaceOK.X64.printIn_of_placeOKAt h)
        (Scc.Cert.PlaceOK.X64.abortIn_of_placeOKAt h)
        hsw hin hph hgrow hset hfn hR' (by show 8 - L ≤ _; omega) (by show (0 : Int) ≤ 8; decide)) hS2
        fun _ _ h1 h2 => ⟨h1, h2⟩)
      fun s c h1 h2 => rtM_w2R hp h1 h2.1 h2.2.1 h2.2.2
  · exact MainSW.ofFalse fun m hm => hv hm.1.1.1

open Spike.Lib.X64.Flow.Ret0 in
open Spike.Lib.X64.Flow (XExitW) in
open Spike.Lib.X64.Rt (swFSL rS0 setupMC rtCodeOkS mainSRR CFactsC) in
/-- **The exit tail's states inside `W2AtL` at any current placement `L0`,
`ls`, at every frames, the post's controls placed state by state**
(`hWx_ofPlaceOKR` at `L0`, `ls`; `hWx_ofPlaceOK` over `mainSW_sfactsR`,
`rtM_w2R`): the post's controls' `CFactsC` (`hCP`) and `MainCtlC` at the
frames (`hQP`), their placement at both placements at the exit tail's
states at the switch region's top at every frames (`hPlX`). -/
theorem hWx_ofPlaceOKRL {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {L0 : Lbl} {ls : Lsize} {c0 : Ctl} {L : Int} (hp : ProgNoS ZBad p)
    (hL : 8 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0)
    {sw : Nat} (hsw : sw < 6) (hc : rtCodeOkS (Ly).prog (setupMC sw) = true)
    (hph : MainPhS (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (Ly).lab (setupMC sw))
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).grow))
    (hset : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).setup))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).fn))
    (hLZ : 8 + 8 + (setupMC sw).Z.toInt + 8 ≤ L) {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hC0 : CFacts (Ly).Λ lbl0 c0) (hCP : ∀ c fs v, Post c fs v → CFactsC c)
    (hQP : ∀ c fs v, Post c fs v → MainCtlC c fs)
    (hPlX : ∀ fs, XExitW (fun s c => Placed (Ly).Λ lbl0 s c ∧ PlacedS (Ly).Λ L0 s c fs) (fun _ _ => False)
      (Ly).exe (Ly).endPc ((swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64) m ∧
        CallerCells (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0) (-8 - 0) (8 - L) 8 m)
      (mainSRR (Ly).lab (setupMC sw) (fun c v => Post c fs v)) (-8 - (setupMC sw).Z.toInt) (-8) (setupMC sw).k 4 4 5) :
    ∀ v fs, XExitW (fun s c => W2AtL h i p rd (rS0 (Ly)) J Dt ls0 L0 ls s c fs)
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
    have H1 := (mainSW_sfactsR (ms := MSAtL h i p rd J none ls0 L0 ls []) (lbl := lbl0) hI hsw hin
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
      (x0 := (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec) (ms := MSAtL h i p rd J none ls0 L0 ls [])
      (F := fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64) m ∧
        CallerCells (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0) (-8 - 0) (8 - L) 8 m) hI
      (Scc.Cert.PlaceOK.X64.printIn_of_placeOKAt h) (Scc.Cert.PlaceOK.X64.abortIn_of_placeOKAt h)
      hsw hin hph hgrow hset hfn hR' (by show 8 - L ≤ _; omega) (by show (0 : Int) ≤ 8; decide)).exit
    have hw : ∀ s c, SFacts (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly))
        (Spike.Lib.X64.PhRec.Tk (Ly)) lbl0 s c →
        (RtM (Spike.Lib.X64.PhRec.μ (Ly)) (arOf (Ly).Λ) (Ly).lab s c ∧
          (MainCtlC c fs ∧ PlacedS (Ly).Λ L0 s c fs)) →
        W2AtL h i p rd (rS0 (Ly)) J Dt ls0 L0 ls s c fs :=
      fun _ _ h1 h2 => rtM_w2R hp h1 h2.1 h2.2.1 h2.2.2
    exact ⟨BlkW.imp H1.w0 (BlkW.imp H2.w0 (BlkW.imp (Spike.Lib.X64.Rt.BlkW.ofSt fun _ _ hJ _ => hQP _ _ _ hJ.1)
        (hPlX fs).w0 fun _ _ a b => ⟨a, b.2⟩) fun _ _ a b => ⟨a, b⟩) hw,
      NodeW.imp H1.w1 (NodeW.imp H2.w1 (NodeW.imp
        (Spike.Lib.X64.Rt.NodeW.ofSt fun _ _ ⟨_, _, hJ, _⟩ _ => hQP _ _ _ hJ.1)
        (hPlX fs).w1 fun _ _ a b => ⟨a, b.2⟩) fun _ _ a b => ⟨a, b⟩) hw⟩
  · exact ⟨Spike.Lib.X64.Rt.blkW_ofFalse fun m hm => hv hm.1.1.1,
      Spike.Lib.X64.Rt.nodeW_ofFalse fun m hm => hv hm.1.1.1⟩

end Place

/-- info: 'Spike.Lib.LowerX64.w2AtL_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms w2AtL_none

/-- info: 'Spike.Lib.LowerX64.mainSW_ofPlaceOKRL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainSW_ofPlaceOKRL

/-- info: 'Spike.Lib.LowerX64.hWx_ofPlaceOKRL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hWx_ofPlaceOKRL

end Spike.Lib.LowerX64
