/-
**`h0` with the user function's post at a held pair** (x86-64; its A64
twin `Spike/Lib/LowerA64/RtMainXN.lean` is pending): at a pair whose control is a callee's
`ret` at pending frames (`fs ≠ []`), the post's control has neither
`CFacts` nor `CFactsC` (its `ret` breaks `noRet`), so `hWx_ofPlaceOK`'s
`hCP` and `hWx_ofPlaceOKR`'s `hPost` cannot hold. Here the exit tail's
states carry `SFacts` at the entry's control `c0` (at every state, the
node's control starred away) and `W2` asks of the post's control only
`MainCtlN`: its frames' run, `main`'s `ret` excluded at no frame, its
placement.

- `BlkW.ofStar`, `NodeW.ofStar`: a block's (a node's) states inside
  `W · c★` from the node with its control replaced by `c★`;
- `exitW_sfactsAt`: the exit tail inside `SFacts` at a control `c★` of
  `CFacts`, for any post;
- `MainCtlN`, `rtM_w2N`: `W2` from `SFacts` at another control `c'` not at
  an overflow, `RtM` and `MainCtlN` at the frames;
- `hWx_ofPlaceOKN`: `hWx_ofPlaceOK` at `MainCtlN` of the post's controls,
  `SFacts` at `c0` (`hC0`, `hov`);
- `h0_ofPlaceOK_setupFN`: `h0_ofPlaceOK_setupFR` with the post's
  controls' `MainCtlN` (`hPost`) and no exit tail's placement (`hPlX`).
-/
import Spike.Lib.LowerX64.RtMainXR

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS
open Spike.Lib.X64 (NodeW BlkW ND At)
open Spike.Lib.X64.Flow (ofNat_zero' ofNat_add' xExit xExit_ok prologueIn exitIn XExitW)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.X64.Rt (InstOk setupMC MainSW mainSIn marshal blkW_postO nodeW_syscall_postO mainSRR)
open Spike.Lib.X64.Rt.MainU (xExit_noRet)

section Star

variable {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop}

/-- **A block's states inside `W` at a fixed control `cs`** from the block
at the node with its control replaced by `cs` (any control of the node's
invariant witnessing the state). -/
theorem BlkW.ofStar {cs : Ctl} {n : ND} {blk : List (Directive × Nat)}
    (h : BlkW W K exe endPc R F ⟨n.pc, n.o, fun σ c => c = cs ∧ ∃ c', n.J σ c'⟩ blk) :
    BlkW (fun s _ => W s cs) K exe endPc R F n blk :=
  fun s σ c he hn hdc hpc hA hF hJ k hk m hA' hD => h s σ cs he hn hdc hpc hA hF ⟨rfl, c, hJ⟩ k hk m hA' hD

/-- **A node's states inside `W` at a fixed control `cs`** from the node
with its control replaced by `cs`. -/
theorem NodeW.ofStar {cs : Ctl} {n : ND} (h : NodeW W K exe endPc R F ⟨n.pc, n.o, fun σ c => c = cs ∧ ∃ c', n.J σ c'⟩) :
    NodeW (fun s _ => W s cs) K exe endPc R F n := fun s c ⟨he, hn, hdc, hpc, σ, hA, hF, hJ⟩ =>
  h s cs ⟨he, hn, hdc, hpc, σ, hA, hF, rfl, c, hJ⟩

end Star

section Exit

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {lbl : Lbl}

/-- **`scc_rt_main`'s exit tail inside `SFacts` at a fixed control** `cs`
of `CFacts` (`hC`), for any post: `mainSW_sfacts`' exit part at the
starred nodes (`blkW_postO`, `nodeW_syscall_postO`), under its code
(`hin`), phase facts (`hph`) and region facts. -/
theorem exitW_sfactsAt (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    {sw : Nat} (hsw : sw < 6) (hin : mainSIn cells (setupMC sw) = true)
    {Post : Ctl → BitVec 64 → Prop} {cs : Ctl} (hC : CFacts Λ lbl cs) (hph : MainPhS okPc ph lab (setupMC sw))
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hR8 : R.base.toNat % 8 = 0)
    (hlo : R.lo ≤ -8 - (setupMC sw).Z.toInt) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) :
    XExitW (fun s _ => SFacts Λ μ own rS Tk lbl s cs) K exe endPc R F
      (mainSRR (_root_.Executable.labels exe).label (setupMC sw) Post) (-8 - (setupMC sw).Z.toInt) (-8)
      (setupMC sw).k 4 4 5 := by
  have hZ := setupMC_Z sw hsw
  have hk := setupMC_k sw hsw
  have h := hin
  simp only [mainSIn, prologueIn, exitIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, bEx, bSvc⟩ := h
  rw [hI.labOk]
  refine ⟨BlkW.ofStar (W := fun s c => SFacts Λ μ own rS Tk lbl s c) ?_,
    NodeW.ofStar (W := fun s c => SFacts Λ μ own rS Tk lbl s c) ?_⟩
  · -- the tail's block
    exact blkW_postO hI bEx (ofNat_zero' _)
      (xExit_ok (lo := -8 - (setupMC sw).Z.toInt) (hi := 0) _ _ _ _ (by
        simp only [Spike.Lib.offOk, decide_eq_true_eq, hk, hZ]
        refine ⟨?_, ?_, ?_⟩ <;> omega))
      hR hlo hhi hR8 hl hh (fun _ _ hJ => hJ.1 ▸ hC) hph.ex
      (fun _ _ _ k hk hr => (noRet_false (xExit_noRet _ _ _ _) k hk hr).elim) (fun _ _ _ => rfl)
      hsub hfit hFO
  · -- the `exit_group`
    exact nodeW_syscall_postO (p := lab (setupMC sw).sp1 + Int64.ofNat 13) hI bSvc rfl
      (by
        show lab (setupMC sw).sp1 + Int64.ofNat 4 + Int64.ofNat 4 + Int64.ofNat 5 = _
        rw [← ofNat_add', ← ofNat_add'])
      (fun _ _ hJ => hJ.1 ▸ hC) hph.svc.1 hph.svc.2 hR hR8 hl hh hsub hFO
      (fun _ _ ⟨_, _, h, _⟩ => by rw [h]; decide)

end Exit

section RtN

open A9NoSpawn Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1 Spike.Lib.X64ConsumerA
open Spike.Lib.X64.WriteAb (Ab)
open Spike.Lib.LowerNode (FrOk2 ZBad)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {ar : Arena} {lbl : Lbl} {lab : Label → Int64}

/-- **A source control's facts `W2` asks at the frames `fs` beyond
`SFacts` at another control**: its frames' run free of `ZBad`, `main`'s
`ret` excluded at no frame, placed at `fs` under the labels' placement
`L0` at every state. -/
def MainCtlN (Λ : Scc.Sem.Layout) (L0 : Lbl) (c : Ctl) (fs : List TermRun.Frame) : Prop :=
  FrOk2 c fs ∧ (fs = [] → ∀ a, c.term ≠ .ret a) ∧ ∀ s, PlacedS Λ L0 s c fs

/-- **`W2` at a runtime state at the frames `fs`, `SFacts` at another
control** (`rtM_w2F` with the state's facts at `c'`): `SFacts` at `c'` not
at an overflow (`hov`), `RtM`, and the control's `MainCtlN` at `fs`. -/
theorem rtM_w2N {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : Own} {rS : Range}
    {Tk : State → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl} {lsize : Lsize} (hp : ProgNoS ZBad p)
    {s : State} {c c' : Ctl} {fs : List TermRun.Frame} (hS : SFacts Λ μ own rS Tk lbl0 s c')
    (hov : ¬ OvfReady c') (hM : RtM μ ar lab s c) (hQ : MainCtlN Λ lbl c fs) :
    W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c fs := by
  have hP := w2Part_of_wrOff (J := J) (rd := rd) (G := G) (p := p) (lsize := lsize) hM.1 (hQ.2.2 s) hM.2 hS
  exact w2_of hp hQ.1 (hS.toSt.dt_mono fun _ h => h.elim) hP.1 hQ.2.1 (.of_placedS hP.2.1) hP.2.2.1
    (abortOkA_of_ne (noAbort_of_sfacts hov hS)) hP.2.2.2

end RtN

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
open Spike.Lib.X64.Rt (swFSL rS0 setupMC rtCodeOkS mainSRR) in
/-- **The exit tail's states inside `W2At` at every frames, the post at a
held pair** (`hWx_ofPlaceOK` over `exitW_sfactsAt`, `rtM_w2N`): `SFacts`
at the entry's control (`hC0`, not at an overflow `hov`) at every exit
state, the post's controls' `MainCtlN` at the frames (`hQP`). -/
theorem hWx_ofPlaceOKN {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {c0 : Ctl} {L : Int} (hp : ProgNoS ZBad p)
    (hL : 8 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0)
    {sw : Nat} (hsw : sw < 6) (hc : rtCodeOkS (Ly).prog (setupMC sw) = true)
    (hph : MainPhS (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (Ly).lab (setupMC sw))
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).grow))
    (hset : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).setup))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).fn))
    (hLZ : 8 + 8 + (setupMC sw).Z.toInt + 8 ≤ L) {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hC0 : CFacts (Ly).Λ lbl0 c0) (hov : ¬ OvfReady c0)
    (hQP : ∀ c fs v, Post c fs v → MainCtlN (Ly).Λ (fun _ => none) c fs) :
    ∀ v fs, XExitW (fun s c => W2At h i p rd (rS0 (Ly)) J Dt ls0 s c fs)
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
      (x0 := (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec) (ms := MSAt h i p rd J none ls0 [])
      (F := fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64) m ∧
        CallerCells (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0) (-8 - 0) (8 - L) 8 m) hI
      (Scc.Cert.PlaceOK.X64.printIn_of_placeOKAt h) (Scc.Cert.PlaceOK.X64.abortIn_of_placeOKAt h)
      hsw hin hph hgrow hset hfn hR' (by show 8 - L ≤ _; omega) (by show (0 : Int) ≤ 8; decide)).exit
    have hw : ∀ s c, SFacts (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly))
        (Spike.Lib.X64.PhRec.Tk (Ly)) lbl0 s c0 →
        (RtM (Spike.Lib.X64.PhRec.μ (Ly)) (arOf (Ly).Λ) (Ly).lab s c ∧ MainCtlN (Ly).Λ (fun _ => none) c fs) →
        W2At h i p rd (rS0 (Ly)) J Dt ls0 s c fs :=
      fun _ _ h1 h2 => rtM_w2N hp h1 hov h2.1 h2.2
    exact ⟨BlkW.imp H1.w0 (BlkW.ofCtl H2.w0 fun _ _ hJ => hQP _ _ _ hJ.1) hw,
      NodeW.imp H1.w1 (NodeW.ofCtl H2.w1 fun _ _ ⟨_, _, hJ, _⟩ => hQP _ _ _ hJ.1) hw⟩
  · exact ⟨Spike.Lib.X64.Rt.blkW_ofFalse fun m hm => hv hm.1.1.1,
      Spike.Lib.X64.Rt.nodeW_ofFalse fun m hm => hv hm.1.1.1⟩

open Spike.Lib.X64.Flow.Ret0 in
open Spike.Lib.X64.Rt (SetupCode SetupCallWS MainCallWSF MainSW SetupArgs swFSL mainSIn oU rS0 entryR rtF setupMC
  rtCodeOkS mainS0R mainSRR CFactsC) in
open Spike.Lib.AllocReach (IN) in
/-- **The consumer's `h0` at a placed output, an entry state and a setup
block, `main` returning at pending frames, the post at a held pair**
(`h0_ofPlaceOK_setupFR` over `hWx_ofPlaceOKN`): back from the setup block
the controls' `CFactsC ∧ MainCtlC` (`hPostS`), their placement at the
marshalling block's states (`hPlS`); back from the user function only
`MainCtlN` at the frames (`hPost`), the exit tail's states carrying
`SFacts` at the entry's control, so no exit tail's placement. -/
theorem h0_ofPlaceOK_setupFN {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
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
    (hPost : ∀ c fs v, Post c fs v → MainCtlN (Ly).Λ (fun _ => none) c fs)
    (hPlS : BlkW (fun s c => Placed (Ly).Λ lbl0 s c ∧ PlacedS (Ly).Λ (fun _ => none) s c []) (fun _ _ => False)
      (Ly).exe (Ly).endPc ((swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64) m ∧
        CallerCells (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0) (-8 - 0) (8 - L) 8 m)
      (mainS0R (Ly).lab (setupMC sw) PostS
        ⟨stacksA (Ly).lab + 0#64 + 16384#64 - 8#64, tpOf (pinA (Ly).lab + 0#64 + 8#64), c0⟩
        (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec)
      (marshal (setupMC sw).sw (setupMC sw).fn))
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
  have hW0 := mainSW_ofPlaceOKR h i (rd := rd) (J := J) (Dt := Dt) (ls0 := ls0) (ab := ab)
    (Post := fun _ _ => False) hp hL hLm hL8 hsw hc hph hgrow hset hfn (by omega) hC0
    (fun c rs h => (hPostS c rs h).1) (fun _ _ h => h.elim) ⟨hf0, hov, hpl0⟩ (fun c rs h => (hPostS c rs h).2)
    (fun _ _ h => h.elim) hPlS
    ⟨Spike.Lib.X64.Rt.BlkW.ofSt fun _ _ hJ => hJ.1.elim, Spike.Lib.X64.Rt.NodeW.ofSt fun _ _ ⟨_, _, hJ, _⟩ => hJ.1.elim⟩
  have hWx := hWx_ofPlaceOKN h i (rd := rd) (J := J) (Dt := Dt) (ls0 := ls0) hp hL hLm hL8 hsw hc hph
    hgrow hset hfn (by omega) hC0 hov hPost
  have hW : ∀ v, MainSW (Spike.Lib.X64.Rt.nilW (W2At h i p rd (rS0 (Ly)) J Dt ls0))
      (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) (Ly).exe (Ly).endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m) (MSAt h i p rd J ab ls0 [])
      (setupMC sw) PostS (fun c v => Post c [] v)
      ⟨stacksA (Ly).lab + 0#64 + 16384#64 - 8#64, tpOf (pinA (Ly).lab + 0#64 + 8#64), c0⟩
      (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec := fun v =>
    ⟨(hW0 v).pro, (hW0 v).call0, (hW0 v).sp0, hWx v []⟩
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

/-- info: 'Spike.Lib.LowerX64.BlkW.ofStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BlkW.ofStar

/-- info: 'Spike.Lib.LowerX64.NodeW.ofStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NodeW.ofStar

/-- info: 'Spike.Lib.LowerX64.exitW_sfactsAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exitW_sfactsAt

/-- info: 'Spike.Lib.LowerX64.rtM_w2N' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rtM_w2N

/-- info: 'Spike.Lib.LowerX64.hWx_ofPlaceOKN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hWx_ofPlaceOKN

/-- info: 'Spike.Lib.LowerX64.h0_ofPlaceOK_setupFN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h0_ofPlaceOK_setupFN

end Spike.Lib.LowerX64
