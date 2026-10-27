/-
**The `exit_group` tail inside `W2` at held frames** (AArch64): under
option A, `main` returns at the held pair `(c, fs)`, `c` the callee's
`ret`, `fs ≠ []`. `hWx_ofPlaceOK(R)` (`Spike/Lib/LowerA64/RtMainXF.lean`,
`Spike/Lib/LowerA64/RtMainXR.lean`) ask `CFacts`/`CFactsC` at the post's
controls, whose `noRet` fails at `ret`. `W2` asks it only at `fs = []`, and
`SFacts` enters `W2` only through its state facts (`w2Part_of_wrOff`,
`noAbort_of_sfacts` take it at any control). So the tail's states take
`SFacts` at the start control `c0` (`CFacts c0` placed everywhere), and the
post's controls only what `W2` asks of them (`MainCtlN`).

- `BlkW.ofStar`, `NodeW.ofStar`: a block's or node's states inside
  a predicate at one fixed control, from the node with its controls
  replaced by that one;
- `exitW_sfactsAt`: the tail's states carry `SFacts` at a fixed control
  `cs` with `CFacts cs`, for any post;
- `MainCtlN`: a post control's facts `W2` asks at `fs` (`FrOk2`, no `ret`
  at `fs = []`, placed at `fs` at every state); `rtM_w2N`: `W2` from
  `SFacts` at another control `c'` not at an overflow, `RtM` and
  `MainCtlN`;
- `hWx_ofPlaceOKN`, `h0_ofPlaceOK_setupFN`: `hWx_ofPlaceOK` and
  `h0_ofPlaceOK_setupFR` at the post's `MainCtlN` (no `CFacts`, no `hPlX`).
-/
import Spike.Lib.LowerA64.RtMainXR

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (StackOff MainG limA)
open Scc.Cert.Rt.A64 (blockAt)
open MainS MainU

/-! ## At one fixed control -/

section Star

variable {W : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **A block's states inside `W` at the fixed control `cs`**, from the
node with its controls replaced by `cs`. -/
theorem BlkW.ofStar {n : ND} {blk : List Directive} {cs : Ctl}
    (h : BlkW W K exe endPc R F ⟨n.pc, n.o, fun σ c => c = cs ∧ ∃ c', n.J σ c'⟩ blk) :
    BlkW (fun s _ => W s cs) K exe endPc R F n blk :=
  fun s σ c he hn hd hpc hA hF hJ k hk m hA' hD => h s σ cs he hn hd hpc hA hF ⟨rfl, c, hJ⟩ k hk m hA' hD

/-- **A node's states inside `W` at the fixed control `cs`**, from the
node with its controls replaced by `cs`. -/
theorem NodeW.ofStar {n : ND} {cs : Ctl}
    (h : NodeW W K exe endPc R F ⟨n.pc, n.o, fun σ c => c = cs ∧ ∃ c', n.J σ c'⟩) :
    NodeW (fun s _ => W s cs) K exe endPc R F n :=
  fun _ c ⟨he, hn, hd, hpc, σ, hA, hD, hJ⟩ => h _ cs ⟨he, hn, hd, hpc, σ, hA, hD, rfl, c, hJ⟩

end Star

section Exit

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}

/-- **The `exit_group` tail's states carry `SFacts` at a fixed control
`cs`** (`CFacts cs`, `hC`), for any post `Post`: `mainSW_sfacts`' exit part
at the nodes with their controls replaced by `cs`, its facts as there. -/
theorem exitW_sfactsAt {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    {sc : SetupCode} (hin : mainSIn prog sc = true) {Post : Ctl → BitVec 64 → Prop} {cs : Ctl}
    (hC : CFacts Λ lbl cs) (hph : MainPhS okPc ph lab sc)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -sc.Z.toInt) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (h16 : sc.Z.toInt % 16 = 0) (hk : Spike.Lib.offOk (-sc.Z.toInt) 0 (-sc.Z.toInt + sc.k.toInt) = true)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) :
    ExitW (fun s _ => SFacts Λ μ own rS Tk lbl s cs) K exe endPc R F
      (mainSR (_root_.Executable.labels exe).label sc Post) sc.k := by
  have h := hin
  simp only [mainSIn, prologueIn, exitIn, Bool.and_eq_true] at h
  obtain ⟨-, bEx, bSvc⟩ := h
  have hR8 : R.base.toNat % 8 = 0 := by omega
  rw [hI.labOk]
  refine ⟨BlkW.ofStar (W := fun s c => SFacts Λ μ own rS Tk lbl s c) (cs := cs) ?_,
    NodeW.ofStar (W := fun s c => SFacts Λ μ own rS Tk lbl s c) (cs := cs) ?_⟩
  · exact blkW_postO hI bEx (ofNat4_zero _) (exitTail_ok (lo := -sc.Z.toInt) (hi := 0) hk
        (by show (-sc.Z.toInt) % 16 = 0; omega)) hR hal hlo hhi (fun _ _ h => h.1 ▸ hC)
      hph.ex (fun _ _ _ k hk r hr => (noRet_false (exitTail_noRet _) k hk r hr).elim) (fun _ _ _ => rfl) hl hh hsub
      hfit hFO
  · exact nodeW_svc_postO hI bSvc rfl (pc3 _).symm (fun _ _ h => h.1 ▸ hC) hph.svc.1
      hph.svc.2 hR hR8 hl hh hsub hFO (fun _ _ ⟨_, _, hx, _⟩ => by rw [hx]; decide)

end Exit

end Spike.Lib.A64.Rt

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

/-- **A post control's facts `W2` asks at the frames `fs`** beyond the
state's: its frame runs free of `ZBad`, not a `ret` at no frame (`W2`'s
`noRet`), placed at `fs` under the labels' placement `L0` at every state. -/
def MainCtlN (Λ : Scc.Sem.Layout) (L0 : Lbl) (c : Ctl) (fs : List TermRun.Frame) : Prop :=
  FrOk2 c fs ∧ (fs = [] → ∀ a, c.term ≠ .ret a) ∧ ∀ s, PlacedS Λ L0 s c fs

/-- **`W2` at a runtime state at the frames `fs`, at a held control**:
`SFacts` at another control `c'` not at an overflow (its state facts), `RtM`,
and the control's `MainCtlN` at `fs`. -/
theorem rtM_w2N {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : Own} {rS : Range}
    {Tk : State → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl} {lsize : Lsize} (hp : ProgNoS ZBad p)
    {s : State} {c c' : Ctl} {fs : List TermRun.Frame} (hS : SFacts Λ μ own rS Tk lbl0 s c')
    (hov : ¬ OvfReady c') (hM : RtM μ ar lab s c) (hQ : MainCtlN Λ lbl c fs) :
    W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c fs := by
  have hP := w2Part_of_wrOff (J := J) (rd := rd) (G := G) (p := p) (lsize := lsize) hM.1 (hQ.2.2 s) hM.2 hS
  exact w2_of hp hQ.1 (hS.toSt.dt_mono fun _ h => h.elim) hP.1 hQ.2.1 (.of_placedS hP.2.1) hP.2.2.1
    (abortOkA_of_ne (noAbort_of_sfacts hov hS)) hP.2.2.2

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
/-- **The exit tail's states inside `W2At` at every frames, at held
controls** (`hWx_ofPlaceOK`): `exitW_sfactsAt` at the start control `c0`
(`hC0`, not at an overflow `hov`) and `mainSW_rtM`'s exit part, joined by
`rtM_w2N` with the post's controls' `MainCtlN` at `fs` (`hQP`). -/
theorem hWx_ofPlaceOKN {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {c0 : Ctl} {L : Int} (hp : ProgNoS ZBad p)
    (hL0 : 0 ≤ L) (hL : L ≤ 16384) (hL8 : L % 8 = 0)
    {sw : Nat} (hsw : sw < 8) (hc : Spike.Lib.A64.Rt.rtCodeOkS (Ly).prog (setupMC sw) = true)
    (hph : MainPhS (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (Ly).lab (setupMC sw))
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).grow))
    (hset : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).setup))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).fn))
    (hLZ : (setupMC sw).Z.toInt ≤ L) {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hC0 : CFacts (Ly).Λ lbl0 c0) (hov : ¬ OvfReady c0)
    (hQP : ∀ c fs v, Post c fs v → MainCtlN (Ly).Λ (fun _ => none) c fs) :
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
      (x0 := pinA (Ly).lab + 0#64 + 8#64) (ms := MSAt h i p rd J none ls0 [])
      (F := swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64)) hI
      (Scc.Cert.PlaceOK.A64.printIn_of_placeOKAt h) (Scc.Cert.PlaceOK.A64.abortIn_of_placeOKAt h) hsw hin hph
      hgrow hset hfn hok h16 (by show -L ≤ _; omega) (Int.le_refl _) (fun _ hm => hm.1.2)).exit
    have H3 : ExitW (fun _ c => MainCtlN (Ly).Λ (fun _ => none) c fs) (fun _ _ => False) (Ly).exe (Ly).endPc
        (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0)
        (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64))
        (Spike.Lib.A64.Rt.mainSR (Ly).lab (setupMC sw) (fun c v => Post c fs v)) (setupMC sw).k :=
      ⟨BlkW.ofCtl fun _ _ hJ => hQP _ _ _ hJ, NodeW.ofCtl fun _ _ ⟨_, _, hJ, _⟩ => hQP _ _ _ hJ⟩
    exact ExitW.imp H1 (ExitW.imp (W := fun s c => RtM (Spike.Lib.A64.PhRec.μ (Ly)) (Spike.Lib.A64.Rt.arOf (Ly).Λ)
        (Ly).lab s c ∧ MainCtlN (Ly).Λ (fun _ => none) c fs) H2 H3 fun _ _ h1 h2 => ⟨h1, h2⟩)
      fun s c hS ⟨hM, hQ⟩ => rtM_w2N hp hS hov hM hQ
  · exact (Spike.Lib.A64.Rt.mainSW_ofFalse (PostS := fun _ _ => False) (Post := fun c v => Post c fs v)
      (ms := MSAt h i p rd J none ls0 []) (sc := setupMC sw)
      (g := ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩)
      (x0 := pinA (Ly).lab + 0#64 + 8#64) fun m hm => hv hm.1.1).exit

open Spike.Lib.A64.Flow.Ret0 in
open Spike.Lib.A64.Rt (SetupCallWS MainCallWSF SetupArgs swFSL rS0 entryR rtF) in
/-- **The consumer's `h0` at a placed output with a setup block, `main`
returning at held frames** (`h0_ofPlaceOK_setupFR`): the post's controls
by their `MainCtlN` alone (`hPost`; no `CFacts`, no placement obligation
`hPlX`), `hWx` from `hWx_ofPlaceOKN`, `hW` the prologue, setup call and
marshalling block from `mainSW_ofPlaceOKR` with its exit `hWx` at `[]`.
Left as `h0_ofPlaceOK_setupFR`'s otherwise. -/
theorem h0_ofPlaceOK_setupFN {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
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
    (hPost : ∀ c fs v, Post c fs v → MainCtlN (Ly).Λ (fun _ => none) c fs)
    (hPlS : BlkW (fun s c => Placed (Ly).Λ lbl0 s c ∧ PlacedS (Ly).Λ (fun _ => none) s c []) (fun _ _ => False)
      (Ly).exe (Ly).endPc (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0)
      (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64))
      (Spike.Lib.A64.Rt.mainS0 (Ly).lab (setupMC sw) PostS
        ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩
        (pinA (Ly).lab + 0#64 + 8#64))
      (Spike.Lib.A64.Rt.marshal (setupMC sw).sw (setupMC sw).fn))
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
  have hWx := hWx_ofPlaceOKN h i (rd := rd) (J := J) (Dt := Dt) (ls0 := ls0) hp hL0 hL hL8 hsw hc hph
    hgrow hset hfn (by omega) hC0 hov hPost
  have hWR := mainSW_ofPlaceOKR h i (rd := rd) (J := J) (Dt := Dt) (ls0 := ls0) (ab := ab)
    (Post := fun _ _ => False) hp hL0 hL hL8 hsw hc hph hgrow hset hfn (by omega) hC0
    (fun c rs h => (hPostS c rs h).1) (fun _ _ h => h.elim) ⟨hf0, hov, hpl0⟩ (fun c rs h => (hPostS c rs h).2)
    (fun _ _ h => h.elim) hPlS
    ⟨fun _ _ _ _ _ _ _ _ _ hJ => hJ.elim, fun _ _ ⟨_, _, _, _, _, _, _, _, _, hJ, _⟩ => hJ.elim⟩
  have hW : ∀ v, MainSW (Spike.Lib.A64.Rt.nilW (W2At h i p rd (rS0 (Ly)) J Dt ls0))
      (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) (Ly).exe (Ly).endPc
      (swR v (-L) 0) (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v) (MSAt h i p rd J ab ls0 [])
      (setupMC sw) PostS (fun c v => Post c [] v)
      ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩
      (pinA (Ly).lab + 0#64 + 8#64) := fun v => ⟨(hWR v).pro, (hWR v).call0, (hWR v).sp0, hWx v []⟩
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
      (rS0_eq_lab _) hsub hSM.1 hSM.2.1 hSM.2.2 (Spike.Lib.A64.Rt.fitS_of_sub _ hsub) h16t hok hL8 (by simp) hpl0)
    (Spike.Lib.A64.Rt.mainSIn_of_okS hc) h16 hZ16 hsw7 hZw hk
    hD10 hD18 hD20 hD28 hL1 hL2 (limOk_ofPlaceOK h i hZM) (limOk_ofPlaceOK h i hZS) (limOk_ofPlaceOK h i hZU) hS
    hcall hPS (hWC_ofPlaceOK h i (sc := setupMC sw) hp hL0 hL hL8 hproS hphS hlS hC0 ⟨hf0, hov, hpl0⟩) hU
    (fun R' F' s c fs v hP hAt => uPostRF_exit R' F' s c fs v (hPU c fs v hP) hAt) hW hWx

end Place

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64.Rt.exitW_sfactsAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Rt.exitW_sfactsAt

/-- info: 'Spike.Lib.LowerA64.rtM_w2N' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rtM_w2N

/-- info: 'Spike.Lib.LowerA64.hWx_ofPlaceOKN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hWx_ofPlaceOKN

/-- info: 'Spike.Lib.LowerA64.h0_ofPlaceOK_setupFN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h0_ofPlaceOK_setupFN

end Spike.Lib.LowerA64
