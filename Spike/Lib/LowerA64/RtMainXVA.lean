/-
**`h0` with the user function's post placed by its value** (AArch64; the
twin of `Spike/Lib/LowerX64/RtMainXV.lean`): at a held pair the post's
control is placed at no fixed state, its returned atom's words only where
the exit tail keeps the value. `MainCtlN`'s placement at every state is
replaced by `MainCtlV`: every word of a variable the control reads
represents the returned value `v`, the suspended frames placed at every
state. The `exit_group` tail keeps the value in `x0` at every state (the
block stores and reloads it), which places the control.

- `MainCtlV`, `placedS_ofV`: the post's facts, and the frames placed at a
  state from them and a place holding the value;
- `rtM_w2V`: `rtM_w2N` at the placement at the state;
- `exitTail_take_X0`, `exitW_placedV`: the tail's block keeps `x0`; the
  tail's states placed from `MainCtlV` at its entry's controls;
- `hWx_ofPlaceOKV`, `h0_ofPlaceOK_setupFV`: `hWx_ofPlaceOKN`,
  `h0_ofPlaceOK_setupFN` at `MainCtlV`.
-/
import Spike.Lib.LowerA64.RtMainXN

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

variable {Λ : Scc.Sem.Layout} {μ : Marks} {ar : Arena} {lbl : Lbl} {lab : Label → Int64}

/-- **A post control's facts at the frames `fs` and the returned value
`v`**: its frames' run free of `ZBad`, `main`'s `ret` excluded at no frame,
every word of a variable its term reads representing `v`, the suspended
frames placed at every state under `L0`. -/
def MainCtlV (Λ : Scc.Sem.Layout) (L0 : Lbl) (c : Ctl) (fs : List TermRun.Frame) (v : BitVec 64) : Prop :=
  FrOk2 c fs ∧ (fs = [] → ∀ a, c.term ≠ .ret a) ∧
    (∀ y ∈ exprFv c.term, ∀ t ws, TermRun.lookupE c.env y = some (t, ws) → ∀ w ∈ ws, ValRep L0 w.val v.toNat) ∧
    ∀ s, FramesPlaced Λ L0 s fs

/-- **The frames placed at a state holding the value**: every word of a
variable the term reads at the place `pl`, which holds `v`. -/
theorem placedS_ofV {Λ : Scc.Sem.Layout} {L0 : Lbl} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    {v : BitVec 64}
    (hV : ∀ y ∈ exprFv c.term, ∀ t ws, TermRun.lookupE c.env y = some (t, ws) → ∀ w ∈ ws, ValRep L0 w.val v.toNat)
    (hf : FramesPlaced Λ L0 s fs) (pl : Place (machine (kernel 1)).I.RegId)
    (hpl : placeVal (machine (kernel 1)) s pl = some v.toNat) : PlacedS Λ L0 s c fs := by
  classical
  refine PlacedS.ofFrames ⟨fun y _ => if y ∈ exprFv c.term then some (.one pl) else none, ?_, ?_, ?_⟩ hf
  · intro y t ws hl k wd wp hwd hwp
    by_cases hy : y ∈ exprFv c.term
    · simp only [hy, ite_true, Option.some.injEq] at hwp
      subst hwp
      exact ⟨v.toNat, hpl, hV y hy t ws hl wd (List.mem_of_getElem? hwd)⟩
    · simp [hy] at hwp
  · intro y hy t ws _ k _
    exact ⟨.one pl, by simp [hy]⟩
  · intro y k n h
    by_cases hy : y ∈ exprFv c.term <;> simp [hy] at h

/-- **`W2` at a runtime state at the frames `fs`, `SFacts` at another
control, placed at the state** (`rtM_w2N` with the placement at `s` alone). -/
theorem rtM_w2V {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : Own} {rS : Range}
    {Tk : State → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl} {lsize : Lsize} (hp : ProgNoS ZBad p)
    {s : State} {c c' : Ctl} {fs : List TermRun.Frame} (hS : SFacts Λ μ own rS Tk lbl0 s c')
    (hov : ¬ OvfReady c') (hM : RtM μ ar lab s c) (hf : FrOk2 c fs) (hnr : fs = [] → ∀ a, c.term ≠ .ret a)
    (hpl : PlacedS Λ lbl s c fs) :
    W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c fs := by
  have hP := w2Part_of_wrOff (J := J) (rd := rd) (G := G) (p := p) (lsize := lsize) hM.1 hpl hM.2 hS
  exact w2_of hp hf (hS.toSt.dt_mono fun _ h => h.elim) hP.1 hnr (.of_placedS hP.2.1) hP.2.2.1
    (abortOkA_of_ne (noAbort_of_sfacts hov hS)) hP.2.2.2

section Exit

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **The tail's block keeps `x0`** at every state before its last
instruction runs: the store leaves the registers, the load puts back the
stored word. -/
theorem exitTail_take_X0 (lab : Label → Int64) (pc : Int64) (o : SO) (σ : AS) (k : Int64) {j : Nat}
    (hj : j < (exitTail k).length) :
    (arun lab ((exitTail k).take j) ⟨pc, o, σ⟩).σ.regs.X0 = σ.regs.X0 := by
  simp only [exitTail, List.length_cons, List.length_nil] at hj
  obtain _ | _ | _ | j := j
  · rfl
  · simp [exitTail, spStr, RW.dir, AI.toDir, arun, Reg64s.getRegOrZr_X, dstep, Spike.Lib.A64.Flow.classify, AI.so,
      AI.step, AI.tgt]
  · simp [exitTail, spStr, RW.dir, AI.toDir, arun, Reg64s.getRegOrZr_X, dstep, Spike.Lib.A64.Flow.classify, AI.so,
      AI.step, AI.tgt, upd_apply, Reg64s.setRegOrZr, Reg64s.setRegOrZr64, SO.kill, SO.killZ]
  · omega

/-- **The `exit_group` tail's states placed** at the frames `fs`: every
control of the entry's invariant at `MainCtlV` of the value in `x0`, each
state of the tail has the control at `FrOk2`, `main`'s `ret` excluded at no
frame, and placed by `x0` (kept by the block, the entry's at the `svc`). -/
theorem exitW_placedV {Λ : Scc.Sem.Layout} {L0 : Lbl} {fs : List TermRun.Frame} {n : ND} {k : Int64}
    (hJ : ∀ σ c, n.J σ c → MainCtlV Λ L0 c fs σ.regs.X0.toBitVec) :
    ExitW (fun s c => FrOk2 c fs ∧ (fs = [] → ∀ a, c.term ≠ .ret a) ∧ PlacedS Λ L0 s c fs) (fun _ _ => False)
      exe endPc R F n k := by
  refine ⟨?_, ?_⟩
  · intro s σ c _ _ _ _ _ _ hJn j hj m hA' _
    obtain ⟨hf, hnr, hV, hFP⟩ := hJ σ c hJn
    refine ⟨⟨hf, hnr, placedS_ofV hV (hFP _) (.reg (.x 0)) ?_⟩, fun _ h => h⟩
    show some (m.regs.X0.toBitVec.toNat) = _
    rw [hA'.regs, exitTail_take_X0 _ _ _ σ _ hj]
  · rintro s c ⟨-, -, -, -, σ, hA, -, -, σ0, hJ0, hx⟩
    obtain ⟨hf, hnr, hV, hFP⟩ := hJ σ0 c hJ0
    refine ⟨⟨hf, hnr, placedS_ofV hV (hFP _) (.reg (.x 0)) ?_⟩, fun _ h => h⟩
    show some (s.st.1.regs.X0.toBitVec.toNat) = _
    rw [hA.regs, hx]

end Exit

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
controls placed by the value** (`hWx_ofPlaceOKN` at `MainCtlV`): the
post's controls' `MainCtlV` at `fs` (`hQP`), each tail state placing the
control by `x0` (`exitW_placedV`), joined by `rtM_w2V`. -/
theorem hWx_ofPlaceOKV {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {c0 : Ctl} {L : Int} (hp : ProgNoS ZBad p)
    (hL0 : 0 ≤ L) (hL : L ≤ 16384) (hL8 : L % 8 = 0)
    {sw : Nat} (hsw : sw < 8) (hc : Spike.Lib.A64.Rt.rtCodeOkS (Ly).prog (setupMC sw) = true)
    (hph : MainPhS (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (Ly).lab (setupMC sw))
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).grow))
    (hset : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).setup))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).fn))
    (hLZ : (setupMC sw).Z.toInt ≤ L) {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hC0 : CFacts (Ly).Λ lbl0 c0) (hov : ¬ OvfReady c0)
    (hQP : ∀ c fs v, Post c fs v → MainCtlV (Ly).Λ (fun _ => none) c fs v) :
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
    have H3 := exitW_placedV (Λ := (Ly).Λ) (L0 := fun _ => none) (fs := fs) (exe := (Ly).exe)
      (endPc := (Ly).endPc) (R := swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0)
      (F := swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64))
      (n := Spike.Lib.A64.Rt.mainSR (Ly).lab (setupMC sw) (fun c v => Post c fs v)) (k := (setupMC sw).k)
      fun _ _ hJ => hQP _ _ _ hJ
    exact ExitW.imp H1 (ExitW.imp (W := fun s c => RtM (Spike.Lib.A64.PhRec.μ (Ly)) (Spike.Lib.A64.Rt.arOf (Ly).Λ)
        (Ly).lab s c ∧ (FrOk2 c fs ∧ (fs = [] → ∀ a, c.term ≠ .ret a) ∧ PlacedS (Ly).Λ (fun _ => none) s c fs))
        H2 H3 fun _ _ h1 h2 => ⟨h1, h2⟩)
      fun s c hS ⟨hM, hf, hnr, hpl⟩ => rtM_w2V hp hS hov hM hf hnr hpl
  · exact (Spike.Lib.A64.Rt.mainSW_ofFalse (PostS := fun _ _ => False) (Post := fun c v => Post c fs v)
      (ms := MSAt h i p rd J none ls0 []) (sc := setupMC sw)
      (g := ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩)
      (x0 := pinA (Ly).lab + 0#64 + 8#64) fun m hm => hv hm.1.1).exit

open Spike.Lib.A64.Flow.Ret0 in
open Spike.Lib.A64.Rt (SetupCallWS MainCallWSF SetupArgs swFSL rS0 entryR rtF) in
/-- **The consumer's `h0` at a placed output with a setup block, `main`
returning at held frames placed by the value** (`h0_ofPlaceOK_setupFN` at
`MainCtlV`, over `hWx_ofPlaceOKV`): the post's controls by their `MainCtlV`
in place of `MainCtlN`, as there otherwise; formerly: the post's controls
by their `MainCtlN` alone (`hPost`; no `CFacts`, no placement obligation
`hPlX`), `hWx` from `hWx_ofPlaceOKN`, `hW` the prologue, setup call and
marshalling block from `mainSW_ofPlaceOKR` with its exit `hWx` at `[]`.
Left as `h0_ofPlaceOK_setupFR`'s otherwise. -/
theorem h0_ofPlaceOK_setupFV {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
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
    (hPost : ∀ c fs v, Post c fs v → MainCtlV (Ly).Λ (fun _ => none) c fs v)
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
  have hWx := hWx_ofPlaceOKV h i (rd := rd) (J := J) (Dt := Dt) (ls0 := ls0) hp hL0 hL hL8 hsw hc hph
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

/-- info: 'Spike.Lib.LowerA64.placedS_ofV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms placedS_ofV

/-- info: 'Spike.Lib.LowerA64.rtM_w2V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rtM_w2V

/-- info: 'Spike.Lib.LowerA64.exitW_placedV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exitW_placedV

/-- info: 'Spike.Lib.LowerA64.hWx_ofPlaceOKV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hWx_ofPlaceOKV

/-- info: 'Spike.Lib.LowerA64.h0_ofPlaceOK_setupFV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h0_ofPlaceOK_setupFV

end Spike.Lib.LowerA64
