/-
**`h0` with the user function's post placed by its value** (x86-64): at a
held pair (a callee's `ret` with `main`'s frame pending) the post's control
is placed at no fixed state: its returned atom's words are only where the
exit tail keeps the value. `MainCtlN`'s placement at every state is
replaced by `MainCtlV`: every word of a variable the control reads
represents the returned value `v`, the suspended frames placed at every
state. At each state of the `exit_group` tail the value is in a register
(`%rax` in the block, `%rdi` at the `syscall`), which places the control.

- `MainCtlV`, `placedS_ofV`: the post's facts, and the frames placed at a
  state from them and a place holding the value;
- `rtM_w2V`: `rtM_w2N` at the placement at the state;
- `xExit_take_rax`, `xExitW_placedV`: the tail's block keeps `%rax`; the
  tail's states placed from `MainCtlV` at its entry's controls;
- `hWx_ofPlaceOKV`, `h0_ofPlaceOK_setupFV`: `hWx_ofPlaceOKN`,
  `h0_ofPlaceOK_setupFN` at `MainCtlV`.
-/
import Spike.Lib.LowerX64.RtMainXN
import Spike.Lib.LowerX64.HPlSOfSPostC

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

section V

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

end V

section RtV

open A9NoSpawn Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1 Spike.Lib.X64ConsumerA
open Spike.Lib.X64.WriteAb (Ab)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {ar : Arena} {lbl : Lbl} {lab : Label → Int64}

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

end RtV

section Exit

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **The tail's block keeps `%rax`** at every state before its last
instruction runs. -/
theorem xExit_take_rax (lab : String → Int64) (pc : Int64) (sp b : Int) (σ : AS) (n : Int64) (z0 z1 z2 : Nat)
    {k : Nat} (hk : k < (xExit n z0 z1 z2).length) :
    (arun lab ((xExit n z0 z1 z2).take k) ⟨pc, ⟨sp, [(.rbp, b)]⟩, σ⟩).σ.regs.rax = σ.regs.rax := by
  simp only [xExit, List.length_cons, List.length_nil] at hk
  obtain _ | _ | _ | k := k
  · rfl
  · simp only [xExit, List.take_succ_cons, List.take_zero]; x64simp
  · simp only [xExit, List.take_succ_cons, List.take_zero]; x64simp
  · omega

/-- **The `exit_group` tail's states placed** at the frames `fs`: from a
node whose offsets are `%rbp`'s alone, every control of its invariant at
`MainCtlV` of the value in `%rax`, each state of the tail has the control
at `FrOk2`, `main`'s `ret` excluded at no frame, and placed: by `%rax` in
the block, by `%rdi` (the entry's `%rax`) at the `syscall`. -/
theorem xExitW_placedV {Λ : Scc.Sem.Layout} {L0 : Lbl} {fs : List TermRun.Frame} {n : ND} {sp b : Int} {k : Int64}
    {z0 z1 z2 : Nat} (hno : n.o = ⟨sp, [(.rbp, b)]⟩)
    (hJ : ∀ σ c, n.J σ c → MainCtlV Λ L0 c fs σ.regs.rax.toBitVec) :
    XExitW (fun s c => FrOk2 c fs ∧ (fs = [] → ∀ a, c.term ≠ .ret a) ∧ PlacedS Λ L0 s c fs) (fun _ _ => False)
      exe endPc R F n sp b k z0 z1 z2 := by
  obtain ⟨pc, o, Jn⟩ := n
  cases hno
  refine ⟨?_, ?_⟩
  · intro s σ c _ _ _ _ _ _ hJn j hj m hA' _
    obtain ⟨hf, hnr, hV, hFP⟩ := hJ σ c hJn
    refine ⟨⟨hf, hnr, placedS_ofV hV (hFP _) (.reg (.r .rax)) ?_⟩, fun _ h => h⟩
    rw [placeVal_reg]
    show some (m.regs.get64 .rax).toNat = _
    rw [hA'.regs]
    show some ((arun _ _ ⟨pc, ⟨sp, [(.rbp, b)]⟩, σ⟩).σ.regs.rax.toBitVec.toNat) = _
    rw [xExit_take_rax _ _ _ _ σ _ _ _ _ hj]
  · rintro s c ⟨-, -, -, -, σ, hA, -, -, σ0, hJ0, hx⟩
    obtain ⟨hf, hnr, hV, hFP⟩ := hJ σ0 c hJ0
    refine ⟨⟨hf, hnr, placedS_ofV hV (hFP _) (.reg (.r .rdi)) ?_⟩, fun _ h => h⟩
    refine (placeVal_reg s .rdi).trans ?_
    rw [hA.regs]
    show some σ.regs.rdi.toBitVec.toNat = _
    rw [hx]

end Exit

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
held pair placed by its value** (`hWx_ofPlaceOKN` at `MainCtlV`): `SFacts`
at the entry's control (`hC0`, not at an overflow `hov`) at every exit
state, the post's controls' `MainCtlV` at the frames (`hQP`), the control
placed at each tail state by the register holding the value
(`xExitW_placedV`). -/
theorem hWx_ofPlaceOKV {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {c0 : Ctl} {L : Int} (hp : ProgNoS ZBad p)
    (hL : 8 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0)
    {sw : Nat} (hsw : sw < 6) (hc : rtCodeOkS (Ly).prog (setupMC sw) = true)
    (hph : MainPhS (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (Ly).lab (setupMC sw))
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).grow))
    (hset : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).setup))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).fn))
    (hLZ : 8 + 8 + (setupMC sw).Z.toInt + 8 ≤ L) {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hC0 : CFacts (Ly).Λ lbl0 c0) (hov : ¬ OvfReady c0)
    (hQP : ∀ c fs v, Post c fs v → MainCtlV (Ly).Λ (fun _ => none) c fs v) :
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
    have H3 := xExitW_placedV (Λ := (Ly).Λ) (L0 := fun _ => none) (fs := fs) (exe := (Ly).exe)
      (endPc := (Ly).endPc) (R := (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).callee (-8 - 0) (8 - L) 8)
      (F := fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64) m ∧
        CallerCells (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0) (-8 - 0) (8 - L) 8 m)
      (n := mainSRR (Ly).lab (setupMC sw) (fun c v => Post c fs v)) (k := (setupMC sw).k) (z0 := 4) (z1 := 4)
      (z2 := 5) rfl fun _ _ hJ => hQP _ _ _ hJ.1
    have hw : ∀ s c, SFacts (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly))
        (Spike.Lib.X64.PhRec.Tk (Ly)) lbl0 s c0 →
        (RtM (Spike.Lib.X64.PhRec.μ (Ly)) (arOf (Ly).Λ) (Ly).lab s c ∧
          (FrOk2 c fs ∧ (fs = [] → ∀ a, c.term ≠ .ret a) ∧ PlacedS (Ly).Λ (fun _ => none) s c fs)) →
        W2At h i p rd (rS0 (Ly)) J Dt ls0 s c fs :=
      fun _ _ h1 h2 => rtM_w2V hp h1 hov h2.1 h2.2.1 h2.2.2.1 h2.2.2.2
    exact ⟨BlkW.imp H1.w0 (BlkW.imp H2.w0 H3.w0 fun _ _ a b => ⟨a, b⟩) hw,
      NodeW.imp H1.w1 (NodeW.imp H2.w1 H3.w1 fun _ _ a b => ⟨a, b⟩) hw⟩
  · exact ⟨Spike.Lib.X64.Rt.blkW_ofFalse fun m hm => hv hm.1.1.1,
      Spike.Lib.X64.Rt.nodeW_ofFalse fun m hm => hv hm.1.1.1⟩

open Spike.Lib.X64.Flow.Ret0 in
open Spike.Lib.X64.Rt (SetupCode SetupCallWS MainCallWSF MainSW SetupArgs swFSL mainSIn oU rS0 entryR rtF setupMC
  rtCodeOkS mainS0R mainSRR CFactsC) in
open Spike.Lib.AllocReach (IN) in
/-- **The consumer's `h0` at a placed output, an entry state and a setup
block, `main` returning at pending frames, the post at a held pair placed
by its value** (`h0_ofPlaceOK_setupFN` over `hWx_ofPlaceOKV`): back from
the user function `MainCtlV` at the frames and the returned value
(`hPost`) in place of `MainCtlN`. -/
theorem h0_ofPlaceOK_setupFV {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
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
    (hPost : ∀ c fs v, Post c fs v → MainCtlV (Ly).Λ (fun _ => none) c fs v)
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
  have hWx := hWx_ofPlaceOKV h i (rd := rd) (J := J) (Dt := Dt) (ls0 := ls0) hp hL hLm hL8 hsw hc hph
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

/-- info: 'Spike.Lib.LowerX64.placedS_ofV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms placedS_ofV

/-- info: 'Spike.Lib.LowerX64.rtM_w2V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rtM_w2V

/-- info: 'Spike.Lib.LowerX64.xExitW_placedV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms xExitW_placedV

/-- info: 'Spike.Lib.LowerX64.hWx_ofPlaceOKV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hWx_ofPlaceOKV

/-- info: 'Spike.Lib.LowerX64.h0_ofPlaceOK_setupFV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h0_ofPlaceOK_setupFV

end Spike.Lib.LowerX64
