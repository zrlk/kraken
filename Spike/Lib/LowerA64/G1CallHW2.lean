/-
**A held plain call's result store inside `W2` at the held frames**
(AArch64): the premise `hWH` of `callC2H_ofFW`
(`Spike/Lib/LowerA64/G1CallHW.lean`) at the world `W2` with the write abort
`Ab lab` and the immediates `Λ.imms`, for a code predicate inside `CdCLE`.

At the result's store the source is held at the callee's `ret a`, one frame
above `fs` (`heldND`), the landing node's control `cR` one return step
below. The held pair is placed: its suspended frame is the landing's
current frame with the result variable dropped and the frames below it the
landing's (`framesPlaced_ret`), and its current control reads at most the
returned word, which `x0` holds (`ret0_of_frameStep`, the result's
register at `x0` in the landing's slot file). It is free of `ZBad` (the
landing's `FrOk2`) and off `main`'s `ret` (it is at depth); the block is
the result's store (`blkW_w2CallBlk`).

- `lookupE_cons_neH`: a source lookup past another variable's binding;
- `placed_ofPlacedS`: every frame placed places the current one;
- `framesPlaced_ret`: the landing placed places the held frames;
- `callW2_hWH`: the premise.
-/
import Spike.Lib.LowerA64.G1CallW2
import Spike.Lib.LowerA64.HeldTailRet
import Spike.Lib.LowerA64.CallC2H

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region FrameRun FrameRunM)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (FStable BlkW ND classify AI okBlk)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.A64.WriteAb (Ab)
open Spike.Lib.LowerNode
open Spike.Lib.Form (lookupS SEnv)
open Scc.Emit.A64 (FnCtx directives Item)
open Scc.Lower.InvA64

/-- A source lookup past another variable's binding. -/
theorem lookupE_cons_neH {env : TermRun.Env} {y x : String} {t : Ty} {ws : List TermRun.Word} (h : y ≠ x) :
    TermRun.lookupE ((x, t, ws) :: env) y = TermRun.lookupE env y := by
  have hne : (x == y) = false := by simp only [beq_eq_false_iff_ne]; exact fun e => h e.symm
  simp only [TermRun.lookupE, List.find?_cons, hne]

/-- **Every frame placed places the current one** (`envm 0`). -/
theorem placed_ofPlacedS {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (h : PlacedS Λ lbl s c fs) : Placed Λ lbl s c := by
  obtain ⟨envm, hrep, htot, himm⟩ := h
  exact ⟨envm 0, fun x ty ws hl k wd wp hwd hwp => hrep 0 c.env (by simp [envsOf]) x ty ws hl k wd wp hwd hwp,
    fun x hx ty ws hl k hk => htot 0 c.env _ (by simp [envsOf]) (by simp [fvOf]) x hx ty ws hl k hk,
    fun x k n h => himm 0 c.term x k n (by simp [termsOf]) h⟩

/-- **The landing placed places the held frames**: at a return step from
`c` at `f :: fs` to `cR` at `fs`, the frame `f` is `cR`'s current frame
with `f`'s result variable dropped (`cR`'s environment binds it over
`f`'s, its term `f`'s body), the frames below it `cR`'s. -/
theorem framesPlaced_ret {p : Prog} {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {c cR : Ctl}
    {f : TermRun.Frame} {fs : List TermRun.Frame} (hst : FrameStep p (c, f :: fs) (cR, fs)) (h : PlacedS Λ lbl s cR fs) : FramesPlaced Λ lbl s (f :: fs) := by
  cases hst with
  | @ret _ _ _ a' t ws _ _ _ =>
    obtain ⟨envm, hrep, htot, himm⟩ := h
    refine ⟨fun d => match d with
      | 0 => fun y k => if y = f.x then none else envm 0 y k
      | d + 1 => envm (d + 1), ?_, ?_, ?_⟩
    · intro d g hg y ty ws' hy k wd wp hwd hwp
      rcases d with _ | d
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
        subst hg
        by_cases hyx : y = f.x
        · simp [hyx] at hwp
        · simp only [hyx, ite_false] at hwp
          refine hrep 0 ((f.x, f.ty, ws) :: f.env) rfl y ty ws' ?_ k wd wp hwd hwp
          rw [lookupE_cons_neH hyx]; exact hy
      · exact hrep (d + 1) g.env (by simp only [List.getElem?_cons_succ] at hg; simp [envsOf, hg]) y ty ws' hy
          k wd wp hwd hwp
    · intro d g hg y hy ty ws' hl k hk
      rcases d with _ | d
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
        subst hg
        simp only [List.mem_filter, bne_iff_ne, ne_eq] at hy
        obtain ⟨hy, hyx⟩ := hy
        simp only [hyx, ite_false]
        refine htot 0 ((f.x, f.ty, ws) :: f.env) _ rfl rfl y hy ty ws' ?_ k hk
        rw [lookupE_cons_neH hyx]; exact hl
      · simp only [List.getElem?_cons_succ] at hg
        exact htot (d + 1) g.env _ (by simp [envsOf, hg]) (by simp [fvOf, hg]) y hy ty ws' hl k hk
    · intro d g y k n hg hn
      rcases d with _ | d
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
        subst hg
        by_cases hyx : y = f.x
        · simp [hyx] at hn
        · simp only [hyx, ite_false] at hn
          exact himm 0 f.body y k n rfl hn
      · simp only [List.getElem?_cons_succ] at hg
        exact himm (d + 1) g.body y k n (by simp [termsOf, hg]) hn

section W

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {ar : Arena} {Jv : InvS} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}

/-- **`callC2H_ofFW`'s `hWH` at `W2`**: the result's store of `Cd` inside
`CdCLE` (`hCd`) at its held node, inside `W2` at the held frames
(`blkW_w2CallBlk` at `f :: fs`): each state placed at the held pair
(`framesPlaced_ret` from the landing placed with the result's slot at
`x0`, `placedS_of_abs_updX0`; the callee's `ret` reading at most the
returned word, at `x0`, `ret0_of_frameStep`), the held pair free of `ZBad`
(the landing's `FrOk2`, its control in `G0`, `hG0`, `hG0F`). -/
theorem callW2_hWH {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0) (hFS : FStable R F)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {G0 : Ctl → Prop} (hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs)
    (hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c') {fp ra : BitVec 64} {tp : UInt64}
    {ra0 : Int64}
    {Cd : Int64 → List Directive → Prop} (hCd : ∀ pc blk, Cd pc blk → CdCLE prog okPc ph lab ra0 pc blk) :
    ∀ (f : TermRun.Frame) (c0 : Ctl) (Q : Ctl → Prop) (pcR : Int64) (x : String) (e : Expr) (s : SEnv)
      (d : Scc.IR.Reg) (ls : List Item) (off : Int), G0 c0 → cx.setReg d .X0 = .ok ls → rsOf cx d = some off →
      Cd pcR (directives ls) → lookupS s x = some (.int, [.one (.reg d)]) →
      (∀ y ∈ Scc.Sem.exprFv e, (lookupS s y).isSome) → LocBaseRegAt s e → ImmIn Λ.imms s e →
      BlkW (fun st c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize st c (f :: fs)) K exe endPc R F
        (heldND p f fs x e (retCN2 p lbl cx fp ra tp c0 fs Q pcR e s off)) (directives ls) := by
  intro f c0 Q pcR x e s d ls off hc0 hs hoff hc hx htot hlb hic
  have hb : CallBlk cx (directives ls) := .inr ⟨d, ls, hs, rfl⟩
  have hlen : (directives ls).length ≤ 1 := by
    obtain ⟨o, ho, -⟩ := bind_eq_ok hs
    have hs' := hs
    rw [setReg_eq hf (by omega) ho] at hs'
    cases ok_inj hs'
    simp [directives, Scc.Emit.A64.ins]
  refine blkW_w2CallBlk (fs := f :: fs) hI hpr hab hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp rfl
    ((SubCd.whole hc).mono hCd) hb ?_ ?_
  · intro st σ c _ _ _ _ _ hF hJn k hk m hA' hD
    refine ⟨?_, fun _ h => h⟩
    obtain rfl : k = 0 := by omega
    obtain ⟨hfx, -, a, cR, ht, hst, hjR, -⟩ := hJn
    have hPR := placedS_of_abs_updX0 (Λ := Λ) (fs := fs) (s := { st with st := (m, pcR + Int64.ofNat (4 * 0)) })
      hA' (SlotRepAt.of_nodeJE hjR htot hlb hic) (rsOf_off hf h16 hlo hhi) (hfp _ (hFS _ _ hF hD)).choose_spec
    obtain ⟨t', ws, hlw, -, hwr⟩ := hjR.2.2.lookup hx
    match ws, hwr with
    | [w], ⟨⟨v, hv, hvr⟩, _⟩ =>
      have hv' : v = σ.regs.X0.toBitVec.toNat := by
        simp [Spike.Lib.Form.opdVal, hoff, Spike.Lib.upd_apply] at hv
        exact hv.symm
      subst hv'
      have hr : WordPlaceRep (machine (kernel 1)) lbl { st with st := (m, pcR + Int64.ofNat (4 * 0)) }
          (.one (.reg (.x 0))) w.val := by
        refine ⟨_, ?_, hvr⟩
        show some ((xRegs m.regs).getD 0 0).toBitVec.toNat = _
        rw [hA'.regs]; rfl
      rw [← hfx] at hlw
      exact PlacedS.ofFrames (placed_ofPlacedS (placedS_ret0 (ret0_of_frameStep ht hst hlw hr)))
        (framesPlaced_ret hst hPR)
  · rintro σ c ⟨-, hfb, a, cR, ht, hst, hjR, -, -, hrun, -⟩
    have hok := hG0F cR (hG0 c0 cR hc0 hrun)
    refine ⟨fun h => (nomatch h), ?_⟩
    refine ⟨by rw [ht]; trivial, fun fr hfr => ?_⟩
    rcases List.mem_cons.mp hfr with rfl | hfr
    · rw [hfb, ← hjR.1]; exact hok.1
    · exact hok.2 fr hfr

end W

end Spike.Lib.LowerA64

/-- info: 'Spike.Lib.LowerA64.framesPlaced_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.framesPlaced_ret

/-- info: 'Spike.Lib.LowerA64.callW2_hWH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.callW2_hWH
