/-
**A context's `ResumeCx2` from `CxLB`** (AArch64): `resume_stk`'s premise
at a caller's context (`ResumeCx2`, `Spike/Lib/LowerA64/ResumeStk2.lean`)
inside the `W2` instance, its region facts, ghosts' closure, lane stores
(`laneC_w2E`) and buffers (`newBufC_of`) from the context's base facts
`CxLB` (`Spike/Lib/LowerA64/CxLB.lean`), as `fnSpecC2_ofCxLB` takes them;
the rest (the code's program, the blocks' `BlkW` at `W2` at the frames,
the aborts, the plain calls and prints) as premises. The adapter for
`H1OpenA.hres` (`Spike/Lib/LowerA64/H1InLandA.lean`).

- `resumeCx2_ofCxLB`: `ResumeCx2` at `W2` from `CxLB` and the rest;
- `resumeCx2_ofCxLB_noCall`: the same for a block with no call at any
  point of its body (`callC2_of_noCallee`, `printCallC_of_noCall`).
-/
import Spike.Lib.LowerA64.CxLB
import Spike.Lib.LowerA64.ResumeStk2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region FrameRun FrameRunM)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (FStable At blD AS BlkW ND)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.WriteAb (Ab)
open Spike.Lib.LowerNode (ZBad TailOf)

section Fn

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {Jv : InvS} {Dt : State → Prop}
  {lbl : Lbl} {lsize : Lsize} {ms : List TermRun.Frame → MemSide isaLSE2}

/-- **A context's `ResumeCx2` inside `W2` from `CxLB`**: at a compiled
block at the code `CdCLE` and the immediates `Λ.imms` (its calls in the
code, `hBl`; its allocations' element types `elem2`, `hTn`), a context
with `CxLB` (`H`) at a return address with `RaOk` resumes inside `W2`: the
region facts and the ghosts' closure from `H`, the lane stores by
`laneC_w2E`, the buffers by `newBufC_of`; the code's program (`hprog`),
the blocks' `BlkW` at `W2` at the frames `fs` (`hWB`, `hW`, `hWp`), the
aborts (`habN`), the plain calls (`hcall`) and prints (`hpc`) given. -/
theorem resumeCx2_ofCxLB (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hA : Spike.Lib.A64.Flow.allocIn prog = true)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hp : ProgNoS ZBad p)
    {RaOk : BitVec 64 → Prop} {T : Expr → Prop} {d : Decl}
    (c : FnCode2 exe prog endPc RaOk (fun ra => CdCLE prog okPc ph lab (Int64.ofBitVec ra)) Λ.imms T d)
    (hTn : ∀ x cn τ e, T (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64}
    {G0 : Ctl → Prop} {Ab' : FragS isaLSE2} (hra : RaOk ra)
    (hBl : ∀ pc g k, c.Bl ra pc g k → CdOf exe endPc pc [blD g])
    (H : CxLB Λ μ p rd G own rS Tk ar Jv Dt lab K exe endPc ms lbl lsize c.lcx c.cx
      (CdCLE prog okPc ph lab (Int64.ofBitVec ra)) (c.Bl ra) Λ.imms T (RetLk d.retTy) R F fs fp ra tp G0 Ab')
    (hprog : c.lcx.prog = p)
    (hWB : ∀ (n : ND) blk, SubCd (CdCLE prog okPc ph lab (Int64.ofBitVec ra)) n.pc blk → n.o = oF c.cx →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) → CallBlk c.cx blk →
      BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F n blk)
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd (CdCLE prog okPc ph lab (Int64.ofBitVec ra)) pc blk →
      Kind2 c.cx blk →
      BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F
        (bodyN2 p lbl lsize Λ.imms c.cx fp ra c0 pc t s lits cs bufs) blk)
    (hWp : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk,
      SubCd (CdCLE prog okPc ph lab (Int64.ofBitVec ra)) pc blk → Kind2 c.cx blk → blk.length ≤ 1 →
      BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F
        (pendN2 p lbl lsize Λ.imms c.cx fp ra c0 pc t s lits cs bufs k) blk)
    (habN : ∀ c0, G0 c0 → ∀ s c',
      At exe endPc R F (abortN2 Λ.imms T p lbl c.cx (_root_.Executable.labels exe).label fp ra c0) s c' →
        Ab' s c' fs)
    (hcall : CallC2 p lbl lsize c.lcx c.cx (CdCLE prog okPc ph lab (Int64.ofBitVec ra)) (c.Bl ra) exe endPc R F
      (fun s c fs => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K ms fp ra tp fs G0 Λ.imms T Ab'
      (RetLk d.retTy))
    (hpc : PrintCallC p lbl lsize c.lcx c.cx (CdCLE prog okPc ph lab (Int64.ofBitVec ra)) (c.Bl ra) exe endPc R F
      (fun s c fs => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K ms fp ra tp fs G0 Λ.imms T Ab') :
    ResumeCx2 (fun s c fs => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K p lbl lsize ms c
      R F fs fp ra tp G0 Ab' := by
  refine ⟨hprog, H.hFS, H.hR, H.hal, H.hhi, H.hG0,
    fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs, fun _ _ h => h, hWB, hW, hWp, habN,
    hcall, ?_, ?_, hpc⟩
  · exact laneC_w2E hI hpr hab c.hf c.h1 c.h16 H.hR H.hal H.hloF H.hhi H.hl H.hh hsub hfit H.hFO H.hFS hp H.hrs
      H.hfp c.lcx tp (fun _ _ h => h) H.hrd H.hroom H.hrg H.hwn H.hHW H.hG0F
  · exact newBufC_of c.hf c.h1 c.h16 c.hp c.hend hA H.hFS H.hR H.hal H.hloA H.hhi (c.hCd ra hra) hBl
      (W₀ := fun lbl lsize s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) (fun _ _ h => h) H.hK
      H.hG0 hTn c.lcx H.hAW H.hAb

/-- **`resumeCx2_ofCxLB` for a block without calls**: the walk predicate
`T` only at points of the body (`hT`), none of them a call (`hnc`); the
plain calls by `callC2_of_noCallee`, the prints by
`printCallC_of_noCall`. -/
theorem resumeCx2_ofCxLB_noCall (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hA : Spike.Lib.A64.Flow.allocIn prog = true)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hp : ProgNoS ZBad p)
    {RaOk : BitVec 64 → Prop} {T : Expr → Prop} {d : Decl}
    (c : FnCode2 exe prog endPc RaOk (fun ra => CdCLE prog okPc ph lab (Int64.ofBitVec ra)) Λ.imms T d)
    (hT : ∀ t, T t → TailOf t d.body)
    (hnc : (tailsL d.body).all (fun t => !isCallLet t) = true)
    (hTn : ∀ x cn τ e, T (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64}
    {G0 : Ctl → Prop} {Ab' : FragS isaLSE2} (hra : RaOk ra)
    (hBl : ∀ pc g k, c.Bl ra pc g k → CdOf exe endPc pc [blD g])
    (H : CxLB Λ μ p rd G own rS Tk ar Jv Dt lab K exe endPc ms lbl lsize c.lcx c.cx
      (CdCLE prog okPc ph lab (Int64.ofBitVec ra)) (c.Bl ra) Λ.imms T (RetLk d.retTy) R F fs fp ra tp G0 Ab')
    (hprog : c.lcx.prog = p)
    (hWB : ∀ (n : ND) blk, SubCd (CdCLE prog okPc ph lab (Int64.ofBitVec ra)) n.pc blk → n.o = oF c.cx →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) → CallBlk c.cx blk →
      BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F n blk)
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd (CdCLE prog okPc ph lab (Int64.ofBitVec ra)) pc blk →
      Kind2 c.cx blk →
      BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F
        (bodyN2 p lbl lsize Λ.imms c.cx fp ra c0 pc t s lits cs bufs) blk)
    (hWp : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk,
      SubCd (CdCLE prog okPc ph lab (Int64.ofBitVec ra)) pc blk → Kind2 c.cx blk → blk.length ≤ 1 →
      BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F
        (pendN2 p lbl lsize Λ.imms c.cx fp ra c0 pc t s lits cs bufs k) blk)
    (habN : ∀ c0, G0 c0 → ∀ s c',
      At exe endPc R F (abortN2 Λ.imms T p lbl c.cx (_root_.Executable.labels exe).label fp ra c0) s c' →
        Ab' s c' fs) :
    ResumeCx2 (fun s c fs => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K p lbl lsize ms c
      R F fs fp ra tp G0 Ab' := by
  have hno : ∀ x g is a ts e, ¬ T (.let_ x (.call g is a ts) e) := fun x g is a ts e hT' =>
    noCall_of_tailsL hnc x g is a ts e (hT _ hT')
  exact resumeCx2_ofCxLB hI hpr hab hA hsub hfit hp c hTn hra hBl H hprog hWB hW hWp habN
    (callC2_of_noCallee fun x g is a ts e hT' _ => hno x g is a ts e hT') (printCallC_of_noCall hno)

end Fn

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.resumeCx2_ofCxLB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms resumeCx2_ofCxLB

/--
info: 'Spike.Lib.LowerA64.resumeCx2_ofCxLB_noCall' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms resumeCx2_ofCxLB_noCall

end Spike.Lib.LowerA64
