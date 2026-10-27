/-
**A call-free compiled block's `ResumeCx2` inside `W2` from the placement
check** (AArch64): `resumeCx2_ofCxLB_noCall`
(`Spike/Lib/LowerA64/ResumeCxLB.lean`) at the placement check's code facts
at the theorem's immediates (`fnCode2OfPMe`), as `fnSpecC2_ofCxLBMe`
(`Spike/Lib/LowerA64/CxLBP.lean`) does for `fnSpecC2_ofCxLB`. The record's
instance, the runtime's code, the calls' code and the block's program come
from the placement check; left are the allocator's code (`hA`), the stack
(`hsub`, `hfit`), `hpN`, the block's points (no call, `hnc`; one-word
elements, `hTn`), the context's `CxLB` (`H`) and its blocks inside `W2`
(`hWB`, `hW`, `hWp`) and aborts (`habN`).

- `resumeCx2_ofCxLBMe`: the `j`th compiled block's `ResumeCx2` at
  `fnCode2OfPMe`, at any placement `lbl`, `lsize` and memory side `ms`.
-/
import Spike.Lib.LowerA64.CxLBP
import Spike.Lib.LowerA64.ResumeCxLB

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (Marks Range)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.A64.Flow
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerS (InvS)
open Spike.Lib.A64.Rt (RuntimeLayout bareMC)
open Spike.Lib.LowerNode (ZBad compiled2 TailAt2 imms2Me)

section Place

variable {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
  {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

local notation "LY" => RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))
set_option hygiene false in
/-- The runtime layout at the theorem's immediates. -/
local notation "LM" => RuntimeLayout.ofPlaceOK h (imms2Me Λm p)

/-- **A call-free compiled block's `ResumeCx2` from the placement check**
(`resumeCx2_ofCxLB_noCall` at `fnCode2OfPMe`): the `j`th compiled block
`d`, none of its body's points a call (`hnc`), its allocations' elements
one word (`hTn`), inside the `W2` instance at the layout `(LM).Λ`, the
record's `μ`, `own`, `Tk`, `K` and write abort, at any placement `lbl`,
`lsize` and memory side `ms`; at a context with `RaOk` (`hra`), its facts
`CxLB` (`H`), its blocks inside `W2` (`hWB`, `hW`, `hWp`) and its aborts
(`habN`). The block's program is `p` (`fnCode2OfPMe_spec`), its calls in
the code (`cdOf_of_blC`). -/
theorem resumeCx2_ofCxLBMe (Λm : Scc.Sem.Layout) {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    (hA : Spike.Lib.A64.Flow.allocIn OP = true)
    {rS : Range} (hsub : rS.Sub (LM).Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hpN : ProgNoS ZBad p)
    (hnc : (tailsL d.body).all (fun t => !isCallLet t) = true)
    (hTn : ∀ x cn τ e, TailAt2 p j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS} {Dt : State → Prop}
    {lbl : Lbl} {lsize : Lsize} {ms : List TermRun.Frame → MemSide isaLSE2}
    {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64}
    {G0 : Ctl → Prop} {Ab' : FragS isaLSE2}
    (hra : Spike.Lib.A64.PhRec.ph LY (Int64.ofBitVec ra).toBitVec.toNat =
      Spike.Lib.A64.PhRec.ph LY (Int64.ofBitVec ((LY).lab bareMC.e0 + 4).toBitVec).toBitVec.toNat)
    (H : CxLB (LM).Λ (Spike.Lib.A64.PhRec.μ LY) p rd G (Spike.Lib.A64.PhRec.own LY) rS (Spike.Lib.A64.PhRec.Tk LY)
      ar J Dt (LY).lab (Spike.Lib.A64.PhRec.K LY rS) (LY).exe (LY).endPc ms lbl lsize
      (fnCode2OfPMe hp h Λm j d hd).lcx (fnCode2OfPMe hp h Λm j d hd).cx
      (CdCLE OP (Spike.Lib.A64.PhRec.okPc LY) (Spike.Lib.A64.PhRec.ph LY) (LY).lab (Int64.ofBitVec ra))
      ((fnCode2OfPMe hp h Λm j d hd).Bl ra) (imms2Me Λm p) (TailAt2 p j) (RetLk d.retTy)
      R F fs fp ra tp G0 Ab')
    (hWB : ∀ (n : ND) blk,
      SubCd (CdCLE OP (Spike.Lib.A64.PhRec.okPc LY) (Spike.Lib.A64.PhRec.ph LY) (LY).lab (Int64.ofBitVec ra))
        n.pc blk → n.o = oF (fnCode2OfPMe hp h Λm j d hd).cx →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) → CallBlk (fnCode2OfPMe hp h Λm j d hd).cx blk →
      BlkW (fun s c => W2 (LM).Λ (Spike.Lib.A64.PhRec.μ LY) p rd G (Spike.Lib.A64.PhRec.own LY) rS
          (Spike.Lib.A64.PhRec.Tk LY) ar J Dt (A64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
        (Spike.Lib.A64.PhRec.K LY rS) (LY).exe (LY).endPc R F n blk)
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk,
      SubCd (CdCLE OP (Spike.Lib.A64.PhRec.okPc LY) (Spike.Lib.A64.PhRec.ph LY) (LY).lab (Int64.ofBitVec ra))
        pc blk → Kind2 (fnCode2OfPMe hp h Λm j d hd).cx blk →
      BlkW (fun s c => W2 (LM).Λ (Spike.Lib.A64.PhRec.μ LY) p rd G (Spike.Lib.A64.PhRec.own LY) rS
          (Spike.Lib.A64.PhRec.Tk LY) ar J Dt (A64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
        (Spike.Lib.A64.PhRec.K LY rS) (LY).exe (LY).endPc R F
        (bodyN2 p lbl lsize (imms2Me Λm p) (fnCode2OfPMe hp h Λm j d hd).cx fp ra c0 pc t s lits cs bufs) blk)
    (hWp : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk,
      SubCd (CdCLE OP (Spike.Lib.A64.PhRec.okPc LY) (Spike.Lib.A64.PhRec.ph LY) (LY).lab (Int64.ofBitVec ra))
        pc blk → Kind2 (fnCode2OfPMe hp h Λm j d hd).cx blk → blk.length ≤ 1 →
      BlkW (fun s c => W2 (LM).Λ (Spike.Lib.A64.PhRec.μ LY) p rd G (Spike.Lib.A64.PhRec.own LY) rS
          (Spike.Lib.A64.PhRec.Tk LY) ar J Dt (A64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
        (Spike.Lib.A64.PhRec.K LY rS) (LY).exe (LY).endPc R F
        (pendN2 p lbl lsize (imms2Me Λm p) (fnCode2OfPMe hp h Λm j d hd).cx fp ra c0 pc t s lits cs bufs k) blk)
    (habN : ∀ c0, G0 c0 → ∀ s c',
      At (LY).exe (LY).endPc R F (abortN2 (imms2Me Λm p) (TailAt2 p j) p lbl (fnCode2OfPMe hp h Λm j d hd).cx
        (_root_.Executable.labels (LY).exe).label fp ra c0) s c' → Ab' s c' fs) :
    ResumeCx2 (fun s c fs => W2 (LM).Λ (Spike.Lib.A64.PhRec.μ LY) p rd G (Spike.Lib.A64.PhRec.own LY) rS
        (Spike.Lib.A64.PhRec.Tk LY) ar J Dt (A64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
      (Spike.Lib.A64.PhRec.K LY rS) p lbl lsize ms (fnCode2OfPMe hp h Λm j d hd) R F fs fp ra tp G0 Ab' := by
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms2Of p) (rS := rS)
  refine resumeCx2_ofCxLB_noCall (Λ := (LM).Λ) hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hA hsub hfit
    hpN (fnCode2OfPMe hp h Λm j d hd) (fun t ht => ht d hd) hnc hTn hra ?_ H ?_ hWB hW hWp habN
  · intro pc g k hb
    rw [(fnCode2OfPMe_spec hp h Λm j d hd).2.1] at hb
    exact cdOf_of_blC hI hb.1.1
  · rw [(fnCode2OfPMe_spec hp h Λm j d hd).1]

end Place

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.resumeCx2_ofCxLBMe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms resumeCx2_ofCxLBMe

end Spike.Lib.LowerA64
