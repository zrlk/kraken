/-
**A call-free compiled block's segment inside `W2` from the placement
check** (x86-64; the twin of `Spike/Lib/LowerA64/CxLBP.lean`):
`fnSpecC2_ofCxLB` (`Spike/Lib/LowerX64/CxLB.lean`) at the placement
check's code facts at the theorem's immediates (`fnCode2OfPMe`,
`Spike/Lib/LowerX64/FnCode2Me.lean`), inside the `W2` instance at the
runtime layout of the output at `imms2Me Λm p`. The record's instance, the
runtime's code and the calls' code come from the placement check; left are
the allocator's code (`hA`), the stack (`hsub`, `hfit`), `hpN`, the block's
points (no call, `hnc`; one-word elements, `hTn`) and at each context `CxLB`
in the rebased region `rbR R` (`hcx`).

- `fnSpecC2_ofCxLBMe`: the `j`th compiled block's `FnSpecC2` at
  `fnCode2OfPMe`.
-/
import Spike.Lib.LowerX64.CxLB
import Spike.Lib.LowerX64.FnCode2Me

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem (Marks Range)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region MemSide)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerS (InvS)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.LowerNode (ZBad compiled2 TailAt2 imms2Me)

section Place

variable {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
  {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

local notation "LY" => RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)
set_option hygiene false in
/-- The runtime layout at the theorem's immediates. -/
local notation "LM" => RuntimeLayout.ofPlaceOK h (imms2Me Λm p)

/-- **A call-free compiled block's `FnSpecC2` from the placement check**
(`fnSpecC2_ofCxLB` at `fnCode2OfPMe`): the `j`th compiled block `d`, none
of its body's points a call (`hnc`), its allocations' elements one word
(`hTn`), inside the `W2` instance at the layout `(LM).Λ` (immediates
`imms2Me Λm p`), the record's `μ`, `own`, `Tk`, `K` and write abort; at
every context `CxOk` (with `RaOk`) the facts `CxLB` in the rebased region
`rbR R` at the block's lowering context, frame, code and calls. -/
theorem fnSpecC2_ofCxLBMe (Λm : Scc.Sem.Layout) {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    (hA : Spike.Lib.X64.Alloc.allocIn OP = true)
    {rS : Range} (hsub : rS.Sub (LM).Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hpN : ProgNoS ZBad p)
    (hnc : (tailsL d.body).all (fun t => !isCallLet t) = true)
    (hTn : ∀ x cn τ e, TailAt2 p j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS} {Dt : State → Prop}
    {lbl : Lbl} {lsize : Lsize} {ms : List TermRun.Frame → MemSide isa}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    (hcx : ∀ R F fs fp ra tp G0 Ab, CxOk R F fs fp ra tp G0 Ab →
      Spike.Lib.X64.PhRec.ph LY (Int64.ofBitVec ra).toBitVec.toNat =
        Spike.Lib.X64.PhRec.ph LY ((LY).lab raL).toBitVec.toNat →
      CxLB (LM).Λ (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS (Spike.Lib.X64.PhRec.Tk LY)
        ar J Dt (LY).lab (Spike.Lib.X64.PhRec.K LY rS) (LY).exe (LY).endPc ms lbl lsize
        (fnCode2OfPMe hp h Λm j d hd).lcx (fnCode2OfPMe hp h Λm j d hd).fr
        (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab (Int64.ofBitVec ra))
        ((fnCode2OfPMe hp h Λm j d hd).Bl ra) (imms2Me Λm p) (TailAt2 p j) (RetLk d.retTy)
        (rbR R) F fs fp ra tp G0 Ab) :
    FnSpecC2 (fun s c fs => W2 (LM).Λ (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
        (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
      (Spike.Lib.X64.PhRec.K LY rS) p lbl lsize ms CxOk (fnCode2OfPMe hp h Λm j d hd) := by
  haveI := (LY).valid
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms2Of p) (rS := rS)
  refine fnSpecC2_ofCxLB (Λ := (LM).Λ) hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hA hsub hfit hpN
    (fnCode2OfPMe hp h Λm j d hd) (fun t ht => ht d hd) hnc hTn ?_ hcx
  intro ra _ pc zc g k hb
  rw [(fnCode2OfPMe_spec hp h Λm j d hd).2.1] at hb
  exact cdOf_blC hI.lays hI.endOk pc zc g k (by rw [hI.labOk]; exact hb.1.1)

end Place

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.fnSpecC2_ofCxLBMe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnSpecC2_ofCxLBMe

end Spike.Lib.LowerX64
