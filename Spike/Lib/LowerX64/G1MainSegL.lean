/-
**`main`'s segment at every reachable placement from the function
segment** (x86-64): `MainSeg2L` (`Spike/Lib/LowerX64/G1MainStmtL.lean`)
from `FnSpecC2AtL` (`Spike/Lib/LowerX64/G1FnSpecL.lean`) at the bottom keys
`fun _ _ => True`, the branch-target check `tgOkB` and the write tail's
premises at the output call and the three aborts.

At `main`'s frame (`cxG2ML_main`, the context facts `MainCx2L` at the
rebased region `rbR R`), the aborts' fragment is `AbG2L` (its segment
`abG2L_seg`), the constructs are the base context's producers at `main`'s
return address's phase (`MainCx2L.hraK`): the plain calls `callC2R_ofCxG2ML`
and `callC2H_ofCxG2ML` (the callees' segments from `FnSpecC2AtL` at the
call order `hord_ofAccepted2`), the lane stores and buffers `laneBuf2L`,
the output calls `print2L` and `print2HL`. `CalleePre2R` at the prologue's
region `R` has its blocks inside `W2AtL` (`cxBlk2_ofW2` at `rbR R`) and its
region facts read back from `rbR R`'s.

- `rbR_base_inv`, `rbR_ok_inv`, `rbR_fstable_inv`, `stackOff_of_rbR`: a
  region's facts from its rebased region's;
- `mainSeg2L_of`: `MainSeg2L` from `FnSpecC2AtL`.
-/
import Spike.Lib.LowerX64.G1MainCxL
import Spike.Lib.LowerX64.G1CallC2HL
import Spike.Lib.LowerX64.G1PrintHL
import Spike.Lib.LowerX64.G1AbG2L
import Spike.Lib.LowerX64.G1LaneBufL
import Spike.Lib.LowerX64.G1CallW
import Spike.Lib.LowerX64.G1Room2
import Spike.Lib.LowerX64.G1LimOkL
import Spike.Lib.LowerX64.HordC2

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region FrameRunM)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (FStable AS)
open Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (StackOff limA pinA tpOf)
open Spike.Lib.X64.Rt (rS0 arOf)
open Spike.Lib.AllocReach (Reach)
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2 imms2Me IsNum)

/-! ## A region's facts from its rebased region's -/

/-- **The region's base is the rebased region's raised by `8`** when the
rebased region does not wrap and reaches `16` above its base. -/
theorem rbR_base_inv {R : Region} (hR : (rbR R).OK) (hhi : 16 ≤ (rbR R).hi) :
    (R.base.toNat : Int) = (rbR R).base.toNat + 8 := by
  have h2 := hR.hi
  have hlt := R.base.isLt
  have e8 : (BitVec.ofInt 64 (-8)).toNat = 18446744073709551608 := rfl
  have e : (rbR R).base.toNat = (R.base.toNat + 18446744073709551608) % 18446744073709551616 := by
    show (R.base + BitVec.ofInt 64 (-8)).toNat = _
    rw [BitVec.toNat_add, e8]
  have hhi' : (rbR R).hi = R.hi + 8 := rfl
  omega

/-- **The region does not wrap** when its rebased region does not and
reaches `16` above its base. -/
theorem rbR_ok_inv {R : Region} (hR : (rbR R).OK) (hhi : 16 ≤ (rbR R).hi) : R.OK := by
  have hb := rbR_base_inv hR hhi
  have h1 := hR.lo
  have h2 := hR.hi
  have hlo' : (rbR R).lo = R.lo + 8 := rfl
  have hhi' : (rbR R).hi = R.hi + 8 := rfl
  exact ⟨by omega, by omega⟩

/-- The rebased region covers the same bytes: a frame condition stable
under it is stable under the region. -/
theorem rbR_fstable_inv {R : Region} {F : MachineData → Prop} (hR : (rbR R).OK) (hhi : 16 ≤ (rbR R).hi)
    (hF : FStable (rbR R) F) : FStable R F := by
  have hb := rbR_base_inv hR hhi
  have hlo' : (rbR R).lo = R.lo + 8 := rfl
  have hhi' : (rbR R).hi = R.hi + 8 := rfl
  intro m m' hm hd
  exact hF m m' hm fun a ha hout => hd a ha (by omega)

/-- The words of `rS` off the rebased region are off the region. -/
theorem stackOff_of_rbR {rS : Scc.Sem.Range} {R : Region} {m : MachineData} (hR : (rbR R).OK)
    (hhi : 16 ≤ (rbR R).hi) (h : StackOff rS (rbR R) m) : StackOff rS R m := by
  have hb := rbR_base_inv hR hhi
  have hlo' : (rbR R).lo = R.lo + 8 := rfl
  have hhi' : (rbR R).hi = R.hi + 8 := rfl
  intro a h8 ha ha7 hout
  exact h a h8 ha ha7 (by omega)

section G1MainSegL

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates. -/
local notation "LY0" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output. -/
local notation "OUT" => Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)

set_option hygiene false in
/-- The `j`th compiled block's code facts at the theorem's immediates. -/
local notation "FC" j:max d:max hd:max => fnCode2OfPMe hp h Λ j d hd

set_option hygiene false in
/-- The code predicate at the return address `ra`. -/
local notation "CD" ra:max => CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab
  (Int64.ofBitVec ra)

/-- **`main`'s segment at every reachable placement** (`MainSeg2L`): from
the function segment at every reachable placement (`HF`, the bottom keys
`fun _ _ => True`), the branch-target check (`htg`), the write tail `Dt`
at the output call's system call (`hDt`) and at the overflow, write and
heap aborts (`hDtO`, `hDtW`, `hDtH`); the room, limit and call rows are
their proofs (`room2Own`, `room2Callee`, `lim2Callee`, `limOk2L`,
`proCallG2L`, `wCallG2L`, `callC2_ofFW`). -/
theorem mainSeg2L_of (hp : Scc.Lower.Accepted2 p = true) (htg : tgOkB OP = true) {Dt : State → Prop}
    (hDt : ∀ (R' : Region) (F' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (ko : Int) (σC : AS) s c',
      Spike.Lib.X64.At (Ly).exe (Ly).endPc R' F'
        (Spike.Lib.X64.PrintCall.pN (_root_.Executable.labels (Ly).exe).label Pc Qc ko σC .sys) s c' → Dt s)
    (hDtO : ∀ (R' : Region) (F' : MachineData → Prop) c s c', Spike.Lib.X64.At (Ly).exe (Ly).endPc R' F'
      (Spike.Lib.X64.Abort.N (Ly).lab Spike.Lib.X64.Abort.overflow c .sys) s c' → Dt s)
    (hDtW : ∀ (R' : Region) (F' : MachineData → Prop) c s c', Spike.Lib.X64.At (Ly).exe (Ly).endPc R' F'
      (Spike.Lib.X64.Abort.N (Ly).lab Spike.Lib.X64.Abort.write c .sys) s c' → Dt s)
    (hDtH : ∀ (R' : Region) (F' : MachineData → Prop) c s c', Spike.Lib.X64.At (Ly).exe (Ly).endPc R' F'
      (Spike.Lib.X64.Abort.N (Ly).lab Spike.Lib.X64.Abort.heap c .sys) s c' → Dt s)
    {J : InvS} (HF : FnSpecC2AtL h hp Dt J (fun _ _ => True)) : MainSeg2L h hp Dt J := by
  intro L ls hre j d hd hn R F' g cP hc hE
  haveI := (LY0).valid
  have hown := room2Own h hp
  have hrc := room2Callee h hp
  have hlc := lim2Callee h hp
  have hlok := limOk2L h hp
  have hpc := proCallG2L h hp hown hrc hlc
  have hwc := wCallG2L h hp hown
  have hcx : CxG2ML h hp Dt J L ls j R F' [] g.fp g.ra g.tp (fun c => FrameRunM p (cP, []) (c, []))
      (AbG2L h hp Dt J L ls) :=
    cxG2ML_main h hp (fp := g.fp) hd hn hre hc hE
  have hra := hc.hraK
  have hIH : ∀ g' dg, CallIn2 (FC j d hd).lcx d.body g' → p.find? (·.name == g') = some dg →
      ∃ j' : Nat, j' < j ∧ ∃ hd' : (compiled2 p)[j']? = some dg,
        FnSpecC2 (W2AtL h (imms2Me Λ p) p IsNum (rS0 (Ly)) J Dt (fun _ => 0) L ls)
          (Spike.Lib.X64.Flow.Ret0.TakeK ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL) (rS0 (Ly))) p L ls
          (MSAtL h (imms2Me Λ p) p IsNum J (ab2 p (Ly).lab) (fun _ => 0) L ls)
          (CxOkS (p := p) (lbl := L) (lsize := ls) (fnCode2OfPMe hp h Λ) (CxG2L h hp Dt J L ls)
            (fun _ _ => True) j') (FC j' dg hd') := by
    intro g' dg hci hf
    obtain ⟨j', hlt, hd'⟩ := hord_ofAccepted2 hp (fnCode2OfPMe hp h Λ) (fun j d hd => by
      rw [(fnCode2OfPMe_spec hp h Λ j d hd).1]) j d hd g' dg hci hf
    exact ⟨j', hlt, hd', HF L ls hre j' dg hd'⟩
  obtain ⟨hlane, hbuf⟩ := laneBuf2L h hp Dt J L ls j d hd R F' [] g.fp g.ra g.tp _ _ hcx hra
  refine ⟨AbG2L h hp Dt J L ls, fun JE hedge => ?_,
    callC2R_ofCxG2ML h callC2_ofFW hp hown hrc hlc hlok htg hpc hwc (Bot := fun _ _ => True) hd hcx hra
      (fun _ _ => trivial) hIH,
    hlane, hbuf,
    print2L h hp Dt hDt J L ls j d hd R F' [] g.fp g.ra g.tp _ _ hcx hra,
    callC2H_ofCxG2ML h hp hown hrc hlc hlok htg hpc (Bot := fun _ _ => True) hd hcx hra
      (fun _ _ => trivial) hIH,
    print2HL h hp Dt hDt J L ls j d hd R F' [] g.fp g.ra g.tp _ _ hcx hra,
    abG2L_seg h hp hown J L ls hre hDtO hDtW hDtH⟩
  -- `CalleePre2R` at the prologue's region `R`
  have hc' := hcx.1
  have hRb := hc'.hR
  have hhib := hc'.hhi
  have hlo' : (rbR R).lo = R.lo + 8 := rfl
  have hhi' : (rbR R).hi = R.hi + 8 := rfl
  have hb := rbR_base_inv hRb hhib
  have hrow := hown j d hd 256 ((rbR R).lo - 8) (hc'.room d hd)
  have hR8b := hc'.hR8
  have hlb := hc'.hl
  have hhb := hc'.hh
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (imms2Me Λ p) (rS := rS0 (Ly))
  have hWs := cxBlk2_ofW2 (rd := IsNum)
    (G := Spike.Lib.X64.PhRec.GOf (Ly) (Spike.Lib.X64.PhRec.m0Of (Ly).Λ OP (OUT).secs))
    (ar := Spike.Lib.X64.Rt.arOf (Ly).Λ)
    (J := Spike.Lib.AllocReach.IN (Spike.Lib.X64.Rt.arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) (Dt := Dt)
    (lbl := L) (lsize := ls) (fs := []) (fp := g.fp) (ra := g.ra)
    hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h)
    (Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp) (FC j d hd).hf (FC j d hd).h1
    hc'.hFS hRb hR8b (by omega) hhib hlb hhb (Spike.Lib.X64.Rt.rS0_sub (Ly))
    (Spike.Lib.X64.Rt.fitS_of_sub (Ly) (Spike.Lib.X64.Rt.rS0_sub (Ly))) hc'.hFO hc'.hfp hc'.hG0F
    (Cd := CD g.ra) (fun _ _ h => h) hc.hraP
    (hTg_of_tgOkB htg (fun _ _ h => h) _)
  exact
    { hcx := trivial
      hF := rbR_fstable_inv hRb hhib hc'.hFS
      hR := rbR_ok_inv hRb hhib
      hlo := by omega
      hhi := by omega
      hG0 := hc'.hG0
      hW := hWs.1
      hWp := hWs.2
      hab := fun c0 hg s c' hAt => hcx.2 s c' []
        ⟨j, d, hd, _, F', [], g.fp, g.ra, g.tp, _, hc', .inl ⟨rfl, c0, hg, hAt⟩⟩
      hg0 := .refl _
      hedge := hedge
      hR8 := by omega
      hl := by omega
      hh := by omega
      hFO := fun m hm => stackOff_of_rbR hRb hhib (hc'.hFO m hm) }

end G1MainSegL

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.mainSeg2L_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainSeg2L_of
