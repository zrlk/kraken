/-
**`main`'s segment at every reachable placement, for any `Accepted2`
program** (AArch64): `MainSeg2L` (`Spike/Lib/LowerA64/G1MainStmtL.lean`)
from every compiled block's segment at every reachable placement
(`FnSpecC2AtL`, `Spike/Lib/LowerA64/G1FnSpecL.lean`) and the write tails
at the abort stubs and the output call.

At a reachable placement `L`, `ls`, `main`'s frame with `MainCx2L` is a
base context at no suspended frames (`cxCore2_mainL`), its aborts' fragment
every base context's aborts at `L`, `ls` (`AbG2L`), so `CxG2ML` holds there.
The constructs' segments are the base context's producers at the frames
`[]`: the plain calls (`callC2R_ofCxG2ML`, the callees' segments from
`FnSpecC2AtL` at the callees, blocks before `main`'s, `hord_ofAccepted2`),
the held calls (`callC2H_ofCxG2ML`), the lane stores and buffers
(`laneBuf2L`), the output calls (`print2L`, `print2HL`), and the aborts'
segment (`abG2L_seg`). `CalleePre2R` is `calleePre2_callG2ML`'s at `main`'s
own frame: the blocks inside `W2` (`cxBlk2_ofW2`), the abort node's states
`AbG2L`'s.

- `calleePre2R_main`: `CalleePre2R` at `main`'s frame;
- `mainSeg2L_of`: `MainSeg2L`.
-/
import Spike.Lib.LowerA64.G1MainCx
import Spike.Lib.LowerA64.G1FnSpecStmtLOf
import Spike.Lib.LowerA64.G1CalleePreL
import Spike.Lib.LowerA64.G1CallC2HL
import Spike.Lib.LowerA64.G1PrintHL
import Spike.Lib.LowerA64.G1AbG2L

namespace Spike.Lib.LowerA64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region FrameRunM)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (StackOff limA pinA WcG)
open Spike.Lib.A64.Rt (rS0 arOf)
open Spike.Lib.AllocReach (Reach)
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2 imms2Me IsNum)

section G1MainSegL

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates. -/
local notation "LY0" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output. -/
local notation "OUT" => Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))

set_option hygiene false in
/-- `MSAtL` at `Closed2AtA`'s instance, placement `L`, `ls`. -/
local notation "MSL" J:max L:max ls:max => MSAtL h (imms2Me Λ p) p IsNum J (ab2 p (Ly).lab) (fun _ => 0) L ls

set_option hygiene false in
/-- `W2AtL` at `Closed2AtA`'s instance, placement `L`, `ls`. -/
local notation "W2L" J:max L:max ls:max => W2AtL h (imms2Me Λ p) p IsNum (rS0 (Ly)) J Dt (fun _ => 0) L ls

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => Spike.Lib.A64.Flow.Ret0.TakeK ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The `j`th compiled block's code facts at the theorem's immediates. -/
local notation "FC" j:max d:max hd:max => fnCode2OfPMe hp h Λ j d hd

/-- **`CalleePre2R` at `main`'s frame** (`calleePre2_callG2ML`'s fields at
`main`'s own frame): at a reachable placement `L`, `ls`, `main`'s
compiled block `j`, a callee frame with `MainCx2L` and an entry control
`cP` free of `ZBad`, at the trivial base context, the aborts `AbG2L` at
`L`, `ls`: the region facts from `cxCore2_mainL`, the region covering the
frame (`room2Own`), the blocks inside `W2` (`cxBlk2_ofW2`, the branch
targets from `tgOkB`), the abort node's states `AbG2L`'s. -/
theorem calleePre2R_main (hp : Scc.Lower.Accepted2 p = true) (htg : tgOkB OP = true) {Dt : State → Prop}
    {J : InvS} {L : WeakMem.AllocLabel → Option Nat} {ls : WeakMem.AllocLabel → Nat}
    (hre : Reach (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) L ls) {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) (hn : d.name = "main") {R : Region} {F' : MachineData → Prop}
    {g : WcG} {cP : Ctl} (hc : MainCx2L h L ls R F' g.ra g.tp) (hE : FrOk2 cP []) :
    CalleePre2R (W2L J L ls) (KT) p L ls (MSL J L ls) (fun _ _ _ _ _ _ _ _ => True) (FC j d hd)
      (rS0 (Ly)) R F' [] g.fp g.ra g.tp (fun c => FrameRunM p (cP, []) (c, [])) (AbG2L h hp Dt J L ls) cP := by
  have hC : CxCore2L h hp Dt J L ls j R F' [] g.fp g.ra g.tp (fun c => FrameRunM p (cP, []) (c, [])) :=
    cxCore2_mainL h hp hre hd hn hc hE
  have hlo0 := room2Own h hp j d hd 256 R.lo (hC.room d hd)
  have hlo : R.lo ≤ -((FC j d hd).cx.frame : Int) := by omega
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (imms2Me Λ p) (rS := rS0 (Ly))
  have hWs := cxBlk2_ofW2 (rd := IsNum)
    (G := Spike.Lib.A64.PhRec.GOf (Ly) (Spike.Lib.A64.PhRec.m0Of (Ly).Λ OP (OUT).secs))
    (ar := Spike.Lib.A64.Rt.arOf (Ly).Λ)
    (J := Spike.Lib.AllocReach.IN (Spike.Lib.A64.Rt.arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) (Dt := Dt)
    (lbl := L) (lsize := ls) (fs := []) (fp := g.fp) (ra := g.ra)
    hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h)
    (Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp) (FC j d hd).hf (FC j d hd).h1 (FC j d hd).h16
    hC.hFS hC.hR hC.hal hlo hC.hhi hC.hl hC.hh (Spike.Lib.A64.Rt.rS0_sub (Ly))
    (Spike.Lib.A64.Rt.fitS_of_sub (Ly) (Spike.Lib.A64.Rt.rS0_sub (Ly))) hC.hFO hC.hfp hC.hG0F
    (Cd := CdCLE OP (Spike.Lib.A64.PhRec.okPc LY0) (Spike.Lib.A64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec g.ra))
    (fun _ _ h => h) hc.hraP
    (hTg_of_tgOkB htg (FC j d hd).hf (FC j d hd).h1 (FC j d hd).h16 (fun _ _ h => h) _)
  exact
    { hcx := trivial
      hF := hC.hFS
      hR := hC.hR
      hal := hC.hal
      hlo := hlo
      hhi := hC.hhi
      hG0 := hC.hG0
      hW := hWs.1
      hWp := hWs.2
      hab := fun c0 hg s c' hAt => ⟨j, d, hd, R, F', [], g.fp, g.ra, g.tp, _, hC, .inl ⟨rfl, c0, hg, hAt⟩⟩
      hg0 := .refl _
      hl := hC.hl
      hh := hC.hh
      hFO := hC.hFO }

/-- **`main`'s segment at every reachable placement** (`MainSeg2L`, see the
module docstring): from every compiled block's segment at every reachable
placement at the records `fun _ _ => True` (`HF`), the branch-target check
(`htg`) and the write tails at the output call's `svc` (`hDt`) and the abort
stubs' (`hDtO`, `hDtW`, `hDtH`); the aborts' fragment `AbG2L` at the
placement. -/
theorem mainSeg2L_of (hp : Scc.Lower.Accepted2 p = true) (htg : tgOkB OP = true) {Dt : State → Prop}
    (hDt : ∀ (R' : Region) (F' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (σC : AS) s c',
      Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc R' F'
        (Spike.Lib.A64.Flow.PrintCall.pN (_root_.Executable.labels (Ly).exe).label Pc Qc σC .svc) s c' → Dt s)
    (hDtO : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (Ly).exe (Ly).endPc R' F'
      (A64.Abort.N (Ly).lab A64.Abort.overflow c .svc) s c' → Dt s)
    (hDtW : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (Ly).exe (Ly).endPc R' F'
      (A64.Abort.N (Ly).lab A64.Abort.write c .svc) s c' → Dt s)
    (hDtH : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (Ly).exe (Ly).endPc R' F'
      (A64.Abort.N (Ly).lab A64.Abort.heap c .svc) s c' → Dt s)
    (J : InvS) (HF : FnSpecC2AtL h hp Dt J (fun _ _ => True)) : MainSeg2L h hp Dt J := by
  intro L ls hre j d hd hn R F' g cP hc hE
  have hown := room2Own h hp
  have hrc := room2Callee h hp
  have hlc := lim2Callee h hp
  have hlok := limOk2L h hp
  have hpc := proCallG2L h hp hown hrc hlc
  have hwc := wCallG2L h hp hown
  have hC : CxCore2L h hp Dt J L ls j R F' [] g.fp g.ra g.tp (fun c => FrameRunM p (cP, []) (c, [])) :=
    cxCore2_mainL h hp hre hd hn hc hE
  have hcx : CxG2ML h hp Dt J L ls j R F' [] g.fp g.ra g.tp (fun c => FrameRunM p (cP, []) (c, []))
      (AbG2L h hp Dt J L ls) := ⟨hC, fun _ _ _ h' => h'⟩
  have hIH : ∀ g' dg, CallIn2 (FC j d hd).lcx d.body g' → p.find? (·.name == g') = some dg →
      ∃ j' : Nat, j' < j ∧ ∃ hd' : (compiled2 p)[j']? = some dg,
        FnSpecC2 (W2L J L ls) (KT) p L ls (MSL J L ls)
          (CxOkS (p := p) (lbl := L) (lsize := ls) (fnCode2OfPMe hp h Λ) (CxG2L h hp Dt J L ls)
            (fun _ _ => True) j') (FC j' dg hd') := by
    intro g' dg hcl hf
    obtain ⟨j', hj', hd'⟩ := hord_ofAccepted2 hp (fnCode2OfPMe hp h Λ)
      (fun j d hd => by rw [(fnCode2OfPMe_spec hp h Λ j d hd).1]) j d hd g' dg hcl hf
    exact ⟨j', hj', hd', HF L ls hre j' dg hd'⟩
  obtain ⟨hlane, hbuf⟩ := laneBuf2L h hp Dt J L ls j d hd R F' [] g.fp g.ra g.tp _ _ hcx hc.hraK
  exact ⟨AbG2L h hp Dt J L ls, calleePre2R_main h hp htg hre hd hn hc hE,
    callC2R_ofCxG2ML h callC2_ofFW hp hown hrc hlc hlok htg hpc hwc hd hcx hc.hraK (fun _ _ => trivial) hIH,
    hlane, hbuf,
    print2L h hp Dt hDt J L ls j d hd R F' [] g.fp g.ra g.tp _ _ hcx hc.hraK,
    callC2H_ofCxG2ML h hp hown hrc hlc hlok htg hpc hd hcx hc.hraK (fun _ _ => trivial) hIH,
    print2HL h hp Dt hDt J L ls j d hd R F' [] g.fp g.ra g.tp _ _ hcx hc.hraK,
    abG2L_seg h hp hown J L ls hre hDtO hDtW hDtH⟩

end G1MainSegL

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.calleePre2R_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.calleePre2R_main

/-- info: 'Spike.Lib.LowerA64.mainSeg2L_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.mainSeg2L_of
