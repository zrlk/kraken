/-
**The bare start's `h0`: the start's segment without a setup block**
(x86-64; the twin of `Spike/Lib/LowerA64/G1NoSetupH0.lean`): from `_start`
through `scc_rt_main` at `bareMC` (`startUF_segWSF`,
`Spike/Lib/LowerX64/G1NoSetupRt.lean`), `scc_rt_main`'s own states inside
`W2At` (`mainUW_ofPlaceOKU`, `hWx_ofPlaceOKU`,
`Spike/Lib/LowerX64/G1NoSetupMain.lean`), and `H0InW`
(`Spike/Lib/LowerX64/Closed2AtW.lean`) from `main`'s call `HU0X`
(`Spike/Lib/LowerX64/G1NoSetupDefs.lean`).

- `hstk0_of_placeOKAt`: `scc_rt_main`'s grow stub label in the code
  without a setup block (A12 at `mainThread0 ⟨.unit, true⟩ 0`);
- `hfn0_of_placeOKAt`: `main`'s label off the write abort (its prologue's
  head, `mainHead_ofPlaceOK`);
- `h0_ofPlaceOK_bareF`: the start's segment inside `W2At` at a placed
  output without a setup block, `main`'s call `UserCallWSF` under the extra
  frame `Fw` after the switch;
- `h0InW_bare`: `H0InW` from `main`'s call `HU0X` at some `Bounds0X`.
-/
import Spike.Lib.LowerX64.G1NoSetupMain
import Spike.Lib.LowerX64.G1NoSetupDefs
import Spike.Lib.LowerX64.G1NoSetupCallStmt
import Spike.Lib.LowerX64.G1NoSetupCallA
import Spike.Lib.LowerX64.H0InSetupVBF
import Spike.Lib.LowerX64.SetupCodeOf
import Spike.Lib.LowerX64.StkOf

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open A9NoSpawn Scc.Cert.WideX64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (swR FStable)
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.AllocReach (Reach IN)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Spike.Lib.X64.Rt (MainUW mainUIn bareMC UserCallWSF swFSL rS0 entryR rtF arOf)
open Spike.Lib.X64.Rt.MainU (MainPh)

/-! ## The code facts -/

/-- **`scc_rt_main`'s grow stub label is in the code without a setup
block** (the twin of `hstk_of_placeOKAt`): A12 at `mainThread0 ⟨.unit, true⟩ 0`,
a stack-checked function of the lowered IR. -/
theorem hstk0_of_placeOKAt {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : CoreTerm.Prog}
    {sizes : List Nat} {labelOffs : List (String × Nat)} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (hp : Scc.Lower.Accepted2 p = true) (hs : Scc.Lower.setupOf p = none) :
    Scc.Cert.Rt.X64.InRunB (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog
      ".Lscc_rt_main.stk" 0 := by
  obtain ⟨n, hn⟩ := mem_starts _ 0 (mainThread0_bare h hp hs)
  have h12 := Scc.Cert.PlaceOK.X64.fnCode1_of_placeOKAt h (Scc.Cert.PlaceOK.X64.place_ir_ofEmitted _ _ _)
  exact inRunB_proL_of_fnOk1 (Scc.Cert.Code1X64.fnOk1_of_fnCode1Ok h12 hn rfl)

/-- **`main`'s label is a position off the write abort** at an `Accepted2`
output passing `placeOKAt`: its prologue's head at offset `0`
(`mainHead_ofPlaceOK`), the label none of the write abort's. -/
theorem hfn0_of_placeOKAt {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : CoreTerm.Prog}
    {sizes : List Nat} {labelOffs : List (String × Nat)} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (hp : Scc.Lower.Accepted2 p = true) (lab : Label → Int64) :
    PosOff (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog lab (lab bareMC.fn) := by
  have hfnB : Scc.Cert.Rt.X64.blockAtB (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog
      bareMC.fn 0 Spike.Lib.X64.Flow.xHead = true := mainHead_ofPlaceOK hp h 0
  have h' := posOff_of_blockAtB (lab := lab) hfnB (by decide) (by decide)
  rwa [Spike.Lib.X64.Flow.ofNat_zero'] at h'

/-! ## At a placed output -/

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.X64.placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h i

/-- **The consumer's `h0` at a placed output without a setup block, `main`
returning at held frames placed by its value, with an extra frame `Fw`
after the switch** (`startUF_segWSF`): `scc_rt_start`'s states from
`startEW_w2G` (under `Fw`, `StartEW.toF`), `scc_rt_main`'s from
`mainUW_ofPlaceOKU` and `hWx_ofPlaceOKU`, `main`'s exit from `UPostRF`
(`uPostRF_exit`). Left: the entry's frame condition `FE` (`hFE`, `hFEs`,
`hFEk`) and `Fw` (`hFw`, `hFwS`), the start control's facts (`hf0`, `hov`,
`hC0`, `hpl0`), the switch depth (`hL`, `hLm`, `hL8`), `scc_rt_main`'s code
and phase facts and its two targets (`hin`, `hph`, `hgrow`, `hfn`), `main`'s
room `D` and limit room `ZU` (`hD0`, `hD8`, `hLD`, `hZM`, `hZU`), the
post's facts (`hPU`, `hPost`) and `main`'s call (`hU`). -/
theorem h0_ofPlaceOK_bareF {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {ab : Option (State → Prop)} {c0 : Ctl} {L : Int} {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ)
    {FE : MachineData → Prop} (hFE : ∀ m, FE m → rtF (Ly) m) (hFEs : FStable (entryR E) FE)
    (hFEk : ∀ m pm, FE m → FE (takeMem pm (rS0 (Ly)) m))
    {Fw : _root_.Mem 64 → Prop} (hFw : ∀ m, FE m → Fw m.dmem)
    (hFwS : ∀ v, FStable (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
      (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m))
    (hp : ProgNoS ZBad p) (hf0 : FrOk2 c0 []) (hov : ¬ OvfReady c0) (hC0 : CFacts (Ly).Λ lbl0 c0)
    (hpl0 : ∀ s, PlacedS (Ly).Λ (fun _ => none) s c0 [])
    (hL : 8 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0)
    (hin : mainUIn (Ly).prog bareMC = true)
    (hph : MainPh (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (Ly).lab bareMC)
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab bareMC.grow))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab bareMC.fn))
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) {ZU : Int64} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hLD : 8 + 8 + bareMC.Z.toInt + 8 + D ≤ L)
    (hZM : (Ly).stacksA.toNat + 4096 ≤
      (stacksA (Ly).lab + 0#64 + 16384#64 - 8#64 - 8#64 - bareMC.Z.toBitVec).toNat)
    (hZU : (Ly).stacksA.toNat + 4096 ≤ (stacksA (Ly).lab + 0#64 + 16384#64 - 8#64 - 8#64 - bareMC.Z.toBitVec -
      8#64 - 8#64 - ZU.toBitVec).toNat)
    (hPU : ∀ c fs v, Post c fs v → UPostRF p (fun _ => none) c fs v)
    (hPost : ∀ c fs v, Post c fs v → MainCtlV (Ly).Λ (fun _ => none) c fs v)
    (hU : ∀ v, UserCallWSF (W2At h i p rd (rS0 (Ly)) J Dt ls0) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSAt h i p rd J ab ls0) (Ly).exe (Ly).endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => (Fw m.dmem ∧ swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m) ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      bareMC.fn bareMC.Z D ZU Post ((Ly).lab bareMC.sp0).toBitVec c0
      (tpOf (pinA (Ly).lab + 0#64 + 8#64))) :
    SegWS (W2At h i p rd (rS0 (Ly)) J Dt ls0) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p (fun _ => none)
      (MSAt h i p rd J ab ls0)
      ((Spike.Lib.X64.At (Ly).exe (Ly).endPc (entryR E) FE (Spike.Lib.X64.Rt.entryN0 (Ly).lab c0)).at [])
      fun _ _ _ => False := by
  have hZ := bareMC_Z
  have hsub := Spike.Lib.X64.Rt.rS0_sub (Ly)
  have hL0 : (0 : Int) ≤ L := by omega
  have hWx := hWx_ofPlaceOKU h i (rd := rd) (J := J) (Dt := Dt) (ls0 := ls0) (Fw := Fw) hp hL hLm hL8 hin hph
    hgrow hfn (by omega) hC0 hov hPost
  have hW := mainUW_ofPlaceOKU h i (rd := rd) (J := J) (Dt := Dt) (lbl0 := lbl0) (ls0 := ls0) (ab := ab)
    (Fw := Fw) (Post := fun c v => Post c [] v) hp hL hLm hL8 hin hph hgrow hfn (by omega) hC0
    ⟨hf0, hov, hpl0⟩ fun v => hWx v []
  have hpl : ∀ s c, Placed (Ly).Λ (fun _ => none) s c → (MSAt h i p rd J ab ls0 []).pl s c := by
    intro s c hP; cases ab <;> exact ⟨rfl, hP⟩
  obtain ⟨hhdr, htcb, hfld, htk⟩ := rows_ofPlaceOK h i (p := p) (rd := rd) (ar := arOf (Ly).Λ)
    (J := IN (arOf (Ly).Λ) (fun _ => none) ls0 J) (ab := ab) (lsize := ls0) hFE
  have h8 : (stacksA (Ly).lab + 0#64 + 16384#64).toNat % 8 = 0 := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
  have hok : (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).OK := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ hL0 hLm
  exact Spike.Lib.X64.Rt.startUF_segWSF (Ly).lays rfl (Spike.Lib.X64.Rt.rtCodeTi_of_placeOKAt h) msOfAX_K_abi hFEs
    (Spike.Lib.X64.Rt.entryR_ok hE) (Spike.Lib.X64.Rt.entryR_al hE) (by show (-65536 : Int) ≤ -304; decide)
    (by show (0 : Int) ≤ 0; decide) 0#64 0#64 c0 (by decide) hhdr htcb (by decide) hfld htk hok
    (by rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rS0_subRD _ hL0 hLm)
    (hun_ofPlaceOK h i hFE) hFw hFwS (Spike.Lib.X64.Rt.rS_of_sub _ hE hsub) (Spike.Lib.X64.Rt.fitS_of_sub _ hsub)
    (Spike.Lib.X64.Rt.outS_of_sub _ hE hsub) hFEk
    (Spike.Lib.X64.Rt.StartEW.toF (startEW_w2G h i (lbl0 := lbl0) (J := IN (arOf (Ly).Λ) (fun _ => none) ls0 J)
      (Dt := Dt) (lsize := ls0)
      hp hf0 hov hC0 (Spike.Lib.X64.Rt.entryR_ok hE) (by show (-65536 : Int) ≤ -304; decide)
      (by show (0 : Int) ≤ 0; decide) hFE (by rw [Spike.Lib.X64.Rt.stacksA_lab0]) hsub
      (Spike.Lib.X64.Rt.outS_of_sub _ hE hsub) h8 hok hL hL8 (by decide) hpl0) Fw)
    hin (by rw [hZ]; decide) (by rw [hZ]; decide) (by decide) (by decide) hD0 hD8 hLD hL8
    (limOk_ofPlaceOK h i hZM) (limOk_ofPlaceOK h i hZU) hU
    (fun R' F' s c fs v hP hAt => uPostRF_exit (Λ := (Ly).Λ) hpl R' F' s c fs v (hPU c fs v hP) hAt)
    hW hWx

end Place

/-! ## `H0InW` -/

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Spike.Lib.LowerNode.imms2Me Λ p)

set_option hygiene false in
/-- The program's start control (`S0X`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).env, none⟩ : Ctl)

/-- **`H0InW` for an `Accepted2` program without a setup block**
(`h0_ofPlaceOK_bareF` at `FE := WordsNone ∧ rtF`, `Fw := WordsNone`,
`rd := IsNum`, `ls0 := 0`, `ab := ab2` and the program's start control,
which is `c0`, `c0_start_none`): `main`'s call from `HU0X` at the bounds
`Bounds0X` (`hB`), the stack grow stub and `main`'s label from the
placement check (`hstk0_of_placeOKAt`, `hfn0_of_placeOKAt`), the phase
facts at the bare tail (`mainPh_bare_ofPlaceOK`). -/
theorem h0InW_bare {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) (hs : Scc.Lower.setupOf p = none)
    (hE : E.Ok (lay2 Λ p)) {L D : Int} {lM : String} {fM nM : Nat}
    (hB : Bounds0X cfg p sizes labelOffs (Ly) L D lM fM nM) (hU : HU0X h E El Dt) :
    H0InW h E El Dt := by
  obtain ⟨-, -, -, -, -, -, hL, hLm, hL8, hD0, hD8, hLD, hZM, hZU, -⟩ := id hB
  have hwf := wf_link_of_placeOKAt (Spike.Lib.LowerNode.imms2Me Λ p) h
  have he := c0_start_none hs (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))
  have hf0 : FrOk2 C0 [] := by rw [he]; exact frOk2_c0
  have hov : ¬ OvfReady C0 := by
    rw [he]; rintro ⟨_, _, _, _, _, _, _, _, _, _, ht, -⟩; cases ht
  have hC0 : CFacts (lay2 Λ p) (fun _ => none) C0 := by
    rw [he]; exact Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0
  have hpl0 : ∀ s, PlacedS (lay2 Λ p) (fun _ => none) s C0 [] := by
    rw [he]; exact fun _ => placedS_c0
  have hL0 : (0 : Int) ≤ L := by omega
  have htl := tail_bare_of_accepted2 h hp hs
  have hin := mainUIn_bare2 h hp hs
  refine ⟨fun J hJ => h0_ofPlaceOK_bareF h (Spike.Lib.LowerNode.imms2Me Λ p) (rd := Spike.Lib.LowerNode.IsNum)
    (J := J) (Dt := Dt) (ls0 := fun _ => 0) (ab := ab2 p (Ly).lab) hE
    (FE := fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧ rtF (Ly) m) (fun _ hm => hm.2)
    (Spike.Lib.X64.Alloc.wordsNone_and_fstable hwf hE.1 (Spike.Lib.X64.Rt.entryR_ok hE)
      (.inl (Spike.Lib.cellsR_entry hE)) (Spike.Lib.X64.Rt.rtF_stable _ hE)).1
    (fun _ _ hm => ⟨Spike.Lib.X64.Rt.wordsNone_takeMem hwf (Spike.Lib.X64.Rt.rS0_sub _) hm.1,
      Spike.Lib.X64.Rt.rtF_takeMem _ (Spike.Lib.X64.Rt.rS0_sub _) hm.2⟩)
    (Fw := Spike.Lib.DmemPriv.WordsNone (Ly).Λ) (fun _ hm => hm.1)
    (fun _ => Spike.Lib.X64.Rt.wordsNone_swFSL_fstable hwf (Spike.Lib.X64.Rt.rS0_sub _)
      (by rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ hL0 hLm) hL hL8
      (by rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rS0_subRD _ hL0 hLm)
      (by rw [Spike.Lib.X64.Rt.pinA_lab0]; exact Spike.Lib.X64.Rt.rt_hfit _)
      (by rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_houtD _ hL0 hLm)
      (Spike.Lib.X64.Rt.fitS_of_sub _ (Spike.Lib.X64.Rt.rS0_sub _)))
    (Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp) hf0 hov hC0 hpl0 hL hLm hL8 hin
    (Spike.Lib.X64.Rt.PhRecOf.mainPh_bare_ofPlaceOK h _ htl)
    ⟨".Lscc_rt_main.stk", 0, hstk0_of_placeOKAt h hp hs, by decide, by simp [bareMC]⟩
    (hfn0_of_placeOKAt h hp _) hD0 hD8 hLD hZM hZU (fun _ _ _ h => h.1) (fun _ _ _ h => h.2)
    (hU L D lM fM nM hB J hJ)⟩

end Assembled

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hstk0_of_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hstk0_of_placeOKAt

/-- info: 'Spike.Lib.LowerX64.hfn0_of_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hfn0_of_placeOKAt

/-- info: 'Spike.Lib.LowerX64.h0_ofPlaceOK_bareF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h0_ofPlaceOK_bareF

/-- info: 'Spike.Lib.LowerX64.h0InW_bare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h0InW_bare

end Spike.Lib.LowerX64
