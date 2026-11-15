/-
**The bare start's `h0`** (AArch64): the consumer's start segment of an
`Accepted2` program without a setup block inside `W2`, at the start's frame
condition `WordsNone ∧ rtF` (`H0InAW`, `Spike/Lib/LowerA64/Closed2AtWA.lean`),
over `startUF_segWSF` (`Spike/Lib/LowerA64/G1NoSetupRt.lean`): `_start` to
the switch as after a setup block (`startEW_w2G`), then `scc_rt_main` at
`bareMC` (`Spike/Lib/LowerA64/G1NoSetupMain.lean`) calling `main` directly,
`main` returning at held frames placed by its value.

- `hstk0A_of_placeOKAt`: `scc_rt_main`'s grow stub label in the code
  without a setup block (`hstkA_of_placeOKAt` at `mainThread0 ⟨.unit, true⟩ 0`);
- `hfn0A_of_placeOKAt`: `main`'s label a position off the write abort;
- `h0_ofPlaceOK_bareF`: the start's segment at a placed output, from
  `main`'s call `UserCallWSF` under the extra frame `Fw` after the switch;
- `h0InAW_bare`: `H0InAW` from `main`'s call `HU0A` at some `Bounds0A`.
-/
import Spike.Lib.LowerA64.G1NoSetupMain
import Spike.Lib.LowerA64.G1NoSetupDefs
import Spike.Lib.LowerA64.G1NoSetupCallStmt
import Spike.Lib.LowerA64.RtMainXNBF
import Spike.Lib.LowerA64.SetupCodeOf
import Spike.Lib.Rt.A64SwWordsNone

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Rt (MainUW mainUIn bareMC UserCallWSF swFSL rS0 entryR rtF arOf)
open Spike.Lib.A64.Rt.MainU (MainPh)
open Spike.Lib.A64.AllocG (abLabs)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Spike.Lib.AllocReach (Reach IN)
open Scc.Cert.Code1A64 (ctxOf fnOk1_of_fnCode1Ok)
open Spike.Lib.A64.Flow.Ret0 (blkW_mono nodeW_mono proW_mono)

/-! ## The code facts -/

/-- **`scc_rt_main`'s grow stub label is in the code without a setup
block** (the twin of `hstkA_of_placeOKAt`): A12 at `mainThread0 ⟨.unit, true⟩ 0`,
a function of the lowered IR with stack growth. -/
theorem hstk0A_of_placeOKAt {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : CoreTerm.Prog}
    {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (hp : Scc.Lower.Accepted2 p = true) (hs : Scc.Lower.setupOf p = none) :
    Scc.Cert.Rt.A64.InRun (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog ".L1_scc_rt_main.stack_grow" 0 := by
  obtain ⟨em, hem⟩ := lowerAll?_ok_of_placeOKC h
  obtain ⟨ws, rt, -, hrt, -, hir, -⟩ := Spike.Lib.LowerNode.lowerAll_accepted2_a64 cfg hp hem
  have he : Spike.Lib.LowerNode.entry2 p = ⟨.unit, true⟩ := by simp [Spike.Lib.LowerNode.entry2, hs]
  have hw : Spike.Lib.LowerNode.setupWords2 p = 0 := by simp [Spike.Lib.LowerNode.setupWords2, hs]
  have hmk : Spike.Lib.LowerNode.setupMask2 p = [] := by simp [Spike.Lib.LowerNode.setupMask2, hs]
  rw [he, hw, hmk] at hrt
  generalize hir' : (Scc.Lower.A64.lowerAll cfg p).low.ir = ir at hir
  have hf : (Scc.Lower.Inv.mainThread0 ⟨.unit, true⟩ 0 [], 1) ∈ ir.funcs.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, hir]
    simp only [Scc.Lower.Inv.progOf]
    have h1 := mainThread0_idx hrt
    have hlt : 1 < rt.length := (List.getElem?_eq_some_iff.mp h1).1
    rw [List.getElem?_append_left hlt, h1]
  have h12 := Scc.Cert.PlaceOK.A64.fnCode1_of_placeOKAt h
    ((Scc.Cert.PlaceOK.A64.place_ir_ofEmitted _).trans (congrArg some hir'))
  have hok := fnOk1_of_fnCode1Ok h12 hf rfl
  have hm : (ctxOf ir 1 (Scc.Lower.Inv.mainThread0 ⟨.unit, true⟩ 0 [])).maps = true := by
    show ir.growth.isSome = true
    rw [hir]; rfl
  have hL := inRun_proL_of_fnOk1 hok
  simp only [proL, hm, ↓reduceIte, mainLocal] at hL
  exact hL

/-- **`main`'s label is a position off the write abort** at an `Accepted2`
output passing `placeOKAt`: its prologue (`mainPro_ofPlaceOK`) puts its
stack check's head right after the label, off the write abort's labels. -/
theorem hfn0A_of_placeOKAt {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : CoreTerm.Prog}
    {Λ : Scc.Sem.Layout} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe]
    {kp : Nat} (hl : Scc.Cert.Rt.A64.Lays exe (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog kp)
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (hp : Scc.Lower.Accepted2 p = true) :
    PosOff (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog (_root_.Executable.labels exe).label
      ((_root_.Executable.labels exe).label bareMC.fn) := by
  obtain ⟨chk, entry, Z, lim, Lg, ps, hpr, hab⟩ := mainPro_ofPlaceOK hp h 0
  simp only [prologueIn, Bool.and_eq_true] at hpr
  have hb := posOff_of_blockAt (lab := (_root_.Executable.labels exe).label) hpr.1.1.1.1.2 hab (i := 0)
    (by simp [chkHead])
  rw [show 4 * (0 + 0) = 4 * 0 from rfl, ofNat4_zero] at hb
  exact posOff_of_labelGap hl hpr.1.1.1.1.1 hb

/-! ## At a placed output -/

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.A64.placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h i

open Spike.Lib.A64.Flow.Ret0 in
/-- **The consumer's `h0` at a placed output without a setup block, `main`
returning at held frames placed by its value, with an extra frame `Fw`
after the switch** (`startUF_segWSF`): `scc_rt_start`'s states from
`startEW_w2G` (under `Fw`, `startEWF_of`), `scc_rt_main`'s from
`mainUW_ofPlaceOKU` and `hWx_ofPlaceOKU` (under `Fw`, `blkW_mono`,
`nodeW_mono`, `proW_mono`), `main`'s exit from `UPostRF` (`uPostRF_exit`).
Left: the entry's frame condition `FE` (`hFE`, `hFEs`, `hFEk`) and `Fw`
(`hFw`, `hFwS`), the start control's facts (`hf0`, `hov`, `hC0`, `hpl0`),
the switch depth (`hL0`, `hL`, `hL8`), `scc_rt_main`'s code and phase
facts and its two targets (`hin`, `hph`, `hgrow`, `hfn`), `main`'s room
`D` and limit room `ZU` (`hD0`, `hD8`, `hLD`, `hZM`, `hZU`), the post's
facts (`hPU`, `hPost`) and `main`'s call (`hU`). -/
theorem h0_ofPlaceOK_bareF {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {ab : Option (State → Prop)} {c0 : Ctl} {L : Int} {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ)
    {FE : MachineData → Prop} (hFE : ∀ m, FE m → rtF (Ly) m) (hFEs : FStable (entryR E) FE)
    (hFEk : ∀ m pm, FE m → FE (takeMem pm (rS0 (Ly)) m))
    {Fw : _root_.Mem 64 → Prop} (hFw : ∀ m, FE m → Fw m.dmem)
    (hFwS : ∀ v, FStable (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
      (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v m))
    (hp : ProgNoS ZBad p) (hf0 : FrOk2 c0 []) (hov : ¬ OvfReady c0) (hC0 : CFacts (Ly).Λ lbl0 c0)
    (hpl0 : ∀ s, PlacedS (Ly).Λ (fun _ => none) s c0 [])
    (hL0 : 0 ≤ L) (hL : L ≤ 16384) (hL8 : L % 8 = 0)
    (hin : mainUIn (Ly).prog bareMC = true)
    (hph : MainPh (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (Ly).lab bareMC)
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab bareMC.grow))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab bareMC.fn))
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) {ZU : Int64} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hLD : bareMC.Z.toInt + D ≤ L)
    (hZM : (Ly).stacksA.toNat + 4096 ≤ (stacksA (Ly).lab + 0#64 + 16384#64 - bareMC.Z.toBitVec).toNat)
    (hZU : (Ly).stacksA.toNat + 4096 ≤
      (stacksA (Ly).lab + 0#64 + 16384#64 - bareMC.Z.toBitVec - ZU.toBitVec).toNat)
    (hPU : ∀ c fs v, Post c fs v → UPostRF p (fun _ => none) c fs v)
    (hPost : ∀ c fs v, Post c fs v → MainCtlV (Ly).Λ (fun _ => none) c fs v)
    (hU : ∀ v, UserCallWSF (W2At h i p rd (rS0 (Ly)) J Dt ls0) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSAt h i p rd J ab ls0) (Ly).exe (Ly).endPc
      (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v m)
      bareMC.fn bareMC.Z D ZU Post ((Ly).lab bareMC.e0 + 4).toBitVec c0
      (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) :
    SegWS (W2At h i p rd (rS0 (Ly)) J Dt ls0) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p (fun _ => none)
      (MSAt h i p rd J ab ls0)
      ((Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc (entryR E) FE (entryN (Ly).lab c0)).at [])
      fun _ _ _ => False := by
  have hZ := bareMC_Z
  have hWx := hWx_ofPlaceOKU h i (rd := rd) (J := J) (Dt := Dt) (ls0 := ls0) hp hL0 hL hL8 hin hph
    hgrow hfn (by omega) hC0 hov hPost
  have hW := mainUW_ofPlaceOKU h i (rd := rd) (J := J) (Dt := Dt) (lbl0 := lbl0) (ls0 := ls0) (ab := ab)
    (Post := fun c v => Post c [] v) hp hL0 hL hL8 hin hph hgrow hfn (by omega) hC0 ⟨hf0, hov, hpl0⟩
    fun v => hWx v []
  have hWF : ∀ v, MainUW (Spike.Lib.A64.Rt.nilW (W2At h i p rd (rS0 (Ly)) J Dt ls0))
      (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) (Ly).exe (Ly).endPc
      (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v m) (MSAt h i p rd J ab ls0 [])
      bareMC (fun c v => Post c [] v)
      ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩ := fun v =>
    ⟨proW_mono (hW v).pro fun _ h => h.2, blkW_mono (hW v).call fun _ h => h.2,
      ⟨blkW_mono (hW v).exit.w0 fun _ h => h.2, nodeW_mono (hW v).exit.w1 fun _ h => h.2⟩⟩
  have h16 : bareMC.Z.toInt % 16 = 0 := by rw [hZ]; decide
  have hZ16 : 16 ≤ bareMC.Z.toInt := by rw [hZ]; decide
  have hk : Spike.Lib.offOk (-bareMC.Z.toInt) 0 (-bareMC.Z.toInt + bareMC.k.toInt) = true := by
    simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ, bareMC_k]; refine ⟨?_, ?_, ?_⟩ <;> omega
  have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
  have hSM := stackM_rS0 (Ly) hE
  obtain ⟨hhdr, htcb, hfld, htk⟩ := rows_ofPlaceOK h i (p := p) (rd := rd) (ar := Spike.Lib.A64.Rt.arOf (Ly).Λ)
    (J := IN (Spike.Lib.A64.Rt.arOf (Ly).Λ) (fun _ => none) ls0 J) (ab := ab) (lsize := ls0) hFE
  have h16t : (stacksA (Ly).lab + 0#64 + 16384#64).toNat % 16 = 0 := by
    rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_h16 _
  have hok : (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).OK := by
    rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hL
  exact Spike.Lib.A64.Rt.startUF_segWSF (Ly).lays rfl (Spike.Lib.A64.Rt.rtCode0_of_placeOKAt h) msOfAX_K_abi hFEs
    (Spike.Lib.A64.Rt.entryR_ok hE) (Spike.Lib.A64.Rt.entryR_al hE) (by show (-65536 : Int) ≤ -304; decide)
    (by show (0 : Int) ≤ 0; decide) 0#64 0#64 c0 (by decide) hhdr htcb (by simp) hfld htk h16t hok
    (by rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rS0_subRD _ hL0 hL)
    (hun_ofPlaceOK h i hFE) hFw hFwS (Spike.Lib.A64.Rt.rS_of_sub _ hE hsub) (Spike.Lib.A64.Rt.fitS_of_sub _ hsub)
    (Spike.Lib.A64.Rt.outS_of_sub _ hE hsub) hFEk
    (startEWF_of (startEW_w2G h i (lbl0 := lbl0) (J := IN (Spike.Lib.A64.Rt.arOf (Ly).Λ) (fun _ => none) ls0 J)
      (Dt := Dt) (lsize := ls0) (L := L) hp hf0 hov hC0 (Spike.Lib.A64.Rt.entryR_ok hE)
      (Spike.Lib.A64.Rt.entryR_al hE) (by show (-65536 : Int) ≤ -304; decide) (by show (0 : Int) ≤ 0; decide) hFE
      (rS0_eq_lab _) hsub hSM.1 hSM.2.1 hSM.2.2 (Spike.Lib.A64.Rt.fitS_of_sub _ hsub) h16t hok hL8 (by simp) hpl0))
    hin h16 hZ16 hk hD0 hD8 hLD (limOk_ofPlaceOK h i hZM) (limOk_ofPlaceOK h i hZU) hU
    (fun R' F' s c fs v hP hAt => uPostRF_exit R' F' s c fs v (hPU c fs v hP) hAt) hWF
    fun v fs => ⟨blkW_mono (hWx v fs).w0 fun _ h => h.2, nodeW_mono (hWx v fs).w1 fun _ h => h.2⟩

end Place

/-! ## `H0InAW` -/

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Spike.Lib.LowerNode.imms2Me Λ p)

set_option hygiene false in
/-- The program's start control (`S0A`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).env, none⟩ : Ctl)

/-- **`H0InAW` for an `Accepted2` program without a setup block**
(`h0_ofPlaceOK_bareF` at `FE := WordsNone ∧ rtF`, `Fw := WordsNone`,
`rd := IsNum`, `ls0 := 0`, `ab := ab2` and the program's start control,
which is `c0`, `c0_start_none`): `main`'s call from `HU0A` at the bounds
`Bounds0A` (`hB`), the stack grow stub and `main`'s label from the
placement check (`hstk0A_of_placeOKAt`, `hfn0A_of_placeOKAt`), the phase
facts at the bare tail (`hmph_ofPlaceOK`). -/
theorem h0InAW_bare {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) (hs : Scc.Lower.setupOf p = none)
    (hE : E.Ok (lay2 Λ p)) {L D : Int} {lM : String} {fM nM : Nat}
    (hB : Bounds0A cfg p (Ly) L D lM fM nM) (hU : HU0A h E El Dt) :
    H0InAW h E El Dt := by
  obtain ⟨-, -, -, -, -, hL0, hLm, hL8, hD0, hD8, hLD, hZM, hZU, -⟩ := id hB
  have hwf := wf_link_of_placeOKAt (Spike.Lib.LowerNode.imms2Me Λ p) h
  have he := c0_start_none hs (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))
  have hf0 : FrOk2 C0 [] := by rw [he]; exact frOk2_c0
  have hov : ¬ OvfReady C0 := by
    rw [he]; rintro ⟨_, _, _, _, _, _, _, _, _, _, ht, -⟩; cases ht
  have hC0 : CFacts (lay2 Λ p) (fun _ => none) C0 := by
    rw [he]; exact Spike.Lib.A64.Flow.Ret0.Inst.cfacts_c0
  have hpl0 : ∀ s, PlacedS (lay2 Λ p) (fun _ => none) s C0 [] := by
    rw [he]; exact fun _ => placedS_c0
  have hZ := bareMC_Z
  have hL8' : (8 : Int) ≤ L := by omega
  have htl := tail_bare_of_accepted2A h hp hs
  have hin := mainUIn_bare2A h hp hs
  refine ⟨fun J hJ => h0_ofPlaceOK_bareF h (Spike.Lib.LowerNode.imms2Me Λ p) (rd := Spike.Lib.LowerNode.IsNum)
    (J := J) (Dt := Dt) (ls0 := fun _ => 0) (ab := ab2 p (Ly).lab) hE
    (FE := fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧ rtF (Ly) m) (fun _ hm => hm.2)
    (Spike.Lib.A64.Alloc.wordsNone_and_fstable hwf hE.1 (Spike.Lib.A64.Rt.entryR_ok hE)
      (.inl (Spike.Lib.cellsR_entry hE)) (Spike.Lib.A64.Rt.rtF_stable _ hE)).1
    (fun _ _ hm => ⟨Spike.Lib.A64.Rt.wordsNone_takeMem hwf (Spike.Lib.A64.Rt.rS0_sub _) hm.1,
      Spike.Lib.A64.Rt.rtF_takeMem _ (Spike.Lib.A64.Rt.rS0_sub _) hm.2⟩)
    (Fw := Spike.Lib.DmemPriv.WordsNone (Ly).Λ) (fun _ hm => hm.1)
    (fun _ => Spike.Lib.A64.Rt.wordsNone_swFSL_fstable hwf (Spike.Lib.A64.Rt.rS0_sub _)
      (by rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hLm) hL8' hL8
      (by rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rS0_subRD _ hL0 hLm)
      (by rw [Spike.Lib.A64.Rt.pinA_lab0]; exact Spike.Lib.A64.Rt.rt_hfit _)
      (by rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_houtD _ hL0 hLm)
      (Spike.Lib.A64.Rt.fitS_of_sub _ (Spike.Lib.A64.Rt.rS0_sub _)))
    (Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp) hf0 hov hC0 hpl0 hL0 hLm hL8 hin
    (Spike.Lib.A64.PhRec.hmph_ofPlaceOK h _ htl)
    ⟨".L1_scc_rt_main.stack_grow", 0, hstk0A_of_placeOKAt h hp hs, by decide, ofNat4_zero _⟩
    (hfn0A_of_placeOKAt (Ly).lays h hp) hD0 hD8 hLD hZM hZU (fun _ _ _ h => h.1) (fun _ _ _ h => h.2)
    (hU L D lM fM nM hB J hJ)⟩

end Assembled

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.hstk0A_of_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hstk0A_of_placeOKAt

/-- info: 'Spike.Lib.LowerA64.hfn0A_of_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hfn0A_of_placeOKAt

/-- info: 'Spike.Lib.LowerA64.h0_ofPlaceOK_bareF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h0_ofPlaceOK_bareF

/-- info: 'Spike.Lib.LowerA64.h0InAW_bare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h0InAW_bare

end Spike.Lib.LowerA64
