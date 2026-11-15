/-
**The allocating block's plain calls at a landing's extended placement**
(AArch64): `CallLUStmt` (`Spike/Lib/LowerA64/G1H1Stmt.lean`) for any
`Accepted2` program with a setup block. A landing context `CxOkH`
(`Spike/Test/A64Hello1CxOkH.lean`, the setup frame of `rodata`) with its
bottom key `BotH` is a base context `CxCore2L` at the extended placement
`upd L l b`, `updN ls l n` (reachable: `Reach.step`), at the write tail
`fun _ => True`:

- the region's facts from `CxOkH`'s setup call premises and bounds (as
  `cxCore2_setup`'s), the frame placed at the placement from no label;
- the room from the need table's row of `rodata` in the bottom key's
  `Bounds2A`, its depth `D1` the context's (the key's region is the
  context's: `SetupBot`);
- the limit room by `limS_setup`;
- the allocations' `W2` instance from `allocW2AtL_ofCxOkH`
  (`Spike/Lib/LowerA64/G1AllocL.lean`).

Its plain calls are then `callC2R_ofCxG2ML`'s (the callee's records at
the bottom keys `fun _ _ => True`, the callees' segments from
`fnSpecC2StmtL`) at its suspended frame (`CallC2R.ofCons`), its lane
stores, buffers and output calls `laneBuf2L`'s and `print2L`'s, the
aborts' fragment `AbG2L` at the extended placement, ending nowhere by
`abG2L_seg`.

- `cxCore2L_ofCxOkH`: a landing context is a base context at a reachable
  placement, given the allocations' `W2` instance there;
- `callLU_ofCxOkH`: one landing context's plain calls, lane stores,
  buffers and output calls at the extended placement;
- `callLUStmt`: `CallLUStmt`.
-/
import Spike.Lib.LowerA64.G1H1Stmt
import Spike.Lib.LowerA64.G1AbG2L
import Spike.Lib.LowerA64.G1AllocL
import Spike.Lib.LowerA64.G1CallC2RL
import Spike.Lib.LowerA64.G1FnSpecStmtLOf
import Spike.Lib.LowerA64.G1SetupCx
import Spike.Lib.LowerA64.FramesPlacedSetup

namespace Spike.Lib.LowerA64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Rt (setupMC rS0 arOf swFSL rtF)
open Spike.Lib.LowerNode (FrOk2 setupWords2 compiled2 imms2Me TailAt2 IsNum)
open Spike.Lib.AllocReach (Reach IN)

section CallLU

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates. -/
local notation "LY0" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))

set_option hygiene false in
/-- The record's static memory. -/
local notation "M0" => Spike.Lib.A64.PhRec.m0Of (Ly).Λ OP (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).secs

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.A64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- `MSAt` at `Closed2AtA`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max => MSAt h (imms2Me Λ p) p IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- `MSAtL` at `Closed2AtA`'s instance and the placement `L`, `ls`. -/
local notation "MSL" J:max L:max ls:max => MSAtL h (imms2Me Λ p) p IsNum J (ab2 p (Ly).lab) (fun _ => 0) L ls

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The `j`th compiled block's code facts at the theorem's immediates. -/
local notation "FC" j:max d:max hd:max => fnCode2OfPMe hp h Λ j d hd

set_option hygiene false in
/-- The code predicate at the return address `ra`. -/
local notation "CD" ra:max => CdCLE OP (Spike.Lib.A64.PhRec.okPc LY0) (Spike.Lib.A64.PhRec.ph LY0) (LY0).lab
  (Int64.ofBitVec ra)

set_option hygiene false in
/-- The start's frame condition (`Closed2AtWA`'s). -/
local notation "WNF" => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧ rtF (Ly) m

set_option hygiene false in
/-- The frame invariant `J` holds at the starts of the landings `ElH`. -/
local notation "StJ" J:max => ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
  ∀ s c fs, StartsSA h E (WNF) (ElH h hp) (fun _ => True) (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs

/-- **A landing context is a base context at a reachable placement**
(`CxCore2L` at the write tail `fun _ => True`): `CxOkH` with its bottom key
`BotH`, at a placement `L`, `ls` reachable from none, given the
allocations' `W2` instance there (`hAW`); the region's facts as
`cxCore2_setup`'s, the room from the bottom key's need row. -/
theorem cxCore2L_ofCxOkH (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hcfg : CfgNeedOkA pcfg = true) (J : InvS) {L : Lbl} {ls : Lsize}
    (hre : Reach (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) L ls) {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame}
    {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isaLSE2}
    (hC : CxOkH h hp j R F fs fp ra tp G0 Ab) (hB : BotH h ⟨j, R, F, fp, ra, tp, G0⟩ fs)
    (hAW : AllocW2At p L ls (FC j d hd).lcx (FC j d hd).cx (CD ra) ((FC j d hd).Bl ra)
      (fun lbl lsize s c => W2 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p IsNum (Spike.Lib.A64.PhRec.GOf Ly M0)
        (Spike.Lib.A64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly)) (arOf (Ly).Λ)
        (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) (fun _ => True) (Spike.Lib.A64.WriteAb.Ab (Ly).lab) lbl lsize s c fs)
      (KT) (Ly).exe (Ly).endPc R F ((MSL J L ls) fs) fp ra tp G0 (imms2Me Λ p) (TailAt2 p j) (RetLk d.retTy)) :
    CxCore2L h hp (fun _ => True) J L ls j R F fs fp ra tp G0 := by
  obtain ⟨⟨J'', L'', D1'', fS'', v'', D2, lS, lM, nS'', fM, nM, hB2, hSB2⟩, -⟩ := hB
  obtain ⟨d', hd', LD, D1, fS, nS, v, g, fr, J', hn, hfS, hnS, hL0, hLm, hL8, hD18, hL1, hrow,
    ⟨hR0, hal, hF', hFF, -, -, hct, -⟩, hwn, -, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hC
  obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
  obtain ⟨hrS, -, -, hnS2, -⟩ := hB2
  obtain ⟨-, -, hkR, -⟩ := hSB2
  have hD1 : -D1 = -D1'' := congrArg Region.lo hkR
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2A h hp hs') (rtCodeOkS_setupWords2A h hp hs')).1
  have hZ := setupMC_Z _ hsw
  have hpN := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  obtain ⟨w, fi, -, -, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  have hframe : (FC j d hd).cx.frame = fS := by
    rw [hcx]; exact hrow _ _ hmem rfl (by show Scc.Lower.Names.user d.name = _; rw [hn])
  have hlo0 : -D1 ≤ -((FC j d hd).cx.frame : Int) := by rw [hframe]; omega
  have hhi : (0 : Int) ≤ 0 := Int.le_refl _
  have hFO0 : ∀ m, F m → StackOff (rS0 (Ly))
      ((swR v (-LD) 0).callee (-(setupMC (setupWords2 p)).Z.toInt) (-D1) 0) m := by
    intro m hm
    obtain ⟨⟨⟨hv, -⟩, hoff⟩, hcc⟩ := hFF m hm
    subst hv
    have hok : (swR (TOP) (-LD) 0).OK := by
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hLm
    have h8 : (swR (TOP) (-LD) 0).base.toNat % 8 = 0 := by
      show (TOP).toNat % 8 = 0
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; have := Spike.Lib.A64.Rt.rt_h16 (Ly); omega
    exact Spike.Lib.A64.Flow.Ret0.Inst.stackOff_callee hok h8 (by show (-LD) % 8 = 0; omega)
      (by show (0 : Int) % 8 = 0; rfl)
      (by show -LD ≤ _; omega) (by omega) (by show _ < (0 : Int); omega) (by omega) hoff hcc
  have hfr : fr.env = (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).term,
      (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).env, none⟩ : Ctl).env := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, rfl⟩ := hct
    rfl
  refine
    { hre := hre
      hR := hR0
      hal := hal
      hl := by show (-D1) % 8 = 0; omega
      hh := by show (0 : Int) % 8 = 0; rfl
      hhi := hhi
      hFS := hF'
      hFO := hFO0
      hrs := fun d' hd' r k hr => ?_
      hfp := fun s _ => (framesPlaced_setup h hp hty hct s).imp fun _ hB =>
        framesPlacedInI_mono_lbl (by intro _ _ h'; cases h') hB
      hes := fun _ _ f hf => ?_
      hfs := fun _ => List.cons_ne_nil _ _
      hrd := ?_
      hwn := hwn
      hG0F := fun _ hc => FrOk2.runM hpN hc (FrOk2.step hpN (hct.step []) (hf0_start2A hty _))
      hG0 := fun _ _ h1 h2 => h1.trans h2
      hK := msOfAX_K_abi
      hAW := fun d' hd' _ => ?_
      room := fun d' hd' => ?_
      lim := fun m hm d' hd' => ?_
      htp := rfl
      hun := fun m hm => (hFF m hm).1.1.2 }
  · obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
    exact regionOff_of_rsOf (FC j d hd).hf hlo0 hhi hr
  · rw [List.mem_singleton] at hf
    subst hf
    rw [hfr]
    exact envSmall_C0 hp hty
  · dsimp only [MSAtL]; generalize ab2 p _ = ab; cases ab <;> exact fun _ h' => h'
  · obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
    exact hAW
  · obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
    rw [hn]
    exact ⟨lS, fS'', nS'', hrS, by show -D1 ≤ _; omega⟩
  · obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
    have hl := limS_setup h hp hs' hcfg hL0 hLm (by omega) hL1 J (hFF m hm).1.1.1 hd hn
    revert hl
    dsimp only [MSAt, MSAtL]; generalize ab2 p _ = ab; cases ab <;> exact id

/-- **One landing context's constructs at the extended placement**: at a
reachable placement extended by a fresh label (`Reach.step`), the landing
context `CxOkH` with its bottom key and the allocations' `W2` instance
there is a base context (`cxCore2L_ofCxOkH`) whose aborts' fragment is
`AbG2L` there; its plain calls by `callC2R_ofCxG2ML` at the bottom keys
`fun _ _ => True`, the callees' segments from `fnSpecC2StmtL`, at its
suspended frame (`CallC2R.ofCons`); its lane stores and buffers by
`laneBuf2L`, its output calls by `print2L`; `AbG2L` ends nowhere
(`abG2L_seg`). -/
theorem callLU_ofCxOkH (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hcfg : CfgNeedOkA pcfg = true) (htg : tgOkB OP = true) (J : InvS) {L : Lbl} {ls : Lsize}
    (hre : Reach (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) L ls) {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame}
    {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isaLSE2}
    (hC : CxOkH h hp j R F fs fp ra tp G0 Ab) (hB : BotH h ⟨j, R, F, fp, ra, tp, G0⟩ fs)
    (hAW : AllocW2At p L ls (FC j d hd).lcx (FC j d hd).cx (CD ra) ((FC j d hd).Bl ra)
      (fun lbl lsize s c => W2 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p IsNum (Spike.Lib.A64.PhRec.GOf Ly M0)
        (Spike.Lib.A64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly)) (arOf (Ly).Λ)
        (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) (fun _ => True) (Spike.Lib.A64.WriteAb.Ab (Ly).lab) lbl lsize s c fs)
      (KT) (Ly).exe (Ly).endPc R F ((MSL J L ls) fs) fp ra tp G0 (imms2Me Λ p) (TailAt2 p j) (RetLk d.retTy))
    (hra : Spike.Lib.A64.PhRec.ph (LY0) (Int64.ofBitVec ra).toBitVec.toNat =
      Spike.Lib.A64.PhRec.ph (LY0)
        (Int64.ofBitVec ((LY0).lab Spike.Lib.A64.Rt.bareMC.e0 + 4).toBitVec).toBitVec.toNat) :
    CallC2 p L ls (FC j d hd).lcx (FC j d hd).cx (CD ra) ((FC j d hd).Bl ra) (LY0).exe (LY0).endPc R F
        (W2AtL h (imms2Me Λ p) p IsNum (rS0 (Ly)) J (fun _ => True) (fun _ => 0) L ls) (KT) (MSL J L ls)
        fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j) (AbG2L h hp (fun _ => True) J L ls) (RetLk d.retTy) ∧
      LaneC p L ls (FC j d hd).lcx (FC j d hd).cx (CD ra) ((FC j d hd).Bl ra) (LY0).exe (LY0).endPc R F
        (W2AtL h (imms2Me Λ p) p IsNum (rS0 (Ly)) J (fun _ => True) (fun _ => 0) L ls) (KT) (MSL J L ls)
        fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j) (AbG2L h hp (fun _ => True) J L ls) ∧
      NewBufC p L ls (FC j d hd).lcx (FC j d hd).cx (CD ra) ((FC j d hd).Bl ra) (LY0).exe (LY0).endPc R F
        (W2AtL h (imms2Me Λ p) p IsNum (rS0 (Ly)) J (fun _ => True) (fun _ => 0) L ls) (KT) (MSL J L ls)
        fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j) (AbG2L h hp (fun _ => True) J L ls) (RetLk d.retTy) ∧
      PrintCallC p L ls (FC j d hd).lcx (FC j d hd).cx (CD ra) ((FC j d hd).Bl ra) (LY0).exe (LY0).endPc R F
        (W2AtL h (imms2Me Λ p) p IsNum (rS0 (Ly)) J (fun _ => True) (fun _ => 0) L ls) (KT) (MSL J L ls)
        fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j) (AbG2L h hp (fun _ => True) J L ls) ∧
      SegWS (W2AtL h (imms2Me Λ p) p IsNum (rS0 (Ly)) J (fun _ => True) (fun _ => 0) L ls) (KT) p L (MSL J L ls)
        (AbG2L h hp (fun _ => True) J L ls) fun _ _ _ => False := by
  have hcore := cxCore2L_ofCxOkH h hp hty hcfg J hre hd hC hB hAW
  have hown := room2Own h hp
  have hrc := room2Callee h hp
  have hlc := lim2Callee h hp
  have hspec := fnSpecC2StmtL cfg pcfg p Λ hp hcfg h htg (fun _ => True) (fun _ _ _ _ _ _ _ _ => trivial) J
    (fun _ _ => True) L ls hre
  have hfs : fs ≠ [] := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, rfl, -⟩ := hC
    exact List.cons_ne_nil _ _
  have hcx : CxG2ML h hp (fun _ => True) J L ls j R F fs fp ra tp G0 (AbG2L h hp (fun _ => True) J L ls) :=
    ⟨hcore, fun _ _ _ h' => h'⟩
  obtain ⟨hlane, hbuf⟩ := laneBuf2L h hp (fun _ => True) J L ls j d hd R F fs fp ra tp G0 _ hcx hra
  refine ⟨CallC2R.ofCons hfs <| callC2R_ofCxG2ML h callC2_ofFW hp hown hrc hlc (limOk2L h hp) htg
      (proCallG2L h hp hown hrc hlc) (wCallG2L h hp hown) (Bot := fun _ _ => True) hd hcx hra
      (fun _ _ => trivial) fun g dg hc hf => ?_, hlane, hbuf,
    print2L h hp (fun _ => True) (fun _ _ _ _ _ _ _ _ => trivial) J L ls j d hd R F fs fp ra tp G0 _ hcx hra,
    abG2L_seg h hp hown J L ls hre (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
      (fun _ _ _ _ _ _ => trivial)⟩
  obtain ⟨j', hj', hd'⟩ := hord_ofAccepted2 hp (fnCode2OfPMe hp h Λ)
    (fun j d hd => by rw [(fnCode2OfPMe_spec hp h Λ j d hd).1]) j d hd g dg hc hf
  exact ⟨j', hj', hd', hspec j' dg hd'⟩

/-- **`CallLUStmt`** for any `Accepted2` program with a setup block: at the
extended placement (`Reach.step`), the allocations' `W2` instance from
`allocW2AtL_ofCxOkH`, the rest by `callLU_ofCxOkH`. -/
theorem callLUStmt (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hcfg : CfgNeedOkA pcfg = true) (hobj : Scc.Obj.nShift cfg.layout.obj < 22) (htg : tgOkB OP = true)
    (E : Entry) : CallLUStmt h hp E := by
  intro J hJ L ls l b n hre hl hland j d hd R F fs fp ra tp G0 Ab hC hB hra
  have hre' := Reach.step hre hl hland
  exact ⟨_, callLU_ofCxOkH h hp hty hcfg htg J hre' hd hC hB
    (allocW2AtL_ofCxOkH h hp hty hobj E hJ hre' hd hC hB fun _ h' => h') hra⟩

end CallLU

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.cxCore2L_ofCxOkH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.cxCore2L_ofCxOkH

/-- info: 'Spike.Lib.LowerA64.callLU_ofCxOkH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.callLU_ofCxOkH

/-- info: 'Spike.Lib.LowerA64.callLUStmt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.callLUStmt
