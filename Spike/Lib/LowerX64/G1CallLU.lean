/-
**The allocating block's constructs at a landing's extended placement**
(x86-64; the twin of `Spike/Lib/LowerA64/G1CallLU.lean`): a landing context
`CxOkH` (`Spike/Test/X64Hello1CxOkH.lean`, the setup frame of `rodata`) with
its bottom key `BotH` is a base context `CxCore2L` in its rebased region
`rbR R` at a reachable placement, at the write tail `fun _ => True`:

- the region's facts from `CxOkH`'s setup call premises and bounds (as
  `cxCore2_setup`'s), the frame placed at the placement from no label;
- the room from the need table's row of `rodata` in the bottom key's
  `Bounds2`, its depth `D1` the context's (the key's region is the
  context's: `SetupBot`);
- the limit room by `limS_setup`;
- the allocations' `W2` instance given (`hAW`).

Where x86-64 differs from AArch64: `CxOkH` keeps the callee region's base
8-aligned only, and `CxCore2L.hal` asks the rebased region's base 16-aligned,
which follows from the switch region's top being the first stack's
(`v = TOP`); `CxOkH` gives that top under its frame condition only, so
`cxCore2L_ofCxOkH` asks some memory in the frame condition (`hm`), and
`callLU_ofCxOkH` takes the constructs as empty segments when there is none
(their nodes are at the frame condition).

The plain calls are then `callC2R_ofCxG2ML`'s (the callee's records at the
bottom keys `fun _ _ => True`, the callees' segments from `fnSpecC2StmtL`)
at the context's suspended frame (`CallC2R.ofCons`), its lane stores,
buffers and output calls `laneBuf2L`'s and `print2L`'s, the aborts'
fragment `AbG2L` at the placement, ending nowhere by `abG2L_seg`.

- `cxCore2L_ofCxOkH`: a landing context is a base context at a reachable
  placement, given the allocations' `W2` instance there and a memory in
  its frame condition;
- `callLU_ofCxOkH`: one landing context's plain calls, lane stores,
  buffers and output calls at a reachable placement.
-/
import Spike.Lib.LowerX64.G1H1Stmt
import Spike.Lib.LowerX64.G1AbG2L
import Spike.Lib.LowerX64.G1CallC2RL
import Spike.Lib.LowerX64.G1LaneBufL
import Spike.Lib.LowerX64.G1PrintL
import Spike.Lib.LowerX64.G1FnSpecStmtLOf
import Spike.Lib.LowerX64.G1SetupCx
import Spike.Lib.LowerX64.AllocW2Full

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (swR)
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Rt (setupMC rS0 arOf)
open Spike.Lib.LowerNode (FrOk2 setupWords2 compiled2 imms2Me TailAt2 IsNum)
open Spike.Lib.AllocReach (Reach IN)

section CallLU

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
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)

set_option hygiene false in
/-- The record's static memory. -/
local notation "M0" => Spike.Lib.X64.PhRec.m0Of (Ly).Λ OP
  (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).secs

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- `W2AtL` at `Closed2At`'s instance, the write tail `fun _ => True` and the placement `L`, `ls`. -/
local notation "W2L" J:max L:max ls:max => W2AtL h (imms2Me Λ p) p IsNum (rS0 (Ly)) J (fun _ => True) (fun _ => 0) L ls

set_option hygiene false in
/-- `MSAtL` at `Closed2At`'s instance and the placement `L`, `ls`. -/
local notation "MSL" J:max L:max ls:max => MSAtL h (imms2Me Λ p) p IsNum J (ab2 p (Ly).lab) (fun _ => 0) L ls

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The `j`th compiled block's code facts at the theorem's immediates. -/
local notation "FC" j:max d:max hd:max => fnCode2OfPMe hp h Λ j d hd

set_option hygiene false in
/-- The code predicate at the return address `ra`. -/
local notation "CD" ra:max => CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab
  (Int64.ofBitVec ra)

/-- **A landing context is a base context at a reachable placement**
(`CxCore2L` in the rebased region `rbR R` at the write tail `fun _ => True`):
`CxOkH` with its bottom key `BotH`, at a placement `L`, `ls` reachable from
none, given a memory in the frame condition (`hm`, for the switch region's
top) and the allocations' `W2` instance there (`hAW`); the region's facts
as `cxCore2_setup`'s, the room from the bottom key's need row. -/
theorem cxCore2L_ofCxOkH (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hcfg : CfgNeedOk pcfg = true) (J : InvS) {L : Lbl} {ls : Lsize}
    (hre : Reach (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) L ls) {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame}
    {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isa}
    (hC : CxOkH h hp j R F fs fp ra tp G0 Ab) (hB : BotH h ⟨j, R, F, fp, ra, tp, G0⟩ fs) (hm : ∃ m, F m)
    (hAW : AllocW2At p L ls (FC j d hd).lcx (FC j d hd).fr (CD ra) ((FC j d hd).Bl ra)
      (fun lbl lsize s c => W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p IsNum (Spike.Lib.X64.PhRec.GOf Ly M0)
        (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly)) (arOf (Ly).Λ)
        (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) (fun _ => True) (Spike.Lib.X64.WriteAb.Ab (Ly).lab)
        lbl lsize s c fs)
      (KT) (Ly).exe (Ly).endPc (rbR R) F ((MSL J L ls) fs) fp ra tp G0 (imms2Me Λ p) (TailAt2 p j)
      (RetLk d.retTy)) :
    CxCore2L h hp (fun _ => True) J L ls j (rbR R) F fs fp ra tp G0 := by
  obtain ⟨⟨J'', L'', D1'', fS'', v'', D2, lS, lM, nS'', fM, nM, hB2, hSB2⟩, -⟩ := hB
  obtain ⟨d', hd', LD, D1, fS, nS, v, g, fr, J', hn, hfS, hnS, hL0, hLm, hL8, hD18, hL1, hrow,
    ⟨hR0, hb8, hF', hFF, -, -, hct, -⟩, hwn, -, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hC
  obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
  obtain ⟨hrS, -, -, hnS2, -⟩ := hB2
  obtain ⟨-, -, hkR, -⟩ := hSB2
  have hD1 : -D1 = -D1'' := congrArg Region.lo hkR
  obtain ⟨m0, hm0⟩ := hm
  have hv : v = TOP := (hFF m0 hm0).1.1.2.1.1
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2 h hp hs') (rtCodeOkS_setupWords2 h hp hs')).1
  have hZ := setupMC_Z _ hsw
  have hpN := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  obtain ⟨w, -, -, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  have hframe : (FC j d hd).fr.size = fS := by
    rw [hcx]; exact hrow _ hmem rfl (by show Scc.Lower.Names.user d.name = _; rw [hn])
  -- the regions: the switch region, its callee, the setup call's `RC`, its rebased `rbR RC`
  have hok : (swR v (-LD) 0).OK := by
    rw [hv, Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ (by omega) hLm
  have htop8 : v.toNat % 8 = 0 := by
    rw [hv, Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
  have hR1 : ((swR v (-LD) 0).callee (-8 - 0) (8 - LD) 8).OK :=
    Region.callee_ok hok (by show -LD ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
      (by show _ ≤ (0 : Int); omega)
  have hb1 : (((swR v (-LD) 0).callee (-8 - 0) (8 - LD) 8).base.toNat : Int) = v.toNat - 8 :=
    Region.callee_base hok (by show -LD ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
  have hb8' : ((swR v (-LD) 0).callee (-8 - 0) (8 - LD) 8).base.toNat % 8 = 0 := by omega
  have hbc := Region.callee_base (hi' := 8) (kc := -8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0)
    (lo' := -D1) hR1 (by show 8 - LD ≤ _; omega) (by omega) (by show _ < (8 : Int); omega)
  have hlo1 : (((swR v (-LD) 0).callee (-8 - 0) (8 - LD) 8).callee
      (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8).lo ≤ -8 := by
    show -D1 ≤ -8; omega
  have hhi1 : (0 : Int) ≤ (((swR v (-LD) 0).callee (-8 - 0) (8 - LD) 8).callee
      (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8).hi := by
    show (0 : Int) ≤ 8; decide
  have hb := rbR_base hR0 hlo1 hhi1
  have hlo0 : (rbR (((swR v (-LD) 0).callee (-8 - 0) (8 - LD) 8).callee
      (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8)).lo ≤ -((FC j d hd).fr.size : Int) := by
    show -D1 + 8 ≤ _; rw [hframe]; omega
  have hhi : (0 : Int) ≤ (rbR (((swR v (-LD) 0).callee (-8 - 0) (8 - LD) 8).callee
      (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8)).hi := by
    show (0 : Int) ≤ 8 + 8; decide
  have hfr : fr.env = (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).term,
      (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).env, none⟩ : Ctl).env := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, rfl⟩ := hct
    rfl
  refine
    { hre := hre
      hR := rbR_ok hR0 hlo1 hhi1
      hR8 := by omega
      hal := by
        have h16v : v.toNat % 16 = 0 := by
          rw [hv, Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_h16 (Ly)
        omega
      hl := by show (-D1 + 8) % 8 = 0; omega
      hh := by show ((8 : Int) + 8) % 8 = 0; decide
      hhi := by show (16 : Int) ≤ 8 + 8; decide
      hFS := rbR_fstable hR0 hlo1 hhi1 hF'
      hFO := fun m hm => stackOff_rbR hR0 hlo1 hhi1
        (Spike.Lib.X64.Rt.stackOff_callee hR1 hb8' (by show (8 - LD) % 8 = 0; omega)
          (by show (8 : Int) % 8 = 0; decide) (by show 8 - LD ≤ _; omega) (by omega)
          (by show _ < (8 : Int); omega) (by omega)
          (Spike.Lib.X64.Rt.stackOff_callee hok htop8 (by show (-LD) % 8 = 0; omega)
            (by show (0 : Int) % 8 = 0; rfl) (by show -LD ≤ _; omega) (by omega)
            (by show _ < (0 : Int); omega) (by decide) (hFF m hm).1.1.2.2 (hFF m hm).1.2)
          (hFF m hm).2)
      hrs := fun d' hd' r k hr => ?_
      hfp := fun s _ => (framesPlaced_setup h hp hty hct s).imp fun _ hB =>
        framesPlacedInI_mono_lbl (by intro _ _ h'; cases h') hB
      hes := fun _ _ f hf => ?_
      hfs := fun _ => List.cons_ne_nil _ _
      hrd := ?_
      hwn := hwn
      hG0F := fun _ hc => FrOk2.runM hpN hc (FrOk2.step hpN (hct.step []) (hf0_start2 hty _))
      hG0 := fun _ _ h1 h2 => h1.trans h2
      hK := msOfAX_K_abi
      hAW := fun d' hd' _ => ?_
      room := fun d' hd' => ?_
      lim := fun m hm d' hd' => ?_
      htp := rfl
      hun := fun m hm => (hFF m hm).1.1.2.1.2 }
  · obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
    exact regionOff_of_rsOf (FC j d hd).hf hlo0 hhi hr
  · rw [List.mem_singleton] at hf
    subst hf
    rw [hfr]
    exact envSmall_C0 hp hty
  · intro w'
    dsimp only [MSAtL]
    generalize ab2 p _ = ab
    cases ab <;> exact fun hw => hw
  · obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
    exact hAW
  · obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
    rw [hn]
    exact ⟨lS, fS'' + 8, nS'', hrS, by show -D1 + 8 - 8 ≤ _; omega⟩
  · obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
    have hl := limS_setup h hp hs' hcfg hL0 hLm (by omega) hL1 J hv hd hn
    revert hl
    dsimp only [MSAt, MSAtL]; generalize ab2 p _ = ab; cases ab <;> exact id

/-- **One landing context's constructs at a reachable placement**: the
landing context `CxOkH` with its bottom key and the allocations' `W2`
instance there; with a memory in its frame condition it is a base context
(`cxCore2L_ofCxOkH`) whose aborts' fragment is `AbG2L` there: its plain
calls by `callC2R_ofCxG2ML` at the bottom keys `fun _ _ => True`, the
callees' segments from `fnSpecC2StmtL`, at its suspended frame
(`CallC2R.ofCons`); its lane stores and buffers by `laneBuf2L`, its output
calls by `print2L`. Without one, each construct's node is empty. `AbG2L`
ends nowhere (`abG2L_seg`). -/
theorem callLU_ofCxOkH (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hcfg : CfgNeedOk pcfg = true) (htg : tgOkB OP = true) (J : InvS) {L : Lbl} {ls : Lsize}
    (hre : Reach (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) L ls) {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame}
    {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isa}
    (hC : CxOkH h hp j R F fs fp ra tp G0 Ab) (hB : BotH h ⟨j, R, F, fp, ra, tp, G0⟩ fs)
    (hAW : AllocW2At p L ls (FC j d hd).lcx (FC j d hd).fr (CD ra) ((FC j d hd).Bl ra)
      (fun lbl lsize s c => W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p IsNum (Spike.Lib.X64.PhRec.GOf Ly M0)
        (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly)) (arOf (Ly).Λ)
        (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) (fun _ => True) (Spike.Lib.X64.WriteAb.Ab (Ly).lab)
        lbl lsize s c fs)
      (KT) (Ly).exe (Ly).endPc (rbR R) F ((MSL J L ls) fs) fp ra tp G0 (imms2Me Λ p) (TailAt2 p j)
      (RetLk d.retTy))
    (hra : Spike.Lib.X64.PhRec.ph LY0 (Int64.ofBitVec ra).toBitVec.toNat =
      Spike.Lib.X64.PhRec.ph LY0 ((LY0).lab raL).toBitVec.toNat) :
    CallC2 p L ls (FC j d hd).lcx (FC j d hd).fr (CD ra) ((FC j d hd).Bl ra) (LY0).exe (LY0).endPc (rbR R) F
        (W2L J L ls) (KT) (MSL J L ls) fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j)
        (AbG2L h hp (fun _ => True) J L ls) (RetLk d.retTy) ∧
      LaneC p L ls (FC j d hd).lcx (FC j d hd).fr (CD ra) ((FC j d hd).Bl ra) (LY0).exe (LY0).endPc (rbR R) F
        (W2L J L ls) (KT) (MSL J L ls) fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j)
        (AbG2L h hp (fun _ => True) J L ls) ∧
      NewBufC p L ls (FC j d hd).lcx (FC j d hd).fr (CD ra) ((FC j d hd).Bl ra) (LY0).exe (LY0).endPc (rbR R) F
        (W2L J L ls) (KT) (MSL J L ls) fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j)
        (AbG2L h hp (fun _ => True) J L ls) (RetLk d.retTy) ∧
      PrintCallC p L ls (FC j d hd).lcx (FC j d hd).fr (CD ra) ((FC j d hd).Bl ra) (LY0).exe (LY0).endPc
        (rbR R) F (W2L J L ls) (KT) (MSL J L ls) fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j)
        (AbG2L h hp (fun _ => True) J L ls) ∧
      SegWS (W2L J L ls) (KT) p L (MSL J L ls) (AbG2L h hp (fun _ => True) J L ls) fun _ _ _ => False := by
  have hown := room2Own h hp
  have hAbQ := abG2L_seg h hp hown J L ls hre (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ => trivial)
  by_cases hm : ∃ m, F m
  case neg =>
    refine ⟨?_, ?_, ?_, ?_, hAbQ⟩ <;>
      (intro _; intros; exact SegWS.empty fun _ _ _ h' => hm ⟨_, at_F h'.1⟩)
  have hcore := cxCore2L_ofCxOkH h hp hty hcfg J hre hd hC hB hm hAW
  have hrc := room2Callee h hp
  have hlc := lim2Callee h hp
  have hspec := fnSpecC2StmtL cfg pcfg p sizes labelOffs Λ hp hcfg h htg (fun _ => True)
    (fun _ _ _ _ _ _ _ _ _ => trivial) J (fun _ _ => True) L ls hre
  have hfs : fs ≠ [] := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hfs', _⟩ := hC
    rw [hfs']
    exact List.cons_ne_nil _ _
  have hcx : CxG2ML h hp (fun _ => True) J L ls j R F fs fp ra tp G0 (AbG2L h hp (fun _ => True) J L ls) :=
    ⟨hcore, fun _ _ _ h' => h'⟩
  obtain ⟨hlane, hbuf⟩ := laneBuf2L h hp (fun _ => True) J L ls j d hd R F fs fp ra tp G0 _ hcx hra
  refine ⟨CallC2R.ofCons hfs <| callC2R_ofCxG2ML h callC2_ofFW hp hown hrc hlc (limOk2L h hp) htg
      (proCallG2L h hp hown hrc hlc) (wCallG2L h hp hown) (Bot := fun _ _ => True) hd hcx hra
      (fun _ _ => trivial) fun g dg hc hf => ?_, hlane, hbuf,
    print2L h hp (fun _ => True) (fun _ _ _ _ _ _ _ _ _ => trivial) J L ls j d hd R F fs fp ra tp G0 _ hcx hra,
    hAbQ⟩
  obtain ⟨j', hj', hd'⟩ := hord_ofAccepted2 hp (fnCode2OfPMe hp h Λ)
    (fun j d hd => by rw [(fnCode2OfPMe_spec hp h Λ j d hd).1]) j d hd g dg hc hf
  exact ⟨j', hj', hd', hspec j' dg hd'⟩

end CallLU

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.cxCore2L_ofCxOkH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.cxCore2L_ofCxOkH

/-- info: 'Spike.Lib.LowerX64.callLU_ofCxOkH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.callLU_ofCxOkH
