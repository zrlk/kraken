/-
**The setup frame is a base context** (x86-64; the twin of
`Spike/Lib/LowerA64/G1SetupCx.lean`): `CxCore2`
(`Spike/Lib/LowerX64/G1FnSpec.lean`) at the setup call's callee context in
the rebased region (`rbR` of the region `RC` below the first stack's top,
the switch region and `scc_rt_main`'s frame `Z`; the frames `[fr]`, the
saved pair of the call's ghost `g`, the first TCB, the ghosts `GR g fr`),
from the setup call's premises `PREF` and the bounds `Bounds2`, for any
`Accepted2` program with a setup block.

- `limS_setup`: the setup block's limit room at the callee's entry `%rsp`
  (`calleeRow`: the row's need within `12288` less `Z` and `16`; the limit
  word's values the limit or `0`, `room_of_le`);
- `envSmall_C0`: the start's environment is small;
- `cxCore2_setup`: `CxCore2` at the setup context: the region's facts from
  `PREF` and the bounds (as `setupCxLB_ofPreT`'s), the frame placed
  (`framesPlaced_setup`) with the start's environment, the ghosts along the
  setup frame's run, the room from `Bounds2`'s `nS + 48 + 208 ≤ D1`, the
  limit room by `limS_setup` (`CfgNeedOk`, `hcfg`) and the allocator's `W2`
  instance (`hAW`, a premise: `openAWF_of_accepted2` gives it at the write
  tail `fun _ => True`).
-/
import Spike.Lib.LowerX64.G1FnSpec
import Spike.Lib.LowerX64.G1SetupHS
import Spike.Lib.LowerX64.StackBounds2
import Spike.Lib.X64StartOfPlaceOK

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region FrameRun EnvSmall)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (swR FStable At)
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Flow.Ret0 (LimOk WcG CallerCells limA)
open Spike.Lib.X64.Rt (SetupCallWSB SetupGF swFSL rS0 rtF setupMC arOf)
open Spike.Lib.X64.WriteAb (Ab)
open Spike.Lib.LowerNode (FrOk2 ZBad setupWords2 compiled2 addFreeT TailAt2 imms2Me)
open Spike.Lib.AllocReach (Reach IN)

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates (`fnCode2OfP`'s). -/
local notation "LY0" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output. -/
local notation "OUT" => Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.X64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)

set_option hygiene false in
/-- The canonical load's memory of the output. -/
local notation "M0" => Spike.Lib.X64.PhRec.m0Of (Ly).Λ OP
  (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).secs

set_option hygiene false in
/-- The program's start control (`S0X`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).env, none⟩ : Ctl)

set_option hygiene false in
/-- `W2At` at `Closed2At`'s instance. -/
local notation "W2S" J:max => W2At h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum (rS0 (Ly)) J Dt (fun _ => 0)

set_option hygiene false in
/-- `MSAt` at `Closed2At`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max =>
  MSAt h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- **The start's frame condition**: the runtime's words unloaded and no
heap or image word loaded (`Closed2AtW`'s). -/
local notation "WNF" => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧ rtF (Ly) m

set_option hygiene false in
/-- The frame invariant `J` holds at the starts (`StartsSX` at `WNF`). -/
local notation "StJ" J:max => ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
  ∀ s c fs, StartsSX h E (WNF) El Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs

set_option hygiene false in
/-- The switch region at depth `L`, below the top `v`. -/
local notation "RS" v:max => ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)

set_option hygiene false in
/-- The switch region's frame condition with `WordsNone`, below the top
`v` (`X64Hello1ClosedBVBF`'s). -/
local notation "FS" v:max => (fun m => (Spike.Lib.DmemPriv.WordsNone (Ly).Λ m.dmem ∧
  swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64) (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m) ∧
  CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => tpOf (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The setup call's callee region. -/
local notation "RC" => (RS v).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
set_option linter.unusedVariables false in
/-- The setup call's segment's premises at the callee's frame condition
`F'`, ghost `g` and frame `fr` (`X64Hello1HS`'s `PRE` at `FS` with
`WordsNone`). -/
local notation "PREF" F':max g:max fr:max => (RC).OK ∧ FStable (RC) F' ∧
  (∀ m, F' m → (FS v) m ∧ CallerCells (RS v) (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8 m) ∧
  g.ra = ((Ly).lab (setupMC (setupWords2 p)).sp0).toBitVec ∧ g.tp = TP0 ∧
  Spike.Lib.X64.Flow.CallTo p C0 g.c0 fr ∧ (RC).base = g.sp

set_option hygiene false in
set_option linter.unusedVariables false in
/-- The ghosts at the setup frame: the controls a frame run reaches from
the callee's entry `g.c0` at the frames `[fr]`. -/
local notation "GR" g:max fr:max => fun c => Spike.Lib.FrameRunM p (g.c0, [fr]) (c, [fr])

set_option hygiene false in
/-- The stack records' bottom keys at the setup frame (`SetupBot` at `FS`
with `WordsNone`). -/
local notation "SB" J:max v:max D1:max fS:max => fun k fs =>
  SetupBot p (Ly).lab ((MSS J) []) (RS v) (FS v) (setupMC (setupWords2 p)) D1 (Int64.ofInt fS)
    ⟨TOP - 8#64, TP0, C0⟩ (TP0).toBitVec k fs


/-- **The setup block's limit room at the setup call's callee's entry
`%rsp`** (`CxCore2.lim` at the setup context, `(rbR RC).base + 8`), the
switch region's top the first stack's (`v = TOP`): the setup block `rodata`
is a stack-checked callee of `scc_rt_main` whose need `n` fits
`Z + 16 + n ≤ 12288` (`calleeRow` at `CfgNeedOk`), so above the limit
`stacksA + 4096` or the limit word's initial `0` (`room_of_le`) the need fits
below the callee's entry `TOP - 24 - Z`. -/
theorem limS_setup (hp : Scc.Lower.Accepted2 p = true) (hs : (Scc.Lower.setupOf p).isSome = true)
    (hcfg : CfgNeedOk pcfg = true) {L D1 : Int} (hL0 : 8 ≤ L) (hLm : L ≤ 16384) (hD8 : 8 ≤ D1)
    (hL1 : 8 + 8 + (setupMC (setupWords2 p)).Z.toInt + 8 + D1 ≤ L) (J : InvS) {v : BitVec 64}
    (hv : v = TOP) {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) (hn : d.name = "rodata") :
    LimRoomX (OUT).place.need (Scc.Lower.Names.user d.name)
      (((MSS J) []).G ⟨limA (TP0), 8⟩) ((rbR (RC)).base.toNat + 8) := by
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2 h hp hs) (rtCodeOkS_setupWords2 h hp hs)).1
  have hZ := setupMC_Z _ hsw
  obtain ⟨f, hf, hck, hfn⟩ := userFn2 h hp hd
  have hcall := (user_mem_callees2 (setupWords2 p) (Spike.Lib.LowerNode.setupMask2 p)).1
  rw [← hn, ← hfn] at hcall
  obtain ⟨l, n, hr, -, hn'⟩ := calleeRow h hp hs hcfg hf hck hcall
  rw [hfn] at hr
  refine ⟨l, _, n, hr, fun w hw => ?_⟩
  -- the callee's entry: `TOP - 8 - 16 - Z`
  have hok : (swR v (-L) 0).OK := by
    rw [hv, Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ (by omega) hLm
  have hR1 : (RS v).OK :=
    Region.callee_ok hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
      (by show _ ≤ (0 : Int); omega)
  have hb1 : ((RS v).base.toNat : Int) = v.toNat - 8 :=
    Region.callee_base hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
  have hRC : (RC).OK :=
    Region.callee_ok hR1 (by show 8 - L ≤ _; omega) (by omega) (by show _ < (8 : Int); omega)
      (by show _ ≤ (8 : Int); omega)
  have hbc := Region.callee_base (hi' := 8) (kc := -8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0)
    (lo' := -D1) hR1 (by show 8 - L ≤ _; omega) (by omega) (by show _ < (8 : Int); omega)
  have hb2 := rbR_base hRC (by show -D1 ≤ -8; omega) (by show (0 : Int) ≤ 8; decide)
  have htop : v.toNat = (Ly).stacksA.toNat + 16384 := by
    rw [hv, show stacksA (Ly).lab = (Ly).stacksA from (Ly).lab_stacks, Spike.Lib.X64.Rt.top0_toNat]
  have hw' := Spike.Lib.X64.PhRec.room_of_le h (imms2Me Λ p)
    (b := (rbR (RC)).base.toNat + 8 + 8 - n) (by omega) w (by
      revert hw
      rw [Spike.Lib.X64.Rt.pinA_lab0]
      dsimp only [MSAt]; generalize ab2 p _ = ab; cases ab <;> exact fun h' => h')
  omega

/-- **The start's environment is small** (`me`'s word the first TCB's
address, a 64-bit number; `u` no word). -/
theorem envSmall_C0 (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty) :
    EnvSmall (C0).env := by
  have _ := hp
  have hc0 : (C0).env = [("me", .ptr .pub .void,
      [meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)]), ("u", .unit, [])] := by
    simp only [th02, hty]
  rw [hc0]
  intro b hb w hw k hk
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
  rcases hb with rfl | rfl
  · simp only [List.mem_singleton] at hw
    subst hw
    simp only [meW2, Spike.Lib.LowerNode.meNum, TermRun.cst] at hk
    have hk' := WeakMem.Val.num.inj hk
    subst hk'
    exact BitVec.isLt _
  · simp at hw

/-- **The setup frame is a base context** (`CxCore2` at the setup call's
callee context, in the rebased region `rbR RC`), the switch region's top
the first stack's (`v = TOP`): the region's facts from `PREF` and the
bounds (as `setupCxLB_ofPreT`'s), the frame placed (`framesPlaced_setup`)
with the start's environment (`envSmall_C0`), the ghosts' `FrOk2` along the
setup frame's run, the rows' memory side's kernel and reads, the room from
`Bounds2`'s `nS + 48 + 208 ≤ D1`, the limit room by `limS_setup` (`hcfg`),
and the allocator's `W2` instance at the context (`hAW`). -/
theorem cxCore2_setup {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) {ty : Ty}
    (hty : Scc.Lower.setupOf p = some ty) (hcfg : CfgNeedOk pcfg = true)
    {L D1 D2 : Int} {lS lM : String} {fS nS fM nM : Nat}
    (hB : Bounds2 cfg p sizes labelOffs (Ly) L D1 D2 lS lM fS nS fM nM) (J : InvS) {v : BitVec 64}
    (hv : v = TOP) {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) (hn : d.name = "rodata")
    {F' : MachineData → Prop} {g : WcG} {fr : TermRun.Frame} (hP : PREF F' g fr)
    (hAW : AllocW2At p (fun _ => none) (fun _ => 0) (fnCode2OfPMe hp h Λ j d hd).lcx (fnCode2OfPMe hp h Λ j d hd).fr
      (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec g.ra))
      ((fnCode2OfPMe hp h Λ j d hd).Bl g.ra)
      (fun lbl lsize s c => W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum
        (Spike.Lib.X64.PhRec.GOf Ly M0) (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly))
        (arOf (Ly).Λ) (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) Dt (Ab (Ly).lab) lbl lsize s c [fr])
      (KT) (Ly).exe (Ly).endPc (rbR (RC)) F' ((MSS J) [fr]) g.fp g.ra (TP0) (GR g fr) (imms2Me Λ p)
      (TailAt2 p j) (RetLk d.retTy)) :
    CxCore2 h hp Dt J j (rbR (RC)) F' [fr] g.fp g.ra (TP0) (GR g fr) := by
  obtain ⟨hrS, hfS, -, hnS, -, -, -, -, -, -, hrow, -, hL0, hLm, hL8, hD0, hD18, -, -, hD8, hL1, -⟩ := id hB
  obtain ⟨hR0, hF', hFF, -, -, hct, -⟩ := id hP
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2 h hp hs') (rtCodeOkS_setupWords2 h hp hs')).1
  have hZ := setupMC_Z _ hsw
  have hpN := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  obtain ⟨w, -, -, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  have hframe : (fnCode2OfPMe hp h Λ j d hd).fr.size = fS := by
    rw [hcx]; exact hrow _ hmem rfl (by show Scc.Lower.Names.user d.name = _; rw [hn])
  -- the regions: the switch region, its callee `RS TOP`, the setup call's `RC`, its rebased `rbR RC`
  have hok : (swR v (-L) 0).OK := by
    rw [hv, Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ (by omega) hLm
  have htop8 : v.toNat % 8 = 0 := by
    rw [hv, Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
  have hR1 : (RS v).OK :=
    Region.callee_ok hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
      (by show _ ≤ (0 : Int); omega)
  have hb1 : ((RS v).base.toNat : Int) = v.toNat - 8 :=
    Region.callee_base hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
  have hb8 : (RS v).base.toNat % 8 = 0 := by omega
  have hbc := Region.callee_base (hi' := 8) (kc := -8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0)
    (lo' := -D1) hR1 (by show 8 - L ≤ _; omega) (by omega) (by show _ < (8 : Int); omega)
  have hlo1 : (RC).lo ≤ -8 := by show -D1 ≤ -8; omega
  have hhi1 : (0 : Int) ≤ (RC).hi := by show (0 : Int) ≤ 8; decide
  have hb := rbR_base hR0 hlo1 hhi1
  have hlo0 : (rbR (RC)).lo ≤ -((fnCode2OfPMe hp h Λ j d hd).fr.size : Int) := by
    show -D1 + 8 ≤ _; rw [hframe]; omega
  have hhi : (0 : Int) ≤ (rbR (RC)).hi := by show (0 : Int) ≤ 8 + 8; decide
  have hfr : fr.env = (C0).env := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, rfl⟩ := hct
    rfl
  refine
    { hR := rbR_ok hR0 hlo1 hhi1
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
        (Spike.Lib.X64.Rt.stackOff_callee hR1 hb8 (by show (8 - L) % 8 = 0; omega)
          (by show (8 : Int) % 8 = 0; decide) (by show 8 - L ≤ _; omega) (by omega)
          (by show _ < (8 : Int); omega) (by omega)
          (Spike.Lib.X64.Rt.stackOff_callee hok htop8 (by show (-L) % 8 = 0; omega)
            (by show (0 : Int) % 8 = 0; rfl) (by show -L ≤ _; omega) (by omega)
            (by show _ < (0 : Int); omega) (by decide) (hFF m hm).1.1.2.2 (hFF m hm).1.2)
          (hFF m hm).2)
      hrs := fun d' hd' r k hr => ?_
      hfp := fun s _ => framesPlaced_setup h hp hty hct s
      hes := fun _ _ f hf => ?_
      hfs := fun _ => List.cons_ne_nil _ _
      hrd := ?_
      hwn := fun m hm => (hFF m hm).1.1.1
      hG0F := fun _ hc => FrOk2.runM hpN hc (FrOk2.step hpN (hct.step []) (hf0_start2 hty _))
      hG0 := fun _ _ h1 h2 => h1.trans h2
      hK := msOfAX_K_abi
      hAW := fun d' hd' _ => ?_
      room := fun d' hd' => ?_
      lim := fun m hm d' hd' => ?_
      htp := rfl
      hun := fun m hm => (hFF m hm).1.1.2.1.2 }
  · obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
    exact regionOff_of_rsOf (fnCode2OfPMe hp h Λ j d hd).hf hlo0 hhi hr
  · rw [List.mem_singleton] at hf
    subst hf
    rw [hfr]
    exact envSmall_C0 hp hty
  · intro w'
    dsimp only [MSAt]
    generalize ab2 p _ = ab
    cases ab <;> exact fun hw => hw
  · obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
    exact hAW
  · obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
    rw [hn]
    exact ⟨lS, fS + 8, nS, hrS, by show -D1 + 8 - 8 ≤ _; omega⟩
  · obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
    exact limS_setup h hp hs' hcfg hL0 hLm hD8 hL1 J hv hd hn

end Assembled

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.limS_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms limS_setup

/-- info: 'Spike.Lib.LowerX64.envSmall_C0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms envSmall_C0

/-- info: 'Spike.Lib.LowerX64.cxCore2_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cxCore2_setup

end Spike.Lib.LowerX64
