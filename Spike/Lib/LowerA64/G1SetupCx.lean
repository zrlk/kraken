/-
**The setup frame is a base context** (AArch64): `CxCore2`
(`Spike/Lib/LowerA64/G1FnSpec.lean`) at the setup call's callee context
(the region `RC` below the switch region's top `v` and `scc_rt_main`'s
frame `Z`, the frames `[fr]`, the saved pair and the thread pointer of the
call's ghost `g`, the first TCB, the ghosts `GR g fr`), from the setup
call's premises `PREF`, the setup frame's bottom key and the bounds
`Bounds2A`, for any `Accepted2` program with a setup block.

- `limS_setup`: the setup block's limit room at the callee region's base,
  the switch region's top the first stack's (`calleeRowA`: the row's need
  within `12288` less `Z`; the limit word's values the limit or `0`);
- `cxCore2_setup`: `CxCore2` at the setup context: the region's facts from
  `PREF` and the bounds (as `hS_ofOpenG`'s), the frame placed
  (`framesPlaced_setup`), its environment the start's (`me`, `u`), the
  ghosts along the setup frame's run, the room from `Bounds2A`'s
  `nS + 48 + 208 ≤ D1`, the limit room by `limS_setup` (`CfgNeedOkA`,
  `hcfg`) and the allocator's `W2` instance at the hello-style context
  `CxOkH` (`AllocWH`, a premise: `openAHA_of_accepted2` gives it at the
  write tail `fun _ => True`).
-/
import Spike.Lib.LowerA64.G1FnSpec
import Spike.Lib.LowerA64.G1SetupHS
import Spike.Lib.LowerA64.G1AllocOpen
import Spike.Lib.LowerA64.StackBounds2A

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region EnvSmall)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Rt (setupMC rS0 arOf swFSL rtF)
open Spike.Lib.A64.WriteAb (Ab)
open Spike.Lib.LowerNode (FrOk2 setupWords2 compiled2 TailAt2 imms2Me)
open Spike.Lib.A64.Flow.Ret0 (LimOk WcG CallerCells limA)
open Spike.Lib.AllocReach (Reach IN)

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))

set_option hygiene false in
/-- The record's static memory. -/
local notation "M0" => Spike.Lib.A64.PhRec.m0Of (Ly).Λ OP (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).secs

set_option hygiene false in
/-- `MSAt` at `Closed2AtA`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max =>
  MSAt h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- The program's start control (`S0A`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).env, none⟩ : Ctl)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The first TCB's address. -/
local notation "X0" => pinA (Ly).lab + 0#64 + 8#64

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => UInt64.ofBitVec (X0)

set_option hygiene false in
/-- The switch region's frame condition with `WordsNone`, below the top `v`
(`A64Hello1ClosedBVBF`'s). -/
local notation "FS" v:max => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧
  swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) v m

set_option hygiene false in
/-- The setup call's callee region. -/
local notation "RC" => (swR v (-L) 0).callee (-(setupMC (setupWords2 p)).Z.toInt) (-D1) 0

set_option hygiene false in
set_option linter.unusedVariables false in
/-- The ghosts at the setup frame: the controls a frame run reaches from
the callee's entry `g.c0` at the frames `[fr]`. -/
local notation "GR" g:max fr:max => fun c => Spike.Lib.FrameRunM p (g.c0, [fr]) (c, [fr])

set_option hygiene false in
set_option linter.unusedVariables false in
/-- The setup call's segment's premises at the callee's frame condition
`F'`, ghost `g` and frame `fr` (`A64Hello1HS`'s `PRE` at `FS` with
`WordsNone`). -/
local notation "PREF" F':max g:max fr:max => (RC).OK ∧ (RC).base.toNat % 16 = 0 ∧ FStable (RC) F' ∧
  (∀ m, F' m → (FS v) m ∧ CallerCells (swR v (-L) 0) (-(setupMC (setupWords2 p)).Z.toInt) (-D1) 0 m) ∧
  g.ra = ((Ly).lab (setupMC (setupWords2 p)).e0 + 4).toBitVec ∧ g.tp = TP0 ∧
  Spike.Lib.A64.Flow.CallTo p C0 g.c0 fr ∧ (RC).base = g.sp

set_option hygiene false in
/-- The stack records' bottom keys at the setup frame (`SetupBot` at `FS`
with `WordsNone`). -/
local notation "SB" J:max v:max D1:max fS:max => fun k fs =>
  SetupBot p (Ly).lab ((MSS J) []) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
    (setupMC (setupWords2 p)) D1 (Int64.ofInt fS) ⟨TOP, TP0, C0⟩ (X0) k fs

/-- **The setup block's limit room at the setup call's callee region**
(`CxCore2.lim` at the setup context), the switch region's top the first
stack's (`v = TOP`, the frame condition's): the setup block `rodata` is a
stack-checked callee of `scc_rt_main` whose need `n` fits `Z + n ≤ 12288`
(`calleeRowA` at `CfgNeedOkA`), so above the limit `stacksA + 4096` or the
limit word's initial `0` (`gOf_lim`, `limInit_ofPlaceOK`) the need fits
below the callee region's base `TOP - Z`. -/
theorem limS_setup (hp : Scc.Lower.Accepted2 p = true) (hs : (Scc.Lower.setupOf p).isSome = true)
    (hcfg : CfgNeedOkA pcfg = true) {L D1 : Int} (hL0 : 0 ≤ L) (hLm : L ≤ 16384) (hD10 : 0 ≤ D1)
    (hL1 : (setupMC (setupWords2 p)).Z.toInt + D1 ≤ L) (J : InvS) {v : BitVec 64} (hv : v = TOP)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) (hn : d.name = "rodata") :
    LimRoomA (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need (Scc.Lower.Names.user d.name)
      (((MSS J) []).G ⟨limA (TP0), 8⟩) (RC).base.toNat := by
  subst hv
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2A h hp hs) (rtCodeOkS_setupWords2A h hp hs)).1
  have hZ8 := setupMC_Z _ hsw
  obtain ⟨f, fi, hf, hck, hfn⟩ := userFn2A h hp hd
  have hcall := (user_mem_calleesA (setupWords2 p) (Spike.Lib.LowerNode.setupMask2 p)).1
  rw [← hn, ← hfn] at hcall
  obtain ⟨l, n, hr, -, hn⟩ := calleeRowA h hp hs hcfg hf hck hcall
  rw [hfn] at hr
  refine ⟨l, _, n, hr, fun w hw => ?_⟩
  -- the callee region's base: `TOP - Z`
  have hok : (swR (TOP) (-L) 0).OK := by
    rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hLm
  have hb := Region.callee_base (kc := -(setupMC (setupWords2 p)).Z.toInt) (lo' := -D1) (hi' := 0) hok (by show -L ≤ _; omega) (by omega)
    (by show _ < (0 : Int); omega)
  have htop : ((swR (TOP) (-L) 0).base.toNat : Int) = (Ly).stacksA.toNat + 16384 := by
    show ((TOP).toNat : Int) = _
    rw [show stacksA (Ly).lab = (Ly).stacksA from (Ly).lab_stacks, Spike.Lib.A64.Rt.top0_toNat]; rfl
  have hw' : Spike.Lib.A64.PhRec.GOf Ly M0 ⟨(Ly).pinA + 16#64, 8⟩ w := by
    revert hw
    rw [(Ly).lab_pin, Spike.Lib.A64.Rt.limA_tcb0]
    dsimp only [MSAt]; generalize ab2 p _ = ab; cases ab <;> exact fun h' => h'
  have := (Ly).pool_fit
  obtain ⟨h1, h2⟩ := (Ly).stacks_sub
  simp only at h1 h2
  rcases Spike.Lib.A64.PhRec.gOf_lim hw' with rfl | rfl
  · have hv : ((Spike.Lib.A64.PhRec.limV (Ly)).setWidth 64).toNat = (Ly).stacksA.toNat + 4096 := by
      simp only [Spike.Lib.A64.PhRec.limV, BitVec.setWidth_setWidth_of_le _ (by decide : 64 ≤ 128),
        BitVec.setWidth_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    rw [hv]
    omega
  · have hv : (((M0).initVal ⟨(Ly).pinA + 16#64, 8⟩).setWidth 64).toNat = 0 := by
      rw [Spike.Lib.A64.PhRec.limInit_ofPlaceOK h (imms2Me Λ p)]
      rfl
    rw [hv]
    omega

/-- **The start's environment is small** (`me`'s word the first TCB's
address, a 64-bit number; `u` no word). -/
theorem envSmall_C0 (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty) :
    EnvSmall (C0).env := by
  have _ := hp
  have hc0 : (C0).env = [("me", .ptr .pub .void, [meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))]),
      ("u", .unit, [])] := by
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
callee context): the region's facts from `PREF` and the bounds (as
`hS_ofOpenG`'s), the frame placed (`framesPlaced_setup`) with the start's
environment (`envSmall_C0`), the ghosts' `FrOk2` along the setup frame's
run, the rows' memory side's kernel and reads, the room from `Bounds2A`'s
`nS + 48 + 208 ≤ D1`, the limit room by `limS_setup` (`hcfg`), and the
allocator's `W2` instance at the context `CxOkH` the same one (`hAW`). -/
theorem cxCore2_setup {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) {ty : Ty}
    (hty : Scc.Lower.setupOf p = some ty) (hcfg : CfgNeedOkA pcfg = true)
    {L D1 D2 : Int} {lS lM : String} {fS nS fM nM : Nat}
    (hB : Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM) (J : InvS) (v : BitVec 64)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) (hn : d.name = "rodata")
    (hAW : AllocWH h Dt hp J v L D1 fS hd)
    {F' : MachineData → Prop} {g : WcG} {fr : TermRun.Frame} (hP : PREF F' g fr)
    (hSB : (SB J v D1 fS) ⟨j, RC, F', g.fp, g.ra, TP0, GR g fr⟩ [fr]) :
    CxCore2 h hp Dt J j (RC) F' [fr] g.fp g.ra (TP0) (GR g fr) := by
  obtain ⟨hrS, hfS, -, hnS, -, -, -, -, hrow, -, hL0, hLm, hL8, hD10, hD18, -, -, hL1, -, -, -, -, -⟩ := id hB
  obtain ⟨hR0, hal, hF', hFF, hra, htp, hct, hbase⟩ := id hP
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2A h hp hs') (rtCodeOkS_setupWords2A h hp hs')).1
  have hZ := setupMC_Z _ hsw
  have hpN := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  obtain ⟨w, fi, -, -, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  have hframe : (fnCode2OfPMe hp h Λ j d hd).cx.frame = fS := by
    rw [hcx]; exact hrow _ _ hmem rfl (by show Scc.Lower.Names.user d.name = _; rw [hn])
  have hlo0 : -D1 ≤ -((fnCode2OfPMe hp h Λ j d hd).cx.frame : Int) := by rw [hframe]; omega
  have hhi : (0 : Int) ≤ 0 := Int.le_refl _
  have hFO0 : ∀ m, F' m → StackOff (rS0 (Ly)) (RC) m := by
    intro m hm
    obtain ⟨⟨-, ⟨hv, -⟩, hoff⟩, hcc⟩ := hFF m hm
    subst hv
    have hok : (swR (TOP) (-L) 0).OK := by
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hLm
    have h8 : (swR (TOP) (-L) 0).base.toNat % 8 = 0 := by
      show (TOP).toNat % 8 = 0
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; have := Spike.Lib.A64.Rt.rt_h16 (Ly); omega
    exact Spike.Lib.A64.Flow.Ret0.Inst.stackOff_callee hok h8 (by show (-L) % 8 = 0; omega)
      (by show (0 : Int) % 8 = 0; rfl)
      (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega) (by omega) hoff hcc
  have hfr : fr.env = (C0).env := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, rfl⟩ := hct
    rfl
  refine
    { hR := hR0
      hal := hal
      hl := by show (-D1) % 8 = 0; omega
      hh := by show (0 : Int) % 8 = 0; rfl
      hhi := hhi
      hFS := hF'
      hFO := hFO0
      hrs := fun d' hd' r k hr => ?_
      hfp := fun s _ => framesPlaced_setup h hp hty hct s
      hes := fun _ _ f hf => ?_
      hfs := fun _ => List.cons_ne_nil _ _
      hrd := ?_
      hwn := fun m hm => (hFF m hm).1.1
      hG0F := fun _ hc => FrOk2.runM hpN hc (FrOk2.step hpN (hct.step []) (hf0_start2A hty _))
      hG0 := fun _ _ h1 h2 => h1.trans h2
      hK := msOfAX_K_abi
      hAW := fun d' hd' _ => ?_
      room := fun d' hd' => ?_
      lim := fun m hm d' hd' => ?_
      htp := rfl
      hun := fun m hm => (hFF m hm).1.2.1.2 }
  · obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
    exact regionOff_of_rsOf (fnCode2OfPMe hp h Λ j d hd).hf hlo0 hhi hr
  · rw [List.mem_singleton] at hf
    subst hf
    rw [hfr]
    exact envSmall_C0 hp hty
  · dsimp only [MSAt]; generalize ab2 p _ = ab; cases ab <;> exact fun _ h' => h'
  · obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
    exact hAW _ _ _ _ _ _ _ _
      ⟨d, hd, L, D1, fS, nS, v, g, fr, J, hn, hfS, hnS, hL0, hLm, hL8, hD18, hL1, hrow,
        ⟨hR0, hal, hF', fun m hm => ⟨(hFF m hm).1.2, (hFF m hm).2⟩, hra, htp, hct, hbase⟩,
        fun m hm => (hFF m hm).1.1, hSB, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hSB
  · obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
    rw [hn]
    exact ⟨lS, fS, nS, hrS, by show -D1 ≤ _; omega⟩
  · obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
    exact limS_setup h hp hs' hcfg hL0 hLm hD10 hL1 J (hFF m hm).1.2.1.1 hd hn

end Assembled

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.limS_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.limS_setup

/-- info: 'Spike.Lib.LowerA64.envSmall_C0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.envSmall_C0

/-- info: 'Spike.Lib.LowerA64.cxCore2_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.cxCore2_setup
