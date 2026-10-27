/-
**`hello1`'s setup call `hS` on x86-64 at the start's frame condition
`WordsNone ∧ rtF`, no `hwn`** (the twin of `Spike/Test/X64Hello1HS.lean`'s
`hS_ofOpen` and `Spike/Test/X64Hello1SetupOpenOf.lean`'s `setupOpen_ofPre`
at `Spike/Test/X64Hello1ClosedBVBF.lean`'s frame condition): the setup call
at the switch region's frame condition `(WordsNone ∧ swFSL) ∧ CallerCells`
(`HSBVF`), so the private memory's `WordsNone` (`setupCxLB_ofPre`'s `hwn`)
is the frame condition's own.

The setup call is `setupCallWSB_ofPlaceOKC` at the frame condition directly
(`hS_assembledBC`'s proof; `hS_assembledBC` itself is stated at the frame
condition without `WordsNone`); the rest is `hS_ofOpen`'s proof with the
frame condition's projections moved past `WordsNone`. `setupCxLB_ofPre`'s
frame premise drops `WordsNone`, its `hwn` takes it.

Left (`SetupPreF`, at the setup call's premises `PREF F' g fr`): the
allocator's `W2` instance (`hAW`) and the buffer allocations' heap aborts'
segment (`habA`).

- `SetupOpenF`, `OpenSF`: `SetupOpen`, `OpenS` at the frame condition with
  `WordsNone` and the starts at `WordsNone ∧ rtF`;
- `hS_ofOpenF`, `hSBVF_ofOpenSF`: `hS` from them (`HSBVF`);
- `SetupPreF`, `OpenPF`: the remaining premises, at one choice and at every
  choice of the bounds;
- `setupOpenF_ofPre`: `SetupOpenF … (SetupCxLB …)` from the allocator's
  code, the block's points, the output's jump check and `SetupPreF`;
- `openSF_of_openPF`, `hello1_hSF_ofPre`: at `hello1o`, `OpenSF` and
  `HSBVF` from `OpenPF`.
-/
import Spike.Test.X64Hello1SetupOpenOf
import Spike.Test.X64Hello1ClosedBVBF

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region FrameRun)
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

set_option linter.unusedVariables false in
/-- **The setup frame's open premises at the frame condition with
`WordsNone`** (`SetupOpen` at `FS` with `WordsNone`; the bottom keys `SB`
at it), the aborts `AbU2` at the memory side of a family `Ja` (any: the
abort node's states do not see it; `Ja := J` for `SetupCxLB`, the family of
all pairs for the landings' `CxOkH`). -/
structure SetupOpenF (Dt : State → Prop) (hp : Scc.Lower.Accepted2 p = true) (J Ja : InvS) (v : BitVec 64)
    (L D1 : Int) (fS : Nat) {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    (CxOk0 : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop) : Prop where
  /-- The setup function's segment at the contexts with their stack records (`SetupOpen.hs`). -/
  hs : FnSpecC2 (W2S J) (KT) p (fun _ => none) (fun _ => 0) (MSS J)
    (CxOkS (p := p) (lbl := fun _ => none) (lsize := fun _ => 0) (fnCode2OfPMe hp h Λ) CxOk0 (SB J v D1 fS) j)
    (fnCode2OfPMe hp h Λ j d hd)
  /-- The base context at the setup frame (`SetupOpen.hcx`), at its bottom key. -/
  hcx : ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PREF F' g fr →
    (SB J v D1 fS) ⟨j, RC, F', g.fp, g.ra, TP0, GR g fr⟩ [fr] →
    CxOk0 j (RC) F' [fr] g.fp g.ra TP0 (GR g fr)
      (AbU2 p (MSS Ja) (fun _ => none) (fnCode2OfPMe hp h Λ j d hd) (rbR (RC)) F' [fr] g.fp g.ra (GR g fr))
  /-- The buffer allocations' heap aborts' segment at the setup frame (`SetupOpen.habA`), at the aborts'
  family `Ja`. -/
  habA : ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PREF F' g fr →
    SegWS (W2S J) (KT) p (fun _ => none) (MSS J)
      (AbAl2 (MSS Ja) (fun _ => none) (fnCode2OfPMe hp h Λ j d hd) (rbR (RC)) F' [fr]) (fun _ _ _ => False)
  /-- The setup function's construct blocks' jump and call targets off the write abort (`SetupOpen.hTg`). -/
  hTg : ∀ pc blk, SubCd (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab
      (Int64.ofBitVec ((Ly).lab (setupMC (setupWords2 p)).sp0).toBitVec)) pc blk →
    Kind2 (fnCode2OfPMe hp h Λ j d hd).fr blk → ∀ k (hk : k < blk.length) L,
      (Spike.Lib.X64.classify blk[k].1 = some (.jmp L) ∨ Spike.Lib.X64.classify blk[k].1 = some (.call L) ∨
        ∃ cc, Spike.Lib.X64.classify blk[k].1 = some (.jcc cc L)) → PosOff OP (Ly).lab ((Ly).lab L)

/-- **The setup call's `hS` at the frame condition with `WordsNone`, from
the open premises** (`hS_ofOpen`'s proof at `FS` with `WordsNone`, the call
by `setupCallWSB_ofPlaceOKC` at it, as `hS_assembledBC`'s). -/
theorem hS_ofOpenF {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) {ty : Ty}
    (hty : Scc.Lower.setupOf p = some ty) (hu : ∀ dr, p.find? (·.name == "rodata") = some dr → dr.argTy = .unit)
    {L D1 : Int} {fS : Nat} (hfD : (fS : Int) + 48 ≤ D1) (hL0 : 8 ≤ L) (hLm : L ≤ 16384)
    (hL8 : L % 8 = 0) (hD0 : 0 ≤ D1) (hD18 : D1 % 8 = 0)
    (hL1 : 8 + 8 + (setupMC (setupWords2 p)).Z.toInt + 8 + D1 ≤ L)
    (hrow : ∀ f, f ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs → f.checkStack = true →
      f.name = Scc.Lower.Names.user "rodata" → (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size = fS)
    (hno : ∀ (j : Nat) (d : Decl), (compiled2 p)[j]? = some d → d.name = "rodata" → addFreeT d.body = true)
    (J Ja : InvS) (v : BitVec 64)
    (H : ∀ j d (hd : (compiled2 p)[j]? = some d), d.name = "rodata" →
      ∃ CxOk0, SetupOpenF h Dt hp J Ja (TOP) L D1 fS hd CxOk0) :
    SetupCallWSB (W2S J) (KT) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (RS v) (FS v)
      (setupMC (setupWords2 p)).setup (setupMC (setupWords2 p)).Z D1 (Int64.ofInt fS) (SRetR (fun _ => none) ty)
      ((Ly).lab (setupMC (setupWords2 p)).sp0).toBitVec C0 TP0
      (SetupGF p (Ly).lab ((MSS J) []) (RS v) (FS v) (setupMC (setupWords2 p)) D1 (Int64.ofInt fS)
        ⟨TOP - 8#64, TP0, C0⟩ (TP0).toBitVec) := by
  -- off the first stack's top, no state is in the switch region's frame condition (`swF`)
  refine (Classical.em (v = TOP)).elim (fun hv => ?pos) (fun hv => ?neg)
  case neg =>
    intro F' _ _ hFF _ _ _ _ _ _
    refine ⟨fun _ _ _ => False, fun s c fs hP => ?_, fun _ _ _ h => h.elim, fun _ _ _ h => h.elim⟩
    obtain ⟨⟨-, -, -, -, σ, -, hF, -⟩, -⟩ := hP
    exact hv (hFF _ hF).1.1.2.1.1
  subst hv
  obtain ⟨dr, hf, hrt⟩ := Spike.Lib.LowerNode.rodata_of_setupOf hp hty
  obtain ⟨j, hd, hn⟩ := Spike.Lib.LowerNode.rodata_compiled2 hf
  obtain ⟨CxOk0, HO⟩ := H j dr hd hn
  obtain ⟨w, hLw, hna, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j dr hd
  have hframe : (fnCode2OfPMe hp h Λ j dr hd).fr.size = fS := by
    rw [hcx]; exact hrow _ hmem rfl (by show Scc.Lower.Names.user dr.name = _; rw [hn])
  have hna0 : (fnCode2OfPMe hp h Λ j dr hd).na = 0 := by
    have h1 := hLw.1
    rw [hu dr hf] at h1
    exact hna.trans (Option.some.inj (h1.symm.trans rfl))
  have hL : PosOff (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog (Ly).lab
      ((Ly).lab (proL (fnCode2OfPMe hp h Λ j dr hd).fr)) := by
    obtain ⟨n, hst⟩ := mem_starts (Scc.Lower.X64.lowerAll cfg p).low.ir 0 hmem
    have hok := Scc.Cert.Code1X64.fnOk1_of_fnCode1Ok
      (Scc.Cert.PlaceOK.X64.fnCode1_of_placeOKAt h (lowerAll_place_ir cfg p sizes labelOffs)) hst rfl
    rw [hcx]
    exact posOff_proL_of_fnOk1 hok (labelOf_user_not_abLabs _ _) _
  have hc0 : C0 = Spike.Lib.Ctl.mk Scc.Sem.SrcSem.setupTerm [("me", .ptr .pub .void,
      [meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)]), ("u", .unit, [])]
      none := by
    simp only [th02, hty]
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2 h hp hs') (rtCodeOkS_setupWords2 h hp hs')).1
  have hZ := setupMC_Z _ hsw
  have hpN := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  -- the setup call's return point (`scc_rt_main`'s marshalling block at `sp0`) is off the write abort
  have hraP : PosOff OP (Ly).lab ((Ly).lab (setupMC (setupWords2 p)).sp0) := by
    have hin := Spike.Lib.X64.Rt.mainSIn_of_okS (rtCodeOkS_setupWords2 h hp hs')
    simp only [Spike.Lib.X64.Rt.mainSIn, Bool.and_eq_true] at hin
    have h0 := posOff_of_blockAtB (lab := (Ly).lab) hin.1.1.2 (by simp only [setupMC]; decide)
      (by simp [Spike.Lib.X64.Rt.marshal] <;> omega)
    rwa [Spike.Lib.X64.Flow.ofNat_zero'] at h0
  rw [← hrt]
  refine setupCallWSB_ofPlaceOKC h (Λw := (Ly).Λ) (fnCode2OfPMe hp h Λ j dr hd)
    (fnCode2OfPMe_spec hp h Λ j dr hd).2.2 (raOk_setup _ _) HO.hs (hu dr hf) hna0
    (by rw [(fnCode2OfPMe hp h Λ j dr hd).hfn, hn]; rfl) (by rw [hframe]) hc0 ?_ ?_ hL
    (Spike.Lib.LowerNode.imms2Me_setupK hty) (valRep_meW2_of_placeOKAt h _) ?_ (fun _ hm => hm.1.2.1.2)
    (Spike.Lib.X64.Rt.rS0_sub _) (Spike.Lib.X64.Rt.fitS_of_sub _ (Spike.Lib.X64.Rt.rS0_sub _)) hpN ?_
  · intro cE fr hct
    have hcall := callTo_setupTerm (p := p) (c0 := C0) (by rw [hc0]) (by rw [hc0]; rfl) hf
    exact (CallTo.unique hct hcall).1
  · intro _ _ _ hl
    revert hl
    dsimp only [MSAt]
    generalize ab2 p _ = ab
    cases ab <;> exact fun hl => ⟨hl.rt, hl.mp, hl.unmapped, hl.room⟩
  · rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.limA_tcb0]
    exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1
  · intro F' hR0 hF' hFF g fr hra htp hct hGF hbase
    have hSB := fun j G0 => setupBot_ofGF hGF hbase j G0
    -- the regions: the switch region, its callee `RS v`, the setup call's `RC`
    have hok : (swR (TOP) (-L) 0).OK := by
      rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ (by omega) hLm
    have htop8 : (TOP).toNat % 8 = 0 := by
      rw [Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
    have hR1 : (RS (TOP)).OK :=
      Region.callee_ok hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
        (by show _ ≤ (0 : Int); omega)
    have hb1 : ((RS (TOP)).base.toNat : Int) = (TOP).toNat - 8 :=
      Region.callee_base hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
    have hb8 : (RS (TOP)).base.toNat % 8 = 0 := by omega
    have hbc := Region.callee_base (hi' := 8) (kc := -8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0)
      (lo' := -D1) hR1 (by show 8 - L ≤ _; omega) (by omega) (by show _ < (8 : Int); omega)
    have hlo0 : ((RS (TOP)).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8).lo ≤
        -8 - ((fnCode2OfPMe hp h Λ j dr hd).fr.size : Int) := by
      show -D1 ≤ _; rw [hframe]; omega
    have hhi0 : (8 : Int) ≤ ((RS (TOP)).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8).hi := by
      show (8 : Int) ≤ 8; exact Int.le_refl _
    have hFO0 : ∀ m, F' m → StackOff (rS0 (Ly))
        ((RS (TOP)).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8) m := fun m hm =>
      Spike.Lib.X64.Rt.stackOff_callee hR1 hb8 (by show (8 - L) % 8 = 0; omega)
        (by show (8 : Int) % 8 = 0; decide) (by show 8 - L ≤ _; omega) (by omega)
        (by show _ < (8 : Int); omega) (by omega)
        (Spike.Lib.X64.Rt.stackOff_callee hok htop8 (by show (-L) % 8 = 0; omega)
          (by show (0 : Int) % 8 = 0; rfl) (by show -L ≤ _; omega) (by omega)
          (by show _ < (0 : Int); omega) (by decide) (hFF m hm).1.1.2.2 (hFF m hm).1.2)
        (hFF m hm).2
    -- the body's blocks inside `W2` in the rebased region (`cxBlk2_ofFn`)
    obtain ⟨hF2, hR2, hlo2, hhi2⟩ := rbR_facts hF' hR0 hlo0 hhi0
    have hb2 := rbR_base hR0 (by omega) (by omega)
    have hblk : CxBlk2 (W2S J) (KT) p (fun _ => none) (fun _ => 0) (fnCode2OfPMe hp h Λ j dr hd)
        (rbR ((RS (TOP)).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8)) F' [fr] g.fp g.ra
        (GR g fr) :=
      cxBlk2_ofFn (Λ := (Ly).Λ) (Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms2Of p) (rS := rS0 (Ly)))
      (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hpN (fnCode2OfPMe hp h Λ j dr hd) hF2 hR2
      (by omega) hlo2 hhi2 (by show (-D1 + 8) % 8 = 0; omega) (by show ((8 : Int) + 8) % 8 = 0; decide)
      (Spike.Lib.X64.Rt.rS0_sub _) (Spike.Lib.X64.Rt.fitS_of_sub _ (Spike.Lib.X64.Rt.rS0_sub _))
      (fun m hm => stackOff_rbR hR0 (by omega) (by omega) (hFO0 m hm))
      (fun s _ => framesPlaced_setup h hp hty hct s)
      (G0 := GR g fr) (fun _ hc => FrOk2.runM hpN hc (FrOk2.step hpN (hct.step []) (hf0_start2 hty _)))
      (fp := g.fp) (ra := g.ra) (fun _ _ h => h) (by rw [hra, Int64.ofBitVec_toBitVec]; exact hraP)
      (by rw [hra]; exact HO.hTg)
    refine ⟨GR g fr,
      AbU2 p (MSS Ja) (fun _ => none) (fnCode2OfPMe hp h Λ j dr hd) _ F' [fr] g.fp g.ra (GR g fr),
      fun he => {
        hcx := CxOkS.bot (HO.hcx F' g fr ⟨hR0, hF', hFF, hra, htp, hct, hbase⟩ (htp ▸ hSB j (GR g fr)))
          (htp ▸ hSB j (GR g fr))
        hF := hF'
        hR := hR0
        hlo := by
          show -D1 ≤ -8 - ((fnCode2OfPMe hp h Λ j dr hd).fr.size : Int)
          rw [hframe]; omega
        hhi := by show (8 : Int) ≤ 8; exact Int.le_refl _
        hG0 := fun _ _ h1 h2 => h1.trans h2
        hW := hblk.1
        hWp := hblk.2
        hab := fun c0 hc0' _ _ hA => .inl ⟨rfl, c0, hc0', hA⟩
        hg0 := .refl _
        hedge := he
        hR8 := by omega
        hl := by show (-D1) % 8 = 0; omega
        hh := by show (8 : Int) % 8 = 0; rfl
        hFO := hFO0 },
      FrOk2.step hpN (hct.step []) (hf0_start2 hty _),
      SegWS.or_pre (abOf2_seg_addFree (hno j dr hd hn) hd)
        (HO.habA F' g fr ⟨hR0, hF', hFF, hra, htp, hct, hbase⟩)⟩

/-- **The open premises at every choice of the bounds** at the frame
condition with `WordsNone` (`OpenS`'s shape at `SetupOpenF`, the starts at
`WordsNone ∧ rtF`). -/
def OpenSF (hp : Scc.Lower.Accepted2 p = true) (E : Entry)
    (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa) (Dt : State → Prop) : Prop :=
  ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
    Bounds2 cfg p sizes labelOffs (Ly) L D1 D2 lS lM fS nS fM nM →
    ∀ J : InvS, StJ J → ∀ j d (hd : (compiled2 p)[j]? = some d), d.name = "rodata" →
      ∃ CxOk0, SetupOpenF h Dt hp J J (TOP) L D1 fS hd CxOk0

/-- **`HSBVF` from the open premises** (`hS_ofOpenF` at each choice of the
bounds). -/
theorem hSBVF_ofOpenSF (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hu : ∀ dr, p.find? (·.name == "rodata") = some dr → dr.argTy = .unit)
    {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa} {Dt : State → Prop}
    (hno : ∀ (j : Nat) (d : Decl), (compiled2 p)[j]? = some d → d.name = "rodata" → addFreeT d.body = true)
    (H : OpenSF h hp E El Dt) : HSBVF h ty E El Dt := by
  intro L D1 D2 lS lM fS nS fM nM hB J hJ v
  obtain ⟨-, -, -, -, hfD, -, -, -, -, -, hrow, -, hL0, hLm, hL8, hD0, hD18, -, -, -, hL1, -⟩ := id hB
  exact hS_ofOpenF h hp hty hu hfD hL0 hLm hL8 hD0 hD18 hL1 hrow hno J J v
    fun j d hd hn => H L D1 D2 lS lM fS nS fM nM hB J hJ j d hd hn

set_option linter.unusedVariables false in
/-- **The setup call's remaining premises at the frame condition with
`WordsNone`** at the bounds `L`, `D1` and the setup block's compiled index
`j` (`SetupPre` without `hwn`: the frame condition gives it). -/
structure SetupPreF (Dt : State → Prop) (hp : Scc.Lower.Accepted2 p = true) (J : InvS) (v : BitVec 64)
    (L D1 : Int) (fS : Nat) {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) : Prop where
  /-- The allocator's `W2` instance at the setup frame (`SetupPre.hAW`), at its bottom key. -/
  hAW : ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PREF F' g fr →
    (SB J v D1 fS) ⟨j, RC, F', g.fp, g.ra, TP0, GR g fr⟩ [fr] →
    AllocW2At p (fun _ => none) (fun _ => 0) (fnCode2OfPMe hp h Λ j d hd).lcx (fnCode2OfPMe hp h Λ j d hd).fr
      (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec g.ra))
      ((fnCode2OfPMe hp h Λ j d hd).Bl g.ra)
      (fun lbl lsize s c => W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum
        (Spike.Lib.X64.PhRec.GOf Ly M0) (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly))
        (arOf (Ly).Λ) (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) Dt (Ab (Ly).lab) lbl lsize s c [fr])
      (KT) (Ly).exe (Ly).endPc (rbR (RC)) F' ((MSS J) [fr]) g.fp g.ra (TP0) (GR g fr) (imms2Me Λ p)
      (TailAt2 p j) (RetLk d.retTy)
  /-- The buffer allocations' heap aborts' segment at the setup frame (`SetupOpenF.habA`). -/
  habA : ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PREF F' g fr →
    SegWS (W2S J) (KT) p (fun _ => none) (MSS J)
      (AbAl2 (MSS J) (fun _ => none) (fnCode2OfPMe hp h Λ j d hd) (rbR (RC)) F' [fr]) (fun _ _ _ => False)

/-- **`SetupOpenF` at `SetupCxLB` from the remaining premises**
(`setupOpen_ofPre` at the frame condition with `WordsNone`): `hcx` by
`setupCxLB_ofPre` at the frame premise without `WordsNone` and `hwn` the
frame condition's `WordsNone`. -/
theorem setupOpenF_ofPre (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {Dt : State → Prop} (J : InvS) {L D1 : Int} {fS nS : Nat} (hfS : fS + 8 ≤ nS)
    (hnS : (nS : Int) + 48 + 208 ≤ D1) (hL0 : 8 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0) (hD18 : D1 % 8 = 0)
    (hL1 : 8 + 8 + (setupMC (setupWords2 p)).Z.toInt + 8 + D1 ≤ L)
    (hrow : ∀ f, f ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs → f.checkStack = true →
      f.name = Scc.Lower.Names.user "rodata" → (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size = fS)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) (hn : d.name = "rodata")
    (hA : Spike.Lib.X64.Alloc.allocIn OP = true)
    (hnc : (tailsL d.body).all (fun t => !isCallLet t) = true)
    (hTn : ∀ x cn τ e, TailAt2 p j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    (hTg : tgOkB OP = true) (H : SetupPreF h Dt hp J (TOP) L D1 fS hd) :
    SetupOpenF h Dt hp J J (TOP) L D1 fS hd (SetupCxLB h hp Dt J hd) := by
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2 h hp hs') (rtCodeOkS_setupWords2 h hp hs')).1
  have hZ := setupMC_Z _ hsw
  have hok : (swR (TOP) (-L) 0).OK := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ (by omega) hLm
  have htop8 : (TOP).toNat % 8 = 0 := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
  have hR1 : (RS (TOP)).OK :=
    Region.callee_ok hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
      (by show _ ≤ (0 : Int); omega)
  have hb1 : ((RS (TOP)).base.toNat : Int) = (TOP).toNat - 8 :=
    Region.callee_base hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
  have hbc := Region.callee_base (hi' := 8) (kc := -8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0)
    (lo' := -D1) hR1 (by show 8 - L ≤ _; omega) (by omega) (by show _ < (8 : Int); omega)
  have hR8 : ((RS (TOP)).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8).base.toNat % 8 = 0 := by
    omega
  exact {
    hs := setupHs_ofCxLB0 h hp J hd _ hA hnc hTn
    hcx := fun F' g fr hP hB =>
      setupCxLB_ofPre h hp hty J (TOP) hfS hnS hL0 hLm hL8 hD18 hL1 hrow hd hn hP.1 hR8 hP.2.1
        (fun m hm => ⟨⟨(hP.2.2.1 m hm).1.1.2, (hP.2.2.1 m hm).1.2⟩, (hP.2.2.1 m hm).2⟩)
        hP.2.2.2.2.2.1 (fun m hm => (hP.2.2.1 m hm).1.1.1) (H.hAW F' g fr hP hB)
        fun Jc pcR _ _ hJ _ hA => Or.inr ⟨rfl, Jc, pcR, hJ, hA⟩
    habA := H.habA
    hTg := hTg_of_tgOkB hTg (fun _ _ h => h) (Ly).lab }

/-- **The remaining premises at every choice of the bounds** at the frame
condition with `WordsNone` (`SetupPreF` at `Bounds2`'s `L`, `D1`, every
invariant holding at the starts at `WordsNone ∧ rtF` and the setup block's
compiled index; `OpenSF`'s shape). -/
def OpenPF (hp : Scc.Lower.Accepted2 p = true) (E : Entry)
    (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa) (Dt : State → Prop) : Prop :=
  ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
    Bounds2 cfg p sizes labelOffs (Ly) L D1 D2 lS lM fS nS fM nM →
    ∀ J : InvS, StJ J → ∀ j d (hd : (compiled2 p)[j]? = some d), d.name = "rodata" →
      SetupPreF h Dt hp J (TOP) L D1 fS hd

end Assembled

/-- The program. -/
local notation "P1" => Spike.Test.Hello1MainSrc.hello1o

/-- `ld`'s layout of the linked executable. -/
local notation "Le" => Spike.Test.Hello1LinkedX64.Λe

/-- **`hello1o`'s open premises at the frame condition with `WordsNone`
from the remaining ones** (`OpenSF` from `OpenPF`: `setupOpenF_ofPre` at
`hello1_allocIn`, `hello1_rodata_noCall`, `hello1_rodata_elem2`,
`hello1_tgOkB`). -/
theorem openSF_of_openPF
    (h' : placeOKAt SccCertificate.placeCfg (lay2 Le P1)
      (Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1)
        SccCertificate.sizes SccCertificate.labelOffs) = true)
    {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa} {Dt : State → Prop}
    (H : OpenPF h' Spike.Lib.LowerNode.hello1o_accepted2 E El Dt) :
    OpenSF h' Spike.Lib.LowerNode.hello1o_accepted2 E El Dt := by
  intro L D1 D2 lS lM fS nS fM nM hB J hJ j d hd hn
  refine ⟨SetupCxLB h' Spike.Lib.LowerNode.hello1o_accepted2 Dt J hd, ?_⟩
  obtain ⟨-, hfS, -, hnS, -, -, -, -, -, -, hrow, -, hL0, hLm, hL8, -, hD18, -, -, -, hL1, -⟩ := id hB
  exact setupOpenF_ofPre h' Spike.Lib.LowerNode.hello1o_accepted2 hello1_hty.choose_spec J hfS hnS hL0 hLm
    hL8 hD18 hL1 hrow hd hn (hello1_allocIn h') (hello1_rodata_noCall j d hd hn) (hello1_rodata_elem2 hd hn)
    hello1_tgOkB (H L D1 D2 lS lM fS nS fM nM hB J hJ j d hd hn)

/-- **`hello1`'s setup call `hS` on x86-64 at the frame condition with
`WordsNone`, from the remaining premises** (`HSBVF`, `X64Hello1ClosedBVBF`'s
setup hole: `hSBVF_ofOpenSF` at `openSF_of_openPF`). -/
theorem hello1_hSF_ofPre
    (h' : placeOKAt SccCertificate.placeCfg (lay2 Le P1)
      (Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1)
        SccCertificate.sizes SccCertificate.labelOffs) = true)
    {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa} {Dt : State → Prop}
    (H : OpenPF h' Spike.Lib.LowerNode.hello1o_accepted2 E El Dt) :
    HSBVF h' hello1_hty.choose E El Dt :=
  hSBVF_ofOpenSF h' Spike.Lib.LowerNode.hello1o_accepted2 hello1_hty.choose_spec hello1_hu hello1_rodata_addFree
    (openSF_of_openPF h' H)

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hS_ofOpenF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hS_ofOpenF

/-- info: 'Spike.Lib.LowerX64.hSBVF_ofOpenSF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hSBVF_ofOpenSF

/-- info: 'Spike.Lib.LowerX64.setupOpenF_ofPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms setupOpenF_ofPre

/-- info: 'Spike.Lib.LowerX64.openSF_of_openPF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms openSF_of_openPF

/-- info: 'Spike.Lib.LowerX64.hello1_hSF_ofPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_hSF_ofPre

end Spike.Lib.LowerX64
