/-
**The setup call's `hS` for any `Accepted2` program with a setup block, at
an abstract abort fragment** (x86-64; the twin of
`Spike/Lib/LowerA64/G1SetupHS.lean`): `hS_ofOpenF`
(`Spike/Test/X64Hello1SetupOpenOfF.lean`) with the callee's aborts' fragment
`Ab` chosen by the open premises instead of fixed to the setup context's own
aborts (`AbU2`), so that a base context whose aborts' fragment contains every
context's aborts (`CxG2`, `Spike/Lib/LowerX64/G1FnSpec.lean`) can be the
setup frame's; the setup block's argument type from `Accepted2` (`setup2`)
instead of a premise, and no addition-free premise on the setup block (the
abort node's states are inside `Ab`, whose segment is an open premise).

- `SetupOpenG`, `OpenSG`: the setup frame's open premises at one choice and
  at every choice of the bounds (`SetupOpenF`, `OpenSF` with `hcx` giving
  the aborts' fragment, its inclusion of the abort node's states and its
  segment);
- `hS_ofOpenG`, `hSBVF_ofOpenSG`: `HSBVF`'s `hS` from them.
-/
import Spike.Test.X64Hello1SetupOpenOfF
import Spike.Lib.Src.ImmIn2
import Spike.Lib.Src.NumQLower

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
/-- **The setup frame's open premises at an abstract aborts' fragment**
(`SetupOpenF` with `hcx` choosing the callee's aborts' fragment `Ab`: the
base context at it, the abort node's states inside it, and its segment;
`SetupOpenF.hcx`, `habA` are the instance `Ab := AbU2`). -/
structure SetupOpenG (Dt : State → Prop) (hp : Scc.Lower.Accepted2 p = true) (J : InvS) (v : BitVec 64)
    (L D1 : Int) (fS : Nat) {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    (CxOk0 : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop) : Prop where
  /-- The setup function's segment at the contexts with their stack records (`SetupOpenF.hs`). -/
  hs : FnSpecC2 (W2S J) (KT) p (fun _ => none) (fun _ => 0) (MSS J)
    (CxOkS (p := p) (lbl := fun _ => none) (lsize := fun _ => 0) (fnCode2OfPMe hp h Λ) CxOk0 (SB J v D1 fS) j)
    (fnCode2OfPMe hp h Λ j d hd)
  /-- The base context at the setup frame at some aborts' fragment `Ab`, at the setup frame's bottom key:
  the abort node's states inside `Ab`, and `Ab` never ending inside `W2`. -/
  hcx : ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PREF F' g fr →
    (SB J v D1 fS) ⟨j, RC, F', g.fp, g.ra, TP0, GR g fr⟩ [fr] →
    ∃ Ab : FragS isa, CxOk0 j (RC) F' [fr] g.fp g.ra TP0 (GR g fr) Ab ∧
      (∀ s c fs', AbOf2 p (fun _ => none) (fnCode2OfPMe hp h Λ j d hd) (rbR (RC)) F' [fr] g.fp g.ra (GR g fr)
        s c fs' → Ab s c fs') ∧
      SegWS (W2S J) (KT) p (fun _ => none) (MSS J) Ab (fun _ _ _ => False)
  /-- The setup function's construct blocks' jump and call targets off the write abort (`SetupOpenF.hTg`). -/
  hTg : ∀ pc blk, SubCd (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab
      (Int64.ofBitVec ((Ly).lab (setupMC (setupWords2 p)).sp0).toBitVec)) pc blk →
    Kind2 (fnCode2OfPMe hp h Λ j d hd).fr blk → ∀ k (hk : k < blk.length) L,
      (Spike.Lib.X64.classify blk[k].1 = some (.jmp L) ∨ Spike.Lib.X64.classify blk[k].1 = some (.call L) ∨
        ∃ cc, Spike.Lib.X64.classify blk[k].1 = some (.jcc cc L)) → PosOff OP (Ly).lab ((Ly).lab L)

/-- **The setup call's `hS` at the frame condition with `WordsNone`, from
the open premises at an abstract aborts' fragment** (`hS_ofOpenF`'s proof,
the callee's aborts' fragment `SetupOpenG.hcx`'s, the setup block's argument
type from `Accepted2`'s `setup2`). -/
theorem hS_ofOpenG {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) {ty : Ty}
    (hty : Scc.Lower.setupOf p = some ty)
    {L D1 : Int} {fS : Nat} (hfD : (fS : Int) + 48 ≤ D1) (hL0 : 8 ≤ L) (hLm : L ≤ 16384)
    (hL8 : L % 8 = 0) (hD0 : 0 ≤ D1) (hD18 : D1 % 8 = 0)
    (hL1 : 8 + 8 + (setupMC (setupWords2 p)).Z.toInt + 8 + D1 ≤ L)
    (hrow : ∀ f, f ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs → f.checkStack = true →
      f.name = Scc.Lower.Names.user "rodata" → (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size = fS)
    (J : InvS) (v : BitVec 64)
    (H : ∀ j d (hd : (compiled2 p)[j]? = some d), d.name = "rodata" →
      ∃ CxOk0, SetupOpenG h Dt hp J (TOP) L D1 fS hd CxOk0) :
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
  -- the setup block `rodata` takes `Unit` (`setup2`)
  have hu : ∀ dr, p.find? (·.name == "rodata") = some dr → dr.argTy = .unit := by
    intro dr hfr
    have hds : Scc.Lower.decls2 [] (Scc.Lower.setupOf p) (Scc.Lower.hasPrint p) p = true := by
      simp only [Scc.Lower.Accepted2, Bool.and_eq_true] at hp; exact hp.1.1.1.1.1.1.1.2
    have hrn : dr.name = "rodata" := by simpa using List.find?_some hfr
    obtain ⟨E', hE'⟩ := Spike.Lib.LowerNode.decl2_of_decls2 hds dr (List.mem_of_find?_eq_some hfr)
    have hpe' : Scc.Lower.isPrintExt dr = false := by simp [Scc.Lower.isPrintExt, hrn]
    have hnl' : (Scc.Lower.hasPrint p && "rodata" == "printL") = false := by simp
    simp only [Scc.Lower.decl2, hpe', hrn, hnl', hty, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true] at hE'
    have hmr : ("rodata" == "main") = false := by decide
    simp only [hmr, Bool.false_eq_true, ↓reduceIte] at hE'
    unfold Scc.Lower.setup2 at hE'
    simp only [Bool.and_eq_true, beq_iff_eq] at hE'
    obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hat⟩, -⟩, -⟩, -⟩, -⟩ := hE'
    exact hat
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

    have hB := htp ▸ hSB j (GR g fr)
    obtain ⟨Ab, hcx0, hAbI, hAbS⟩ := HO.hcx F' g fr ⟨hR0, hF', hFF, hra, htp, hct, hbase⟩ hB
    refine ⟨GR g fr, Ab,
      fun he => {
        hcx := CxOkS.bot hcx0 hB
        hF := hF'
        hR := hR0
        hlo := by
          show -D1 ≤ -8 - ((fnCode2OfPMe hp h Λ j dr hd).fr.size : Int)
          rw [hframe]; omega
        hhi := by show (8 : Int) ≤ 8; exact Int.le_refl _
        hG0 := fun _ _ h1 h2 => h1.trans h2
        hW := hblk.1
        hWp := hblk.2
        hab := fun c0 hc0' _ _ hA => hAbI _ _ _ ⟨rfl, c0, hc0', hA⟩
        hg0 := .refl _
        hedge := he
        hR8 := by omega
        hl := by show (-D1) % 8 = 0; omega
        hh := by show (8 : Int) % 8 = 0; rfl
        hFO := hFO0 },
      FrOk2.step hpN (hct.step []) (hf0_start2 hty _), hAbS⟩

/-- **The open premises at every choice of the bounds** at an abstract
aborts' fragment (`OpenSF` at `SetupOpenG`). -/
def OpenSG (hp : Scc.Lower.Accepted2 p = true) (E : Entry)
    (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa) (Dt : State → Prop) : Prop :=
  ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
    Bounds2 cfg p sizes labelOffs (Ly) L D1 D2 lS lM fS nS fM nM →
    ∀ J : InvS, StJ J → ∀ j d (hd : (compiled2 p)[j]? = some d), d.name = "rodata" →
      ∃ CxOk0, SetupOpenG h Dt hp J (TOP) L D1 fS hd CxOk0

/-- **`HSBVF` from the open premises at an abstract aborts' fragment**
(`hS_ofOpenG` at each choice of the bounds), for any `Accepted2` program
with a setup block. -/
theorem hSBVF_ofOpenSG (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa} {Dt : State → Prop}
    (H : OpenSG h hp E El Dt) : HSBVF h ty E El Dt := by
  intro L D1 D2 lS lM fS nS fM nM hB J hJ v
  obtain ⟨-, -, -, -, hfD, -, -, -, -, -, hrow, -, hL0, hLm, hL8, hD0, hD18, -, -, -, hL1, -⟩ := id hB
  exact hS_ofOpenG h hp hty hfD hL0 hLm hL8 hD0 hD18 hL1 hrow J v
    fun j d hd hn => H L D1 D2 lS lM fS nS fM nM hB J hJ j d hd hn

end Assembled

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hS_ofOpenG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hS_ofOpenG

/-- info: 'Spike.Lib.LowerX64.hSBVF_ofOpenSG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hSBVF_ofOpenSG

end Spike.Lib.LowerX64
