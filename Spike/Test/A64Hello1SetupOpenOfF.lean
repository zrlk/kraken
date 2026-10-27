/-
**`hello1`'s setup call `hS` on AArch64 at the frame condition with
`WordsNone`, from the setup frame's premises without `hwn`** (the twin of
`Spike/Test/X64Hello1SetupOpenOfF.lean`): `Spike/Test/A64Hello1HS.lean` and
`Spike/Test/A64Hello1SetupOpenOf.lean` at `A64Hello1ClosedBVBF`'s frame
condition `WordsNone ∧ swFSL` (`FS`) and starts at `WordsNone ∧ rtF`
(`StJ`), for `HSBVFA`. The setup call's premises `PREF` then carry
`WordsNone` of the callee's frame condition, so `setupCxLB_ofPre`'s `hwn`
is a projection of them and leaves the remaining premises.

`hS_assembledBAC` is stated at `swFSL` without `WordsNone`; `hS_ofOpenFA`
calls `setupCallWSB_ofPlaceOKC` (generic in the frame condition) directly,
with the bottom keys by `setupBot_ofGF`.

- `SetupOpenFA`, `OpenSFA`: `SetupOpenA`, `OpenSA` at `PREF`, the bottom keys
  `SetupBot` at `FS`;
- `hS_ofOpenFA`, `hSBVFA_ofOpenSFA`: `hS_ofOpenA`, `hSBA_ofOpenSA` at `FS`
  (`HSBVFA`);
- `SetupPreFA`, `OpenPFA`: `SetupPreA`, `OpenPA` without `hwn` (`hAW`, `habA`);
- `setupOpenFA_ofPre`: `setupOpenA_ofPre` at `PREF`, `hwn` from `PREF`;
- `openSFA_of_openPFA`, `hello1_hSFA_ofPre`: at `hello1o`, `HSBVFA` from
  `OpenPFA` at any landings and write tail.
-/
import Spike.Test.A64Hello1SetupOpenOf
import Spike.Test.A64Hello1ClosedBVBF

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Rt (setupMC SetupCallWSB SetupGF rS0 arOf swFSL rtF)
open Spike.Lib.A64.WriteAb (Ab)
open Spike.Lib.A64.AllocG (abLabs)
open Spike.Lib.LowerNode (FrOk2 setupWords2 compiled2 TailAt2 imms2Me addFreeT)
open Spike.Lib.A64.Flow.Ret0 (LimOk WcG CallerCells limA)
open Spike.Lib.AllocReach (Reach IN)

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates (`fnCode2OfP`'s code facts'). -/
local notation "LY0" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.A64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))

set_option hygiene false in
/-- The record's static memory. -/
local notation "M0" => Spike.Lib.A64.PhRec.m0Of (Ly).Λ OP (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).secs

set_option hygiene false in
/-- `W2At` at `Closed2AtA`'s instance. -/
local notation "W2S" J:max => W2At h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum (rS0 (Ly)) J Dt (fun _ => 0)

set_option hygiene false in
/-- `MSAt` at `Closed2AtA`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max =>
  MSAt h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- **The start's frame condition**: the runtime's words unloaded and no
heap or image word loaded (`Closed2AtWA`'s). -/
local notation "WNF" => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧ rtF (Ly) m

set_option hygiene false in
/-- The frame invariant `J` holds at the starts (`StartsSA` at `WNF`). -/
local notation "StJ" J:max => ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
  ∀ s c fs, StartsSA h E (WNF) El Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

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

set_option linter.unusedVariables false in
/-- **The setup frame's open premises at the frame condition with
`WordsNone`** (`SetupOpenA` at `PREF`, the bottom keys `SB` at `FS`). -/
structure SetupOpenFA (Dt : State → Prop) (hp : Scc.Lower.Accepted2 p = true) (J : InvS) (v : BitVec 64)
    (L D1 : Int) (fS : Nat) {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    (CxOk0 : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop) : Prop where
  /-- The setup function's segment at the contexts with their stack records (`SetupOpenA.hs`). -/
  hs : FnSpecC2 (W2S J) (KT) p (fun _ => none) (fun _ => 0) (MSS J)
    (CxOkS (p := p) (lbl := fun _ => none) (lsize := fun _ => 0) (fnCode2OfPMe hp h Λ) CxOk0 (SB J v D1 fS) j)
    (fnCode2OfPMe hp h Λ j d hd)
  /-- The base context at the setup frame (`SetupOpenA.hcx`), at the setup frame's bottom key. -/
  hcx : ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PREF F' g fr →
    (SB J v D1 fS) ⟨j, RC, F', g.fp, g.ra, TP0, GR g fr⟩ [fr] →
    CxOk0 j (RC) F' [fr] g.fp g.ra TP0 (GR g fr)
      (AbU2 p (MSS J) (fun _ => none) (fnCode2OfPMe hp h Λ j d hd) (RC) F' [fr] g.fp g.ra (GR g fr))
  /-- The setup function's construct blocks' branch and call targets off the write abort
  (`SetupOpenA.hTg`). -/
  hTg : ∀ pc blk, SubCd (CdCLE OP (Spike.Lib.A64.PhRec.okPc LY0) (Spike.Lib.A64.PhRec.ph LY0) (LY0).lab
      (Int64.ofBitVec ((Ly).lab (setupMC (setupWords2 p)).e0 + 4).toBitVec)) pc blk →
    Kind2 (fnCode2OfPMe hp h Λ j d hd).cx blk → ∀ k (hk : k < blk.length) L,
      (classify blk[k] = some (.b L) ∨ classify blk[k] = some (.bl L) ∨
        (∃ cc, classify blk[k] = some (.bcond cc L)) ∨ (∃ t, classify blk[k] = some (.cbz t L)) ∨
        ∃ t, classify blk[k] = some (.cbnz t L)) → PosOff OP (Ly).lab ((Ly).lab L)
  /-- The aborts' segment at the setup frame (`SetupOpenA.hab`). -/
  hab : ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PREF F' g fr →
    SegWS (W2S J) (KT) p (fun _ => none) (MSS J)
      (AbOf2 p (fun _ => none) (fnCode2OfPMe hp h Λ j d hd) (RC) F' [fr] g.fp g.ra (GR g fr)) (fun _ _ _ => False)
  /-- The buffer allocations' heap aborts' segment at the setup frame (`SetupOpenA.habA`). -/
  habA : ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PREF F' g fr →
    SegWS (W2S J) (KT) p (fun _ => none) (MSS J)
      (AbAl2 (MSS J) (fun _ => none) (fnCode2OfPMe hp h Λ j d hd) (RC) F' [fr]) (fun _ _ _ => False)

/-- **The setup call's `hS` at the frame condition with `WordsNone`, from
the open premises** (`hS_ofOpenA`'s proof at `FS`, the call by
`setupCallWSB_ofPlaceOKC` at it as in `hS_assembledBAC`, the bottom keys by
`setupBot_ofGF`). -/
theorem hS_ofOpenFA {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) {ty : Ty}
    (hty : Scc.Lower.setupOf p = some ty) (hu : ∀ dr, p.find? (·.name == "rodata") = some dr → dr.argTy = .unit)
    {L D1 : Int} {fS nS : Nat} (hfS : fS ≤ nS) (hnS : (nS : Int) + 48 ≤ D1) (hL0 : 0 ≤ L) (hLm : L ≤ 16384)
    (hL8 : L % 8 = 0) (hD18 : D1 % 8 = 0) (hL1 : (setupMC (setupWords2 p)).Z.toInt + D1 ≤ L)
    (hrow : ∀ f fi, (f, fi) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx → f.checkStack = true →
      f.name = Scc.Lower.Names.user "rodata" →
        (Scc.Cert.Code1A64.ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi f).frame = fS)
    (J : InvS) (v : BitVec 64)
    (H : ∀ j d (hd : (compiled2 p)[j]? = some d), d.name = "rodata" →
      ∃ CxOk0, SetupOpenFA h Dt hp J v L D1 fS hd CxOk0) :
    SetupCallWSB (W2S J) (KT) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
      (setupMC (setupWords2 p)).setup (setupMC (setupWords2 p)).Z D1 (Int64.ofInt fS) (SRetR (fun _ => none) ty)
      ((Ly).lab (setupMC (setupWords2 p)).e0 + 4).toBitVec C0 (TP0)
      (SetupGF p (Ly).lab ((MSS J) []) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v) (setupMC (setupWords2 p)) D1
        (Int64.ofInt fS) ⟨TOP, TP0, C0⟩ (X0)) := by
  obtain ⟨dr, hf, hrt⟩ := Spike.Lib.LowerNode.rodata_of_setupOf hp hty
  obtain ⟨j, hd, hn⟩ := Spike.Lib.LowerNode.rodata_compiled2 hf
  obtain ⟨CxOk0, HO⟩ := H j dr hd hn
  obtain ⟨w, fi, hLw, hna, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j dr hd
  have hframe : (fnCode2OfPMe hp h Λ j dr hd).cx.frame = fS := by
    rw [hcx]; exact hrow _ _ hmem rfl (by show Scc.Lower.Names.user dr.name = _; rw [hn])
  have hna0 : (fnCode2OfPMe hp h Λ j dr hd).na = 0 := by
    have h1 := hLw.1
    rw [hu dr hf] at h1
    exact hna.trans (Option.some.inj (h1.symm.trans rfl))
  have hL : PosOff (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog (Ly).lab
      ((Ly).lab (proL (fnCode2OfPMe hp h Λ j dr hd).cx)) := by
    have hok := Scc.Cert.Code1A64.fnOk1_of_fnCode1Ok (fnCode1_of_placeOKAt h (lowerAll_place_ir cfg p)) hmem rfl
    have hab : proL (fnCode2OfPMe hp h Λ j dr hd).cx ∉ abLabs := by
      unfold proL; exact local_not_abLabs (fnCode2OfPMe_spec hp h Λ j dr hd).2.2.1 _
    rw [hcx] at hab ⊢
    exact posOff_proL_of_fnOk1 hok hab _
  have hc0 : C0 = Spike.Lib.Ctl.mk Scc.Sem.SrcSem.setupTerm [("me", .ptr .pub .void,
      [meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))]), ("u", .unit, [])] none := by
    simp only [th02, hty]
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2A h hp hs') (rtCodeOkS_setupWords2A h hp hs')).1
  have hZ := setupMC_Z _ hsw
  have hpN := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  rw [← hrt]
  refine setupCallWSB_ofPlaceOKC h (Λw := (Ly).Λ) (fnCode2OfPMe hp h Λ j dr hd)
    (fnCode2OfPMe_spec hp h Λ j dr hd).2.2 (raOk_setup _ _) HO.hs (hu dr hf) hna0
    (by rw [(fnCode2OfPMe hp h Λ j dr hd).hfn, hn]; rfl) (by rw [hframe]) hc0 ?_ ?_ hL
    (Spike.Lib.LowerNode.imms2Me_setupK hty) (valRep_meW2_of_placeOKAtA h _) ?_ (fun _ hm => hm.2.1.2)
    (Spike.Lib.A64.Rt.rS0_sub _) (Spike.Lib.A64.Rt.fitS_of_sub _ (Spike.Lib.A64.Rt.rS0_sub _)) hpN ?_
  · intro cE fr hct
    have hcall := callTo_setupTerm (p := p) (c0 := C0) (by rw [hc0]) (by rw [hc0]; rfl) hf
    exact (CallTo.unique hct hcall).1
  · intro _ _ _ hl
    revert hl
    dsimp only [MSAt]
    generalize ab2 p _ = ab
    cases ab <;> exact fun hl => ⟨hl.rt, hl.mp, hl.unmapped, hl.room⟩
  · rw [(Ly).lab_pin, Spike.Lib.A64.Rt.limA_tcb0]
    exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1
  · intro F' hR0 hal hF' hFF g fr hra htp hct hGF hbase
    have hSB := fun j G0 => setupBot_ofGF hGF hbase j G0
    have hP : PREF F' g fr := ⟨hR0, hal, hF', hFF, hra, htp, hct, hbase⟩
    have hlo0 : (RC).lo ≤ -((fnCode2OfPMe hp h Λ j dr hd).cx.frame : Int) := by
      show -D1 ≤ _; rw [hframe]; omega
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
    -- the setup call's return point (`scc_rt_main`'s marshalling block at `sp0`, one instruction past
    -- `e0`) is off the write abort
    have hraP : PosOff OP (Ly).lab ((Ly).lab (setupMC (setupWords2 p)).e0 + 4) := by
      have hin := Spike.Lib.A64.Rt.mainSIn_of_okS (rtCodeOkS_setupWords2A h hp hs')
      simp only [Spike.Lib.A64.Rt.mainSIn, Bool.and_eq_true] at hin
      have h0 := posOff_of_blockAt (lab := (Ly).lab) hin.1.1.2 (by simp only [setupMC]; decide) (i := 0)
        (by simp [Spike.Lib.A64.Rt.marshal]; omega)
      have hg : (Ly).lab (setupMC (setupWords2 p)).sp0 = (Ly).lab (setupMC (setupWords2 p)).e0 + 4 :=
        Scc.Cert.Rt.A64.label_labelGap (Ly).lays hin.1.1.1.2
      rw [Nat.add_zero, ofNat4_zero, hg] at h0
      exact h0
    -- the body's blocks inside `W2` (`cxBlk2_ofFn`)
    have hblk : CxBlk2 (W2S J) (KT) p (fun _ => none) (fun _ => 0) (fnCode2OfPMe hp h Λ j dr hd) (RC) F' [fr]
        g.fp g.ra (GR g fr) :=
      cxBlk2_ofFn (Λ := (Ly).Λ) (Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms2Of p) (rS := rS0 (Ly)))
        (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hpN (fnCode2OfPMe hp h Λ j dr hd) hF' hR0 hal hlo0
        (show (0 : Int) ≤ 0 from Int.le_refl _) (by show (-D1) % 8 = 0; omega) (by show (0 : Int) % 8 = 0; rfl)
        (Spike.Lib.A64.Rt.rS0_sub _) (Spike.Lib.A64.Rt.fitS_of_sub _ (Spike.Lib.A64.Rt.rS0_sub _)) hFO0
        (fun s _ => framesPlaced_setup h hp hty hct s) (G0 := GR g fr)
        (fun _ hc => FrOk2.runM hpN hc (FrOk2.step hpN (hct.step []) (hf0_start2A hty _)))
        (fp := g.fp) (ra := g.ra) (fun _ _ h => h) (by rw [hra, Int64.ofBitVec_toBitVec]; exact hraP)
        (by rw [hra]; exact HO.hTg)
    refine ⟨GR g fr,
      AbU2 p (MSS J) (fun _ => none) (fnCode2OfPMe hp h Λ j dr hd) (RC) F' [fr] g.fp g.ra (GR g fr),
      ⟨?_, hF', hR0, hal, hlo0, ?_, fun _ _ h1 h2 => h1.trans h2, hblk.1, hblk.2,
        fun c0 hc0' _ _ hA => .inl ⟨rfl, c0, hc0', hA⟩, .refl _, ?_, ?_, hFO0⟩, ?_,
      SegWS.or_pre (HO.hab F' g fr hP) (HO.habA F' g fr hP)⟩
    · have hB := hSB j (GR g fr)
      rw [htp] at hB
      exact CxOkS.bot (HO.hcx F' g fr hP hB) hB
    · show (0 : Int) ≤ 0; exact Int.le_refl _
    · show (-D1) % 8 = 0; omega
    · show (0 : Int) % 8 = 0; rfl
    · exact FrOk2.step hpN (hct.step []) (hf0_start2A hty _)

/-- **The open premises at every choice of the bounds** at the frame
condition with `WordsNone` (`OpenSA`'s shape at `SetupOpenFA`, the starts at
`WordsNone ∧ rtF`). -/
def OpenSFA (hp : Scc.Lower.Accepted2 p = true) (E : Entry)
    (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) (Dt : State → Prop) : Prop :=
  ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
    Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM →
    ∀ J : InvS, StJ J → ∀ v j d (hd : (compiled2 p)[j]? = some d), d.name = "rodata" →
      ∃ CxOk0, SetupOpenFA h Dt hp J v L D1 fS hd CxOk0

/-- **`HSBVFA` from the open premises** (`hS_ofOpenFA` at each choice of
the bounds). -/
theorem hSBVFA_ofOpenSFA (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hu : ∀ dr, p.find? (·.name == "rodata") = some dr → dr.argTy = .unit)
    {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {Dt : State → Prop}
    (H : OpenSFA h hp E El Dt) : HSBVFA h ty E El Dt := by
  intro L D1 D2 lS lM fS nS fM nM hB J hJ v
  obtain ⟨-, hfS, hnS, -, -, -, -, -, hrow, -, hL0, hLm, hL8, -, hD18, -, -, hL1, -, -, -, -, -⟩ := id hB
  exact hS_ofOpenFA h hp hty hu hfS hnS hL0 hLm hL8 hD18 hL1 hrow J v
    fun j d hd hn => H L D1 D2 lS lM fS nS fM nM hB J hJ v j d hd hn

set_option linter.unusedVariables false in
/-- **The setup call's remaining premises at the frame condition with
`WordsNone`** at the bounds `L`, `D1`, the top `v` and the setup block's
compiled index `j` (`SetupPreA` without `hwn`: `PREF` gives it). -/
structure SetupPreFA (Dt : State → Prop) (hp : Scc.Lower.Accepted2 p = true) (J : InvS) (v : BitVec 64)
    (L D1 : Int) (fS : Nat) {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) : Prop where
  /-- The allocator's `W2` instance at the setup frame (`SetupPreA.hAW`), at its bottom key. -/
  hAW : ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PREF F' g fr →
    (SB J v D1 fS) ⟨j, RC, F', g.fp, g.ra, TP0, GR g fr⟩ [fr] →
    AllocW2At p (fun _ => none) (fun _ => 0) (fnCode2OfPMe hp h Λ j d hd).lcx (fnCode2OfPMe hp h Λ j d hd).cx
      (CdCLE OP (Spike.Lib.A64.PhRec.okPc LY0) (Spike.Lib.A64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec g.ra))
      ((fnCode2OfPMe hp h Λ j d hd).Bl g.ra)
      (fun lbl lsize s c => W2 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum
        (Spike.Lib.A64.PhRec.GOf Ly M0) (Spike.Lib.A64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly))
        (arOf (Ly).Λ) (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) Dt (Ab (Ly).lab) lbl lsize s c [fr])
      (KT) (Ly).exe (Ly).endPc (RC) F' ((MSS J) [fr]) g.fp g.ra (TP0) (GR g fr) (imms2Me Λ p) (TailAt2 p j)
      (RetLk d.retTy)
  /-- The buffer allocations' heap aborts' segment at the setup frame (`SetupOpenFA.habA`). -/
  habA : ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PREF F' g fr →
    SegWS (W2S J) (KT) p (fun _ => none) (MSS J)
      (AbAl2 (MSS J) (fun _ => none) (fnCode2OfPMe hp h Λ j d hd) (RC) F' [fr]) (fun _ _ _ => False)

/-- **`SetupOpenFA` at `SetupCxLB` from the remaining premises**
(`setupOpenA_ofPre` at `PREF`): `hcx` by `setupCxLB_ofPre` with the frame
condition's `swFSL ∧ CallerCells` and `hwn` both projections of `PREF`'s. -/
theorem setupOpenFA_ofPre (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {Dt : State → Prop} (J : InvS) (v : BitVec 64) {L D1 : Int} {fS nS : Nat} (hfS : fS ≤ nS)
    (hnS : (nS : Int) + 48 + 208 ≤ D1) (hL0 : 0 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0) (hD18 : D1 % 8 = 0)
    (hL1 : (setupMC (setupWords2 p)).Z.toInt + D1 ≤ L)
    (hrow : ∀ f fi, (f, fi) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx → f.checkStack = true →
      f.name = Scc.Lower.Names.user "rodata" →
        (Scc.Cert.Code1A64.ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi f).frame = fS)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) (hn : d.name = "rodata")
    (hA : Spike.Lib.A64.Flow.allocIn OP = true)
    (hnc : (tailsL d.body).all (fun t => !isCallLet t) = true)
    (hTn : ∀ x cn τ e, TailAt2 p j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    (hno : addFreeT d.body = true) (hTg : tgOkB OP = true) (H : SetupPreFA h Dt hp J v L D1 fS hd) :
    SetupOpenFA h Dt hp J v L D1 fS hd (SetupCxLB h hp Dt J hd) where
  hs := setupHs_ofCxLB0 h hp J hd _ hA hnc hTn
  hcx F' g fr hP hk :=
    setupCxLB_ofPre h hp hty J v hfS hnS hL0 hLm hL8 hD18 hL1 hrow hd hn hP.1 hP.2.1 hP.2.2.1
      (fun m hm => ⟨(hP.2.2.2.1 m hm).1.2, (hP.2.2.2.1 m hm).2⟩) hP.2.2.2.2.2.2.1
      (fun m hm => (hP.2.2.2.1 m hm).1.1) (H.hAW F' g fr hP hk)
  hTg := hTg_of_tgOkB hTg (fnCode2OfPMe hp h Λ j d hd).hf (fnCode2OfPMe hp h Λ j d hd).h1
    (fnCode2OfPMe hp h Λ j d hd).h16 (fun _ _ h => h) (Ly).lab
  hab _ _ _ _ := abOf2_seg_addFree hno hd
  habA := H.habA

/-- **The remaining premises at every choice of the bounds** at the frame
condition with `WordsNone` (`SetupPreFA` at `Bounds2A`'s `L`, `D1`, every
invariant holding at the starts at `WordsNone ∧ rtF`, every top and the
setup block's compiled index; `OpenSFA`'s shape). -/
def OpenPFA (hp : Scc.Lower.Accepted2 p = true) (E : Entry)
    (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) (Dt : State → Prop) : Prop :=
  ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
    Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM →
    ∀ J : InvS, StJ J → ∀ v j d (hd : (compiled2 p)[j]? = some d), d.name = "rodata" →
      SetupPreFA h Dt hp J v L D1 fS hd

end Assembled

/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

variable {Λx : Scc.Sem.Layout}

set_option hygiene false in
/-- The layout: any layout at which the placement check passes (`h`). -/
local notation "LeA" => Λx

/-- **`hello1o`'s open premises at `WordsNone` from the remaining ones**
(`OpenSFA` from `OpenPFA`: `setupOpenFA_ofPre` at `hello1_allocInA`,
`hello1_rodata_noCall`, `hello1_rodata_elem2`, `hello1_rodata_addFree`,
`hello1_tgOkBA`). -/
theorem openSFA_of_openPFA
    (h' : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A)
      (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)) = true)
    {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {Dt : State → Prop}
    (H : OpenPFA h' Spike.Lib.LowerNode.hello1o_accepted2 E El Dt) :
    OpenSFA h' Spike.Lib.LowerNode.hello1o_accepted2 E El Dt := by
  intro L D1 D2 lS lM fS nS fM nM hB J hJ v j d hd hn
  refine ⟨SetupCxLB h' Spike.Lib.LowerNode.hello1o_accepted2 Dt J hd, ?_⟩
  obtain ⟨-, hfS, -, hnS, -, -, -, -, hrow, -, hL0, hLm, hL8, -, hD18, -, -, hL1, -⟩ := id hB
  exact setupOpenFA_ofPre h' Spike.Lib.LowerNode.hello1o_accepted2 hello1_htyA.choose_spec J v hfS hnS hL0
    hLm hL8 hD18 hL1 hrow hd hn hello1_allocInA (hello1_rodata_noCall j d hd hn) (hello1_rodata_elem2 hd hn)
    (hello1_rodata_addFree j d hd hn) hello1_tgOkBA (H L D1 D2 lS lM fS nS fM nM hB J hJ v j d hd hn)

/-- **`hello1`'s setup call `hS` on AArch64 at `WordsNone`, from the
remaining premises without `hwn`**: `HSBVFA` (`hello1_of_closedBVBFA`'s
setup hole) at any landings `El` and write tail `Dt` from `OpenPFA`
(`hAW`, `habA`), by `hSBVFA_ofOpenSFA` at `openSFA_of_openPFA`. -/
theorem hello1_hSFA_ofPre
    (h' : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A)
      (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)) = true)
    {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {Dt : State → Prop}
    (H : OpenPFA h' Spike.Lib.LowerNode.hello1o_accepted2 E El Dt) :
    HSBVFA h' hello1_htyA.choose E El Dt :=
  hSBVFA_ofOpenSFA h' Spike.Lib.LowerNode.hello1o_accepted2 hello1_htyA.choose_spec hello1_huA
    (openSFA_of_openPFA h' H)

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.hS_ofOpenFA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hS_ofOpenFA

/-- info: 'Spike.Lib.LowerA64.setupOpenFA_ofPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms setupOpenFA_ofPre

/-- info: 'Spike.Lib.LowerA64.hello1_hSFA_ofPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_hSFA_ofPre

end Spike.Lib.LowerA64
