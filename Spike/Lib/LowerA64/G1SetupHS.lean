/-
**The setup call's `hS` for any `Accepted2` program with a setup block, at
an abstract abort fragment** (AArch64): `hS_ofOpenFA`
(`Spike/Test/A64Hello1SetupOpenOfF.lean`) with the callee's aborts' fragment
`Ab` chosen by the open premises instead of fixed to the setup context's own
aborts (`AbU2`), so that a base context whose aborts' fragment contains every
context's aborts (`CxG2`, `Spike/Lib/LowerA64/G1FnSpec.lean`) can be the
setup frame's; and the setup block's argument type from `Accepted2`
(`rodata_argTy_of_accepted2`) instead of a premise.

- `rodata_argTy_of_accepted2`: the setup block `rodata` takes `Unit`
  (`setup2`);
- `SetupOpenG`, `OpenSG`: the setup frame's open premises at one choice and
  at every choice of the bounds (`SetupOpenFA`, `OpenSFA` with `hcx` giving
  the aborts' fragment, its inclusion of the abort node's states and its
  segment);
- `hS_ofOpenG`, `hSBVFA_ofOpenSG`: `HSBVFA`'s `hS` from them.
-/
import Spike.Test.A64Hello1SetupOpenOfF

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm

/-- **The setup block `rodata` takes `Unit`** (`setup2`), for an
`Accepted2` program with a setup block. -/
theorem rodata_argTy_of_accepted2 {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {s : Ty}
    (hs : Scc.Lower.setupOf p = some s) : ∀ dr, p.find? (·.name == "rodata") = some dr → dr.argTy = .unit := by
  intro dr hfr
  have hds : Scc.Lower.decls2 [] (Scc.Lower.setupOf p) (Scc.Lower.hasPrint p) p = true := by
    simp only [Scc.Lower.Accepted2, Bool.and_eq_true] at hp; exact hp.1.1.1.1.1.1.1.2
  have hrn : dr.name = "rodata" := by simpa using List.find?_some hfr
  obtain ⟨E', hE'⟩ := decl2_of_decls2 hds dr (List.mem_of_find?_eq_some hfr)
  have hpe' : Scc.Lower.isPrintExt dr = false := by simp [Scc.Lower.isPrintExt, hrn]
  have hnl' : (Scc.Lower.hasPrint p && "rodata" == "printL") = false := by simp
  simp only [Scc.Lower.decl2, hpe', hrn, hnl', hs, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true] at hE'
  have hmr : ("rodata" == "main") = false := by decide
  simp only [hmr, Bool.false_eq_true, ↓reduceIte] at hE'
  unfold Scc.Lower.setup2 at hE'
  simp only [Bool.and_eq_true, beq_iff_eq] at hE'
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hat⟩, -⟩, -⟩, -⟩, -⟩ := hE'
  exact hat

end Spike.Lib.LowerNode

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
/-- **The setup frame's open premises at an abstract aborts' fragment**
(`SetupOpenFA` with `hcx` choosing the callee's aborts' fragment `Ab`: the
base context at it, the abort node's states inside it, and its segment;
`SetupOpenFA.hab`, `habA` are the instance `Ab := AbU2`). -/
structure SetupOpenG (Dt : State → Prop) (hp : Scc.Lower.Accepted2 p = true) (J : InvS) (v : BitVec 64)
    (L D1 : Int) (fS : Nat) {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    (CxOk0 : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop) : Prop where
  /-- The setup function's segment at the contexts with their stack records (`SetupOpenFA.hs`). -/
  hs : FnSpecC2 (W2S J) (KT) p (fun _ => none) (fun _ => 0) (MSS J)
    (CxOkS (p := p) (lbl := fun _ => none) (lsize := fun _ => 0) (fnCode2OfPMe hp h Λ) CxOk0 (SB J v D1 fS) j)
    (fnCode2OfPMe hp h Λ j d hd)
  /-- The base context at the setup frame at some aborts' fragment `Ab`, at the setup frame's bottom key:
  the abort node's states inside `Ab`, and `Ab` never ending inside `W2`. -/
  hcx : ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PREF F' g fr →
    (SB J v D1 fS) ⟨j, RC, F', g.fp, g.ra, TP0, GR g fr⟩ [fr] →
    ∃ Ab : FragS isaLSE2, CxOk0 j (RC) F' [fr] g.fp g.ra TP0 (GR g fr) Ab ∧
      (∀ s c fs', AbOf2 p (fun _ => none) (fnCode2OfPMe hp h Λ j d hd) (RC) F' [fr] g.fp g.ra (GR g fr) s c fs' →
        Ab s c fs') ∧
      SegWS (W2S J) (KT) p (fun _ => none) (MSS J) Ab (fun _ _ _ => False)
  /-- The setup function's construct blocks' branch and call targets off the write abort
  (`SetupOpenFA.hTg`). -/
  hTg : ∀ pc blk, SubCd (CdCLE OP (Spike.Lib.A64.PhRec.okPc LY0) (Spike.Lib.A64.PhRec.ph LY0) (LY0).lab
      (Int64.ofBitVec ((Ly).lab (setupMC (setupWords2 p)).e0 + 4).toBitVec)) pc blk →
    Kind2 (fnCode2OfPMe hp h Λ j d hd).cx blk → ∀ k (hk : k < blk.length) L,
      (classify blk[k] = some (.b L) ∨ classify blk[k] = some (.bl L) ∨
        (∃ cc, classify blk[k] = some (.bcond cc L)) ∨ (∃ t, classify blk[k] = some (.cbz t L)) ∨
        ∃ t, classify blk[k] = some (.cbnz t L)) → PosOff OP (Ly).lab ((Ly).lab L)

/-- **The setup call's `hS` at the frame condition with `WordsNone`, from
the open premises at an abstract aborts' fragment** (`hS_ofOpenFA`'s proof,
the callee's aborts' fragment `SetupOpenG.hcx`'s, the setup block's argument
type by `rodata_argTy_of_accepted2`). -/
theorem hS_ofOpenG {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) {ty : Ty}
    (hty : Scc.Lower.setupOf p = some ty)
    {L D1 : Int} {fS nS : Nat} (hfS : fS ≤ nS) (hnS : (nS : Int) + 48 ≤ D1) (hL0 : 0 ≤ L) (hLm : L ≤ 16384)
    (hL8 : L % 8 = 0) (hD18 : D1 % 8 = 0) (hL1 : (setupMC (setupWords2 p)).Z.toInt + D1 ≤ L)
    (hrow : ∀ f fi, (f, fi) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx → f.checkStack = true →
      f.name = Scc.Lower.Names.user "rodata" →
        (Scc.Cert.Code1A64.ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi f).frame = fS)
    (J : InvS) (v : BitVec 64)
    (H : ∀ j d (hd : (compiled2 p)[j]? = some d), d.name = "rodata" →
      ∃ CxOk0, SetupOpenG h Dt hp J v L D1 fS hd CxOk0) :
    SetupCallWSB (W2S J) (KT) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
      (setupMC (setupWords2 p)).setup (setupMC (setupWords2 p)).Z D1 (Int64.ofInt fS) (SRetR (fun _ => none) ty)
      ((Ly).lab (setupMC (setupWords2 p)).e0 + 4).toBitVec C0 (TP0)
      (SetupGF p (Ly).lab ((MSS J) []) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v) (setupMC (setupWords2 p)) D1
        (Int64.ofInt fS) ⟨TOP, TP0, C0⟩ (X0)) := by
  obtain ⟨dr, hf, hrt⟩ := Spike.Lib.LowerNode.rodata_of_setupOf hp hty
  obtain ⟨j, hd, hn⟩ := Spike.Lib.LowerNode.rodata_compiled2 hf
  obtain ⟨CxOk0, HO⟩ := H j dr hd hn
  have hu := Spike.Lib.LowerNode.rodata_argTy_of_accepted2 hp hty
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
    have hB := hSB j (GR g fr)
    rw [htp] at hB
    obtain ⟨Ab, hcx0, hAbI, hAbS⟩ := HO.hcx F' g fr hP hB
    refine ⟨GR g fr, Ab,
      ⟨CxOkS.bot hcx0 hB, hF', hR0, hal, hlo0, ?_, fun _ _ h1 h2 => h1.trans h2, hblk.1, hblk.2,
        fun c0 hc0' _ _ hA => hAbI _ _ _ ⟨rfl, c0, hc0', hA⟩, .refl _, ?_, ?_, hFO0⟩, ?_, hAbS⟩
    · show (0 : Int) ≤ 0; exact Int.le_refl _
    · show (-D1) % 8 = 0; omega
    · show (0 : Int) % 8 = 0; rfl
    · exact FrOk2.step hpN (hct.step []) (hf0_start2A hty _)

/-- **The open premises at every choice of the bounds** at an abstract
aborts' fragment (`OpenSFA` at `SetupOpenG`). -/
def OpenSG (hp : Scc.Lower.Accepted2 p = true) (E : Entry)
    (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) (Dt : State → Prop) : Prop :=
  ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
    Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM →
    ∀ J : InvS, StJ J → ∀ v j d (hd : (compiled2 p)[j]? = some d), d.name = "rodata" →
      ∃ CxOk0, SetupOpenG h Dt hp J v L D1 fS hd CxOk0

/-- **`HSBVFA` from the open premises at an abstract aborts' fragment**
(`hS_ofOpenG` at each choice of the bounds), for any `Accepted2` program
with a setup block. -/
theorem hSBVFA_ofOpenSG (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {Dt : State → Prop}
    (H : OpenSG h hp E El Dt) : HSBVFA h ty E El Dt := by
  intro L D1 D2 lS lM fS nS fM nM hB J hJ v
  obtain ⟨-, hfS, hnS, -, -, -, -, -, hrow, -, hL0, hLm, hL8, -, hD18, -, -, hL1, -, -, -, -, -⟩ := id hB
  exact hS_ofOpenG h hp hty hfS hnS hL0 hLm hL8 hD18 hL1 hrow J v
    fun j d hd hn => H L D1 D2 lS lM fS nS fM nM hB J hJ v j d hd hn

end Assembled

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerNode.rodata_argTy_of_accepted2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.rodata_argTy_of_accepted2

/-- info: 'Spike.Lib.LowerA64.hS_ofOpenG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hS_ofOpenG

/-- info: 'Spike.Lib.LowerA64.hSBVFA_ofOpenSG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hSBVFA_ofOpenSG

end Spike.Lib.LowerA64
