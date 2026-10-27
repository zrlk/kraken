/-
**The allocator's `W2` instance at the landings' contexts from the
per-allocation premises** (AArch64; the twin of
`Spike/Test/X64Hello1HAWNone.lean`): `OpenAHA`
(`Spike/Test/A64Hello1HolesW.lean`) from `allocW2At_of`
(`Spike/Lib/LowerA64/AllocW2AtOf.lean`) at every `CxOkH` context and the
placement `fun _ => none`, every premise but the per-allocation `AllocPtW`
(`hpt`) closed:

- the record's facts from the placement check (`instOk_ofPlaceOK`,
  `allocIn`/`printIn`/`abortIn_of_placeOKAt`, `allocPhOk_ofPlaceOK`,
  `allocAbOk_ofPlaceOK`, the owned words `PhRec.own` by definition);
- the frame's from `fnCode2OfPMe` (`hf`, `h1`, `h16`, `regionOff_of_rsOf`);
- the region's from `CxOkH`'s `PRE` and bounds (as `hAW_CxOkH`,
  `stackOff_callee`);
- the frame `[fr]` placed at no label (`framesPlaced_setup`), the start's
  family `StJ` (`hJ`), the base placement (`Reach.base`), no label placed
  (`hsz` vacuous);
- the arena's words (`hmem_arOf` at `CxOkH`'s `WordsNone`, `hno_arOf`,
  `hlt_arOf`, `h64_arOf`, `Spike/Lib/LowerA64/ArCallMs.lean`);
- the ghosts `FrOk2` along the setup frame's run, the elements `elem2`.

- `OpenAPtA`: `allocW2At_of`'s `hpt` at `AllocWH`'s instance, at every
  choice of the bounds and `CxOkH` context (`OpenAHA`'s quantifiers);
- `cxLB_hAW_noneA`: `OpenAHA` from `OpenAPtA`, the setup type and the
  bodies' one-word elements;
- `hello1_hAW_noneA`: at `hello1o`, `OpenAHA` at the landings `ElH` and the
  write tail `fun _ => True` from `OpenAPtA` there.
-/
import Spike.Test.A64Hello1HolesW
import Spike.Lib.LowerA64.AllocW2AtOf
import Spike.Lib.LowerA64.ArCallMs
import Spike.Lib.LowerA64.HeldRes
import Spike.Lib.LowerA64.FramesPlacedSetup
import Spike.Test.A64Hello1H1Of

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Rt (setupMC rS0 arOf swFSL rtF)
open Spike.Lib.A64.WriteAb (Ab)
open Spike.Lib.LowerNode (FrOk2 setupWords2 compiled2 TailAt2 imms2Me)
open Spike.Lib.A64.Flow.Ret0 (WcG CallerCells limA)
open Spike.Lib.AllocReach (Reach IN)

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)
set_option hygiene false in
local notation "LY0" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)
set_option hygiene false in
local notation "Ar" => Spike.Lib.A64.Rt.arOf (lay2 Λ p)
set_option hygiene false in
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))
set_option hygiene false in
local notation "M0" => Spike.Lib.A64.PhRec.m0Of (Ly).Λ OP (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).secs
set_option hygiene false in
local notation "MSS" J:max =>
  MSAt h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)
set_option hygiene false in
local notation "WNF" => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧ rtF (Ly) m
set_option hygiene false in
local notation "StJ" J:max => ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
  ∀ s c fs, StartsSA h E (WNF) El Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs
set_option hygiene false in
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).env, none⟩ : Ctl)
set_option hygiene false in
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64
set_option hygiene false in
local notation "X0" => pinA (Ly).lab + 0#64 + 8#64
set_option hygiene false in
local notation "TP0" => UInt64.ofBitVec (X0)
set_option hygiene false in
local notation "FS" v:max => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧
  swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) v m
set_option hygiene false in
local notation "SB" J:max v:max D1:max fS:max => fun k fs =>
  SetupBot p (Ly).lab ((MSS J) []) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
    (setupMC (setupWords2 p)) D1 (Int64.ofInt fS) ⟨TOP, TP0, C0⟩ (X0) k fs
set_option hygiene false in
/-- The `j`th block's code facts. -/
local notation "FC" => fnCode2OfPMe hp h Λ j d hd

set_option linter.unusedVariables false in
/-- **`allocW2At_of`'s per-allocation premise `hpt` at `AllocWH`'s instance**,
at every choice of the bounds, family `J` containing the starts and context
`CxOkH` with the setup frame's bottom key (`hd` is read by `FC`, which the
unused-variables linter does not see through). -/
def OpenAPtA (hp : Scc.Lower.Accepted2 p = true) (E : Entry)
    (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) (Dt : State → Prop) : Prop :=
  ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
    Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM →
    ∀ J : InvS, StJ J → ∀ (v : BitVec 64) (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d),
      d.name = "rodata" →
    ∀ (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64)
      (G0 : Ctl → Prop) (Ab' : FragS isaLSE2), CxOkH h hp j R F fs fp ra tp G0 Ab' →
      (SB J v D1 fS) ⟨j, R, F, fp, ra, tp, G0⟩ fs →
    ∀ (c0 : Ctl) (pc : Int64) (kk : Nat) (x : String) (cn : At) (τ : Ty) (e : Expr)
      (env : Scc.Lower.Env) (n : Nat) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat))
      (tk : Ty) (kv : UInt64) (en em hh : Nat), G0 c0 → TailAt2 p j (.let_ x (.newBuf cn τ) e) →
      Spike.Lib.LowerNode.Fresh env n → Scc.Lower.Inv.atomV env cn = some (tk, [.imm kv]) →
      Spike.Lib.LowerShape.countsO (FC).lcx.obj τ = some (en, em) →
      Scc.Obj.header0 (FC).lcx.obj .array en em = some hh →
      PtC2 (FC).lcx (FC).cx
        (CdCLE OP (Spike.Lib.A64.PhRec.okPc LY0) (Spike.Lib.A64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec ra))
        (BlC2L OP (Spike.Lib.A64.PhRec.okPc LY0) (Spike.Lib.A64.PhRec.ph LY0) (LY0).lab (FC).cx
          (Int64.ofBitVec ra))
        (_root_.Executable.labels (Ly).exe).label (imms2Me Λ p) (TailAt2 p j) (RetLk d.retTy) kk pc env n lits
        cs bufs (.let_ x (.newBuf cn τ) e) →
      AllocPtW (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (Spike.Lib.A64.PhRec.GOf Ly M0)
        (Spike.Lib.A64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly)) (arOf (Ly).Λ)
        (fun _ => none) (fun _ => 0) (S0A h E (WNF)) El J (ab2 p (Ly).lab) Dt (LY0).lab
        ((Ly).lab StackTake.siteL) (fun _ => none) (fun _ => 0) fs (Ly).exe (Ly).endPc R F (FC).cx fp ra tp
        c0 pc x cn τ e env lits cs bufs hh kv
        (Spike.Lib.LowerShape.unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv)

/-- **`OpenAHA` from the per-allocation premises `OpenAPtA`**
(`allocW2At_of` at every `CxOkH` context): the record's facts from the
placement check, the frame's from `fnCode2OfPMe`, the region's from
`CxOkH`'s `PRE` and bounds (as `hAW_CxOkH`), the frame placed at no label,
the arena's words from `ArCallMs` at `CxOkH`'s `WordsNone`, the ghosts along
the setup frame's run, the elements by `hTn`. -/
theorem cxLB_hAW_noneA (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hTn : ∀ j d, (compiled2 p)[j]? = some d →
      ∀ x cn τ e, TailAt2 p j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {Dt : State → Prop}
    (H : OpenAPtA h hp E El Dt) : OpenAHA h hp E El Dt := by
  intro L D1 D2 lS lM fS nS fM nM hB J hJ v j d hd hn R F fs fp ra tp G0 Ab' hc hSB
  have HP := H L D1 D2 lS lM fS nS fM nM hB J hJ v j d hd hn R F fs fp ra tp G0 Ab' hc hSB
  obtain ⟨d', hd', L', D1', fS', nS', v', g, fr, J', -, hfS, hnS, hL0, hLm, hL8, hD18, hL1, hrow,
    ⟨hR0, hal, hF', hFF, -, -, hct, -⟩, hwn, -, rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := hc
  obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
  obtain ⟨w, fi, -, -, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  have hframe : (FC).cx.frame = fS' := by
    rw [hcx]; exact hrow _ _ hmem rfl (by show Scc.Lower.Names.user d.name = _; rw [hn])
  have hpN := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  have hlo0 : -D1' ≤ -((FC).cx.frame : Int) := by rw [hframe]; omega
  have hhi : (0 : Int) ≤ 0 := Int.le_refl _
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2A h hp hs') (rtCodeOkS_setupWords2A h hp hs')).1
  have hZ := setupMC_Z _ hsw
  have hFO : ∀ m, F m → StackOff (rS0 (Ly))
      ((swR v' (-L') 0).callee (-(setupMC (setupWords2 p)).Z.toInt) (-D1') 0) m := by
    intro m hm
    obtain ⟨⟨⟨hv, -⟩, hoff⟩, hcc⟩ := hFF m hm
    subst hv
    have hok : (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L') 0).OK := by
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hLm
    have h8 : (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L') 0).base.toNat % 8 = 0 := by
      show (stacksA (Ly).lab + 0#64 + 16384#64).toNat % 8 = 0
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; have := Spike.Lib.A64.Rt.rt_h16 (Ly); omega
    exact Spike.Lib.A64.Flow.Ret0.Inst.stackOff_callee hok h8 (by show (-L') % 8 = 0; omega)
      (by show (0 : Int) % 8 = 0; rfl)
      (by show -L' ≤ _; omega) (by omega) (by show _ < (0 : Int); omega) (by omega) hoff hcc
  have hc := Spike.Lib.A64.Rt.ctrZ_ofPlaceOK h
  haveI : Kraken.Executable.ValidLayout (Ly).exe := (Ly).valid
  obtain ⟨-, -, -, -, hH, hCt, hU, hO, hCl, -⟩ := msOfAX_fields (Λ := (Ly).Λ) (μ := Spike.Lib.A64.PhRec.μ (Ly))
    (p := p) (rd := Spike.Lib.LowerNode.IsNum) (G := G2 h p) (own := fun s _ => Spike.Lib.A64.PhRec.own (Ly) s)
    (ar := Ar) (I := IN (Ar) (fun _ => none) (fun _ => 0) J) (lbl := fun _ => none) (lsize := fun _ => 0)
    (fs := [fr]) (ab2 p (Ly).lab)
  rw [(fnCode2OfPMe_spec hp h Λ j d hd).2.1]
  exact allocW2At_of (ownOf := Spike.Lib.A64.PhRec.ownOf (Ly))
    (Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms2Of p) (rS := rS0 (Ly))) (allocIn_of_placeOKAt h)
    (Spike.Lib.A64.Rt.allocPhOk_ofPlaceOK h (Scc.Lower.imms2Of p))
    (Spike.Lib.A64.Rt.allocAbOk_ofPlaceOK h (Scc.Lower.imms2Of p)) (printIn_of_placeOKAt h)
    (abortIn_of_placeOKAt h) (fun _ => rfl) (FC).hf (FC).h1 (FC).h16 hR0 hal
    (by show (-D1') % 8 = 0; omega) (by show (0 : Int) % 8 = 0; rfl)
    (by show -D1' ≤ -((FC).cx.frame : Int) + -160 - 48; rw [hframe]; omega) hhi hF'
    (Spike.Lib.A64.Rt.rS0_sub _) (Spike.Lib.A64.Rt.fitS_of_sub _ (Spike.Lib.A64.Rt.rS0_sub _)) hFO hpN hJ
    Reach.base (fun s _ => framesPlaced_setup h hp hty hct s)
    (fun _ _ hr => regionOff_of_rsOf (FC).hf hlo0 hhi hr)
    (fun q hq a ha => hmem_arOf h hc hwn hH hCl hCt hU hO q hq a (by rw [hCt, hU, hCl]; exact ha))
    (hno_arOf h (imms2Me Λ p) hH hO) (hlt_arOf h hc) (h64_arOf h hc)
    (fun _ _ _ _ _ hl => nomatch hl) (hTn j d hd)
    (fun _ hc0 => FrOk2.runM hpN hc0 (FrOk2.step hpN (hct.step []) (hf0_start2A hty _))) HP

end Assembled

/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

/-- `ld`'s layout of the linked executable. -/
local notation "LeA" => Spike.Test.Hello1LinkedA64.Λe

/-- **`hello1`'s allocator `W2` instance at the landings' contexts from the
per-allocation premises** (`cxLB_hAW_noneA` at `hello1_htyA`,
`hello1_hTnA`): `OpenAHA` at the landings `ElH` and the write tail
`fun _ => True` from `OpenAPtA` there, at every entry and placement check. -/
theorem hello1_hAW_noneA
    (HP : ∀ E : Entry, E.Ok (lay2 LeA P1A) → ∀ h' : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A)
      (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)) = true,
      OpenAPtA h' Spike.Lib.LowerNode.hello1o_accepted2 E (ElH h' Spike.Lib.LowerNode.hello1o_accepted2)
        (fun _ => True)) :
    ∀ E : Entry, E.Ok (lay2 LeA P1A) → ∀ h' : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A)
      (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)) = true,
      OpenAHA h' Spike.Lib.LowerNode.hello1o_accepted2 E (ElH h' Spike.Lib.LowerNode.hello1o_accepted2)
        (fun _ => True) := fun E hE h' =>
  cxLB_hAW_noneA h' _ hello1_htyA.choose_spec hello1_hTnA (HP E hE h')

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.cxLB_hAW_noneA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.cxLB_hAW_noneA

/-- info: 'Spike.Lib.LowerA64.hello1_hAW_noneA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_hAW_noneA
