/-
**The allocator's `W2` instance at the setup frame from the per-allocation
premises** (x86-64): `OpenAWF` (`Spike/Test/X64Hello1HolesW.lean`) from
`allocW2At_of` (`Spike/Lib/LowerX64/AllocW2AtOf.lean`) at the setup frame's
region `rbR RC` and the placement `fun _ => none`, every premise but the
per-allocation `AllocPtW` (`hpt`) closed:

- the record's facts from the placement check (`instOk_ofPlaceOK`,
  `allocIn`/`printIn`/`abortIn_of_placeOKAt`, `allocPhOk_ofPlaceOK`,
  `allocAbOk_ofPlaceOK`, the owned words `PhRec.own` by definition);
- the frame's from `fnCode2OfPMe` (`hf`, `h1`, `h16`, `regionOff_of_rsOf`);
- the region's from `PREF` and the bounds (as `setupCxLB_ofPreT`: `rbR_ok`,
  `rbR_fstable`, `stackOff_callee` twice and `stackOff_rbR`);
- the frame `[fr]` placed at no label (`framesPlaced_setup`), the start's
  family `StJ` (`hJ`), the base placement (`Reach.base`), no label placed
  (`hsz` vacuous);
- the arena's words (`hmem_arOf` at `PREF`'s `WordsNone`, `hno_arOf`,
  `hlt_arOf`, `h64_arOf`, `Spike/Lib/LowerX64/ArCallMs.lean`);
- the ghosts `FrOk2` along the setup frame's run, the elements `elem2`.

- `OpenAPt`: `allocW2At_of`'s `hpt` at `OpenAWF`'s instance, at every choice
  of the bounds (`OpenAWF`'s quantifiers);
- `cxLB_hAW_none`: `OpenAWF` from `OpenAPt`, the setup type and the bodies'
  one-word elements;
- `hello1_hAW_none`: at `hello1o`, `OpenAWF` at the landings `ElH` and the
  write tail `fun _ => True` from `OpenAPt` there.
-/
import Spike.Test.X64Hello1HolesW
import Spike.Test.X64Hello1CxLBOf
import Spike.Test.X64Hello1H1Of
import Spike.Lib.LowerX64.AllocW2AtOf
import Spike.Lib.LowerX64.ArCallMs
import Spike.Lib.LowerX64.HeldRes
import Spike.Lib.X64AllocPhPlace

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region FrameRun FragS)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (swR FStable)
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Flow.Ret0 (WcG CallerCells limA)
open Spike.Lib.X64.Rt (swFSL rS0 rtF setupMC arOf)
open Spike.Lib.X64.WriteAb (Ab)
open Spike.Lib.LowerNode (FrOk2 setupWords2 compiled2 TailAt2 imms2Me)
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
/-- `MSAt` at `Closed2At`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max =>
  MSAt h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- **The start's frame condition** (`Closed2AtW`'s). -/
local notation "WNF" => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧ rtF (Ly) m

set_option hygiene false in
/-- The frame invariant `J` holds at the starts (`StartsSX` at `WNF`). -/
local notation "StJ" J:max => ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
  ∀ s c fs, StartsSX h E (WNF) El Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs

set_option hygiene false in
/-- The switch region at depth `L`, below the top `v`. -/
local notation "RS" v:max => ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)

set_option hygiene false in
/-- The switch region's frame condition with `WordsNone`, below the top `v`. -/
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
/-- The setup call's segment's premises at `FS` with `WordsNone` (`PREF`). -/
local notation "PREF" F':max g:max fr:max => (RC).OK ∧ FStable (RC) F' ∧
  (∀ m, F' m → (FS v) m ∧ CallerCells (RS v) (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8 m) ∧
  g.ra = ((Ly).lab (setupMC (setupWords2 p)).sp0).toBitVec ∧ g.tp = TP0 ∧
  Spike.Lib.X64.Flow.CallTo p C0 g.c0 fr ∧ (RC).base = g.sp

set_option hygiene false in
set_option linter.unusedVariables false in
/-- The ghosts at the setup frame. -/
local notation "GR" g:max fr:max => fun c => Spike.Lib.FrameRunM p (g.c0, [fr]) (c, [fr])

set_option hygiene false in
/-- The stack records' bottom keys at the setup frame (`SetupBot` at `FS`
with `WordsNone`; `X64Hello1SetupOpenOfF`'s). -/
local notation "SB" J:max v:max D1:max fS:max => fun k fs =>
  SetupBot p (Ly).lab ((MSS J) []) (RS v) (FS v) (setupMC (setupWords2 p)) D1 (Int64.ofInt fS)
    ⟨TOP - 8#64, TP0, C0⟩ (TP0).toBitVec k fs

set_option hygiene false in
/-- The `j`th block's code (`fnCode2OfPMe`). -/
local notation "FC" => fnCode2OfPMe hp h Λ j d hd

set_option hygiene false in
/-- The setup frame's code at its return address `ra` (`OpenAWF`'s). -/
local notation "CdR" ra:max => CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab
  (Int64.ofBitVec ra)

set_option hygiene false in
/-- The setup frame's calls at its return address `ra` (`fnCode2OfPMe_spec`'s `Bl`). -/
local notation "BlR" ra:max => BlC2L OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab
  (FC).fr (Int64.ofBitVec ra)

set_option linter.unusedVariables false in
/-- **`allocW2At_of`'s per-allocation premise `hpt` at `OpenAWF`'s instance,
at every choice of the bounds** (`OpenAWF`'s quantifiers): at every
allocation of the setup frame's walk, `AllocPtW` at the record (`Ly`'s
world, `LY0`'s code), the arena `arOf`, the placement `fun _ => none`, the
start's family (`S0X` at `WNF`, the landings `El`, the nodes' abort `ab2`),
the frames `[fr]`, the region `rbR RC` and `F'`. -/
def OpenAPt (hp : Scc.Lower.Accepted2 p = true) (E : Entry)
    (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa) (Dt : State → Prop) : Prop :=
  ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
    Bounds2 cfg p sizes labelOffs (Ly) L D1 D2 lS lM fS nS fM nM →
    ∀ J : InvS, StJ J → ∀ j d (hd : (compiled2 p)[j]? = some d), d.name = "rodata" →
      ∀ (v : BitVec 64), v = TOP →
      ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PREF F' g fr →
        (SB J v D1 fS) ⟨j, RC, F', g.fp, g.ra, TP0, GR g fr⟩ [fr] →
        ∀ (c0 : Ctl) (pc : Int64) (kk : Nat) (x : String) (cn : At) (τ : Ty) (e : Expr)
          (env : Scc.Lower.Env) (n : Nat) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat))
          (tk : Ty) (kv : UInt64) (en em hh : Nat), (GR g fr) c0 → TailAt2 p j (.let_ x (.newBuf cn τ) e) →
          Spike.Lib.LowerNode.Fresh env n → Scc.Lower.Inv.atomV env cn = some (tk, [.imm kv]) →
          Spike.Lib.LowerShape.countsO (FC).lcx.obj τ = some (en, em) →
          Scc.Obj.header0 (FC).lcx.obj .array en em = some hh →
          PtC2 (FC).lcx (FC).fr (CdR g.ra) (BlR g.ra) (_root_.Executable.labels (Ly).exe).label
            (imms2Me Λ p) (TailAt2 p j) (RetLk d.retTy) kk pc env n lits cs bufs (.let_ x (.newBuf cn τ) e) →
          AllocPtW (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (Spike.Lib.X64.PhRec.GOf Ly M0)
            (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly)) (arOf (Ly).Λ)
            (fun _ => none) (fun _ => 0) (S0X h E (WNF)) El J (ab2 p (Ly).lab) Dt (LY0).lab
            ((Ly).lab StackTake.siteL) (fun _ => none) (fun _ => 0) [fr] (Ly).exe (Ly).endPc (rbR (RC)) F'
            (FC).fr (CdR g.ra) (BlR g.ra) g.fp g.ra (TP0) c0 pc x cn τ e env lits cs bufs hh kv
            (Spike.Lib.LowerShape.unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv)

/-- **`OpenAWF` from the per-allocation premises `OpenAPt`** (`allocW2At_of`
at the setup frame): the record's facts from the placement check, the
frame's from `fnCode2OfPMe`, the region's from `PREF` and the bounds (as
`setupCxLB_ofPreT`), the frame placed at no label, the arena's words from
`ArCallMs` at `PREF`'s `WordsNone`, the ghosts along the setup frame's run,
the elements by `hTn`. -/
theorem cxLB_hAW_none (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hTn : ∀ j d, (compiled2 p)[j]? = some d →
      ∀ x cn τ e, TailAt2 p j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa} {Dt : State → Prop}
    (H : OpenAPt h hp E El Dt) : OpenAWF h hp E El Dt := by
  intro L D1 D2 lS lM fS nS fM nM hB J hJ j d hd hn v hv F' g fr hP hSB
  have HP := H L D1 D2 lS lM fS nS fM nM hB J hJ j d hd hn v hv F' g fr hP hSB
  obtain ⟨-, hfS, -, hnS, -, -, -, -, -, -, hrow, -, hL0, hLm, hL8, -, hD18, -, -, -, hL1, -⟩ := id hB
  obtain ⟨hR0, hF', hFF, -, -, hct, -⟩ := hP
  have hwn : ∀ m, F' m → Spike.Lib.DmemPriv.WordsNone (lay2 Λ p) m.dmem := fun m hm => (hFF m hm).1.1.1
  obtain ⟨w, -, -, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  have hframe : (FC).fr.size = fS := by
    rw [hcx]; exact hrow _ hmem rfl (by show Scc.Lower.Names.user d.name = _; rw [hn])
  have hpN := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2 h hp hs') (rtCodeOkS_setupWords2 h hp hs')).1
  have hZ := setupMC_Z _ hsw
  have hok : (swR v (-L) 0).OK := by
    rw [hv, Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ (by omega) hLm
  have htop8 : v.toNat % 8 = 0 := by
    rw [hv, Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
  have hR1 : (RS v).OK :=
    Region.callee_ok hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
      (by show _ ≤ (0 : Int); omega)
  have hb1 : ((RS v).base.toNat : Int) = v.toNat - 8 :=
    Region.callee_base hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
  have hbc := Region.callee_base (hi' := 8) (kc := -8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0)
    (lo' := -D1) hR1 (by show 8 - L ≤ _; omega) (by omega) (by show _ < (8 : Int); omega)
  have hlo1 : (RC).lo ≤ -8 := by show -D1 ≤ -8; omega
  have hhi1 : (0 : Int) ≤ (RC).hi := by show (0 : Int) ≤ 8; decide
  have hb := rbR_base hR0 hlo1 hhi1
  have hlo0 : (rbR (RC)).lo ≤ -((FC).fr.size : Int) := by
    show -D1 + 8 ≤ _; rw [hframe]; omega
  have hhi : (0 : Int) ≤ (rbR (RC)).hi := by show (0 : Int) ≤ 8 + 8; decide
  have hFO : ∀ m, F' m → StackOff (rS0 (Ly)) (rbR (RC)) m := by
    intro m hm
    refine stackOff_rbR hR0 hlo1 hhi1 ?_
    have H := hFF m hm
    have hb8 : (RS v).base.toNat % 8 = 0 := by omega
    exact Spike.Lib.X64.Rt.stackOff_callee hR1 hb8 (by show (8 - L) % 8 = 0; omega)
      (by show (8 : Int) % 8 = 0; decide) (by show 8 - L ≤ _; omega) (by omega)
      (by show _ < (8 : Int); omega) (by omega)
      (Spike.Lib.X64.Rt.stackOff_callee hok htop8 (by show (-L) % 8 = 0; omega)
        (by show (0 : Int) % 8 = 0; rfl) (by show -L ≤ _; omega) (by omega)
        (by show _ < (0 : Int); omega) (by decide) H.1.1.2.2 H.1.2)
      H.2
  have hc := Spike.Lib.X64.Rt.ctrZ_ofPlaceOK h
  haveI : Kraken.Executable.ValidLayout (Ly).exe := (Ly).valid
  obtain ⟨-, -, -, -, hH, hCt, hU, hO, hCl, -⟩ := msOfAX_fields (Λ := (Ly).Λ) (μ := Spike.Lib.X64.PhRec.μ (Ly))
    (p := p) (rd := Spike.Lib.LowerNode.IsNum) (G := G2 h p) (own := fun s _ => Spike.Lib.X64.PhRec.own (Ly) s)
    (ar := Ar) (I := IN (Ar) (fun _ => none) (fun _ => 0) J) (lbl := fun _ => none) (lsize := fun _ => 0)
    (fs := [fr]) (ab2 p (Ly).lab)
  rw [(fnCode2OfPMe_spec hp h Λ j d hd).2.1]
  exact allocW2At_of (ownOf := Spike.Lib.X64.PhRec.ownOf (Ly))
    (Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (imms2Me Λ p) (rS := rS0 (Ly))) (allocIn_of_placeOKAt h)
    (Spike.Lib.X64.PhRec.allocPhOk_ofPlaceOK h (Scc.Lower.imms2Of p))
    (Spike.Lib.X64.PhRec.allocAbOk_ofPlaceOK h (Scc.Lower.imms2Of p)) (printIn_of_placeOKAt h)
    (abortIn_of_placeOKAt h) (fun _ => rfl) (FC).hf (FC).h1 (FC).h16 (rbR_ok hR0 hlo1 hhi1) (by omega)
    (by show (-D1 + 8) % 8 = 0; omega) (by show ((8 : Int) + 8) % 8 = 0; decide)
    (by show -D1 + 8 ≤ -((FC).fr.size : Int) - 8 + -160 - 32; rw [hframe]; omega)
    (by show (16 : Int) ≤ 8 + 8; decide) (rbR_fstable hR0 hlo1 hhi1 hF')
    (Spike.Lib.X64.Rt.rS0_sub _) (Spike.Lib.X64.Rt.fitS_of_sub _ (Spike.Lib.X64.Rt.rS0_sub _)) hFO hpN hJ
    Reach.base (fun s _ => framesPlaced_setup h hp hty hct s)
    (fun _ _ hr => regionOff_of_rsOf (FC).hf hlo0 hhi hr)
    (fun q hq a ha => hmem_arOf h hc hwn hH hCl hCt hU hO q hq a (by rw [hCt, hU, hCl]; exact ha))
    (hno_arOf h (imms2Me Λ p) hH hO) (hlt_arOf h hc) (h64_arOf h hc)
    (fun _ _ _ _ _ hl => nomatch hl) (hTn j d hd)
    (fun _ hc0 => FrOk2.runM hpN hc0 (FrOk2.step hpN (hct.step []) (hf0_start2 hty _))) HP

end Assembled

/-- The program. -/
local notation "P1" => Spike.Test.Hello1MainSrc.hello1o

variable {Λx : Scc.Sem.Layout}

set_option hygiene false in
/-- The layout: any layout at which the placement check passes (`h`). -/
local notation "Le" => Λx

/-- The compiler's output for the program at the certificate's sizes and label offsets. -/
local notation "OX" =>
  Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1) SccCertificate.sizes SccCertificate.labelOffs

/-- **`hello1`'s allocator `W2` instance at the setup frame from the
per-allocation premises** (`cxLB_hAW_none` at `hello1_hty`, `hello1_hTn`):
`OpenAWF` at the landings `ElH` and the write tail `fun _ => True` from
`OpenAPt` there, at every entry and placement check. -/
theorem hello1_hAW_none
    (HP : ∀ E : Entry, E.Ok (lay2 Le P1) → ∀ h : placeOKAt SccCertificate.placeCfg (lay2 Le P1) OX = true,
      OpenAPt h Spike.Lib.LowerNode.hello1o_accepted2 E (ElH h) (fun _ => True)) :
    ∀ E : Entry, E.Ok (lay2 Le P1) → ∀ h : placeOKAt SccCertificate.placeCfg (lay2 Le P1) OX = true,
      OpenAWF h Spike.Lib.LowerNode.hello1o_accepted2 E (ElH h) (fun _ => True) := fun E hE h =>
  cxLB_hAW_none h _ hello1_hty.choose_spec hello1_hTn (HP E hE h)

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.cxLB_hAW_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.cxLB_hAW_none

/-- info: 'Spike.Lib.LowerX64.hello1_hAW_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_hAW_none
