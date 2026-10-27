/-
**`hello1`'s setup call `hS` on x86-64 at `WordsNone`, the setup frame's
contexts the landings' `CxOkH`** (`Spike/Test/X64Hello1SetupOpenOfF.lean`
at `CxOk0 := CxOkH`, `Spike/Test/X64Hello1CxOkH.lean`; the twin of
`Spike/Test/A64Hello1SetupOpenOfH.lean`): the setup frame's base context is
the one the landings `ElX` carry, so that the landings and `hS` agree.
`SetupCxLB` at the family `J` at a `CxOkH` context is `cxLB_ofCxOkH`
(`Spike/Test/X64Hello1CxLBOfH.lean`).

Left (`SetupPreH`): the allocator's `W2` instance at every bound (`AllocWH`,
`cxLB_ofCxOkH`'s `hAW`) and the buffer allocations' heap aborts' segment
(`habA`).

- `AllocWH`: `SetupPreF.hAW` at every bound, top and setup call's premises;
- `SetupPreH`, `OpenPH`: the remaining premises, at one choice and at every
  choice of the bounds;
- `setupOpenF_ofPreH`: `SetupOpenF … (CxOkH …)` from `SetupPreH`;
- `openSF_of_openPH`, `hello1_hSF_ofPreH`: at `hello1o`, `OpenSF` and
  `HSBVF` from `OpenPH`.
-/
import Spike.Test.X64Hello1SetupOpenOfF
import Spike.Test.X64Hello1CxLBOfH

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

/-! ## The allocator's `W2` instance at every bound -/

set_option linter.unusedVariables false in
/-- **The allocator's `W2` instance at every bound** (`SetupPreF.hAW` at
every `L`, `D1`, `fS`, top `v`, setup call's premises and bottom key: `cxLB_ofCxOkH`'s `hAW`,
at the family `J`). -/
def AllocWH (Dt : State → Prop) (hp : Scc.Lower.Accepted2 p = true) (J : InvS) {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) : Prop :=
  ∀ (L D1 : Int) (fS : Nat) (v : BitVec 64) (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame),
    PREF F' g fr → (SB J v D1 fS) ⟨j, RC, F', g.fp, g.ra, TP0, GR g fr⟩ [fr] →
    AllocW2At p (fun _ => none) (fun _ => 0) (fnCode2OfPMe hp h Λ j d hd).lcx (fnCode2OfPMe hp h Λ j d hd).fr
      (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec g.ra))
      ((fnCode2OfPMe hp h Λ j d hd).Bl g.ra)
      (fun lbl lsize s c => W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum
        (Spike.Lib.X64.PhRec.GOf Ly M0) (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly))
        (arOf (Ly).Λ) (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) Dt (Ab (Ly).lab) lbl lsize s c [fr])
      (KT) (Ly).exe (Ly).endPc (rbR (RC)) F' ((MSS J) [fr]) g.fp g.ra (TP0) (GR g fr) (imms2Me Λ p)
      (TailAt2 p j) (RetLk d.retTy)

/-! ## The setup frame's open premises at the landings' contexts -/

set_option linter.unusedVariables false in
/-- **The setup call's remaining premises at the landings' contexts** at
the bounds `L`, `D1`, the top `v` and the setup block's compiled index `j`
(`SetupPreF` with `hAW` at every bound, `AllocWH`). -/
structure SetupPreH (Dt : State → Prop) (hp : Scc.Lower.Accepted2 p = true) (J : InvS) (v : BitVec 64)
    (L D1 : Int) {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) : Prop where
  /-- The allocator's `W2` instance at every bound. -/
  hAW : AllocWH h Dt hp J hd
  /-- The buffer allocations' heap aborts' segment at the setup frame (`SetupOpenF.habA`). -/
  habA : ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PREF F' g fr →
    SegWS (W2S J) (KT) p (fun _ => none) (MSS J)
      (AbAl2 (MSS J) (fun _ => none) (fnCode2OfPMe hp h Λ j d hd) (rbR (RC)) F' [fr]) (fun _ _ _ => False)

/-- **`SetupOpenF` at the landings' contexts `CxOkH`** (`setupOpenF_ofPre`
at `CxOk0 := CxOkH`, the aborts' family `Ja := J`): `hs` by
`setupHs_ofCxLB` with `cxLB_ofCxOkH` (`hAW` by `AllocWH`), `hcx` by
`CxOkH`'s own witnesses (the family `J`, the callee region's alignment
`hR8` as in `setupOpenF_ofPre`, `WordsNone` from `PREF`'s frame
condition, the bottom key `SetupOpenF.hcx`'s). -/
theorem setupOpenF_ofPreH (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {Dt : State → Prop} (J : InvS) {L D1 : Int} {fS nS : Nat} (hfS : fS + 8 ≤ nS)
    (hnS : (nS : Int) + 48 + 208 ≤ D1) (hL0 : 8 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0) (hD18 : D1 % 8 = 0)
    (hL1 : 8 + 8 + (setupMC (setupWords2 p)).Z.toInt + 8 + D1 ≤ L)
    (hrow : ∀ f, f ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs → f.checkStack = true →
      f.name = Scc.Lower.Names.user "rodata" → (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size = fS)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) (hn : d.name = "rodata")
    (hA : Spike.Lib.X64.Alloc.allocIn OP = true)
    (hnc : (tailsL d.body).all (fun t => !isCallLet t) = true)
    (hTn : ∀ x cn τ e, TailAt2 p j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    (hTg : tgOkB OP = true) (H : SetupPreH h Dt hp J (TOP) L D1 hd) :
    SetupOpenF h Dt hp J J (TOP) L D1 fS hd (CxOkH h hp) := by
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
    hs := setupHs_ofCxLB h hp J hd (CxOkH h hp) _ hA hnc hTn fun _ _ _ _ _ _ _ _ hC _ =>
      cxLB_ofCxOkH h hp hty J hd H.hAW hC
    hcx := fun F' g fr hP hB => ⟨d, hd, L, D1, fS, nS, TOP, g, fr, J, hn, hfS, hnS, hL0, hLm, hL8, hD18, hL1, hrow,
      ⟨hP.1, hR8, hP.2.1, hP.2.2.1, hP.2.2.2.1, hP.2.2.2.2.1, hP.2.2.2.2.2.1, hP.2.2.2.2.2.2⟩,
      fun m hm => (hP.2.2.1 m hm).1.1.1, hB, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    habA := H.habA
    hTg := hTg_of_tgOkB hTg (fun _ _ h => h) (Ly).lab }

/-- **The remaining premises at every choice of the bounds at the
landings' contexts** (`SetupPreH` at `Bounds2`'s `L`, `D1`, every invariant
holding at the starts at `WordsNone ∧ rtF` and the setup block's compiled
index; `OpenPF`'s shape). -/
def OpenPH (hp : Scc.Lower.Accepted2 p = true) (E : Entry)
    (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa) (Dt : State → Prop) : Prop :=
  ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
    Bounds2 cfg p sizes labelOffs (Ly) L D1 D2 lS lM fS nS fM nM →
    ∀ J : InvS, StJ J → ∀ j d (hd : (compiled2 p)[j]? = some d), d.name = "rodata" →
      SetupPreH h Dt hp J (TOP) L D1 hd

end Assembled

/-- The program. -/
local notation "P1" => Spike.Test.Hello1MainSrc.hello1o

/-- `ld`'s layout of the linked executable. -/
local notation "Le" => Spike.Test.Hello1LinkedX64.Λe

/-- **`hello1o`'s open premises at the landings' contexts from the
remaining ones** (`OpenSF` at `CxOk0 := CxOkH` from `OpenPH`:
`setupOpenF_ofPreH` at `hello1_allocIn`, `hello1_rodata_noCall`,
`hello1_rodata_elem2`, `hello1_tgOkB`). -/
theorem openSF_of_openPH
    (h' : placeOKAt SccCertificate.placeCfg (lay2 Le P1)
      (Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1)
        SccCertificate.sizes SccCertificate.labelOffs) = true)
    {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa} {Dt : State → Prop}
    (H : OpenPH h' Spike.Lib.LowerNode.hello1o_accepted2 E El Dt) :
    OpenSF h' Spike.Lib.LowerNode.hello1o_accepted2 E El Dt := by
  intro L D1 D2 lS lM fS nS fM nM hB J hJ j d hd hn
  refine ⟨CxOkH h' Spike.Lib.LowerNode.hello1o_accepted2, ?_⟩
  obtain ⟨-, hfS, -, hnS, -, -, -, -, -, -, hrow, -, hL0, hLm, hL8, -, hD18, -, -, -, hL1, -⟩ := id hB
  exact setupOpenF_ofPreH h' Spike.Lib.LowerNode.hello1o_accepted2 hello1_hty.choose_spec J hfS hnS hL0 hLm
    hL8 hD18 hL1 hrow hd hn (hello1_allocIn h') (hello1_rodata_noCall j d hd hn) (hello1_rodata_elem2 hd hn)
    hello1_tgOkB (H L D1 D2 lS lM fS nS fM nM hB J hJ j d hd hn)

/-- **`hello1`'s setup call `hS` on x86-64 at `WordsNone`, the setup
frame's contexts the landings' `CxOkH`**: `HSBVF` at any landings `El`
(e.g. `ElX`) and write tail `Dt` from `OpenPH` (`hAW` at every bound,
`habA`). -/
theorem hello1_hSF_ofPreH
    (h' : placeOKAt SccCertificate.placeCfg (lay2 Le P1)
      (Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1)
        SccCertificate.sizes SccCertificate.labelOffs) = true)
    {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa} {Dt : State → Prop}
    (H : OpenPH h' Spike.Lib.LowerNode.hello1o_accepted2 E El Dt) :
    HSBVF h' hello1_hty.choose E El Dt :=
  hSBVF_ofOpenSF h' Spike.Lib.LowerNode.hello1o_accepted2 hello1_hty.choose_spec hello1_hu hello1_rodata_addFree
    (openSF_of_openPH h' H)

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.setupOpenF_ofPreH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms setupOpenF_ofPreH

/-- info: 'Spike.Lib.LowerX64.hello1_hSF_ofPreH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_hSF_ofPreH

end Spike.Lib.LowerX64
