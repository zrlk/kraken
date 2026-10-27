/-
**`hello1`'s setup call `hS` on x86-64 with `SetupOpen` closed but for the
setup frame's premises** (`Spike/Test/X64Hello1HS.lean`'s `SetupOpen` at
`CxOk0 := SetupCxLB`): `hs` by `setupHs_ofCxLB0`
(`Spike/Test/X64Hello1HsOf.lean`), `hcx` by `setupCxLB_ofPre`
(`Spike/Test/X64Hello1CxLBOf.lean`; the callee region's 8-alignment from
the first stack's top and `setupMC_Z`), `hTg` by `hTg_of_tgOkB`
(`Spike/Lib/LowerX64/UserTgt.lean`) at a checked output (`tgOkB`; at
`hello1o`, `hello1_tgOkB`).

Left (`SetupPre`, at the setup call's premises `PRE F' g fr`): the private
memory loads no heap or static word (`hwn`), the allocator's `W2` instance
(`hAW`), and the buffer allocations' heap aborts' segment (`habA`,
`SetupOpen`'s). `setupCxLB_ofPre`'s `hAb` is closed at the setup frame's
aborts `AbU2` (its `AbAl2` side).

- `SetupPre`, `OpenP`: the remaining premises, at one choice and at every
  choice of the bounds;
- `setupOpen_ofPre`: `SetupOpen … (SetupCxLB …)` from the allocator's code,
  the block's points, the output's jump check and `SetupPre`;
- `openS_of_openP`: at `hello1o`, `OpenS` from `OpenP`;
- `hello1_hS_ofPre`: at `hello1o`, `HSBV` from `OpenP`.
-/
import Spike.Test.X64Hello1CxLBOf
import Spike.Test.X64Hello1NoCall
import Spike.Test.X64Hello1TgOk

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (swR FStable At)
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Flow.Ret0 (WcG CallerCells limA)
open Spike.Lib.X64.Flow.NewBuf (nbX)
open Spike.Lib.X64.Rt (setupMC rS0 arOf swFSL rtF)
open Spike.Lib.X64.WriteAb (Ab)
open Spike.Lib.LowerNode (setupWords2 compiled2 TailAt2 imms2Me)
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
/-- The allocator's runtime layout. -/
local notation "Ar" => Spike.Lib.X64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)

set_option hygiene false in
/-- The canonical load's memory of the output. -/
local notation "M0" => Spike.Lib.X64.PhRec.m0Of (Ly).Λ OP
  (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).secs

set_option hygiene false in
/-- `W2At` at `Closed2At`'s instance. -/
local notation "W2S" J:max => W2At h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum (rS0 (Ly)) J Dt (fun _ => 0)

set_option hygiene false in
/-- `MSAt` at `Closed2At`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max =>
  MSAt h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- The frame invariant `J` holds at the starts (`StartsSX`). -/
local notation "StJ" J:max => ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
  ∀ s c fs, StartsSX h E (rtF (Ly)) El Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The program's start control (`S0X`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).env, none⟩ : Ctl)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => tpOf (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The switch region at depth `L`, below the first stack's top. -/
local notation "RS" => ((swR (TOP) (-L) 0).callee (-8 - 0) (8 - L) 8)

set_option hygiene false in
/-- The switch region's frame condition, below the first stack's top. -/
local notation "FS" => (fun m => swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) (TOP) m ∧
  CallerCells (swR (TOP) (-L) 0) (-8 - 0) (8 - L) 8 m)

set_option hygiene false in
/-- The setup call's callee region. -/
local notation "RC" => (RS).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8

set_option hygiene false in
set_option linter.unusedVariables false in
/-- The ghosts at the setup frame. -/
local notation "GR" g:max fr:max => fun c => Spike.Lib.FrameRunM p (g.c0, [fr]) (c, [fr])

set_option hygiene false in
set_option linter.unusedVariables false in
/-- The setup call's segment's premises (`SetupOpen.hcx`'s `PRE`). -/
local notation "PRE" F':max g:max fr:max => (RC).OK ∧ FStable (RC) F' ∧
  (∀ m, F' m → (FS) m ∧ CallerCells (RS) (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8 m) ∧
  g.ra = ((Ly).lab (setupMC (setupWords2 p)).sp0).toBitVec ∧ g.tp = TP0 ∧
  Spike.Lib.X64.Flow.CallTo p C0 g.c0 fr ∧ (RC).base = g.sp

set_option linter.unusedVariables false in
/-- **The setup call's remaining premises** at the bounds `L`, `D1` and the
setup block's compiled index `j` (`setupCxLB_ofPre`'s `hwn`, `hAW` and
`SetupOpen.habA`, under `PRE`). -/
structure SetupPre (Dt : State → Prop) (hp : Scc.Lower.Accepted2 p = true) (J : InvS) (L D1 : Int)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) : Prop where
  /-- The private memory loads no heap or static word. -/
  hwn : ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PRE F' g fr →
    ∀ m, F' m → Spike.Lib.DmemPriv.WordsNone (Ly).Λ m.dmem
  /-- The allocator's `W2` instance at the setup frame. -/
  hAW : ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PRE F' g fr →
    AllocW2At p (fun _ => none) (fun _ => 0) (fnCode2OfPMe hp h Λ j d hd).lcx (fnCode2OfPMe hp h Λ j d hd).fr
      (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec g.ra))
      ((fnCode2OfPMe hp h Λ j d hd).Bl g.ra)
      (fun lbl lsize s c => W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum
        (Spike.Lib.X64.PhRec.GOf Ly M0) (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly))
        (arOf (Ly).Λ) (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) Dt (Ab (Ly).lab) lbl lsize s c [fr])
      (KT) (Ly).exe (Ly).endPc (rbR (RC)) F' ((MSS J) [fr]) g.fp g.ra (TP0) (GR g fr) (imms2Me Λ p)
      (TailAt2 p j) (RetLk d.retTy)
  /-- The buffer allocations' heap aborts' segment at the setup frame (`SetupOpen.habA`). -/
  habA : ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PRE F' g fr →
    SegWS (W2S J) (KT) p (fun _ => none) (MSS J)
      (AbAl2 (MSS J) (fun _ => none) (fnCode2OfPMe hp h Λ j d hd) (rbR (RC)) F' [fr]) (fun _ _ _ => False)

/-- **`SetupOpen` at `SetupCxLB` from the remaining premises**: `hs` by
`setupHs_ofCxLB0` (the allocator's code `hA`, no call `hnc`, one-word
elements `hTn`), `hcx` by `setupCxLB_ofPre` (the callee region's base
8-aligned: the switch region's callee's base is the first stack's top less 8,
the setup call's 16 + `Z` below it, `Z` a multiple of 16 by `setupMC_Z`),
`hTg` by `hTg_of_tgOkB` at the output's jump check (`hTg`). -/
theorem setupOpen_ofPre (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {Dt : State → Prop} (J : InvS) {L D1 : Int} {fS nS : Nat} (hfS : fS + 8 ≤ nS)
    (hnS : (nS : Int) + 48 + 208 ≤ D1) (hL0 : 8 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0) (hD18 : D1 % 8 = 0)
    (hL1 : 8 + 8 + (setupMC (setupWords2 p)).Z.toInt + 8 + D1 ≤ L)
    (hrow : ∀ f, f ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs → f.checkStack = true →
      f.name = Scc.Lower.Names.user "rodata" → (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size = fS)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) (hn : d.name = "rodata")
    (hA : Spike.Lib.X64.Alloc.allocIn OP = true)
    (hnc : (tailsL d.body).all (fun t => !isCallLet t) = true)
    (hTn : ∀ x cn τ e, TailAt2 p j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    (hTg : tgOkB OP = true) (H : SetupPre h Dt hp J L D1 hd) :
    SetupOpen h Dt hp J (TOP) L D1 fS hd (SetupCxLB h hp Dt J hd) := by
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2 h hp hs') (rtCodeOkS_setupWords2 h hp hs')).1
  have hZ := setupMC_Z _ hsw
  have hok : (swR (TOP) (-L) 0).OK := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ (by omega) hLm
  have htop8 : (TOP).toNat % 8 = 0 := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
  have hR1 : (RS).OK :=
    Region.callee_ok hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
      (by show _ ≤ (0 : Int); omega)
  have hb1 : ((RS).base.toNat : Int) = (TOP).toNat - 8 :=
    Region.callee_base hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
  have hbc := Region.callee_base (hi' := 8) (kc := -8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0)
    (lo' := -D1) hR1 (by show 8 - L ≤ _; omega) (by omega) (by show _ < (8 : Int); omega)
  have hR8 : (RC).base.toNat % 8 = 0 := by omega
  exact {
    hs := setupHs_ofCxLB0 h hp J hd _ hA hnc hTn
    hcx := fun F' g fr hP =>
      setupCxLB_ofPre h hp hty J (TOP) hfS hnS hL0 hLm hL8 hD18 hL1 hrow hd hn hP.1 hR8 hP.2.1 hP.2.2.1
        hP.2.2.2.2.2.1 (H.hwn F' g fr hP) (H.hAW F' g fr hP)
        fun Jc pcR _ _ hJ _ hA => Or.inr ⟨rfl, Jc, pcR, hJ, hA⟩
    habA := H.habA
    hTg := hTg_of_tgOkB hTg (fun _ _ h => h) (Ly).lab }

/-- **The remaining premises at every choice of the bounds** (`SetupPre` at
`Bounds2`'s `L`, `D1`, every invariant holding at the starts and the setup
block's compiled index; `OpenS`'s shape). -/
def OpenP (hp : Scc.Lower.Accepted2 p = true) (E : Entry)
    (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa) (Dt : State → Prop) : Prop :=
  ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
    Bounds2 cfg p sizes labelOffs (Ly) L D1 D2 lS lM fS nS fM nM →
    ∀ J : InvS, StJ J → ∀ j d (hd : (compiled2 p)[j]? = some d), d.name = "rodata" →
      SetupPre h Dt hp J L D1 hd

end Assembled

/-- The program. -/
local notation "P1" => Spike.Test.Hello1MainSrc.hello1o

variable {Λx : Scc.Sem.Layout}

set_option hygiene false in
/-- The layout: any layout at which the placement check passes (`h`). -/
local notation "Le" => Λx

/-- **`hello1o`'s open premises from the remaining ones** (`OpenS` from
`OpenP`: `setupOpen_ofPre` at `hello1_allocIn`, `hello1_rodata_noCall`,
`hello1_rodata_elem2`, `hello1_tgOkB`). -/
theorem openS_of_openP
    (h' : placeOKAt SccCertificate.placeCfg (lay2 Le P1)
      (Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1)
        SccCertificate.sizes SccCertificate.labelOffs) = true)
    {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa} {Dt : State → Prop}
    (H : OpenP h' Spike.Lib.LowerNode.hello1o_accepted2 E El Dt) :
    OpenS h' Spike.Lib.LowerNode.hello1o_accepted2 E El Dt := by
  intro L D1 D2 lS lM fS nS fM nM hB J hJ j d hd hn
  refine ⟨SetupCxLB h' Spike.Lib.LowerNode.hello1o_accepted2 Dt J hd, ?_⟩
  obtain ⟨-, hfS, -, hnS, -, -, -, -, -, -, hrow, -, hL0, hLm, hL8, -, hD18, -, -, -, hL1, -⟩ := id hB
  exact setupOpen_ofPre h' Spike.Lib.LowerNode.hello1o_accepted2 hello1_hty.choose_spec J hfS hnS hL0 hLm
    hL8 hD18 hL1 hrow hd hn (hello1_allocIn h') (hello1_rodata_noCall j d hd hn) (hello1_rodata_elem2 hd hn)
    hello1_tgOkB (H L D1 D2 lS lM fS nS fM nM hB J hJ j d hd hn)

/-- **`hello1`'s setup call `hS` on x86-64 from the remaining premises**:
`hello1_hS` at `openS_of_openP`. -/
theorem hello1_hS_ofPre
    (h' : placeOKAt SccCertificate.placeCfg (lay2 Le P1)
      (Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1)
        SccCertificate.sizes SccCertificate.labelOffs) = true)
    {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa} {Dt : State → Prop}
    (H : OpenP h' Spike.Lib.LowerNode.hello1o_accepted2 E El Dt) :
    HSBV h' hello1_hty.choose E El Dt :=
  hello1_hS h' (openS_of_openP h' H)

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.setupOpen_ofPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms setupOpen_ofPre

/-- info: 'Spike.Lib.LowerX64.openS_of_openP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms openS_of_openP

/-- info: 'Spike.Lib.LowerX64.hello1_hS_ofPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_hS_ofPre

end Spike.Lib.LowerX64
