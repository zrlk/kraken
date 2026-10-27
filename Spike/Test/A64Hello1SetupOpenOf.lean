/-
**`hello1`'s setup call `hS` on AArch64 with `SetupOpenA` closed but for the
setup frame's premises** (the twin of `Spike/Test/X64Hello1SetupOpenOf.lean`;
`Spike/Test/A64Hello1HS.lean`'s `SetupOpenA` at `CxOk0 := SetupCxLB`): `hs`
by `setupHs_ofCxLB0` (`Spike/Test/A64Hello1HsOf.lean`), `hcx` by
`setupCxLB_ofPre` (`Spike/Test/A64Hello1CxLBOf.lean`, its premises from
`PRE`), `hTg` by `hTg_of_tgOkB` (`Spike/Lib/LowerA64/UserTgt.lean`) at a
checked output (`tgOkB`; at `hello1o`, `hello1_tgOkBA`), `hab` by
`abOf2_seg_addFree` at an addition-free setup block (`hno`; at `hello1o`,
`hello1_rodata_addFree`).

Left (`SetupPreA`, at the setup call's premises `PRE F' g fr`): the private
memory loads no heap or static word (`hwn`), the allocator's `W2` instance
(`hAW`), and the buffer allocations' heap aborts' segment (`habA`,
`SetupOpenA`'s).

- `SetupPreA`, `OpenPA`: the remaining premises, at one choice and at every
  choice of the bounds;
- `setupOpenA_ofPre`: `SetupOpenA … (SetupCxLB …)` from the allocator's
  code, the block's points, the output's jump check and `SetupPreA`;
- `openSA_of_openPA`: at `hello1o`, `OpenSA` from `OpenPA`;
- `hello1_hSA_ofPre`: at `hello1o`, `HSBA` from `OpenPA`.

Unlike the x86-64 twin: `PRE` carries the callee region's 16-alignment, so
none is derived; `SetupOpenA` has the abort node's segment `hab`, closed
here at an addition-free block.
-/
import Spike.Test.A64Hello1CxLBOf
import Spike.Test.A64Hello1NoCall
import Spike.Test.A64Hello1SetupAb
import Spike.Test.A64Hello1TgOk

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
open Spike.Lib.LowerNode (setupWords2 compiled2 TailAt2 imms2Me addFreeT)
open Spike.Lib.A64.Flow.Ret0 (WcG CallerCells limA)
open Spike.Lib.AllocReach (Reach IN)

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates (`fnCode2OfP`'s). -/
local notation "LY0" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.A64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))

set_option hygiene false in
/-- The canonical load's memory of the output. -/
local notation "M0" => Spike.Lib.A64.PhRec.m0Of (Ly).Λ OP (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).secs

set_option hygiene false in
/-- `W2At` at `Closed2AtA`'s instance. -/
local notation "W2S" J:max => W2At h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum (rS0 (Ly)) J Dt (fun _ => 0)

set_option hygiene false in
/-- `MSAt` at `Closed2AtA`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max =>
  MSAt h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- The frame invariant `J` holds at the starts (`StartsSA`). -/
local notation "StJ" J:max => ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
  ∀ s c fs, StartsSA h E (rtF (Ly)) El Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs

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
/-- The first TCB. -/
local notation "TP0" => UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The switch region's frame condition, below the top `v`. -/
local notation "FS" v:max => swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) v

set_option hygiene false in
/-- The setup call's callee region. -/
local notation "RC" => (swR v (-L) 0).callee (-(setupMC (setupWords2 p)).Z.toInt) (-D1) 0

set_option hygiene false in
set_option linter.unusedVariables false in
/-- The ghosts at the setup frame. -/
local notation "GR" g:max fr:max => fun c => Spike.Lib.FrameRunM p (g.c0, [fr]) (c, [fr])

set_option hygiene false in
/-- The first TCB's address. -/
local notation "X0" => pinA (Ly).lab + 0#64 + 8#64

set_option hygiene false in
/-- The stack records' bottom keys at the setup frame (`SetupOpenA`'s). -/
local notation "SB" J:max v:max D1:max fS:max => fun k fs =>
  SetupBot p (Ly).lab ((MSS J) []) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
    (setupMC (setupWords2 p)) D1 (Int64.ofInt fS) ⟨TOP, TP0, C0⟩ (X0) k fs

set_option hygiene false in
set_option linter.unusedVariables false in
/-- The setup call's segment's premises (`SetupOpenA.hcx`'s `PRE`). -/
local notation "PRE" F':max g:max fr:max => (RC).OK ∧ (RC).base.toNat % 16 = 0 ∧ FStable (RC) F' ∧
  (∀ m, F' m → (FS v) m ∧ CallerCells (swR v (-L) 0) (-(setupMC (setupWords2 p)).Z.toInt) (-D1) 0 m) ∧
  g.ra = ((Ly).lab (setupMC (setupWords2 p)).e0 + 4).toBitVec ∧ g.tp = TP0 ∧
  Spike.Lib.A64.Flow.CallTo p C0 g.c0 fr ∧ (RC).base = g.sp

set_option linter.unusedVariables false in
/-- **The setup call's remaining premises** at the bounds `L`, `D1`, the top
`v` and the setup block's compiled index `j` (`setupCxLB_ofPre`'s `hwn`,
`hAW` and `SetupOpenA.habA`, under `PRE`). -/
structure SetupPreA (Dt : State → Prop) (hp : Scc.Lower.Accepted2 p = true) (J : InvS) (v : BitVec 64)
    (L D1 : Int) (fS : Nat) {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) : Prop where
  /-- The private memory loads no heap or static word. -/
  hwn : ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PRE F' g fr →
    ∀ m, F' m → Spike.Lib.DmemPriv.WordsNone (Ly).Λ m.dmem
  /-- The allocator's `W2` instance at the setup frame, at its bottom key. -/
  hAW : ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PRE F' g fr →
    (SB J v D1 fS) ⟨j, RC, F', g.fp, g.ra, TP0, GR g fr⟩ [fr] →
    AllocW2At p (fun _ => none) (fun _ => 0) (fnCode2OfPMe hp h Λ j d hd).lcx (fnCode2OfPMe hp h Λ j d hd).cx
      (CdCLE OP (Spike.Lib.A64.PhRec.okPc LY0) (Spike.Lib.A64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec g.ra))
      ((fnCode2OfPMe hp h Λ j d hd).Bl g.ra)
      (fun lbl lsize s c => W2 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum
        (Spike.Lib.A64.PhRec.GOf Ly M0) (Spike.Lib.A64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly))
        (arOf (Ly).Λ) (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) Dt (Ab (Ly).lab) lbl lsize s c [fr])
      (KT) (Ly).exe (Ly).endPc (RC) F' ((MSS J) [fr]) g.fp g.ra (TP0) (GR g fr) (imms2Me Λ p) (TailAt2 p j)
      (RetLk d.retTy)
  /-- The buffer allocations' heap aborts' segment at the setup frame (`SetupOpenA.habA`). -/
  habA : ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PRE F' g fr →
    SegWS (W2S J) (KT) p (fun _ => none) (MSS J)
      (AbAl2 (MSS J) (fun _ => none) (fnCode2OfPMe hp h Λ j d hd) (RC) F' [fr]) (fun _ _ _ => False)

/-- **`SetupOpenA` at `SetupCxLB` from the remaining premises**: `hs` by
`setupHs_ofCxLB0` (the allocator's code `hA`, no call `hnc`, one-word
elements `hTn`), `hcx` by `setupCxLB_ofPre` (its region and call facts from
`PRE`), `hTg` by `hTg_of_tgOkB` at the output's jump check (`hTg`, the
frame's facts from `fnCode2OfPMe`), `hab` by `abOf2_seg_addFree` (`hno`). -/
theorem setupOpenA_ofPre (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
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
    (hno : addFreeT d.body = true) (hTg : tgOkB OP = true) (H : SetupPreA h Dt hp J v L D1 fS hd) :
    SetupOpenA h Dt hp J v L D1 fS hd (SetupCxLB h hp Dt J hd) where
  hs := setupHs_ofCxLB0 h hp J hd _ hA hnc hTn
  hcx F' g fr hP hk :=
    setupCxLB_ofPre h hp hty J v hfS hnS hL0 hLm hL8 hD18 hL1 hrow hd hn hP.1 hP.2.1 hP.2.2.1 hP.2.2.2.1
      hP.2.2.2.2.2.2.1 (H.hwn F' g fr hP) (H.hAW F' g fr hP hk)
  hTg := hTg_of_tgOkB hTg (fnCode2OfPMe hp h Λ j d hd).hf (fnCode2OfPMe hp h Λ j d hd).h1
    (fnCode2OfPMe hp h Λ j d hd).h16 (fun _ _ h => h) (Ly).lab
  hab _ _ _ _ := abOf2_seg_addFree hno hd
  habA := H.habA

/-- **The remaining premises at every choice of the bounds** (`SetupPreA`
at `Bounds2A`'s `L`, `D1`, every invariant holding at the starts, every top
and the setup block's compiled index; `OpenSA`'s shape). -/
def OpenPA (hp : Scc.Lower.Accepted2 p = true) (E : Entry)
    (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) (Dt : State → Prop) : Prop :=
  ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
    Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM →
    ∀ J : InvS, StJ J → ∀ v j d (hd : (compiled2 p)[j]? = some d), d.name = "rodata" →
      SetupPreA h Dt hp J v L D1 fS hd

end Assembled

/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

/-- `ld`'s layout of the linked executable. -/
local notation "LeA" => Spike.Test.Hello1LinkedA64.Λe

/-- **`hello1o`'s open premises from the remaining ones** (`OpenSA` from
`OpenPA`: `setupOpenA_ofPre` at `hello1_allocInA`, `hello1_rodata_noCall`,
`hello1_rodata_elem2`, `hello1_rodata_addFree`, `hello1_tgOkBA`). -/
theorem openSA_of_openPA
    (h' : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A)
      (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)) = true)
    {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {Dt : State → Prop}
    (H : OpenPA h' Spike.Lib.LowerNode.hello1o_accepted2 E El Dt) :
    OpenSA h' Spike.Lib.LowerNode.hello1o_accepted2 E El Dt := by
  intro L D1 D2 lS lM fS nS fM nM hB J hJ v j d hd hn
  refine ⟨SetupCxLB h' Spike.Lib.LowerNode.hello1o_accepted2 Dt J hd, ?_⟩
  obtain ⟨-, hfS, -, hnS, -, -, -, -, hrow, -, hL0, hLm, hL8, -, hD18, -, -, hL1, -⟩ := id hB
  exact setupOpenA_ofPre h' Spike.Lib.LowerNode.hello1o_accepted2 hello1_htyA.choose_spec J v hfS hnS hL0
    hLm hL8 hD18 hL1 hrow hd hn hello1_allocInA (hello1_rodata_noCall j d hd hn) (hello1_rodata_elem2 hd hn)
    (hello1_rodata_addFree j d hd hn) hello1_tgOkBA (H L D1 D2 lS lM fS nS fM nM hB J hJ v j d hd hn)

/-- **`hello1`'s setup call `hS` on AArch64 from the remaining premises**:
`hello1_hSA` at `openSA_of_openPA`. -/
theorem hello1_hSA_ofPre
    (h' : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A)
      (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)) = true)
    {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {Dt : State → Prop}
    (H : OpenPA h' Spike.Lib.LowerNode.hello1o_accepted2 E El Dt) :
    HSBA h' hello1_htyA.choose E El Dt :=
  hello1_hSA h' (openSA_of_openPA h' H)

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.setupOpenA_ofPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms setupOpenA_ofPre

/-- info: 'Spike.Lib.LowerA64.openSA_of_openPA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms openSA_of_openPA

/-- info: 'Spike.Lib.LowerA64.hello1_hSA_ofPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_hSA_ofPre

end Spike.Lib.LowerA64
