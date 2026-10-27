/-
**`hello1`'s setup call `hS` on AArch64 at `WordsNone`, the setup frame's
contexts the landings' `CxOkH`** (`Spike/Test/A64Hello1SetupOpenOfF.lean`
at `CxOk0 := CxOkH`, `Spike/Test/A64Hello1CxOkH.lean`): the setup frame's
base context is the one the landings `ElH` carry, so that the landings and
`hS` agree. `SetupCxLB` at the family `J` at a `CxOkH` context is
`cxLB_ofCxOkH` (`Spike/Test/A64Hello1CxLBH.lean`).

Left (`SetupPreHA`): the allocator's `W2` instance at every landings'
context (`AllocWH`) and the buffer allocations' heap aborts' segment
(`habA`).

- `CxOkS.key_single`: a single-frame `CxOkS` context's key is a bottom key
  (when no key is a bottom key at the empty frames);
- `AllocWH`: `cxLB_ofCxOkH`'s `hAW` at every `CxOkH` context with the setup
  frame's bottom key `SB`;
- `SetupPreHA`, `OpenPHA`: the remaining premises, at one choice and at every
  choice of the bounds;
- `setupOpenFA_ofPreH`: `SetupOpenFA … (CxOkH …)` from `SetupPreHA`;
- `openSFA_of_openPHA`, `hello1_hSFA_ofPreH`: at `hello1o`, `OpenSFA` and
  `HSBVFA` from `OpenPHA`.
-/
import Spike.Test.A64Hello1SetupOpenOfF
import Spike.Test.A64Hello1CxLBH

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

section Key

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {exe : _root_.Executable} {prog : List Directive} {endPc : Int64}
  {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
  {i : Expr → String → Nat → Option Nat} {T : Nat → Expr → Prop} {P : Prog}

/-- **At one frame, a context's key is the bottom's** when no bottom key is
at no frames (`hB0`): the records `StkOk` at a single frame are none (one
record would leave the bottom at no frames). -/
theorem CxOkS.key_single {hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe prog endPc RaOk Cd i (T j) d}
    {CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop} {Bot : StkKey → List TermRun.Frame → Prop}
    (hB0 : ∀ k, ¬ Bot k []) {j : Nat} {R : Region} {F : MachineData → Prop} {f : TermRun.Frame}
    {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isaLSE2}
    (h : CxOkS (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk Bot j R F [f] fp ra tp G0 Ab) :
    Bot ⟨j, R, F, fp, ra, tp, G0⟩ [f] := by
  obtain ⟨-, st, hst⟩ := h
  match st, hst with
  | [], hst => exact hst
  | [_], hst => exact (hB0 _ hst.2).elim
  | _ :: _ :: _, hst => exact hst.2.elim

end Key

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

/-! ## The allocator's `W2` instance at the landings' contexts -/

set_option linter.unusedVariables false in
/-- **The allocator's `W2` instance at every landings' context**
(`cxLB_ofCxOkH`'s `hAW` at every `CxOkH` context of the `j`th block, at the
family `J`, whose key is the setup frame's bottom key `SB J v D1 fS`). -/
def AllocWH (Dt : State → Prop) (hp : Scc.Lower.Accepted2 p = true) (J : InvS) (v : BitVec 64) (L D1 : Int)
    (fS : Nat) {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) : Prop :=
  ∀ (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64)
    (G0 : Ctl → Prop) (Ab' : FragS isaLSE2), CxOkH h hp j R F fs fp ra tp G0 Ab' →
    (SB J v D1 fS) ⟨j, R, F, fp, ra, tp, G0⟩ fs →
    AllocW2At p (fun _ => none) (fun _ => 0) (fnCode2OfPMe hp h Λ j d hd).lcx (fnCode2OfPMe hp h Λ j d hd).cx
      (CdCLE OP (Spike.Lib.A64.PhRec.okPc LY0) (Spike.Lib.A64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec ra))
      ((fnCode2OfPMe hp h Λ j d hd).Bl ra)
      (fun lbl lsize s c => W2 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum
        (Spike.Lib.A64.PhRec.GOf Ly M0) (Spike.Lib.A64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly))
        (arOf (Ly).Λ) (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) Dt (Ab (Ly).lab) lbl lsize s c fs)
      (KT) (Ly).exe (Ly).endPc R F ((MSS J) fs) fp ra tp G0 (imms2Me Λ p) (TailAt2 p j) (RetLk d.retTy)

/-! ## The setup frame's open premises at the landings' contexts -/

set_option linter.unusedVariables false in
/-- **The setup call's remaining premises at the landings' contexts** at
the bounds `L`, `D1`, the top `v` and the setup block's compiled index `j`
(`SetupPreFA` with `hAW` at every landings' context, `AllocWH`). -/
structure SetupPreHA (Dt : State → Prop) (hp : Scc.Lower.Accepted2 p = true) (J : InvS) (v : BitVec 64)
    (L D1 : Int) (fS : Nat) {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) : Prop where
  /-- The allocator's `W2` instance at every landings' context. -/
  hAW : AllocWH h Dt hp J v L D1 fS hd
  /-- The buffer allocations' heap aborts' segment at the setup frame (`SetupOpenFA.habA`). -/
  habA : ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PREF F' g fr →
    SegWS (W2S J) (KT) p (fun _ => none) (MSS J)
      (AbAl2 (MSS J) (fun _ => none) (fnCode2OfPMe hp h Λ j d hd) (RC) F' [fr]) (fun _ _ _ => False)

/-- **`SetupOpenFA` at the landings' contexts `CxOkH`** (`setupOpenFA_ofPre`
at `CxOk0 := CxOkH`): `hs` by `setupHs_ofCxLB` with `cxLB_ofCxOkH` (`hAW` by `AllocWH`), `hcx`
by `CxOkH`'s own witnesses (the family `J`, `PREF`'s `WordsNone` split
off). -/
theorem setupOpenFA_ofPreH (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
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
    (hno : addFreeT d.body = true) (hTg : tgOkB OP = true) (H : SetupPreHA h Dt hp J v L D1 fS hd) :
    SetupOpenFA h Dt hp J v L D1 fS hd (CxOkH h hp) where
  hs := fnSpecC2_ofCxLBMe hp h Λ hd hA (Spike.Lib.A64.Rt.rS0_sub _)
    (Spike.Lib.A64.Rt.fitS_of_sub _ (Spike.Lib.A64.Rt.rS0_sub _)) (Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp)
    hnc hTn fun _ _ _ _ _ _ _ _ hC _ => by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, -⟩ := hC.1
      exact cxLB_ofCxOkH h hp hty J hd hC.1
        (H.hAW _ _ _ _ _ _ _ _ hC.1 (CxOkS.key_single (fun _ hk => by obtain ⟨_, h0, -⟩ := hk; cases h0) hC))
  hcx _ g fr hP hk := ⟨d, hd, L, D1, fS, nS, v, g, fr, J, hn, hfS, hnS, hL0, hLm, hL8, hD18, hL1, hrow,
    ⟨hP.1, hP.2.1, hP.2.2.1, fun m hm => ⟨(hP.2.2.2.1 m hm).1.2, (hP.2.2.2.1 m hm).2⟩, hP.2.2.2.2⟩,
    fun m hm => (hP.2.2.2.1 m hm).1.1, hk, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  hTg := hTg_of_tgOkB hTg (fnCode2OfPMe hp h Λ j d hd).hf (fnCode2OfPMe hp h Λ j d hd).h1
    (fnCode2OfPMe hp h Λ j d hd).h16 (fun _ _ h => h) (Ly).lab
  hab _ _ _ _ := abOf2_seg_addFree hno hd
  habA := H.habA

/-- **The remaining premises at every choice of the bounds at the
landings' contexts** (`SetupPreHA` at `Bounds2A`'s `L`, `D1`, every
invariant holding at the starts at `WordsNone ∧ rtF`, every top and the
setup block's compiled index; `OpenPFA`'s shape). -/
def OpenPHA (hp : Scc.Lower.Accepted2 p = true) (E : Entry)
    (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) (Dt : State → Prop) : Prop :=
  ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
    Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM →
    ∀ J : InvS, StJ J → ∀ v j d (hd : (compiled2 p)[j]? = some d), d.name = "rodata" →
      SetupPreHA h Dt hp J v L D1 fS hd

end Assembled

/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

/-- `ld`'s layout of the linked executable. -/
local notation "LeA" => Spike.Test.Hello1LinkedA64.Λe

/-- **`hello1o`'s open premises at the landings' contexts from the
remaining ones** (`OpenSFA` at `CxOk0 := CxOkH` from `OpenPHA`:
`setupOpenFA_ofPreH` at `hello1_allocInA`, `hello1_rodata_noCall`,
`hello1_rodata_elem2`, `hello1_rodata_addFree`, `hello1_tgOkBA`). -/
theorem openSFA_of_openPHA
    (h' : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A)
      (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)) = true)
    {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {Dt : State → Prop}
    (H : OpenPHA h' Spike.Lib.LowerNode.hello1o_accepted2 E El Dt) :
    OpenSFA h' Spike.Lib.LowerNode.hello1o_accepted2 E El Dt := by
  intro L D1 D2 lS lM fS nS fM nM hB J hJ v j d hd hn
  refine ⟨CxOkH h' Spike.Lib.LowerNode.hello1o_accepted2, ?_⟩
  obtain ⟨-, hfS, -, hnS, -, -, -, -, hrow, -, hL0, hLm, hL8, -, hD18, -, -, hL1, -⟩ := id hB
  exact setupOpenFA_ofPreH h' Spike.Lib.LowerNode.hello1o_accepted2 hello1_htyA.choose_spec J v hfS hnS hL0
    hLm hL8 hD18 hL1 hrow hd hn hello1_allocInA (hello1_rodata_noCall j d hd hn) (hello1_rodata_elem2 hd hn)
    (hello1_rodata_addFree j d hd hn) hello1_tgOkBA (H L D1 D2 lS lM fS nS fM nM hB J hJ v j d hd hn)

/-- **`hello1`'s setup call `hS` on AArch64 at `WordsNone`, the setup
frame's contexts the landings' `CxOkH`**: `HSBVFA` at any landings `El`
(e.g. `ElH`) and write tail `Dt` from `OpenPHA` (`hAW` at every landings'
context, `habA`). -/
theorem hello1_hSFA_ofPreH
    (h' : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A)
      (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)) = true)
    {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {Dt : State → Prop}
    (H : OpenPHA h' Spike.Lib.LowerNode.hello1o_accepted2 E El Dt) :
    HSBVFA h' hello1_htyA.choose E El Dt :=
  hSBVFA_ofOpenSFA h' Spike.Lib.LowerNode.hello1o_accepted2 hello1_htyA.choose_spec hello1_huA
    (openSFA_of_openPHA h' H)

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.CxOkS.key_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CxOkS.key_single

/-- info: 'Spike.Lib.LowerA64.setupOpenFA_ofPreH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms setupOpenFA_ofPreH

/-- info: 'Spike.Lib.LowerA64.hello1_hSFA_ofPreH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_hSFA_ofPreH

end Spike.Lib.LowerA64
