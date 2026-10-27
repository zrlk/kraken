/-
**The setup call's open premise on the `WordsNone` chain** (AArch64; the
twin of `Spike/Test/X64Hello1HolesW.lean`): the allocator's `W2` instance
at the landings' contexts alone (`OpenAHA`: `SetupPreHA.hAW` at every
choice of the bounds), `hello1_finalAW_ofT`'s
(`Spike/Test/A64Hello1FinalT.lean`) `HA`. `OpenPHA`'s heap aborts' segment
`habA` is `hello1_habAB` (`Spike/Test/A64Hello1HabA.lean`) at the bounds'
rows, the setup call's premises without `WordsNone`, the write tail
`fun _ => True` closing its `hDtH`.

- `OpenAHA`: `SetupPreHA.hAW` at every choice of the bounds;
- `openPHA_of_openAHA`: `OpenPHA` at the write tail `fun _ => True` from it.
-/
import Spike.Test.A64Hello1ClosedBVBF
import Spike.Test.A64Hello1SetupOpenOfH
import Spike.Test.A64Hello1HabA

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


/-- **The allocator's `W2` instance at every choice of the bounds**
(`SetupPreHA.hAW` at `OpenPHA`'s quantifiers). -/
def OpenAHA (hp : Scc.Lower.Accepted2 p = true) (E : Entry)
    (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) (Dt : State → Prop) : Prop :=
  ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
    Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM →
    ∀ J : InvS, StJ J → ∀ (v : BitVec 64) (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d),
      d.name = "rodata" → AllocWH h Dt hp J v L D1 fS hd

/-- **`OpenPHA` at the write tail `fun _ => True` from `OpenAHA`**: `hAW`
from it, `habA` by `hello1_habAB` at `Bounds2A`'s rows (`PREF`'s
`WordsNone` dropped; the heap stub's `write` tail trivial). -/
theorem openPHA_of_openAHA (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    (H : OpenAHA h hp E El (fun _ => True)) : OpenPHA h hp E El (fun _ => True) := by
  intro L D1 D2 lS lM fS nS fM nM hB J hJ v j d hd hn
  obtain ⟨-, hfS, -, hnS, -, -, -, -, hrow, -, hL0, hLm, hL8, -, hD18, -, -, hL1, -⟩ := id hB
  refine { hAW := H L D1 D2 lS lM fS nS fM nM hB J hJ v j d hd hn
           habA := fun F' g fr hP => ?_ }
  exact hello1_habAB h hp hty hfS hnS hL0 hLm hL8 hD18 hL1 hrow hd hn J v (fun _ _ _ _ _ _ => trivial) F' g fr
    ⟨hP.1, hP.2.1, hP.2.2.1, fun m hm => ⟨(hP.2.2.2.1 m hm).1.2, (hP.2.2.2.1 m hm).2⟩, hP.2.2.2.2⟩

end Assembled

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.openPHA_of_openAHA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.openPHA_of_openAHA

