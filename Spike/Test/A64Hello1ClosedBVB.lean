/-
**`hello1` from the assembled start segment over the setup call's known
frame condition, `main`'s post placed by its value, the holes named**
(AArch64; the twin of `Spike/Test/X64Hello1ClosedBVB.lean`):
`hello1_of_closedAt2A` (`Spike/Test/A64Hello1ClosedAt2.lean`) with `In2A`'s
start segment `H0InA` from `h0InA_setup_assembledBVB`
(`Spike/Lib/LowerA64/H0InAssembledBVBA.lean`), its setup call `hS` from
`hello1_hSA` (`Spike/Test/A64Hello1HS.lean`). `hello1o`'s setup type,
`CfgNeedOkA` and the setup block's argument type are decided; the entry
`hE` is the statement's own (every admissible entry state).

Remaining holes (the hypotheses of `hello1_of_closedBVBA`):
- [ ] `H1InA`: the landings' segments (`Closed2InA`'s `H1InA`);
- [ ] `HUBVA` (`hU`): `main`'s call `MainCallWSF` at the post
  `UPostRF ∧ MainCtlV`, at every choice of the bounds (`Bounds2A`): the
  user call's held exit;
- [ ] `OpenSA`: the setup call's open premises (`SetupOpenA`): the setup
  function's segment `FnSpecC2` at `CxOkS`, the base context, the body's
  blocks inside `W2`, the aborts' segment at the setup frame, and the
  callee rooms the allocator's and `print`'s frames need (`Bounds2A`);
- [ ] `hpa`: the parse check (the certificate's compiled `#guard`).

- `HUBVA`: `main`'s call at every choice of the bounds;
- `OpenBVBA`, `in2A_ofBVB`: `h0InA_setup_assembledBVB`'s open premises with
  `H1InA`, and `In2A` from them;
- `hello1_of_closedBVBA`: the statement at `hello1o` from the holes above.
-/
import Spike.Lib.LowerA64.H0InAssembledBVBA
import Spike.Test.A64Hello1HS

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Rt (SetupCode setupMC SetupCallWS MainCallWSF SetupArgs swFSL rS0 rtF arOf)
open Spike.Lib.A64.AllocG (abLabs)
open Spike.Lib.LowerNode (FrOk2 ZBad setupWords2)
open Spike.Lib.AllocReach (Reach IN)

open Spike.Lib.A64.Rt (SetupCallWSB SetupGF)

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Spike.Lib.LowerNode.imms2Me Λ p)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.A64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The program's start control (`S0A`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).env, none⟩ : Ctl)

set_option hygiene false in
/-- `W2At` at `Closed2AtA`'s instance. -/
local notation "W2S" J:max => W2At h (Spike.Lib.LowerNode.imms2Me Λ p) p Spike.Lib.LowerNode.IsNum (rS0 (Ly)) J Dt (fun _ => 0)

set_option hygiene false in
/-- `MSAt` at `Closed2AtA`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max =>
  MSAt h (Spike.Lib.LowerNode.imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- The frame invariant `J` holds at the starts (`StartsSA`). -/
local notation "StJ" J:max => ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
  ∀ s c fs, StartsSA h E (rtF (Ly)) El Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs

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
/-- The switch region's frame condition, below the top `v`. -/
local notation "FS" v:max => swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) v


/-- **`main`'s call at every choice of the bounds** at the post
`UPostRF ∧ MainCtlV` (`h0InA_setup_assembledBVB`'s `hU`). -/
def HUBVA (ty : Ty) (E : Entry) (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2)
    (Dt : State → Prop) : Prop :=
  ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
    Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM →
    ∀ J : InvS, StJ J → ∀ v, MainCallWSF (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
      (setupMC (setupWords2 p)).fn (setupMC (setupWords2 p)).Z D2 (Int64.ofInt (fM : Int))
      (SetupArgs (SPostC p (fun _ => none) ty C0) (setupMC (setupWords2 p)).sw (X0))
      (fun c fs v => UPostRF p (fun _ => none) c fs v ∧ MainCtlV (lay2 Λ p) (fun _ => none) c fs v)
      ((Ly).lab (setupMC (setupWords2 p)).sp1).toBitVec (TP0)

/-- The open premises of `h0InA_setup_assembledBVB` with `H1InA`, at some
landings' states and write tail. -/
def OpenBVBA (ty : Ty) (E : Entry) : Prop :=
  ∃ (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) (Dt : State → Prop),
    H1InA h E El Dt ∧ HSBA h ty E El Dt ∧ HUBVA h ty E El Dt

/-- **`In2A` from the open premises**: `h0InA_setup_assembledBVB`'s `H0InA`
with `OpenBVBA`'s `H1InA`. -/
theorem in2A_ofBVB (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hcfg : CfgNeedOkA pcfg = true)
    {E : Entry} (hE : E.Ok (lay2 Λ p)) (H : OpenBVBA h ty E) : In2A h E := by
  obtain ⟨El, Dt, H1, hS, hU⟩ := H
  exact ⟨El, Dt, h0InA_setup_assembledBVB h hp hty hcfg hE hS hU, H1⟩

end Assembled

/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

/-- `ld`'s layout of the linked executable. -/
local notation "LeA" => Spike.Test.Hello1LinkedA64.Λe

/-- **`hello1`'s AArch64 statement, the holes named**: at every admissible
entry state and placement, the landings' segments `H1InA`, the setup call's
open premises `OpenSA` (its `hS` by `hello1_hSA`) and `main`'s call
`HUBVA`; and the parse `hpa`. -/
theorem hello1_of_closedBVBA
    (H : ∀ E : Entry, E.Ok (lay2 LeA P1A) →
      ∀ h' : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A)
        (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)) = true,
      ∃ (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) (Dt : State → Prop),
        H1InA h' E El Dt ∧ OpenSA h' Spike.Lib.LowerNode.hello1o_accepted2 E El Dt ∧
        HUBVA h' hello1_htyA.choose E El Dt)
    (hpa : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.out.prog SccCertificate.out.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    Scc.Sem.A64.CorrectE 1
      (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1A) P1A)
      { LeA with static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me LeA P1A } B
      SccCertificate.asm :=
  hello1_of_closedAt2A (fun E hE h' => by
    obtain ⟨El, Dt, H1, hO, hU⟩ := H E hE h'
    exact in2A_ofBVB h' Spike.Lib.LowerNode.hello1o_accepted2 hello1_htyA.choose_spec (by decide) hE
      ⟨El, Dt, H1, hello1_hSA h' hO, hU⟩) hpa hB

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.in2A_ofBVB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms in2A_ofBVB

/-- info: 'Spike.Lib.LowerA64.hello1_of_closedBVBA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_of_closedBVBA

end Spike.Lib.LowerA64
