/-
**`hello1` from the assembled start segment, the holes named** (AArch64;
the twin of `Spike/Test/X64Hello1ClosedAt2B.lean`): `hello1_of_closedAt2A`
(`Spike/Test/A64Hello1ClosedAt2.lean`) with `In2A`'s start segment `H0InA`
from `h0InA_setup_assembledB` (`Spike/Lib/LowerA64/H0InAssembledBA.lean`):
`hello1o`'s setup type and `CfgNeedOkA` decided. What is left, explicit: the landings' segments `H1InA`, the
main thread's posts `hPost`, the setup call `hS`, `main`'s call `hU` (for
every choice of the bounds, `Bounds2A`) and the parse check `hpa`.

- `OpenBA`: the open premises at an output and entry state.
- `in2A_ofB`: `In2A` from them (`h0InA_setup_assembledB`).
- `hello1_htyA`: `hello1o`'s setup type.
- `hello1_of_closedAt2BA`: the statement at `hello1o` from `OpenBA` at its
  admissible entry states.
-/
import Spike.Lib.LowerA64.H0InAssembledBA
import Spike.Test.A64Hello1ClosedAt2

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


/-- The open premises of `h0InA_setup_assembledB` with `H1InA`, at some landings' states and write tail. -/
def OpenBA (ty : Ty) (E : Entry) : Prop :=
  ∃ (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) (Dt : State → Prop),
    H1InA h E El Dt ∧
    (∀ c fs v, UPostRF p (fun _ => none) c fs v → MainCtlN (lay2 Λ p) (fun _ => none) c fs) ∧
    (∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
      Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM →
      ∀ J : InvS, StJ J → ∀ v, SetupCallWS (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
        (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
        (setupMC (setupWords2 p)).setup (setupMC (setupWords2 p)).Z D1 (Int64.ofInt (fS : Int))
        (SRetR (fun _ => none) ty) ((Ly).lab (setupMC (setupWords2 p)).e0 + 4).toBitVec C0 (TP0)) ∧
    (∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
      Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM →
      ∀ J : InvS, StJ J → ∀ v, MainCallWSF (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
        (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
        (setupMC (setupWords2 p)).fn (setupMC (setupWords2 p)).Z D2 (Int64.ofInt (fM : Int))
        (SetupArgs (SPostC p (fun _ => none) ty C0) (setupMC (setupWords2 p)).sw (X0))
        (UPostRF p (fun _ => none)) ((Ly).lab (setupMC (setupWords2 p)).sp1).toBitVec (TP0))

/-- **`In2A` from the open premises**: `h0InA_setup_assembledB`'s `H0InA`
with `OpenBA`'s `H1InA`. -/
theorem in2A_ofB (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hcfg : CfgNeedOkA pcfg = true)
    {E : Entry} (hE : E.Ok (lay2 Λ p)) (H : OpenBA h ty E) : In2A h E := by
  obtain ⟨El, Dt, H1, hPost, hS, hU⟩ := H
  exact ⟨El, Dt, h0InA_setup_assembledB h hp hty hcfg hE hPost hS hU, H1⟩

end Assembled

/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

variable {Λx : Scc.Sem.Layout}

set_option hygiene false in
/-- The layout: any layout at which the placement check passes (`h`). -/
local notation "LeA" => Λx

/-- `hello1o` has a setup block. -/
theorem hello1_htyA : ∃ ty, Scc.Lower.setupOf P1A = some ty := Option.isSome_iff_exists.mp (by decide)

/-- **`hello1`'s AArch64 statement, the holes named**: from `OpenBA` (`H1InA`, `hPost`, `hS`, `hU`) at
every admissible entry state and the parse `hpa`. -/
theorem hello1_of_closedAt2BA
    (h0 : placeOKAt SccCertificate.placeCfg LeA
      (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)) = true)
    (H : ∀ E : Entry, E.Ok (lay2 LeA P1A) →
      ∀ h' : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A)
        (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)) = true,
      OpenBA h' hello1_htyA.choose E)
    (hpa : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.out.prog SccCertificate.out.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    Scc.Sem.A64.CorrectE 1
      (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1A) P1A)
      { LeA with static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me LeA P1A } B
      SccCertificate.asm :=
  hello1_of_closedAt2A h0 (fun E hE h' => in2A_ofB h' Spike.Lib.LowerNode.hello1o_accepted2
    hello1_htyA.choose_spec (by decide) hE (H E hE h')) hpa hB

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.in2A_ofB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms in2A_ofB

/-- info: 'Spike.Lib.LowerA64.hello1_htyA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hello1_htyA

/-- info: 'Spike.Lib.LowerA64.hello1_of_closedAt2BA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_of_closedAt2BA

end Spike.Lib.LowerA64
