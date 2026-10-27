/-
**`hello1` from the assembled start segment, the holes named** (x86-64;
the twin of `Spike/Test/A64Hello1ClosedAt2B.lean`): `hello1_of_closedAt2`
(`Spike/Test/X64Hello1ClosedAt2.lean`) with `In2X`'s start segment `H0In`
from `h0In_setup_assembledB` (`Spike/Lib/LowerX64/H0InAssembledB.lean`):
`hello1o`'s setup type and `CfgNeedOk` decided. What is left, explicit: the landings' segments `H1In`, the
main thread's posts `hPost`, the setup call `hS`, `main`'s call `hU` (for
every choice of the bounds, `Bounds2`) and the parse check `hpa`.

- `OpenB`: the open premises at an output and entry state.
- `in2X_ofB`: `In2X` from them (`h0In_setup_assembledB`).
- `hello1_hty`: `hello1o`'s setup type.
- `hello1_of_closedAt2B`: the statement at `hello1o` from `OpenB` at its
  admissible entry states.
-/
import Spike.Lib.LowerX64.H0InAssembledB
import Spike.Test.X64Hello1ClosedAt2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open A9NoSpawn Scc.Cert.WideX64
open Spike.Lib (Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND At swR FStable)
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.AllocReach (Reach IN)
open Spike.Lib.LowerNode (FrOk2 ZBad setupWords2)
open Spike.Lib.X64.Rt (SetupCode SetupCallWS MainCallWSF MainSW SetupArgs swFSL mainSIn oU rS0 entryR rtF setupMC
  rtCodeOkS mainS0R mainSRR CFactsC arOf marshal)

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Spike.Lib.LowerNode.imms2Me Λ p)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.X64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The program's start control (`S0X`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).env, none⟩ : Ctl)

set_option hygiene false in
/-- `W2At` at `Closed2At`'s instance. -/
local notation "W2S" J:max => W2At h (Spike.Lib.LowerNode.imms2Me Λ p) p Spike.Lib.LowerNode.IsNum (rS0 (Ly)) J Dt
  (fun _ => 0)

set_option hygiene false in
/-- `MSAt` at `Closed2At`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max =>
  MSAt h (Spike.Lib.LowerNode.imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- The frame invariant `J` holds at the starts (`StartsSX`). -/
local notation "StJ" J:max => ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
  ∀ s c fs, StartsSX h E (rtF (Ly)) El Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs

set_option hygiene false in
/-- The switch region at depth `L`, below the top `v`. -/
local notation "RS" v:max => ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)

set_option hygiene false in
/-- The switch region's frame condition, below the top `v`. -/
local notation "FS" v:max => (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
  (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => tpOf (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64


/-- The open premises of `h0In_setup_assembledB` with `H1In`, at some landings' states and write tail. -/
def OpenB (ty : Ty) (E : Entry) : Prop :=
  ∃ (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa) (Dt : State → Prop),
    H1In h E El Dt ∧
    (∀ c fs v, UPostRF p (fun _ => none) c fs v → MainCtlN (lay2 Λ p) (fun _ => none) c fs) ∧
    (∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
      Bounds2 cfg p sizes labelOffs (Ly) L D1 D2 lS lM fS nS fM nM →
      ∀ J : InvS, StJ J → ∀ v, SetupCallWS (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
        (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (RS v) (FS v)
        (setupMC (setupWords2 p)).setup (setupMC (setupWords2 p)).Z D1 (Int64.ofInt (fS : Int))
        (SRetR (fun _ => none) ty) ((Ly).lab (setupMC (setupWords2 p)).sp0).toBitVec C0 TP0) ∧
    (∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
      Bounds2 cfg p sizes labelOffs (Ly) L D1 D2 lS lM fS nS fM nM →
      ∀ J : InvS, StJ J → ∀ v, MainCallWSF (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
        (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (RS v) (FS v)
        (setupMC (setupWords2 p)).fn (setupMC (setupWords2 p)).Z D2 (Int64.ofInt (fM : Int))
        (SetupArgs (SPostC p (fun _ => none) ty C0) (setupMC (setupWords2 p)).sw (TP0).toBitVec)
        (UPostRF p (fun _ => none)) ((Ly).lab (setupMC (setupWords2 p)).sp1).toBitVec TP0)

/-- **`In2X` from the open premises**: `h0In_setup_assembledB`'s `H0In`
with `OpenB`'s `H1In`. -/
theorem in2X_ofB (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hcfg : CfgNeedOk pcfg = true)
    {E : Entry} (hE : E.Ok (lay2 Λ p)) (H : OpenB h ty E) : In2X h E := by
  obtain ⟨El, Dt, H1, hPost, hS, hU⟩ := H
  exact ⟨El, Dt, h0In_setup_assembledB h hp hty hcfg hE hPost hS hU, H1⟩

end Assembled

/-- The program. -/
local notation "P1" => Spike.Test.Hello1MainSrc.hello1o

variable {Λx : Scc.Sem.Layout}

set_option hygiene false in
/-- The layout: any layout at which the placement check passes (`h`). -/
local notation "Le" => Λx

/-- `hello1o` has a setup block. -/
theorem hello1_hty : ∃ ty, Scc.Lower.setupOf P1 = some ty := Option.isSome_iff_exists.mp (by decide)

/-- **`hello1`'s x86-64 statement, the holes named**: from `OpenB` (`H1In`, `hPost`, `hS`, `hU`) at every
admissible entry state and the parse `hpa`. -/
theorem hello1_of_closedAt2B
    (h0 : placeOKAt SccCertificate.placeCfg Le
      (Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config Spike.Test.Hello1MainSrc.hello1o)
        SccCertificate.sizes SccCertificate.labelOffs) = true)
    (H : ∀ E : Entry, E.Ok (lay2 Le P1) →
      ∀ h' : placeOKAt SccCertificate.placeCfg (lay2 Le P1)
        (Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1)
          SccCertificate.sizes SccCertificate.labelOffs) = true,
      OpenB h' hello1_hty.choose E)
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩
      SccCertificate.out.prog SccCertificate.out.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    Scc.Sem.X64.CorrectE 1
      (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1) P1)
      { Le with static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me Le P1 } B
      ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩ :=
  hello1_of_closedAt2 h0 (fun E hE h' => in2X_ofB h' Spike.Lib.LowerNode.hello1o_accepted2 hello1_hty.choose_spec
    (by decide) hE (H E hE h')) hpa hB

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.in2X_ofB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms in2X_ofB

/-- info: 'Spike.Lib.LowerX64.hello1_hty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hello1_hty

/-- info: 'Spike.Lib.LowerX64.hello1_of_closedAt2B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_of_closedAt2B

end Spike.Lib.LowerX64
