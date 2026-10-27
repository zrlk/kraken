/-
**`hello1` from the assembled start segment over the setup call's known
frame condition, `main`'s post placed by its value, the holes named**
(x86-64; the twin of `Spike/Test/A64Hello1ClosedBVB.lean`):
`hello1_of_closedAt2` (`Spike/Test/X64Hello1ClosedAt2.lean`) with `In2X`'s
start segment `H0In` from `h0In_setup_assembledBVB`
(`Spike/Lib/LowerX64/H0InAssembledBVB.lean`). `hello1o`'s setup type and
`CfgNeedOk` are decided; the entry `hE` is the statement's own (every
admissible entry state).

Remaining holes (the hypotheses of `hello1_of_closedBVB`):
- [ ] `H1In`: the landings' segments (`Closed2In`'s `H1In`);
- [ ] `HSBV` (`hS`): the setup call `SetupCallWSB` at `SetupGF`, at every
  choice of the bounds (`Bounds2`): the x86-64 twin of `hello1_hSA`
  (`Spike/Test/A64Hello1HS.lean`, from `hS_assembledB`), with its own open
  premises (the setup function's segment, the base context, the body's
  blocks inside `W2`, the aborts, the allocator's and `print`'s rooms);
- [ ] `HUBV` (`hU`): `main`'s call `MainCallWSF` at the post
  `UPostRF ∧ MainCtlV`, at every choice of the bounds: the user call's held
  exit;
- [ ] `hpa`: the parse check (the certificate's compiled `#guard`).

- `HSBV`, `HUBV`: the setup call and `main`'s call at every choice of the
  bounds;
- `OpenBVB`, `in2X_ofBVB`: `h0In_setup_assembledBVB`'s open premises with
  `H1In`, and `In2X` from them;
- `hello1_of_closedBVB`: the statement at `hello1o` from the holes above.
-/
import Spike.Lib.LowerX64.H0InAssembledBVB
import Spike.Test.X64Hello1ClosedAt2B

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

open Spike.Lib.X64.Rt (SetupCallWSB SetupGF)

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


/-- **The setup call at every choice of the bounds** at the setup call's
known frame condition (`h0In_setup_assembledBVB`'s `hS`). -/
def HSBV (ty : Ty) (E : Entry) (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa)
    (Dt : State → Prop) : Prop :=
  ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
    Bounds2 cfg p sizes labelOffs (Ly) L D1 D2 lS lM fS nS fM nM →
    ∀ J : InvS, StJ J → ∀ v, SetupCallWSB (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (RS v) (FS v)
      (setupMC (setupWords2 p)).setup (setupMC (setupWords2 p)).Z D1 (Int64.ofInt (fS : Int))
      (SRetR (fun _ => none) ty) ((Ly).lab (setupMC (setupWords2 p)).sp0).toBitVec C0 TP0
      (SetupGF p (Ly).lab ((MSS J) []) (RS v) (FS v) (setupMC (setupWords2 p)) D1 (Int64.ofInt (fS : Int))
        ⟨TOP - 8#64, TP0, C0⟩ (TP0).toBitVec)

/-- **`main`'s call at every choice of the bounds** at the post
`UPostRF ∧ MainCtlV` (`h0In_setup_assembledBVB`'s `hU`). -/
def HUBV (ty : Ty) (E : Entry) (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa)
    (Dt : State → Prop) : Prop :=
  ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
    Bounds2 cfg p sizes labelOffs (Ly) L D1 D2 lS lM fS nS fM nM →
    ∀ J : InvS, StJ J → ∀ v, MainCallWSF (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (RS v) (FS v)
      (setupMC (setupWords2 p)).fn (setupMC (setupWords2 p)).Z D2 (Int64.ofInt (fM : Int))
      (SetupArgs (SPostC p (fun _ => none) ty C0) (setupMC (setupWords2 p)).sw (TP0).toBitVec)
      (fun c fs v => UPostRF p (fun _ => none) c fs v ∧ MainCtlV (lay2 Λ p) (fun _ => none) c fs v)
      ((Ly).lab (setupMC (setupWords2 p)).sp1).toBitVec TP0

/-- The open premises of `h0In_setup_assembledBVB` with `H1In`, at some
landings' states and write tail. -/
def OpenBVB (ty : Ty) (E : Entry) : Prop :=
  ∃ (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa) (Dt : State → Prop),
    H1In h E El Dt ∧ HSBV h ty E El Dt ∧ HUBV h ty E El Dt

/-- **`In2X` from the open premises**: `h0In_setup_assembledBVB`'s `H0In`
with `OpenBVB`'s `H1In`. -/
theorem in2X_ofBVB (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hcfg : CfgNeedOk pcfg = true)
    {E : Entry} (hE : E.Ok (lay2 Λ p)) (H : OpenBVB h ty E) : In2X h E := by
  obtain ⟨El, Dt, H1, hS, hU⟩ := H
  exact ⟨El, Dt, h0In_setup_assembledBVB h hp hty hcfg hE hS hU, H1⟩

end Assembled

/-- The program. -/
local notation "P1" => Spike.Test.Hello1MainSrc.hello1o

/-- `ld`'s layout of the linked executable. -/
local notation "Le" => Spike.Test.Hello1LinkedX64.Λe

/-- **`hello1`'s x86-64 statement, the holes named**: from `OpenBVB`
(`H1In`, `hS`, `hU`) at every admissible entry state and placement, and the
parse `hpa`. -/
theorem hello1_of_closedBVB
    (H : ∀ E : Entry, E.Ok (lay2 Le P1) →
      ∀ h' : placeOKAt SccCertificate.placeCfg (lay2 Le P1)
        (Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1)
          SccCertificate.sizes SccCertificate.labelOffs) = true,
      OpenBVB h' hello1_hty.choose E)
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩
      SccCertificate.out.prog SccCertificate.out.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    Scc.Sem.X64.CorrectE 1
      (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1) P1)
      { Le with static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me Le P1 } B
      ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩ :=
  hello1_of_closedAt2 (fun E hE h' => in2X_ofBVB h' Spike.Lib.LowerNode.hello1o_accepted2 hello1_hty.choose_spec
    (by decide) hE (H E hE h')) hpa hB

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.in2X_ofBVB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms in2X_ofBVB

/-- info: 'Spike.Lib.LowerX64.hello1_of_closedBVB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_of_closedBVB

end Spike.Lib.LowerX64
