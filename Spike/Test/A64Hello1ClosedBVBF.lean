/-
**`hello1` from the assembled start segment at the start's frame condition
`WordsNone ∧ rtF`, the holes named** (AArch64; the twin of
`Spike/Test/X64Hello1ClosedBVBF.lean`): `Spike/Test/A64Hello1ClosedBVB.lean`
over `H0InAW` (`h0InA_setup_assembledBVBF`) and
`a64_scc_correctE_text_closedAt2_atW` (`Spike/Lib/LowerA64/Closed2AtWA.lean`):
the setup call `hS` and `main`'s call `hU` at the frame condition
`WordsNone ∧ swFSL`, so that their proofs know the memory loads no heap or
image word.

Remaining holes (the hypotheses of `hello1_of_closedBVBFA`): `H1InAW`,
`HSBVFA`, `HUBVFA`, `hpa`, as in `Spike/Test/A64Hello1ClosedBVB.lean`.

- `HSBVFA`: `HSBA` at `WordsNone` (`HUBVFA`, `Spike/Test/A64Hello1HUF.lean`);
- `OpenBVBFA`, `in2AW_ofBVBF`: their open premises with `H1InAW`, and `In2AW`;
- `hello1_of_closedBVBFA`: the statement at `hello1o` from the holes above;
- `hello1_of_closedBVBFAU`: with `main`'s `hU` closed (`hello1_hUBVFA`), at the write tail
  `fun _ => True`: holes `H1InAW`, `HSBVFA`, `hpa`.
-/
import Spike.Lib.LowerA64.Closed2AtWA
import Spike.Lib.LowerA64.H0InAssembledBVBAF
import Spike.Test.A64Hello1ClosedBVB
import Spike.Test.A64Hello1HUF

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
local notation "W2S" J:max => W2At h (Spike.Lib.LowerNode.imms2Me Λ p) p Spike.Lib.LowerNode.IsNum (rS0 (Ly)) J Dt
  (fun _ => 0)

set_option hygiene false in
/-- `MSAt` at `Closed2AtA`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max =>
  MSAt h (Spike.Lib.LowerNode.imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- **The start's frame condition**: the runtime's words unloaded and no
heap or image word loaded (`Closed2AtWA`'s). -/
local notation "WNF" => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧ rtF (Ly) m

set_option hygiene false in
/-- The frame invariant `J` holds at the starts (`StartsSA` at `WNF`). -/
local notation "StJ" J:max => ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
  ∀ s c fs, StartsSA h E (WNF) El Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs

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
/-- The switch region's frame condition with `WordsNone`, below the top
`v`. -/
local notation "FS" v:max => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧
  swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) v m

/-- **`HSBA` at `WordsNone`** (`h0InA_setup_assembledBVBF`'s `hS`): the
setup call at every choice of the bounds, its frame condition
`WordsNone ∧ swFSL`. -/
def HSBVFA (ty : Ty) (E : Entry) (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2)
    (Dt : State → Prop) : Prop :=
  ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
    Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM →
    ∀ J : InvS, StJ J → ∀ v, SetupCallWSB (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
      (setupMC (setupWords2 p)).setup (setupMC (setupWords2 p)).Z D1 (Int64.ofInt (fS : Int))
      (SRetR (fun _ => none) ty) ((Ly).lab (setupMC (setupWords2 p)).e0 + 4).toBitVec C0 (TP0)
      (SetupGF p (Ly).lab ((MSS J) []) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v) (setupMC (setupWords2 p)) D1
        (Int64.ofInt (fS : Int)) ⟨TOP, TP0, C0⟩ (X0))

/-- The open premises of `h0InA_setup_assembledBVBF` with `H1InAW`, at
some landings' states and write tail. -/
def OpenBVBFA (ty : Ty) (E : Entry) : Prop :=
  ∃ (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) (Dt : State → Prop),
    H1InAW h E El Dt ∧ HSBVFA h ty E El Dt ∧ HUBVFA h ty E El Dt

/-- **`In2AW` from the open premises**: `h0InA_setup_assembledBVBF`'s
`H0InAW` with `OpenBVBFA`'s `H1InAW`. -/
theorem in2AW_ofBVBF (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hcfg : CfgNeedOkA pcfg = true)
    {E : Entry} (hE : E.Ok (lay2 Λ p)) (H : OpenBVBFA h ty E) : In2AW h E := by
  obtain ⟨El, Dt, H1, hS, hU⟩ := H
  exact ⟨El, Dt, h0InA_setup_assembledBVBF h hp hty hcfg hE hS hU, H1⟩

end Assembled

/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

/-- `ld`'s layout of the linked executable. -/
local notation "LeA" => Spike.Test.Hello1LinkedA64.Λe

/-- **`hello1`'s AArch64 statement at `WordsNone ∧ rtF`, the holes named**:
from `OpenBVBFA` (`H1InAW`, `hS`, `hU`) at every admissible entry state and
placement, and the parse `hpa` (`a64_scc_correctE_text_closedAt2_atW`). -/
theorem hello1_of_closedBVBFA
    (H : ∀ E : Entry, E.Ok (lay2 LeA P1A) →
      ∀ h' : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A)
        (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)) = true,
      OpenBVBFA h' hello1_htyA.choose E)
    (hpa : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.out.prog SccCertificate.out.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    Scc.Sem.A64.CorrectE 1
      (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1A) P1A)
      { LeA with static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me LeA P1A } B
      SccCertificate.asm :=
  a64_scc_correctE_text_closedAt2_atW Spike.Lib.LowerNode.hello1o_accepted2 (by decide)
    (hello1_out_eqA ▸ Spike.Test.Hello1LinkedA64.hello1_placeOKAt) (by decide)
    (fun E hE h' => in2AW_ofBVBF h' Spike.Lib.LowerNode.hello1o_accepted2 hello1_htyA.choose_spec
      (by decide) hE (H E hE h')) (hello1_out_eqA ▸ hpa) hB

/-- **`hello1`'s AArch64 statement at `WordsNone ∧ rtF`, `main`'s call
closed** (`hello1_of_closedBVBFA` at `hello1_hUBVFA`, the write tail
`fun _ => True`): from the landings' segments `H1InAW` and the setup call
`HSBVFA` at some landings' states, and the parse `hpa`. -/
theorem hello1_of_closedBVBFAU
    (H : ∀ E : Entry, E.Ok (lay2 LeA P1A) →
      ∀ h' : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A)
        (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)) = true,
      ∃ El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2,
        H1InAW h' E El (fun _ => True) ∧ HSBVFA h' hello1_htyA.choose E El (fun _ => True))
    (hpa : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.out.prog SccCertificate.out.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    Scc.Sem.A64.CorrectE 1
      (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1A) P1A)
      { LeA with static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me LeA P1A } B
      SccCertificate.asm :=
  hello1_of_closedBVBFA (fun E hE h' =>
    let ⟨El, H1, hS⟩ := H E hE h'
    ⟨El, fun _ => True, H1, hS, hello1_hUBVFA h' E El⟩) hpa hB

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.in2AW_ofBVBF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms in2AW_ofBVBF

/-- info: 'Spike.Lib.LowerA64.hello1_of_closedBVBFA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_of_closedBVBFA

/-- info: 'Spike.Lib.LowerA64.hello1_of_closedBVBFAU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_of_closedBVBFAU

end Spike.Lib.LowerA64
