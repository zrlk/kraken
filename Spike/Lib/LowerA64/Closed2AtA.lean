/-
**The AArch64 `Accepted2` compiler theorem from the start's and the
landings' segments** (`a64_scc_correctE_text_closedAt2`): `Closed2StmtA`
from `Closed2InA`, the two segment obligations `rest2A_of'` leaves open
(`H0InA`, `H1InA`) at every instance and admissible entry state, everything
else discharged: `Rest2A` by `rest2A_of'` at the nodes' abort predicate
`ab2` (the write abort's for a `print` program, else none; its `hpr` by
`hpr2`), `Correct` by `a64_scc_correctE_text_closedAt2_of`'s steps.

- `ab2`, `hpr2`: the nodes' abort predicate and its `hpr`.
- `H0InA`: the start's segment inside `W2` (`rest2A_of'`'s `h0`).
- `H1InA`: each landing's segment inside `W2` (`rest2A_of'`'s `h1`).
- `In2A`: some landings' states and write tail with both.
- `rest2A_ofIn`: `Rest2A` from `In2A`.
- `a64_scc_correctE_text_closedAt2_at`: `Closed2StmtA`'s conclusion at one
  instance, from `In2A` at that instance's entry states.
- `Closed2InA`, `a64_scc_correctE_text_closedAt2`: `Closed2InA → Closed2StmtA`.
-/
import Spike.Lib.LowerA64.Closed2OfA
import Spike.Lib.LowerA64.Rest2OfA

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow.Ret0 (TakeK)
open Spike.Lib.AllocReach (Reach IN)
open Spike.Lib.A64.Rt (rtF)

/-- **The nodes' abort predicate**: the write abort's at the labels `lab`
for a program with the output extern, else none. -/
def ab2 (p : Prog) (lab : Label → Int64) : Option (State → Prop) :=
  if Scc.Lower.hasPrint p then some (Spike.Lib.A64.WriteAb.Ab lab) else none

/-- `ab2` is `rest2A_of'`'s `hpr`. -/
theorem hpr2 (p : Prog) (lab : Label → Int64) :
    ab2 p lab = none ∨ (ab2 p lab = some (Spike.Lib.A64.WriteAb.Ab lab) ∧ Scc.Lower.hasPrint p = true) := by
  unfold ab2
  cases Scc.Lower.hasPrint p <;> simp

section In

variable {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.A64.Out} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) o = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Spike.Lib.LowerNode.imms2Me Λ p)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.A64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The record's marks. -/
local notation "Mk" => Spike.Lib.A64.PhRec.μ (Ly)

set_option hygiene false in
/-- **`W2` at the record** at a placement `L`, `ls`, over `IN … J` (as in
`Spike/Lib/LowerA64/Rest2OfA.lean`). -/
local notation "W2R" J:max Dt:max L:max ls:max =>
  fun s c fs => W2 (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (Spike.Lib.A64.PhRec.own (Ly))
    (Spike.Lib.A64.Rt.rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly)) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J) Dt
    (Spike.Lib.A64.WriteAb.Ab (Ly).lab) L ls s c fs

set_option hygiene false in
/-- **The rows' memory side at the record** at the nodes' abort `ab2`. -/
local notation "MSR" J:max L:max ls:max =>
  msOfAX (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (fun s _ => Spike.Lib.A64.PhRec.own (Ly) s) (Ar)
    (IN (Ar) (fun _ => none) (fun _ => 0) J) (ab2 p (Ly).lab) L ls

/-- **The start's segment** (`rest2A_of'`'s `h0` at `ab2`) at an output
passing `placeOKAt` at `lay2 Λ p` (`h`) and an entry state `E`, for the
landings' states `El` and the write tail `Dt`: from `_start`'s node on the
entry stack (`S0A` at `rtF`) inside `W2` over `IN … J` for every frame
invariant `J` holding at the starts (`StartsSA`, with the pairs carrying
their own segment). -/
structure H0InA (E : Entry) (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2)
    (Dt : State → Prop) : Prop where
  /-- The start's segment inside `W2` over `IN … J`. -/
  h0 : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSA h E (rtF (Ly)) El Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs) →
    SegWS (W2R J Dt (fun _ => none) (fun _ => 0))
      (TakeK ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL) (Spike.Lib.A64.Rt.rS0 (Ly))) p (fun _ => none)
      (MSR J (fun _ => none) (fun _ => 0)) (S0A h E (rtF (Ly))) fun _ _ _ => False

/-- **The landings' segments** (`rest2A_of'`'s `h1` at `ab2`): each
landing's states `El L ls l b n`, one allocation past a reachable
placement, inside `W2` over `IN … J` at the placement extended. -/
structure H1InA (E : Entry) (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2)
    (Dt : State → Prop) : Prop where
  /-- Each landing's segment inside `W2` over `IN … J`. -/
  h1 : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSA h E (rtF (Ly)) El Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs) →
    ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
      Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
      SegWS (W2R J Dt (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n))
        (TakeK ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL) (Spike.Lib.A64.Rt.rS0 (Ly))) p
        (Spike.Lib.AllocReach.upd L l b)
        (MSR J (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n))
        (El L ls l b n) fun _ _ _ => False

/-- **The segment obligations at an output and entry state**: some
landings' states `El` and write tail `Dt` with the start's (`H0InA`) and
the landings' (`H1InA`) segments. -/
def In2A (E : Entry) : Prop :=
  ∃ (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) (Dt : State → Prop),
    H0InA h E El Dt ∧ H1InA h E El Dt

/-- **`Rest2A` from the segment obligations** (`rest2A_of'` at `ab2`,
`hpr2`). -/
theorem rest2A_ofIn {arch : WeakMem.Arch} {E : Entry} (hE : E.Ok (lay2 Λ p)) (H : In2A h E) :
    Rest2A (lay2 Λ p) p h arch E := by
  obtain ⟨El, Dt, H0, H1⟩ := H
  exact rest2A_of' h hE H0.h0 H1.h1 (hpr2 p _)

end In

open Scc.Cert.Link.A64 in
/-- **The AArch64 compiler theorem at one instance from its segment
obligations**: `Closed2StmtA`'s conclusion at `cfg`, `pcfg`, `p`, `Λ` and
its premises, from `In2A` at every admissible entry state of that instance
(`H`): `correct2_of` at `rest2A_ofIn` on the parsed output, as in
`a64_scc_correctE_text_closedAt2_of`. -/
theorem a64_scc_correctE_text_closedAt2_at {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog}
    {Λ : Scc.Sem.Layout}
    (hp : Scc.Lower.Accepted2 p = true) (_hR : Scc.Lower.mainRetOk p = true)
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (_hcfg : CfgNeedOkA pcfg = true)
    (H : ∀ E : Entry, E.Ok (lay2 Λ p) →
      ∀ h' : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true,
      In2A h' E)
    {asm : String} (hpa : Scc.Cert.Link.A64.parsesTo asm
      (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog
      (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch p) p)
      { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me Λ p } B asm := by
  intro E hE
  obtain ⟨h1, h2⟩ := parsed_of_parsesTo hpa
  exact correct_of_parsed _ E h1 h2
    (correct2_of hp h (Spike.Lib.A64.Rt.ctrZ_ofPlaceOK h) hB hE
      (hnum2 hp h arch) (hd2 hp h) (hrd2 hp h arch) (rest2A_ofIn h hE (H E hE h)))

/-- **The segment obligations of the `Accepted2` theorem**: `In2A` at every
instance of `Closed2StmtA` and every admissible entry state. -/
def Closed2InA : Prop :=
  ∀ (cfg : Scc.Config) (pcfg : Scc.Cert.PlaceOK.Config) (p : Prog) (Λ : Scc.Sem.Layout),
    Scc.Lower.Accepted2 p = true →
    Scc.Lower.mainRetOk p = true →
    placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true →
    CfgNeedOkA pcfg = true → ∀ (E : Entry), E.Ok (lay2 Λ p) →
    ∀ h' : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true,
    In2A h' E

/-- **The AArch64 compiler theorem for an `Accepted2` program from its
segment obligations**: `Closed2StmtA` from `Closed2InA`
(`a64_scc_correctE_text_closedAt2_at` at each instance). -/
theorem a64_scc_correctE_text_closedAt2 (H : Closed2InA) : Closed2StmtA := by
  intro cfg pcfg p Λ hp hR h hcfg asm hpa B hB arch
  exact a64_scc_correctE_text_closedAt2_at hp hR h hcfg (H cfg pcfg p Λ hp hR h hcfg) hpa hB

/-- info: 'Spike.Lib.LowerA64.rest2A_ofIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rest2A_ofIn

/--
info: 'Spike.Lib.LowerA64.a64_scc_correctE_text_closedAt2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms a64_scc_correctE_text_closedAt2

end Spike.Lib.LowerA64
