/-
**The x86-64 `Accepted2` compiler theorem from the start's and the
landings' segments** (`x64_scc_correctE_text_closedAt2`): `Closed2Stmt`
from `Closed2In`, the two segment obligations `rest2X_of'` leaves open
(`H0In`, `H1In`) at every instance and admissible entry state, everything
else discharged: `Rest2X` by `rest2X_of'` at the nodes' abort predicate
`ab2` (the write abort's for a `print` program, else none; its `hpr` by
`hpr2`), `Correct` by `x64_scc_correctE_text_closedAt2_of`'s steps.

- `ab2`, `hpr2`: the nodes' abort predicate and its `hpr`.
- `H0In`: the start's segment inside `W2` (`rest2X_of'`'s `h0`).
- `H1In`: each landing's segment inside `W2` (`rest2X_of'`'s `h1`).
- `In2X`: some landings' states and write tail with both.
- `rest2X_ofIn`: `Rest2X` from `In2X`.
- `x64_scc_correctE_text_closedAt2_at`: `Closed2Stmt`'s conclusion at one
  instance, from `In2X` at that instance's entry states.
- `Closed2In`, `x64_scc_correctE_text_closedAt2`: `Closed2In → Closed2Stmt`.
-/
import Spike.Lib.LowerX64.Closed2Of
import Spike.Lib.LowerX64.Rest2Of

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64.Flow.Ret0 (TakeK)
open Spike.Lib.AllocReach (Reach IN)
open Spike.Lib.X64.Rt (rtF)

/-- **The nodes' abort predicate**: the write abort's at the labels `lab`
for a program with the output extern, else none. -/
def ab2 (p : Prog) (lab : Label → Int64) : Option (State → Prop) :=
  if Scc.Lower.hasPrint p then some (Spike.Lib.X64.WriteAb.Ab lab) else none

/-- `ab2` is `rest2X_of'`'s `hpr`. -/
theorem hpr2 (p : Prog) (lab : Label → Int64) :
    ab2 p lab = none ∨ (ab2 p lab = some (Spike.Lib.X64.WriteAb.Ab lab) ∧ Scc.Lower.hasPrint p = true) := by
  unfold ab2
  cases Scc.Lower.hasPrint p <;> simp

section In

variable {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.X64.Out} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) o = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Spike.Lib.LowerNode.imms2Me Λ p)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.X64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The record's marks. -/
local notation "Mk" => Spike.Lib.X64.PhRec.μ (Ly)

set_option hygiene false in
/-- **`W2` at the record** at a placement `L`, `ls`, over `IN … J` (as in
`Spike/Lib/LowerX64/Rest2Of.lean`). -/
local notation "W2R" J:max Dt:max L:max ls:max =>
  fun s c fs => W2 (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (Spike.Lib.X64.PhRec.own (Ly))
    (Spike.Lib.X64.Rt.rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly)) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J) Dt
    (Spike.Lib.X64.WriteAb.Ab (Ly).lab) L ls s c fs

set_option hygiene false in
/-- **The rows' memory side at the record** at the nodes' abort `ab2`. -/
local notation "MSR" J:max L:max ls:max =>
  msOfAX (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (fun s _ => Spike.Lib.X64.PhRec.own (Ly) s) (Ar)
    (IN (Ar) (fun _ => none) (fun _ => 0) J) (ab2 p (Ly).lab) L ls

/-- **The start's segment** (`rest2X_of'`'s `h0` at `ab2`) at an output
passing `placeOKAt` at `lay2 Λ p` (`h`) and an entry state `E`, for the
landings' states `El` and the write tail `Dt`: from `_start`'s node on the
entry stack (`S0X` at `rtF`) inside `W2` over `IN … J` for every frame
invariant `J` holding at the starts (`StartsSX`, with the pairs carrying
their own segment). -/
structure H0In (E : Entry) (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa)
    (Dt : State → Prop) : Prop where
  /-- The start's segment inside `W2` over `IN … J`. -/
  h0 : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSX h E (rtF (Ly)) El Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs) →
    SegWS (W2R J Dt (fun _ => none) (fun _ => 0))
      (TakeK ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL) (Spike.Lib.X64.Rt.rS0 (Ly))) p (fun _ => none)
      (MSR J (fun _ => none) (fun _ => 0)) (S0X h E (rtF (Ly))) fun _ _ _ => False

/-- **The landings' segments** (`rest2X_of'`'s `h1` at `ab2`): each
landing's states `El L ls l b n`, one allocation past a reachable
placement, inside `W2` over `IN … J` at the placement extended. -/
structure H1In (E : Entry) (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa)
    (Dt : State → Prop) : Prop where
  /-- Each landing's segment inside `W2` over `IN … J`. -/
  h1 : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSX h E (rtF (Ly)) El Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs) →
    ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
      Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
      SegWS (W2R J Dt (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n))
        (TakeK ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL) (Spike.Lib.X64.Rt.rS0 (Ly))) p
        (Spike.Lib.AllocReach.upd L l b)
        (MSR J (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n))
        (El L ls l b n) fun _ _ _ => False

/-- **The segment obligations at an output and entry state**: some
landings' states `El` and write tail `Dt` with the start's (`H0In`) and
the landings' (`H1In`) segments. -/
def In2X (E : Entry) : Prop :=
  ∃ (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa) (Dt : State → Prop),
    H0In h E El Dt ∧ H1In h E El Dt

/-- **`Rest2X` from the segment obligations** (`rest2X_of'` at `ab2`,
`hpr2`). -/
theorem rest2X_ofIn {arch : WeakMem.Arch} {E : Entry} (hE : E.Ok (lay2 Λ p)) (H : In2X h E) :
    Rest2X (lay2 Λ p) p h arch E := by
  obtain ⟨El, Dt, H0, H1⟩ := H
  exact rest2X_of' h hE H0.h0 H1.h1 (hpr2 p _)

end In

open Scc.Cert.Link.X64 in
/-- **The x86-64 compiler theorem at one instance from its segment
obligations**: `Closed2Stmt`'s conclusion at `cfg`, `pcfg`, `p`, `sizes`,
`labelOffs`, `Λ` and its premises, from `In2X` at every admissible entry
state of that instance (`H`): `correct2_of` at `rest2X_ofIn` on the parsed
output, as in `x64_scc_correctE_text_closedAt2_of`. -/
theorem x64_scc_correctE_text_closedAt2_at {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog}
    {sizes : List Nat} {labelOffs : List (String × Nat)} {Λ : Scc.Sem.Layout}
    (hp : Scc.Lower.Accepted2 p = true) (_hR : Scc.Lower.mainRetOk p = true)
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (_hcfg : CfgNeedOk pcfg = true)
    (H : ∀ E : Entry, E.Ok (lay2 Λ p) →
      ∀ h' : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true,
      In2X h' E)
    {text : String} (hpa : Scc.Cert.Link.X64.parsesTo ⟨text, sizes, labelOffs⟩
      (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog
      (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch p) p)
      { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me Λ p } B ⟨text, sizes, labelOffs⟩ := by
  intro E hE
  obtain ⟨h1, h2⟩ := parsed_of_parsesTo hpa
  exact correct_of_parsed _ E h1 h2
    (correct2_of hp h (Spike.Lib.X64.Rt.ctrZ_ofPlaceOK h) hB hE
      (hnum2 hp h arch) (hd2 hp h) (hrd2 hp h arch) (rest2X_ofIn h hE (H E hE h)))

/-- **The segment obligations of the `Accepted2` theorem**: `In2X` at every
instance of `Closed2Stmt` and every admissible entry state. -/
def Closed2In : Prop :=
  ∀ (cfg : Scc.Config) (pcfg : Scc.Cert.PlaceOK.Config) (p : Prog) (sizes : List Nat)
    (labelOffs : List (String × Nat)) (Λ : Scc.Sem.Layout), Scc.Lower.Accepted2 p = true →
    Scc.Lower.mainRetOk p = true →
    placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true →
    CfgNeedOk pcfg = true → ∀ (E : Entry), E.Ok (lay2 Λ p) →
    ∀ h' : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true,
    In2X h' E

/-- **The x86-64 compiler theorem for an `Accepted2` program from its
segment obligations**: `Closed2Stmt` from `Closed2In`
(`x64_scc_correctE_text_closedAt2_at` at each instance). -/
theorem x64_scc_correctE_text_closedAt2 (H : Closed2In) : Closed2Stmt := by
  intro cfg pcfg p sizes labelOffs Λ hp hR h hcfg text hpa B hB arch
  exact x64_scc_correctE_text_closedAt2_at hp hR h hcfg (H cfg pcfg p sizes labelOffs Λ hp hR h hcfg) hpa hB

/-- info: 'Spike.Lib.LowerX64.rest2X_ofIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rest2X_ofIn

/--
info: 'Spike.Lib.LowerX64.x64_scc_correctE_text_closedAt2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms x64_scc_correctE_text_closedAt2

end Spike.Lib.LowerX64
