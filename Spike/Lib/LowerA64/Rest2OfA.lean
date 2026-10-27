/-
**`Rest2A` from the start's and the landings' segments** (AArch64): the
producer top of the `Accepted2` theorem. At an output passing `placeOKAt`
at `lay2 Λ p`, the witnesses are

- `I := IN (arOf …) (fun _ => none) (fun _ => 0) inv` for the family `inv`
  of `nodes2_of_startsS`,
- `rS := rS0 Ly`, `Tk := PhRec.Tk Ly`, `Ab := WriteAb.Ab Ly.lab`,
- `ab`: `some Ab` for a `print` program (with the extern, `hasPrint`), `none`
  otherwise.

`nodes2_of_startsS` gives the nodes, the take's and the abort's paths and the
`write`s' source (`Svc1S`, `Print2A.hsv`); `Start2Facts` the start facts
(`hst2_of`, `htk0_2`, `hab0_2`). Left open, in `Open2A`: the start's and
the landings' segments inside `W2` (`h0`, `h1`), the start's frame
condition (`hF`) and, for `ab = some Ab`, the extern's presence (`hpr`).

- `S0A`: the start's states, `_start`'s node at the program's start
  control on the entry stack; `StartsSA`: the starts at the record, with the
  pairs carrying their own segment (`StartsS`).
- `Open2A`: the open premises; `rest2A_of`: `Rest2A` from them; `rest2A_of'`: at
  `FE := rtF`, `hF` discharged.
-/
import Spike.Lib.LowerA64.Levels2
import Spike.Lib.LowerA64.Start2Facts

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow.Ret0 (TakeK)
open Spike.Lib.AllocReach (Reach IN)
open Spike.Lib.A64.Rt (rtF entryR)

section Rest

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
/-- **`W2` at the record** at a placement `L`, `ls`, over `IN … J` from no
label placed and no size: `nodes2_of_starts`' world at `rd := IsNum`, `G2`,
the record's owned words, the first stack `rS0`, the take phase `PhRec.Tk`
and the write abort's phase. -/
local notation "W2R" J:max Dt:max L:max ls:max =>
  fun s c fs => W2 (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (Spike.Lib.A64.PhRec.own (Ly))
    (Spike.Lib.A64.Rt.rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly)) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J) Dt
    (Spike.Lib.A64.WriteAb.Ab (Ly).lab) L ls s c fs

set_option hygiene false in
/-- **The rows' memory side at the record** (`msOfAX` as in `W2R`, the
nodes' abort `ab`). -/
local notation "MSR" J:max ab:max L:max ls:max =>
  msOfAX (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (fun s _ => Spike.Lib.A64.PhRec.own (Ly) s) (Ar)
    (IN (Ar) (fun _ => none) (fun _ => 0) J) ab L ls

/-- **The start's states** at an entry state `E` and a frame condition
`FE`: `_start`'s node (`entryN`) at the program's start control (`th02`
at `meW2`, no hold) on the entry stack, no frame (`h0_ofPlaceOK`'s
start). -/
abbrev S0A (E : Entry) (FE : MachineData → Prop) : FragS isaLSE2 :=
  (Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc (entryR E) FE
    (Spike.Lib.A64.Flow.Ret0.entryN (Ly).lab
      ⟨(th02 p (meW2 (lay2 Λ p) o)).term, (th02 p (meW2 (lay2 Λ p) o)).env, none⟩)).at []

/-- **The starts at the record** (`StartsS` at `W2R`'s world, the take's
site and the nodes' abort `ab`): the start's states `S0A h E FE`, the
landings' `El`, and the pairs carrying their own segment over them. -/
abbrev StartsSA (E : Entry) (FE : MachineData → Prop)
    (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) (Dt : State → Prop)
    (ab : Option (State → Prop)) : InvS :=
  StartsS (Ar) (fun _ => none) (fun _ => 0)
    (Sg2 (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (Spike.Lib.A64.PhRec.own (Ly)) (Spike.Lib.A64.Rt.rS0 (Ly))
      (Spike.Lib.A64.PhRec.Tk (Ly)) (Ar) (fun _ => none) (fun _ => 0) Dt (Spike.Lib.A64.WriteAb.Ab (Ly).lab)
      ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL) ab) (S0A h E FE) El

/-- **The facts `rest2A_of` leaves open** at an output passing `placeOKAt`
at `lay2 Λ p` (`h`) and an entry state `E`, for the start's frame
condition `FE`, the landings' states `El`, the write tail `Dt` and the
nodes' abort `ab`. -/
structure Open2A (E : Entry) (FE : MachineData → Prop)
    (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) (Dt : State → Prop)
    (ab : Option (State → Prop)) : Prop where
  /-- The runtime's unloaded words imply the start's frame condition. -/
  hF : ∀ m, rtF (Ly) m → FE m
  /-- The start's segment inside `W2` over `IN … J`. -/
  h0 : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSA h E FE El Dt ab L ls s c fs → J L ls s c fs) →
    SegWS (W2R J Dt (fun _ => none) (fun _ => 0))
      (TakeK ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL) (Spike.Lib.A64.Rt.rS0 (Ly))) p (fun _ => none)
      (MSR J ab (fun _ => none) (fun _ => 0)) (S0A h E FE) fun _ _ _ => False
  /-- Each landing's segment, one allocation past a reachable placement,
  inside `W2` over `IN … J`. -/
  h1 : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSA h E FE El Dt ab L ls s c fs → J L ls s c fs) →
    ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
      Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
      SegWS (W2R J Dt (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n))
        (TakeK ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL) (Spike.Lib.A64.Rt.rS0 (Ly))) p
        (Spike.Lib.AllocReach.upd L l b)
        (MSR J ab (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n))
        (El L ls l b n) fun _ _ _ => False
  /-- No abort predicate, or the write abort's with the output extern
  (`printL` is then `printLD`, `hd2`). -/
  hpr : ab = none ∨
    (ab = some (Spike.Lib.A64.WriteAb.Ab (Ly).lab) ∧
      Scc.Lower.hasPrint p = true)

/-- **`Rest2A` from `Open2A`** at an admissible entry state `E` (`hE`):
the nodes, the paths and `Svc1S` by `nodes2_of_startsS`, the start facts by
`hst2_of`, `htk0_2`, `hab0_2`. -/
theorem rest2A_of {arch : WeakMem.Arch} {E : Entry} (hE : E.Ok (lay2 Λ p)) {FE : MachineData → Prop}
    {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {Dt : State → Prop}
    {ab : Option (State → Prop)} (H : Open2A h E FE El Dt ab) : Rest2A (lay2 Λ p) p h arch E := by
  obtain ⟨inv, hP, hN, hT, hA, -, h1s⟩ := nodes2_of_startsS (Q := SrcSem.srcP1o arch p) H.h0 H.h1
    (Spike.Lib.A64.PhRec.site_ofPlaceOK h _)
  refine ⟨_, _, _, _, ab, hst2_of h hE H.hF hP, hN, ?_, hT, htk0_2 h E, hA, hab0_2 h E⟩
  rcases H.hpr with hn | ⟨rfl, hx⟩
  · exact .inl hn
  · exact .inr ⟨rfl, hx, h1s⟩

/-- **`Rest2A` from the segments at the frame condition `rtF`**
(`rest2A_of` at `FE := rtF Ly`, `hF` by identity): left open, the start's and
the landings' segments (`h0`, `h1`) and `hpr`. `h0_ofPlaceOK` takes
`FE := rtF Ly` (`rtF_stable`, `rtF_takeMem` at `rS0_sub`). -/
theorem rest2A_of' {arch : WeakMem.Arch} {E : Entry} (hE : E.Ok (lay2 Λ p))
    {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {Dt : State → Prop}
    {ab : Option (State → Prop)}
    (h0 : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
        ∀ s c fs, StartsSA h E (rtF (Ly)) El Dt ab L ls s c fs → J L ls s c fs) →
      SegWS (W2R J Dt (fun _ => none) (fun _ => 0))
        (TakeK ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL) (Spike.Lib.A64.Rt.rS0 (Ly))) p (fun _ => none)
        (MSR J ab (fun _ => none) (fun _ => 0)) (S0A h E (rtF (Ly))) fun _ _ _ => False)
    (h1 : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
        ∀ s c fs, StartsSA h E (rtF (Ly)) El Dt ab L ls s c fs → J L ls s c fs) →
      ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
        Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
        SegWS (W2R J Dt (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n))
          (TakeK ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL) (Spike.Lib.A64.Rt.rS0 (Ly))) p
          (Spike.Lib.AllocReach.upd L l b)
          (MSR J ab (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n))
          (El L ls l b n) fun _ _ _ => False)
    (hpr : ab = none ∨
      (ab = some (Spike.Lib.A64.WriteAb.Ab (Ly).lab) ∧
        Scc.Lower.hasPrint p = true)) :
    Rest2A (lay2 Λ p) p h arch E :=
  rest2A_of h hE ⟨fun _ hm => hm, h0, h1, hpr⟩

end Rest

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.rest2A_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rest2A_of

/-- info: 'Spike.Lib.LowerA64.rest2A_of'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rest2A_of'

end Spike.Lib.LowerA64
