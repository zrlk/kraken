/-
**The setup frame's segment `SetupOpen.hs` from `CxLB`** (x86-64; the twin
of `Spike/Test/A64Hello1HsOf.lean`): `fnSpecC2_ofCxLBMe`
(`Spike/Lib/LowerX64/CxLBP.lean`) at the setup frame's world (`W2At …
(imms2Me Λ p)` with `IsNum`, `MSAt`, the take `KT`), the contexts with their
stack records `CxOkS … CxOk0 (SB …) j` at the setup frame's bottom keys. The
stack's range (`rS0_sub`) and `ProgNoS` come from the layout and
`Accepted2`; left are the allocator's code (`hA`), the setup block's points
(no call, `hnc`; one-word elements, `hTn`) and at each base context
`CxOk0 j` with the return address in `RaOk` the facts `CxLB` in the rebased
region `rbR R` (`hcx`) at the block's lowering context, frame, code and
calls.

- `setupHs_ofCxLB`: `SetupOpen.hs` from `hA`, `hnc`, `hTn`, `hcx`.
- `SetupCxLB`, `setupHs_ofCxLB0`: the base context `CxLB` itself, at which
  `hs` needs only `hA`, `hnc`, `hTn` (and `SetupOpen.hcx` is `CxLB` at the
  setup frame).
- at `hello1o`: `hello1_allocIn` (`hA`), `hello1_rodata_elem2` (`hTn`);
  `hnc` is `hello1_rodata_noCall` (`Spike/Test/X64Hello1NoCall.lean`), so
  only `hcx` is left.
-/
import Spike.Lib.LowerX64.CxLBP
import Spike.Test.X64Hello1HS

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Rt (setupMC rS0 arOf)
open Spike.Lib.LowerNode (ZBad setupWords2 compiled2 TailAt2 imms2Me)
open Spike.Lib.AllocReach (IN)

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates (`fnCode2OfP`'s). -/
local notation "LY0" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)

set_option hygiene false in
/-- The canonical load's memory of the output. -/
local notation "M0" => Spike.Lib.X64.PhRec.m0Of (Ly).Λ OP
  (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).secs

set_option hygiene false in
/-- `W2At` at `Closed2At`'s instance. -/
local notation "W2S" J:max => W2At h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum (rS0 (Ly)) J Dt (fun _ => 0)

set_option hygiene false in
/-- `MSAt` at `Closed2At`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max =>
  MSAt h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

/-- **`SetupOpen.hs` from `CxLB`** (`fnSpecC2_ofCxLBMe` at the setup
frame's world): the `j`th compiled block `d`, none of its body's points a
call (`hnc`), its allocations' elements one word (`hTn`), the allocator's
code placed (`hA`); at every base context `CxOk0 j` with the return
address in `fnCode2OfPMe`'s `RaOk`, the facts `CxLB` at the setup frame's
world in the rebased region `rbR R` (`hcx`). The bottom keys `Bot` are any
(`SetupOpen`'s `SB …`). -/
theorem setupHs_ofCxLB (hp : Scc.Lower.Accepted2 p = true) {Dt : State → Prop} (J : InvS)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    (CxOk0 : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop) (Bot : StkKey → List TermRun.Frame → Prop)
    (hA : Spike.Lib.X64.Alloc.allocIn OP = true)
    (hnc : (tailsL d.body).all (fun t => !isCallLet t) = true)
    (hTn : ∀ x cn τ e, TailAt2 p j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    (hcx : ∀ R F fs fp ra tp G0 Ab, CxOk0 j R F fs fp ra tp G0 Ab →
      Spike.Lib.X64.PhRec.ph LY0 (Int64.ofBitVec ra).toBitVec.toNat =
        Spike.Lib.X64.PhRec.ph LY0 ((LY0).lab raL).toBitVec.toNat →
      CxLB (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (Spike.Lib.X64.PhRec.GOf Ly M0)
        (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly)) (arOf (Ly).Λ)
        (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) Dt (Ly).lab (KT) (Ly).exe (Ly).endPc (MSS J)
        (fun _ => none) (fun _ => 0) (fnCode2OfPMe hp h Λ j d hd).lcx (fnCode2OfPMe hp h Λ j d hd).fr
        (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec ra))
        ((fnCode2OfPMe hp h Λ j d hd).Bl ra) (imms2Me Λ p) (TailAt2 p j) (RetLk d.retTy)
        (rbR R) F fs fp ra tp G0 Ab) :
    FnSpecC2 (W2S J) (KT) p (fun _ => none) (fun _ => 0) (MSS J)
      (CxOkS (p := p) (lbl := fun _ => none) (lsize := fun _ => 0) (fnCode2OfPMe hp h Λ) CxOk0 Bot j)
      (fnCode2OfPMe hp h Λ j d hd) :=
  fnSpecC2_ofCxLBMe hp h Λ hd hA (Spike.Lib.X64.Rt.rS0_sub _)
    (Spike.Lib.X64.Rt.fitS_of_sub _ (Spike.Lib.X64.Rt.rS0_sub _)) (Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp)
    hnc hTn fun R F fs fp ra tp G0 Ab hc hra => hcx R F fs fp ra tp G0 Ab hc.cx hra

/-- **The base context `CxLB` at the setup frame's world**: at any key, the
facts `CxLB` in the rebased region at the `j`th compiled block's lowering
context, frame, code and calls (`setupHs_ofCxLB`'s `hcx`'s conclusion as a
base context; the block index argument ignored, the setup frame's records
being at the bottom). -/
def SetupCxLB (hp : Scc.Lower.Accepted2 p = true) (Dt : State → Prop) (J : InvS) {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) (_ : Nat) (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame)
    (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop) (Ab : FragS isa) : Prop :=
  CxLB (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (Spike.Lib.X64.PhRec.GOf Ly M0)
    (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly)) (arOf (Ly).Λ)
    (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) Dt (Ly).lab (KT) (Ly).exe (Ly).endPc (MSS J)
    (fun _ => none) (fun _ => 0) (fnCode2OfPMe hp h Λ j d hd).lcx (fnCode2OfPMe hp h Λ j d hd).fr
    (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec ra))
    ((fnCode2OfPMe hp h Λ j d hd).Bl ra) (imms2Me Λ p) (TailAt2 p j) (RetLk d.retTy)
    (rbR R) F fs fp ra tp G0 Ab

/-- **`SetupOpen.hs` at the base context `SetupCxLB`** (`setupHs_ofCxLB`
with `hcx` by definition): `SetupOpen … (SetupCxLB …)`'s `hs` from the
allocator's code and the block's points; its `hcx` is then `CxLB` at the
setup frame. -/
theorem setupHs_ofCxLB0 (hp : Scc.Lower.Accepted2 p = true) {Dt : State → Prop} (J : InvS)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) (Bot : StkKey → List TermRun.Frame → Prop)
    (hA : Spike.Lib.X64.Alloc.allocIn OP = true)
    (hnc : (tailsL d.body).all (fun t => !isCallLet t) = true)
    (hTn : ∀ x cn τ e, TailAt2 p j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true) :
    FnSpecC2 (W2S J) (KT) p (fun _ => none) (fun _ => 0) (MSS J)
      (CxOkS (p := p) (lbl := fun _ => none) (lsize := fun _ => 0) (fnCode2OfPMe hp h Λ)
        (SetupCxLB h hp Dt J hd) Bot j)
      (fnCode2OfPMe hp h Λ j d hd) :=
  setupHs_ofCxLB h hp J hd _ Bot hA hnc hTn fun _ _ _ _ _ _ _ _ hc _ => hc

end Assembled

/-- The program. -/
local notation "P1" => Spike.Test.Hello1MainSrc.hello1o

/-- **`hello1o`'s output holds the allocator's code** (`setupHs_ofCxLB`'s
`hA`), at every choice of the instructions' sizes and label offsets
(`allocIn_of_placeOKAt` at a placed output). -/
theorem hello1_allocIn {sizes : List Nat} {labelOffs : List (String × Nat)}
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1) sizes labelOffs) = true) :
    Spike.Lib.X64.Alloc.allocIn
      (Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1) sizes labelOffs)) = true :=
  allocIn_of_placeOKAt h

/-- **`rodata`'s allocations have one-word elements** in `hello1o`
(`setupHs_ofCxLB`'s `hTn`). -/
theorem hello1_rodata_elem2 {j : Nat} {d : Decl} (hd : (compiled2 P1)[j]? = some d) (hn : d.name = "rodata") :
    ∀ x cn τ e, TailAt2 P1 j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true := by
  have hc : ∀ d ∈ compiled2 P1, d.name = "rodata" → (tailsL d.body).all (fun t => match t with
      | .let_ _ (.newBuf _ τ) _ => Scc.Lower.elem2 τ
      | _ => true) = true := by
    decide
  intro x cn τ e ht
  simpa using List.all_eq_true.mp (hc d (List.mem_of_getElem? hd) hn) _ (tailOf_mem_tailsL (ht d hd))

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.setupHs_ofCxLB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms setupHs_ofCxLB

/-- info: 'Spike.Lib.LowerX64.setupHs_ofCxLB0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms setupHs_ofCxLB0

/-- info: 'Spike.Lib.LowerX64.hello1_allocIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_allocIn

/-- info: 'Spike.Lib.LowerX64.hello1_rodata_elem2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hello1_rodata_elem2

end Spike.Lib.LowerX64
