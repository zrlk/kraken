/-
**A landing context's `CxLB` at a walk with no allocation** (AArch64; the
twin of `Spike/Test/X64Hello1ResI.lean`): at a walk predicate `T` holding at
no allocation's `let` in the `rodata` block (e.g. `TailAt2 p j` restricted
to `TrNb`, the points after the block's only allocation), a landings'
context `CxOkH` (`Spike/Test/A64Hello1CxOkH.lean`) has `CxLB` at a landing's
extended placement `upd L l b`, `updN ls l n` at `T` with no allocation
premise: `CxLB`'s two fields reading the walk (`hAW`, `hAb`) hold vacuously
there (`allocW2At_noNb`, `nbAb_noNb`), at the start's placement
(`setupCxLB_ofPreT`) and at the extended one (`cxLB_updT`).

- `cxLB_updT`: `CxLB` at the start's placement at a walk `T₁` moved to an
  extended placement at a walk `T₂`, the walk-reading fields given;
- `cxLBT_ofCxOkH`: a context's `CxLB` at an extended placement at a walk
  with no allocation in `rodata`;
- `hello1_cxLBT`: at `hello1o`, at `rodata`'s walk restricted to `TrNb`.
-/
import Spike.Test.A64Hello1CxOkH
import Spike.Test.A64Hello1ResL
import Spike.Lib.LowerA64.NbNone
import Spike.Lib.LowerA64.HeapW
import Spike.Lib.Rt.A64ArenaOfPlaceOK
import Spike.Lib.Rt.A64CtrZOfEmitted
import Spike.Lib.LblRangeReach
import Spike.Lib.AllocReachRoom

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Rt (rS0 arOf)
open Spike.Lib.A64.WriteAb (Ab)
open Spike.Lib.LowerNode (compiled2 TailAt2 imms2Me)
open Spike.Lib.AllocReach (Reach IN)
open Spike.Lib.A64.Flow.NewBuf (nbX)

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates (`fnCode2OfP`'s). -/
local notation "LY0" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))

set_option hygiene false in
/-- The canonical load's memory of the output. -/
local notation "M0" => Spike.Lib.A64.PhRec.m0Of (Ly).Λ OP (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).secs

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.A64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The record's marks. -/
local notation "Mk" => Spike.Lib.A64.PhRec.μ (Ly)

set_option hygiene false in
/-- `MSAt` at `Closed2AtA`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max =>
  MSAt h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- **The rows' memory side at the record** at the nodes' abort `ab2` (`H1InLandA`'s). -/
local notation "MSR" J:max L:max ls:max =>
  msOfAX (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (fun s _ => Spike.Lib.A64.PhRec.own (Ly) s) (Ar)
    (IN (Ar) (fun _ => none) (fun _ => 0) J) (ab2 p (Ly).lab) L ls

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- A context's code at the saved return address (`fnCode2OfPMe`'s). -/
local notation "CD" ra:max =>
  CdCLE OP (Spike.Lib.A64.PhRec.okPc LY0) (Spike.Lib.A64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec ra)

set_option hygiene false in
/-- The `j`th block's code facts (`ElH`'s). -/
local notation "FC" => fnCode2OfPMe hp h Λ j d hd

set_option hygiene false in
/-- **`CxLB` at the record** at a placement `L0`, `ls0` for the `j`th
compiled block's code facts at the return address `ra`, at a walk `T`. -/
local notation "CXT" J:max Dt:max L0:max ls0:max T:max =>
  CxLB (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (Spike.Lib.A64.PhRec.own (Ly)) (rS0 (Ly))
    (Spike.Lib.A64.PhRec.Tk (Ly)) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J) Dt (Ly).lab (KT) (Ly).exe
    (Ly).endPc (MSR J L0 ls0) L0 ls0 (FC).lcx (FC).cx (CD ra) ((FC).Bl ra) (imms2Me Λ p) T (RetLk d.retTy)

set_option hygiene false in
/-- **`SetupCxLB` at any walk predicate `T`** (the start's placement). -/
local notation "SXT" J:max Dt:max T:max =>
  CxLB (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (Spike.Lib.A64.PhRec.GOf Ly M0)
    (Spike.Lib.A64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly)) (arOf (Ly).Λ)
    (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) Dt (Ly).lab (KT) (Ly).exe (Ly).endPc (MSS J)
    (fun _ => none) (fun _ => 0) (FC).lcx (FC).cx (CD ra) ((FC).Bl ra) (imms2Me Λ p) T (RetLk d.retTy)

/-- **`CxLB` at the start's placement moved to an extended placement**, at
any walk predicates `T₁`, `T₂`: at a reachable placement `L`, `ls` with a
fresh label `l` the arena hands out at `b` with `n` words, a `CxLB` at no
label at `T₁` is one at `upd L l b`, `updN ls l n` at `T₂`, given the
fields reading the walk or the extended placement's allocations at `T₂`
(`hAW`, `hAb`): the frames stay placed at more labels
(`FramesPlacedInI.mono_lbl`); the labels' room, range and heap words at the
reachable extended placement (`Reach.lblRoom`, `lblRange_upd`,
`heapW_ofReach`); the rest the given `CxLB`'s. -/
theorem cxLB_updT (hp : Scc.Lower.Accepted2 p = true) {Dt : State → Prop} (J : InvS) {T₁ T₂ : Expr → Prop}
    {L : Lbl} {ls : Lsize} {l : WeakMem.AllocLabel} {b n : Nat} (hL : Reach (Ar) (fun _ => none) (fun _ => 0) L ls)
    (hl : L l = none) (hAL : Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) {R : Region} {F : MachineData → Prop}
    {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab' : FragS isaLSE2}
    (H : (SXT J Dt T₁) R F fs fp ra tp G0 Ab')
    (hAW : AllocW2At p (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n) (FC).lcx (FC).cx
      (CD ra) ((FC).Bl ra)
      (fun lbl lsize s c => W2 (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (Spike.Lib.A64.PhRec.own (Ly))
        (rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly)) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J) Dt
        (Ab (Ly).lab) lbl lsize s c fs)
      (KT) (Ly).exe (Ly).endPc R F
      ((MSR J (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n)) fs) fp ra tp G0 (imms2Me Λ p)
      T₂ (RetLk d.retTy))
    (hAb : ∀ (Jc : AS → Ctl → Prop) (pcR : Int64) s c,
      NbJcOf (imms2Me Λ p) (Spike.Lib.AllocReach.upd L l b) (FC).cx Jc →
      (∀ σ c', Jc σ c' → T₂ c'.term) →
      At (Ly).exe (Ly).endPc R F
        (nbX ((MSR J (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n)) fs)
          (_root_.Executable.labels (Ly).exe).label (Spike.Lib.AllocReach.upd L l b) R
          (FC).cx.frame pcR Jc .abort) s c → Ab' s c fs) :
    (CXT J Dt (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n) T₂) R F fs fp ra tp G0 Ab' := by
  have hR' := hL.step hl hAL
  have hsub := Spike.Lib.A64.Rt.arOf_sub h
  exact {
    hR := H.hR
    hal := H.hal
    hl := H.hl
    hh := H.hh
    hlo := H.hlo
    hhi := H.hhi
    hFS := H.hFS
    hFO := H.hFO
    hrs := H.hrs
    hfp := fun s hs => (H.hfp s hs).imp fun _ hB =>
      FramesPlacedInI.mono_lbl (fun _ _ h0 => by cases h0) hB
    hrd := by
      intro w
      generalize ab2 p _ = ab
      cases ab <;> exact fun hw => hw
    hroom := hR'.lblRoom Spike.Lib.AllocReach.lblRoom_none hsub (below32_of_placeOKAt h)
    hrg := Spike.Lib.lblRange_upd hsub (fun _ => rfl) hL hAL
    hwn := H.hwn
    hHW := heapW_ofReach h (Spike.Lib.A64.Rt.ctrZ_ofPlaceOK h) H.hwn (fun _ => rfl) hR'
    hG0F := H.hG0F
    hG0 := H.hG0
    hK := msOfAX_K_abi
    hAW := hAW
    hAb := hAb }

/-- **A landings' context's `CxLB` at an extended placement at a walk with
no allocation** (no allocation premise): at a walk `T` holding at no
allocation's `let` when the block is `rodata` (`hT`), the context's
`SetupCxLB` at `T` from its setup call's premises (`setupCxLB_ofPreT`,
the walk-reading fields vacuous: `allocW2At_noNb`, `nbAb_noNb`), moved to
the extended placement `upd L l b`, `updN ls l n` at `T` (`cxLB_updT`,
the same fields vacuous). -/
theorem cxLBT_ofCxOkH (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {Dt : State → Prop} (J : InvS) {T : Expr → Prop} {L : Lbl} {ls : Lsize} {l : WeakMem.AllocLabel} {b n : Nat}
    (hL : Reach (Ar) (fun _ => none) (fun _ => 0) L ls) (hl : L l = none)
    (hAL : Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n) {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) (hT : d.name = "rodata" → ∀ x cn τ e, ¬ T (.let_ x (.newBuf cn τ) e))
    {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64}
    {G0 : Ctl → Prop} {Ab' : FragS isaLSE2} (hc : CxOkH h hp j R F fs fp ra tp G0 Ab') :
    (CXT J Dt (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n) T) R F fs fp ra tp G0 Ab' := by
  obtain ⟨d', hd', L1, D1, fS, nS, v, g, fr, J', hn, hfS, hnS, hL0, hLm, hL8, hD18, hL1, hrow,
    ⟨hR0, hal, hF', hFF, -, -, hct, -⟩, hwn, -, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hc
  obtain rfl : d' = d := Option.some.inj (hd'.symm.trans hd)
  have hT' := hT hn
  exact cxLB_updT h hp J hL hl hAL hd
    (setupCxLB_ofPreT (T := T) h hp hty J v hfS hnS hL0 hLm hL8 hD18 hL1 hrow hd hn hR0 hal hF' hFF hct hwn
      (allocW2At_noNb hT') fun _ _ _ _ hJ hJT hA => (nbAb_noNb hT' hJ hJT hA).elim)
    (allocW2At_noNb hT') fun _ _ _ _ hJ hJT hA => (nbAb_noNb hT' hJ hJT hA).elim

end Assembled

section Hello1

open Spike.Lib.LowerNode (hello1o_accepted2)

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg (lay2 Λ Spike.Test.Hello1MainSrc.hello1o)
    (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg Spike.Test.Hello1MainSrc.hello1o)) = true)

set_option hygiene false in
/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ P1A)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates (`fnCode2OfP`'s). -/
local notation "LY0" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of P1A)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.A64.Rt.arOf (lay2 Λ P1A)

set_option hygiene false in
/-- The record's marks. -/
local notation "Mk" => Spike.Lib.A64.PhRec.μ (Ly)

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The `j`th block's code facts. -/
local notation "FC" => fnCode2OfPMe hello1o_accepted2 h Λ j d hd

/-- **`cxLBT_ofCxOkH` at `hello1o`**, at `rodata`'s walk restricted to the
points after its only allocation (`TrNb`; no allocation there:
`hello1_rodata_trNoNbT`). -/
theorem hello1_cxLBT {ty : Ty} (hty : Scc.Lower.setupOf P1A = some ty)
    {Dt : State → Prop} (J : InvS) {L : Lbl} {ls : Lsize} {l : WeakMem.AllocLabel} {b n : Nat}
    (hL : Reach (Ar) (fun _ => none) (fun _ => 0) L ls) (hl : L l = none)
    (hAL : Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n) {j : Nat} {d : Decl}
    (hd : (compiled2 P1A)[j]? = some d)
    {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64}
    {G0 : Ctl → Prop} {Ab' : FragS isaLSE2} (hc : CxOkH h hello1o_accepted2 j R F fs fp ra tp G0 Ab') :
    CxLB (lay2 Λ P1A) (Mk) P1A Spike.Lib.LowerNode.IsNum (G2 h P1A) (Spike.Lib.A64.PhRec.own (Ly)) (rS0 (Ly))
      (Spike.Lib.A64.PhRec.Tk (Ly)) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J) Dt (Ly).lab (KT) (Ly).exe
      (Ly).endPc
      (msOfAX (lay2 Λ P1A) (Mk) P1A Spike.Lib.LowerNode.IsNum (G2 h P1A)
        (fun s _ => Spike.Lib.A64.PhRec.own (Ly) s) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J) (ab2 P1A (Ly).lab)
        (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n))
      (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n) (FC).lcx (FC).cx
      (CdCLE (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg P1A)))
        (Spike.Lib.A64.PhRec.okPc LY0) (Spike.Lib.A64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec ra))
      ((FC).Bl ra) (imms2Me Λ P1A) (fun t => TailAt2 P1A j t ∧ TrNb (TailAt2 P1A j) t) (RetLk d.retTy)
      R F fs fp ra tp G0 Ab' :=
  cxLBT_ofCxOkH h hello1o_accepted2 hty J (T := fun t => TailAt2 P1A j t ∧ TrNb (TailAt2 P1A j) t) hL hl hAL hd
    (hello1_rodata_trNoNbT hd) hc

end Hello1

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.cxLB_updT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.cxLB_updT

/-- info: 'Spike.Lib.LowerA64.cxLBT_ofCxOkH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.cxLBT_ofCxOkH

/-- info: 'Spike.Lib.LowerA64.hello1_cxLBT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_cxLBT
