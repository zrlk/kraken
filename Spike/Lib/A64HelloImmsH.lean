/-
**hello's root immediate table** (AArch64; the twin of `WakeFinalCAW.iW` and
`WakeImmsW.placedSE_startW` for hello): the certificate's table `SccCode.helloImms` keeps only `z`, `m` and
`two` at `helloImm_t0/t1/t2` and has no entry at the setup start's `me`; the root's table
`iH Λ0 := immsH Λ0 helloImms` adds `me` at main's control block (`tcb0`) at `setupTerm`, overriding nothing.

- `helloImms_setup_me`: the certificate's table has no entry at `setupTerm`'s `me`;
- `iH_of_ne`: off that key `iH` is the certificate's table;
- `hme_iH`: at `ofPlaceW hp (iH Λ0)` the start's `hme` (`me` at `tcb0` at `setupTerm`);
- `placedSE_c0SW`: `c0S` is `PlacedSE` at `L0T` at every state at that layout (the non-vacuity check).

Soundness of the extra entry: the table only permits immediates (`Components.env_imm`), while
`Components.env_rep` checks at every state `WordPlaceRep … (.imm n) w = ValRep lbl w n`, so a frame whose
`me` is not main's `ThreadId` box at `tcb0` fails to be placed rather than being wrongly placed
(`WakeImmsC0`'s note). `ofPlaceW hp i` accepts any `i`.
-/
import Spike.Lib.A64HelloC0S
import Spike.Lib.A64HelloCode

namespace Spike.Lib.A64.HelloPh.ImmsH

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib.WakeLoadT (L0T tcb0)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.A64.HelloPh.C0S

/-- **The root's immediate table** at the placement input `Λ0`: the certificate's `helloImms` plus `me` at
`tcb0 Λ0` at `setupTerm` (the twin of wake's `WakeFinalCAW.iW Λ0 := immsW2 Λ0 wakeImms`, which ships in the
released wake theorem). hello's final theorem fixes `i := iH Λ0` at `ofPlaceW` (root), so `hme_iH`
discharges the start's `hme`. -/
noncomputable abbrev iH (Λ0 : Scc.Sem.Layout) : Expr → String → Nat → Option Nat :=
  immsH Λ0 SccCode.helloImms

/-- **`helloImms` has no entry at the setup start's `me`**: `iH` overrides nothing. -/
theorem helloImms_setup_me : SccCode.helloImms Scc.Sem.SrcSem.setupTerm "me" 0 = none := by
  simp [SccCode.helloImms, Scc.Sem.SrcSem.setupTerm, SccCode.helloImm_t0, SccCode.helloImm_t1,
    SccCode.helloImm_t2]

/-- **Off the start's `me`, `iH` is the certificate's table.** -/
theorem iH_of_ne {Λ0 : Scc.Sem.Layout} {e : Expr} {x : String} {k : Nat}
    (h : ¬ (e = Scc.Sem.SrcSem.setupTerm ∧ x = "me" ∧ k = 0)) : iH Λ0 e x k = SccCode.helloImms e x k := by
  simp only [iH, immsH, h, ite_false]

/-- **The start's `hme` at the root's layout**: at `ofPlaceW hp (iH Λ0)`, `me` at `tcb0` at `setupTerm`. -/
theorem hme_iH {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ0 o) :
    let Λ := (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp (iH Λ0)).Λ
    Λ.imms Scc.Sem.SrcSem.setupTerm "me" 0 = some (tcb0 Λ) :=
  immsH_start Λ0 _

/-- **At the root's layout `c0S` is placed at `L0T`** at every state. -/
theorem placedSE_c0SW {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ0 o) (s : State) :
    let Λ := (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp (iH Λ0)).Λ
    PlacedSE Λ (L0T Λ) s c0S [] :=
  placedSE_c0S (hme_iH hp) s

end Spike.Lib.A64.HelloPh.ImmsH

/--
info: 'Spike.Lib.A64.HelloPh.ImmsH.helloImms_setup_me' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ImmsH.helloImms_setup_me

/-- info: 'Spike.Lib.A64.HelloPh.ImmsH.iH_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ImmsH.iH_of_ne

/-- info: 'Spike.Lib.A64.HelloPh.ImmsH.hme_iH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ImmsH.hme_iH

/-- info: 'Spike.Lib.A64.HelloPh.ImmsH.placedSE_c0SW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ImmsH.placedSE_c0SW
