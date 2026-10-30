/-
**wake's flag word is free in the consumer's value invariant**: the premise `hc` of `WakeG.wakeG_iff` at `G0 = GOf Ly m0`
(`Spike/Lib/A64StartOfPlaceOK.lean`), so `wakeG (GOf Ly m0) cT = GOf Ly m0`.

- `heapData_of_placed`: a word inside a label placed by the memory relation
  (`MemRelP.lbl_range`) lies in the heap or `.data`.
- `gOf_placed`: any value-invariant `G0` holding of any value at the heap's
  and `.data`'s words (`hGpl`) holds of any value at a placed word.
- `gOf_cT_ofPlaceOK`: at `RuntimeLayout.ofPlaceW`, `hGpl` is
  `hGpl_ofPlaceOK` (A8's `rtOffOk`: the limit word is clear of the heap and
  `.data`), so `GOf Ly m0` holds of any value at a placed word; no fact about
  the pinned region is needed.
-/
import Spike.Lib.A64StartOfPlaceOK
import Scc.Sem.MemRelP
import Spike.Lib.WakeG
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeGOf

open Kraken Kraken.Promising
open Scc.Sem (MemRelP lrange)

/-- **A placed word lies in the heap or `.data`** (`MemRelP.lbl_range`). -/
theorem heapData_of_placed {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory}
    {tp tq sp : List Nat} (h : MemRelP Λ lbl lsize ts tm sm tp tq sp) {l : WeakMem.AllocLabel} {b x : Nat}
    (hl : lbl l = some b) (hx : (lrange lsize l b).contains x) : Λ.heap.contains x ∨ Λ.data.contains x := by
  have hs := (h.lbl_range l b hl).2
  simp only [lrange, Scc.Sem.Range.contains] at hx
  simp only [Scc.Sem.Range.contains]
  rcases hs with hs | hs | ⟨h0, -⟩
  · simp only [lrange, Scc.Sem.Range.Sub] at hs
    exact .inl ⟨by omega, by omega⟩
  · simp only [lrange, Scc.Sem.Range.Sub] at hs
    exact .inr ⟨by omega, by omega⟩
  · omega

/-- **Any value at a placed word**, from any value at the heap's and
`.data`'s words. -/
theorem gOf_placed {Λ : Scc.Sem.Layout} {G0 : Loc → Val → Prop}
    (hpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G0 (Scc.Sem.wordLoc a) v)
    {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory}
    {tp tq sp : List Nat} (h : MemRelP Λ lbl lsize ts tm sm tp tq sp) {l : WeakMem.AllocLabel} {b x : Nat}
    (hl : lbl l = some b) (hx : (lrange lsize l b).contains x) (v : Val) : G0 (Scc.Sem.wordLoc x) v :=
  hpl x v (heapData_of_placed h hl hx)

open Spike.Lib.A64.PhRec in
/-- **`GOf` at `ofPlaceOK` holds of any value at a placed word**
(`WakeG.wakeG_iff`'s `hc` at the flag's word `cT = wordLoc x`). -/
theorem gOf_cT_ofPlaceOK {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out}
    {Λ : Scc.Sem.Layout} (hp : PlaceW pcfg Λ o)
    (i : CoreTerm.Expr → String → Nat → Option Nat)
    {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory}
    {tp tq sp : List Nat}
    (h : MemRelP (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp i).Λ lbl lsize ts tm sm tp tq sp)
    {l : WeakMem.AllocLabel} {b x : Nat}
    (hl : lbl l = some b) (hx : (lrange lsize l b).contains x) (v : Val) :
    GOf (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp i)
      (m0Of (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp i).Λ o.prog o.secs) (Scc.Sem.wordLoc x) v :=
  gOf_placed (PlaceW.hGpl_ofPlaceW hp i) h hl hx v

/-- **`wakeG` is `GOf`** at `ofPlaceOK` with the flag at a placed word. -/
theorem wakeG_gOf_ofPlaceOK {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out}
    {Λ : Scc.Sem.Layout} (hp : PlaceW pcfg Λ o)
    (i : CoreTerm.Expr → String → Nat → Option Nat)
    {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory}
    {tp tq sp : List Nat}
    (h : MemRelP (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp i).Λ lbl lsize ts tm sm tp tq sp)
    {l : WeakMem.AllocLabel} {b x : Nat}
    (hl : lbl l = some b) (hx : (lrange lsize l b).contains x) {L : Loc} {v : Val} :
    Spike.Lib.WakeG.wakeG (Spike.Lib.A64.PhRec.GOf (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp i)
        (Spike.Lib.A64.PhRec.m0Of (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp i).Λ o.prog o.secs))
        (Scc.Sem.wordLoc x) L v ↔
      Spike.Lib.A64.PhRec.GOf (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp i)
        (Spike.Lib.A64.PhRec.m0Of (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp i).Λ o.prog o.secs) L v :=
  Spike.Lib.WakeG.wakeG_iff (gOf_cT_ofPlaceOK hp i h hl hx)

/-- info: 'Spike.Lib.WakeGOf.wakeG_gOf_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wakeG_gOf_ofPlaceOK

end Spike.Lib.WakeGOf
