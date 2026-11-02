/-
**wake's flag word is free in the consumer's value invariant**: the premise `hc` of
`WakeG.wakeG_iff` at `G0 = GOf Ly m0`
(`Spike/Lib/X64StartOfPlaceOK.lean`), so `wakeG (GOf Ly m0) cT = GOf Ly m0`.

- `heapData_of_placed`: a word inside a label placed by the memory relation
  (`MemRelP.lbl_range`) lies in the heap or `.data`.
- `gOf_placed`: any value-invariant `G0` holding of any value at the heap's
  and `.data`'s words (`hGpl`) holds of any value at a placed word.
- `gOf_cT_ofPlaceOK`: at `RuntimeLayout.ofPlaceWX`, `hGpl` is
  `hGpl_ofPlaceOK` (A8's `rtOffOk`: the limit word is clear of the heap and
  `.data`), so `GOf Ly m0` holds of any value at a placed word; no fact about
  the pinned region is needed.

x86-64 twin of `Spike/Lib/WakeGOf.lean` (same names, namespaces with the
`X64` prefix).
-/
import Spike.Lib.X64StartOfPlaceOK
import Scc.Sem.MemRelP
import Spike.Lib.WakeG
import Spike.Lib.X64PlaceWRt

namespace Spike.Lib.X64WakeGOf

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

open Spike.Lib.X64.PhRec in
/-- **`GOf` at `ofPlaceOK` holds of any value at a placed word**
(`WakeG.wakeG_iff`'s `hc` at the flag's word `cT = wordLoc x`). -/
theorem gOf_cT_ofPlaceOK {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out}
    {Λ : Scc.Sem.Layout} (hp : PlaceWX pcfg Λ o)
    (i : CoreTerm.Expr → String → Nat → Option Nat)
    {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory}
    {tp tq sp : List Nat}
    (h : MemRelP (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i).Λ lbl lsize ts tm sm tp tq sp)
    {l : WeakMem.AllocLabel} {b x : Nat}
    (hl : lbl l = some b) (hx : (lrange lsize l b).contains x) (v : Val) :
    GOf (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i)
      (m0Of (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i).Λ o.prog o.secs) (Scc.Sem.wordLoc x) v :=
  gOf_placed (Spike.Lib.PlaceWX.hGpl_ofPlaceWX hp i) h hl hx v

/-- **`wakeG` is `GOf`** at `ofPlaceOK` with the flag at a placed word. -/
theorem wakeG_gOf_ofPlaceOK {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out}
    {Λ : Scc.Sem.Layout} (hp : PlaceWX pcfg Λ o)
    (i : CoreTerm.Expr → String → Nat → Option Nat)
    {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory}
    {tp tq sp : List Nat}
    (h : MemRelP (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i).Λ lbl lsize ts tm sm tp tq sp)
    {l : WeakMem.AllocLabel} {b x : Nat}
    (hl : lbl l = some b) (hx : (lrange lsize l b).contains x) {L : Loc} {v : Val} :
    Spike.Lib.WakeG.wakeG (Spike.Lib.X64.PhRec.GOf (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i)
        (Spike.Lib.X64.PhRec.m0Of (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i).Λ o.prog o.secs))
        (Scc.Sem.wordLoc x) L v ↔
      Spike.Lib.X64.PhRec.GOf (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i)
        (Spike.Lib.X64.PhRec.m0Of (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i).Λ o.prog o.secs) L v :=
  Spike.Lib.WakeG.wakeG_iff (gOf_cT_ofPlaceOK hp i h hl hx)

/-- info: 'Spike.Lib.X64WakeGOf.wakeG_gOf_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wakeG_gOf_ofPlaceOK

end Spike.Lib.X64WakeGOf
