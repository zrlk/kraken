/-
**Main's permit word after the spawn** (AArch64): the
premise `hS` of `MainAfter.main_closed_wake` (`∀ g, Ret0.StOk ms (Fg g) exe
endPc (tp + 16#64) 0#64`, the park's store of `0` to main's permit word) at
the instance: the runtime's layout of a placed output
(`L := RuntimeLayout.ofPlaceW hp i`), the consumer's memory side `msOf` with
value invariant `wakeG (GOf2 L m0) cT` (`WakeGOf2`), any frame condition inside `rtF L`,
and `tp` the first TCB (`L.pinA + 0 + 8`), so `tp + 16` is the TCB's field
`2`, the permit word.

- `permit_eq`: `tp + 16` is `pinA + 24`, the pinned region's word `3`.
- `permit_free`: no label the memory relation places covers it (A8's
  `rtOffOk`: the word is clear of `.data` and the heap, where every placed
  label lies, `WakeGOf.heapData_of_placed`).
- `hS_ofPlaceOK`: the `StOk` (its mapping from the layout, `mp_rt`; any value
  there, off both limit words, `gOf2_ne`; unmapped under `rtF L`).
- `lim_eq`, `lim_free`, `limOk_ofPlaceOK`: the same for main's limit word
  `tp + 8` (word `2`), the wait loop's `.tls` load (`seg_waitTlsLim`'s `hL`):
  a `LimOk` with room up to any `Z ≥ stacksA + 4096` (`room_of_le`), given the
  flag `cT` is elsewhere.
-/
import Spike.Lib.WakeGOf
import Spike.Lib.WakeGOf2
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeHS

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (MemRelP lrange)
open Spike.Lib.A64.Rt (RuntimeLayout rtF mp_rt)
open Spike.Lib.A64.PhRec (GOf m0Of μ gOf_ne pin_ne)
open Spike.Lib.A64Consumer (msOf)
open Spike.Lib.WakeG (wakeG)
open Spike.Lib.WakeGOf2 (GOf2 gOf2_ne gOf_of_gOf2 pin_ne2)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64

/-- **Main's permit word** is the pinned region's word `3`. -/
theorem permit_eq (L : RuntimeLayout) : L.pinA + 0#64 + 8#64 + 16#64 = L.pinA + BitVec.ofNat 64 (8 * (2 + 1)) := by
  rw [BitVec.add_zero, BitVec.add_assoc]; rfl

/-- **Main's limit word** is the pinned region's word `2`. -/
theorem lim_eq (L : RuntimeLayout) : L.pinA + 0#64 + 8#64 + 8#64 = L.pinA + BitVec.ofNat 64 (8 * (1 + 1)) := by
  rw [BitVec.add_zero, BitVec.add_assoc]; rfl

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **No placed label covers main's permit word**: it is clear of `.data`
and the heap (A8's `rtOffOk`), where every label the memory relation places
lies. -/
theorem permit_free {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory}
    {tp tq sp : List Nat} (h : MemRelP (RuntimeLayout.ofPlaceW hp i).Λ lbl lsize ts tm sm tp tq sp) :
    ¬ ∃ l b, lbl l = some b ∧
      (lrange lsize l b).contains ((RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64 + 16#64).toNat := by
  rintro ⟨l, b, hl, hx⟩
  have hc := Scc.Cert.Rt.A64.clear_of_rtOffOk (PlaceW.rtOff_of_placeW hp) (j := 3) (by decide)
  have hw := (PlaceW.wf_link_of_placeW i hp).inSpace
  have hd := hw _ (by simp [Scc.Sem.Layout.regions] :
    (RuntimeLayout.ofPlaceW hp i).Λ.data ∈ (RuntimeLayout.ofPlaceW hp i).Λ.regions)
  have hh := hw _ (by simp [Scc.Sem.Layout.regions] :
    (RuntimeLayout.ofPlaceW hp i).Λ.heap ∈ (RuntimeLayout.ofPlaceW hp i).Λ.regions)
  change Scc.Cert.Rt.A64.clearB (RuntimeLayout.ofPlaceW hp i).Λ.data
      ((RuntimeLayout.ofPlaceW hp i).pinA + BitVec.ofNat 64 (8 * (2 + 1))) = true ∧
    Scc.Cert.Rt.A64.clearB (RuntimeLayout.ofPlaceW hp i).Λ.heap
      ((RuntimeLayout.ofPlaceW hp i).pinA + BitVec.ofNat 64 (8 * (2 + 1))) = true at hc
  rw [permit_eq] at hx
  have hm := (RuntimeLayout.ofPlaceW hp i).words_small _ ((RuntimeLayout.ofPlaceW hp i).fld_mem (i := 2) (by decide))
  have hs := Spike.Lib.WakeGOf.heapData_of_placed h hl hx
  simp only [Scc.Cert.Rt.A64.clearB, Bool.or_eq_true, decide_eq_true_eq] at hc
  simp only [Scc.Sem.Range.contains] at hs
  omega

/-- **`main_closed_wake`'s `hS` at the instance**: the park's store of
`0` to main's permit word `tp + 16` (`tp` the first TCB) is a runtime store
under `msOf` at `wakeG (GOf2 L m0) cT`, for any frame condition inside
`rtF L`. -/
theorem hS_ofPlaceOK {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory}
    {tp tq sp : List Nat} (h : MemRelP (RuntimeLayout.ofPlaceW hp i).Λ lbl lsize ts tm sm tp tq sp)
    {rd : TermRun.Word → Prop} {own : Spike.Lib.A64Consumer.Own} {cT : Loc}
    {F : MachineData → Prop} (hF : ∀ m, F m → rtF (RuntimeLayout.ofPlaceW hp i) m)
    {exe : _root_.Executable} {endPc : Int64} :
    Spike.Lib.A64.Flow.Ret0.StOk
      (msOf (RuntimeLayout.ofPlaceW hp i).Λ (μ (RuntimeLayout.ofPlaceW hp i)) rd
        (wakeG (GOf2 (RuntimeLayout.ofPlaceW hp i) (m0Of (RuntimeLayout.ofPlaceW hp i).Λ o.prog o.secs)) cT)
        own lbl lsize)
      F exe endPc ((RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64 + 16#64) 0#64 := by
  have ha : (RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64 + 16#64 ∈ (RuntimeLayout.ofPlaceW hp i).rtWords := by
    rw [permit_eq]; exact (RuntimeLayout.ofPlaceW hp i).fld_mem (by decide)
  refine ⟨permit_free hp i h, mp_rt ha true, .inr ?_, fun m hm => hF m hm _ ha⟩
  rw [permit_eq]
  exact gOf2_ne (pin_ne (by decide)) (pin_ne2 (by decide)) _

/-- **No placed label covers main's limit word** `tp + 8` (the pinned
region's word `2`), as `permit_free`. -/
theorem lim_free {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory}
    {tp tq sp : List Nat} (h : MemRelP (RuntimeLayout.ofPlaceW hp i).Λ lbl lsize ts tm sm tp tq sp) :
    ¬ ∃ l b, lbl l = some b ∧
      (lrange lsize l b).contains ((RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64 + 8#64).toNat := by
  rintro ⟨l, b, hl, hx⟩
  have hc := Scc.Cert.Rt.A64.clear_of_rtOffOk (PlaceW.rtOff_of_placeW hp) (j := 2) (by decide)
  have hw := (PlaceW.wf_link_of_placeW i hp).inSpace
  have hd := hw _ (by simp [Scc.Sem.Layout.regions] :
    (RuntimeLayout.ofPlaceW hp i).Λ.data ∈ (RuntimeLayout.ofPlaceW hp i).Λ.regions)
  have hh := hw _ (by simp [Scc.Sem.Layout.regions] :
    (RuntimeLayout.ofPlaceW hp i).Λ.heap ∈ (RuntimeLayout.ofPlaceW hp i).Λ.regions)
  change Scc.Cert.Rt.A64.clearB (RuntimeLayout.ofPlaceW hp i).Λ.data
      ((RuntimeLayout.ofPlaceW hp i).pinA + BitVec.ofNat 64 (8 * (1 + 1))) = true ∧
    Scc.Cert.Rt.A64.clearB (RuntimeLayout.ofPlaceW hp i).Λ.heap
      ((RuntimeLayout.ofPlaceW hp i).pinA + BitVec.ofNat 64 (8 * (1 + 1))) = true at hc
  rw [lim_eq] at hx
  have hm := (RuntimeLayout.ofPlaceW hp i).words_small _ ((RuntimeLayout.ofPlaceW hp i).fld_mem (i := 1) (by decide))
  have hs := Spike.Lib.WakeGOf.heapData_of_placed h hl hx
  simp only [Scc.Cert.Rt.A64.clearB, Bool.or_eq_true, decide_eq_true_eq] at hc
  simp only [Scc.Sem.Range.contains] at hs
  omega

/-- **`seg_waitTlsLim`'s `hL` at the instance**: the wait loop's load of
main's limit word `tp + 8` is a limit load under `msOf` at
`wakeG (GOf2 L m0) cT` (the flag `cT` elsewhere), with room up to any `Z`
at least the limit (`stacksA + 4096`, A8's `rtInitOk` plus
`scc_rt_thread_init`'s store), for any frame condition inside `rtF L`. -/
theorem limOk_ofPlaceOK {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory}
    {tp tq sp : List Nat} (h : MemRelP (RuntimeLayout.ofPlaceW hp i).Λ lbl lsize ts tm sm tp tq sp)
    {rd : TermRun.Word → Prop} {own : Spike.Lib.A64Consumer.Own} {cT : Loc}
    (hcT : (⟨(RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64 + 8#64, 8⟩ : Loc) ≠ cT)
    {F : MachineData → Prop} (hF : ∀ m, F m → rtF (RuntimeLayout.ofPlaceW hp i) m)
    {exe : _root_.Executable} {endPc : Int64} {Z : BitVec 64}
    (hZ : (RuntimeLayout.ofPlaceW hp i).stacksA.toNat + 4096 ≤ Z.toNat) :
    Spike.Lib.A64.Flow.Ret0.LimOk
      (msOf (RuntimeLayout.ofPlaceW hp i).Λ (μ (RuntimeLayout.ofPlaceW hp i)) rd
        (wakeG (GOf2 (RuntimeLayout.ofPlaceW hp i) (m0Of (RuntimeLayout.ofPlaceW hp i).Λ o.prog o.secs)) cT)
        own lbl lsize)
      F exe endPc ((RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64 + 8#64) Z := by
  have ha : (RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64 + 8#64 ∈ (RuntimeLayout.ofPlaceW hp i).rtWords := by
    rw [lim_eq]; exact (RuntimeLayout.ofPlaceW hp i).fld_mem (by decide)
  refine ⟨lim_free hp i h, mp_rt ha false, fun m hm => hF m hm _ ha, fun v hv => ?_⟩
  have hg := Spike.Lib.WakeG.wakeG_off hv hcT
  rw [lim_eq, ← Spike.Lib.A64.Rt.limA_tcb0] at hg
  exact PlaceW.room_of_le hp i hZ v (gOf_of_gOf2 hg)

end Place

/-- info: 'Spike.Lib.WakeHS.hS_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hS_ofPlaceOK

/-- info: 'Spike.Lib.WakeHS.limOk_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms limOk_ofPlaceOK

end Spike.Lib.WakeHS
