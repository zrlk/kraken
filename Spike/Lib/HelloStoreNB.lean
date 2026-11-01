/-
**hello.w: the store phase emits no byte** (the worker's `write` row at a frame run's end). The store phase
(`HelloW1.StorePh`: no frames, at the flag store, the `unpark` or `ret ()`) takes no local step
(`HelloW1.storePh_noStep`), and its control is not `print`'s element load (`loadCP`), so no local run from it
reaches the load, and no byte row (`HelloByteOutP.ByteOutP`) starts there.

- `storePh_not_loadCP`: no local run from the store phase to `loadCP pw wn m k`.
- `byteOutP_not_storePh`: no `ByteOutP` at the store phase's control.
-/
import Spike.Lib.HelloByteOutP
import Spike.Lib.HelloW1Print

namespace Spike.Lib.HelloStoreNB

open CoreLang CoreTerm
open Kraken.Promising
open Spike.Lib Spike.Lib.WorkerSrc
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloW1 (StorePh storePh_noStep localRunS_cases)
open Spike.Lib.HelloPrintSrcPub (loadCP)

variable {cw : TermRun.Word} {cS : WeakMem.Address} {s1 : TermRun.TTh}

/-- **No local run from the store phase reaches `print`'s element load**: the store phase takes no local
step, and its term (the store, the `unpark`, `ret ()`) is not the load's. -/
theorem storePh_not_loadCP (hS : StorePh cw s1) (hcw : cw.val = .loc cS 0) {pw wn : TermRun.Word} {m k : Nat} :
    ¬ LocalRun helloSrc (Ctl.of s1) (loadCP pw wn m k) := by
  intro hr
  rcases localRunS_cases hr.toS with he | ⟨c₁, hs⟩
  · have ht : s1.term = (loadCP pw wn m k).term := congrArg Ctl.term he
    obtain ⟨-, h | h | h, -⟩ := hS <;> rw [h] at ht <;>
      simp [loadCP, HelloPrintSrcPub.printLoadP, wkStore, wkUnpark] at ht
  · exact storePh_noStep hS hcw hs

/-- **No byte row at the store phase's control** (`ByteOutP`'s local run to `loadCP`). -/
theorem byteOutP_not_storePh (hS : StorePh cw s1) (hcw : cw.val = .loc cS 0) {I : ISA}
    {lbl : WeakMem.AllocLabel → Option Nat} {st : I.State} {a : Nat} {Φ : Ctl → Prop} :
    ¬ HelloByteOutP.ByteOutP helloSrc lbl st a (Ctl.of s1) Φ := by
  rintro ⟨pw, wn, l, b, m, k, -, -, -, hr, -⟩
  exact storePh_not_loadCP hS hcw hr

end Spike.Lib.HelloStoreNB

/-- info: 'Spike.Lib.HelloStoreNB.storePh_not_loadCP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloStoreNB.storePh_not_loadCP

/-- info: 'Spike.Lib.HelloStoreNB.byteOutP_not_storePh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloStoreNB.byteOutP_not_storePh
