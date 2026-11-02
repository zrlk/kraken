/-
**hello.w on x86-64: the store phase emits no byte** (the worker's `write` row at a frame run's end). The store phase
(`X64HelloW1.StorePh`: no frames, at the flag store, the `unpark` or `ret ()`) takes no local step
(`X64HelloW1.storePh_noStep`), and its control is not `print`'s element load (`loadCP`), so no local run from it
reaches the load, and no byte row (`X64HelloByteOutP.ByteOutP`) starts there.

- `storePh_not_loadCP`: no local run from the store phase to `loadCP pw wn m k`.
- `byteOutP_not_storePh`: no `ByteOutP` at the store phase's control.

x86-64 twin of `Spike/Lib/HelloStoreNB.lean` (same names, namespaces with the `X64` prefix).
Unlike AArch64, `ByteOutP` is `X64HelloByteOutP`'s (generic in the ISA, as on
AArch64); the proofs are the same.
-/
import Spike.Lib.X64HelloByteOutP
import Spike.Lib.X64HelloW1Print

namespace Spike.Lib.X64HelloStoreNB

open CoreLang CoreTerm
open Kraken.Promising
open Spike.Lib Spike.Lib.WorkerSrc
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloW1 (StorePh storePh_noStep localRunS_cases)
open Spike.Lib.X64HelloPrintSrcPub (loadCP)

variable {cw : TermRun.Word} {cS : WeakMem.Address} {s1 : TermRun.TTh}

/-- **No local run from the store phase reaches `print`'s element load**: the store phase takes no local
step, and its term (the store, the `unpark`, `ret ()`) is not the load's. -/
theorem storePh_not_loadCP (hS : StorePh cw s1) (hcw : cw.val = .loc cS 0) {pw wn : TermRun.Word} {m k : Nat} :
    ¬ LocalRun helloSrc (Ctl.of s1) (loadCP pw wn m k) := by
  intro hr
  rcases localRunS_cases hr.toS with he | ⟨c₁, hs⟩
  · have ht : s1.term = (loadCP pw wn m k).term := congrArg Ctl.term he
    obtain ⟨-, h | h | h, -⟩ := hS <;> rw [h] at ht <;>
      simp [loadCP, X64HelloPrintSrcPub.printLoadP, wkStore, wkUnpark] at ht
  · exact storePh_noStep hS hcw hs

/-- **No byte row at the store phase's control** (`ByteOutP`'s local run to `loadCP`). -/
theorem byteOutP_not_storePh (hS : StorePh cw s1) (hcw : cw.val = .loc cS 0) {I : ISA}
    {lbl : WeakMem.AllocLabel → Option Nat} {st : I.State} {a : Nat} {Φ : Ctl → Prop} :
    ¬ X64HelloByteOutP.ByteOutP helloSrc lbl st a (Ctl.of s1) Φ := by
  rintro ⟨pw, wn, l, b, m, k, -, -, -, hr, -⟩
  exact storePh_not_loadCP hS hcw hr

end Spike.Lib.X64HelloStoreNB

/-- info: 'Spike.Lib.X64HelloStoreNB.storePh_not_loadCP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloStoreNB.storePh_not_loadCP

/-- info: 'Spike.Lib.X64HelloStoreNB.byteOutP_not_storePh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloStoreNB.byteOutP_not_storePh
