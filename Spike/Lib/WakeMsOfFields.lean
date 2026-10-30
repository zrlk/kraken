/-
**The memory-side fields of `WCompat0`/`WCompat` at `msOf`** (AArch64): the fields of main's (`WakeM0.WCompat0`) and the worker's
(`WakeW1.WCompat`) compatibility facts that only read the rows' memory side,
for a side built by the consumers' `Spike.Lib.A64Consumer.msOf`, before the
concrete sides `M`/`D` are fixed.

- `msOf_K`, `msOf_G`, `msOf_own`: the kernel model is the machine's, the
  value invariant and owned words are `msOf`'s arguments (`K0`, `G0`/`G`,
  `own0`/`own`).
- `msOf_abortAt`: `msOf`'s abort test at marks `μ'` is the program's at any
  `μ` with the same abort sites (`abortAt0`; `AbOffW.marks_target` gives
  `μ L` = the canonical target's marks).
- `sysExec_of_exe'`: at a system call the instruction faults, for an
  invariant inside the loaded executable (`sysExec0`, `SvcFault`).
- `cT_of_placed`, `cTin_of_placed`: a word `off < lsize l` of a label `l`
  the memory relation places at `b` is `wordAddr`'s word (`WCompat.cT`) and
  lies in the shared regions (`WCompat.cTin`; `.data` or the heap,
  `WakeGOf.heapData_of_placed`), given those regions inside the address
  space.
-/
import Spike.Lib.A64Consumer
import Spike.Lib.A64SvcFault
import Spike.Lib.WakeGOf

namespace Spike.Lib.WakeMsOf

open Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64Consumer (msOf Own Lbl Lsize)

variable {Λ : Scc.Sem.Layout} {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Own} {lbl : Lbl} {lsize : Lsize}

/-- (`K0`, `K`) -/
theorem msOf_K : (msOf Λ μ rd G own lbl lsize).K = some Scc.Sem.A64.abi := rfl

/-- (`G0`, `G`) -/
theorem msOf_G : (msOf Λ μ rd G own lbl lsize).G = G := rfl

/-- (`own0`, `own`) -/
theorem msOf_own (s : State) : (msOf Λ μ rd G own lbl lsize).own s = own s := rfl

/-- (`abortAt0`) at marks with `msOf`'s abort sites. -/
theorem msOf_abortAt {μ' : Scc.Sem.Marks} (hμ : μ.abortAt = μ'.abortAt) (s : State) :
    (msOf Λ μ rd G own lbl lsize).abortAt s → ∃ k a, μ'.abortAt k = some a ∧ Scc.Sem.A64.pcOf s = a := by
  rw [← hμ]; exact id

/-- (`sysExec0`) for an invariant inside the loaded executable. -/
theorem sysExec_of_exe' {ι κ : Type} {Wi : ι → isaLSE2.State → κ → Prop} {exe : _root_.Executable}
    [Kraken.Executable.ValidLayout exe] (hW : ∀ w s c, Wi w s c → s.exe = exe) :
    ∀ w s c t, Wi w s c → Scc.Sem.A64.abi.atSys s = true → isaLSE2.exec s = some t → ∃ m, t = .fault m :=
  Spike.Lib.A64.SvcFault.sysExec_of_exe hW

/-- (`WCompat.cT`) at a placed word. -/
theorem cT_of_placed {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {a : WeakMem.Address} {b : Nat} (hl : lbl a.label = some b) (ho : a.offset < lsize a.label) :
    ∃ x, Scc.Sem.wordLoc (b + 8 * a.offset) = Scc.Sem.wordLoc x ∧ Scc.Sem.wordAddr lbl a = some x ∧
      a.offset < lsize a.label :=
  ⟨_, rfl, by simp [Scc.Sem.wordAddr, hl], ho⟩

/-- (`WCompat.cTin`) at a placed word, the label regions inside the address
space. -/
theorem cTin_of_placed {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory}
    {tp tq sp : List Nat} (h : Scc.Sem.MemRelP Λ lbl lsize ts tm sm tp tq sp)
    (hsp : ∀ x, Λ.heap.contains x ∨ Λ.data.contains x → x < 2 ^ 64)
    {a : WeakMem.Address} {b : Nat} (hl : lbl a.label = some b) (ho : a.offset < lsize a.label) :
    Spike.Lib.Consumer1.LocIn Λ.shared (Scc.Sem.wordLoc (b + 8 * a.offset)) := by
  intro i hi
  have hi8 : i < 8 := by simpa [Scc.Sem.wordLoc, Scc.Sem.Kernel.locBytes] using hi
  have hin : ∀ j, j < 8 → Λ.heap.contains (b + 8 * a.offset + j) ∨ Λ.data.contains (b + 8 * a.offset + j) :=
    fun j hj => Spike.Lib.WakeGOf.heapData_of_placed h hl
      (by
        have ho' : @LT.lt Nat instLTNat a.offset (lsize a.label) := ho
        have ho'' : a.offset + 1 ≤ lsize a.label := ho'
        show b ≤ b + 8 * a.offset + j ∧ b + 8 * a.offset + j < b + 8 * lsize a.label
        omega)
  have h0 := hsp _ (hin 0 (by omega))
  have hx : (Scc.Sem.wordLoc (b + 8 * a.offset)).addr.toNat = b + 8 * a.offset := by
    simp only [Scc.Sem.wordLoc, BitVec.toNat_ofNat]; omega
  rw [hx]
  rcases hin i hi8 with hh | hd
  · exact .inr (.inl hh)
  · exact .inl hd

end Spike.Lib.WakeMsOf
