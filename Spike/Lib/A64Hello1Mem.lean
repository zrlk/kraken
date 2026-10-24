/-
**`hello1.w` on AArch64: the layout's memory-side facts** the main path's
instance needs (`Spike/Lib/A64Hello1I.lean`), the twin of the first half of
`Spike/Lib/A64Ret0Mem.lean`, in the canonical loader's thread
(`hello1Exe`).

- **The loaded thread** (`hello1Exe`, `hello1End`, `hello1_lays`): the
  canonical loader's thread at the Linux entry state, valid by the loader's
  checks (`hello1Λ_load`).
- **The runtime's words** (`symAt`, `hello1_pinA` …): the six data symbols'
  labels in the loaded thread, decided on its cells with the symbols placed
  by insertion sort (`hello1Cells'`, `placeSyms_eq`), as for `ret0`. They
  are at `ret0`'s addresses: `hello1`'s runtime data is `ret0`'s.
- **The words the runtime touches** (`hello1Words`): the four counters, the
  TCB's header and its six fields; the entry frame condition `hello1F` has
  each of them unmapped in `dmem`. They are clear of the entry stack and the
  stack pool, and mapped in the loaded kernel state and shared
  (`hello1Words_mapped`).

The label lemmas (`labOf`, `labelIdx`, `label_idx`) and the range check
(`clearOf`) are `Spike.Lib.A64.Flow.Ret0.Mem`'s, generic in the executable.
-/
import Spike.Lib.A64Ret0Mem
import Spike.Lib.A64Hello1Code

namespace Spike.Lib.A64.Flow.Hello1.Mem

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (pinA pnA stacksA nextA lockA freeNA)
open Spike.Lib.A64.Flow.Ret0.Mem (labOf labelIdx label_idx clearOf clearOf_iff)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64Consumer (K0)
open SccCode (hello1Λ hello1Prog hello1Secs)

/-! ## The loaded thread's labels -/

/-- **`hello1`'s loaded executable**: the canonical loader's thread at the
Linux entry state. -/
noncomputable abbrev hello1Exe : _root_.Executable :=
  (Scc.Sem.A64.threadAt Scc.Sem.Entry.linux hello1Λ.code.lo hello1Prog
    (Scc.Sem.loadSyms hello1Λ hello1Secs.rodata)).exe

/-- Its end address. -/
noncomputable abbrev hello1End : Int64 := endOf hello1Exe hello1Prog

instance : Kraken.Executable.ValidLayout hello1Exe :=
  Scc.Cert.Link.A64.validLayout_of_loadOk SccCode.hello1Λ_load _

theorem hello1_lays : Lays hello1Exe hello1Prog := Scc.Cert.Rt.A64.lays_threadAt _ _ _ _ (by decide +kernel)

/-- The loader's data symbols in address order, by insertion sort. -/
noncomputable def hello1Syms : List (String × Nat) := symSort (Scc.Sem.loadSyms hello1Λ hello1Secs.rodata)

theorem hello1Syms_perm : hello1Syms.Perm (Scc.Sem.loadSyms hello1Λ hello1Secs.rodata) := by decide +kernel

theorem hello1Syms_sorted : hello1Syms.Pairwise (fun a b => a.2 < b.2) := by decide +kernel

/-- **The loaded thread's cells**, with the data symbols placed in
`hello1Syms`' order (`Scc.Sem.placeSyms` without its `mergeSort`). -/
noncomputable def hello1Cells' : List (Directive × Nat) :=
  hello1Prog.map (fun d => (d, d.fakeSize)) ++
    placeL (Directive.byteArray (.mk #[])) Directive.label (Scc.Sem.A64.codeEnd hello1Λ.code.lo hello1Prog)
      hello1Syms

theorem hello1Exe_cells : hello1Exe.2 = hello1Cells' := by
  unfold hello1Cells'
  rw [← placeSyms_eq _ _ _ hello1Syms_perm hello1Syms_sorted]
  show (Scc.Sem.A64.threadAt _ _ _ _).exe.2 = _
  rw [Scc.Cert.Rt.A64.threadAt_exe_of_above (by decide +kernel)]

/-- **The label `l` is at `a`** in the loaded thread (decided on
`hello1Cells'`). -/
noncomputable def symAt (l : Label) (a : BitVec 64) : Bool :=
  match labelIdx hello1Cells' l with
  | some n =>
    decide (BitVec.ofNat 64 hello1Λ.code.lo + BitVec.ofNat 64 ((hello1Cells'.take n).map (·.2)).sum = a)
  | none => false

theorem lab_of_symAt {l : Label} {a : BitVec 64} (h : symAt l a = true) : (labOf hello1Exe l).toBitVec = a := by
  unfold symAt at h
  split at h
  next n hn =>
    rw [← hello1Exe_cells] at hn
    rw [label_idx hn, hello1Exe_cells]
    exact of_decide_eq_true h
  · cases h

/-- The runtime's data symbols, at their addresses (`ret0`'s). -/
def rtSyms : List (Label × BitVec 64) :=
  [("scc_rt_pinned", 134217728#64), ("scc_rt_pinned_next", 6291472#64), ("scc_rt_stacks", 268435456#64),
    ("scc_rt_stack_next", 6291488#64), ("scc_rt_stack_lock", 6291496#64), ("scc_rt_stack_free_n", 6291504#64)]

theorem rtSyms_ok : rtSyms.all (fun p => symAt p.1 p.2) = true := by decide +kernel

private theorem rtSym {l : Label} {a : BitVec 64} (h : (l, a) ∈ rtSyms) : (labOf hello1Exe l).toBitVec = a :=
  lab_of_symAt (List.all_eq_true.mp rtSyms_ok _ h)

theorem hello1_pinA : pinA (labOf hello1Exe) = 134217728#64 := rtSym (by decide)
theorem hello1_pnA : pnA (labOf hello1Exe) = 6291472#64 := rtSym (by decide)
theorem hello1_stacksA : stacksA (labOf hello1Exe) = 268435456#64 := rtSym (by decide)
theorem hello1_nextA : nextA (labOf hello1Exe) = 6291488#64 := rtSym (by decide)
theorem hello1_lockA : lockA (labOf hello1Exe) = 6291496#64 := rtSym (by decide)
theorem hello1_freeNA : freeNA (labOf hello1Exe) = 6291504#64 := rtSym (by decide)

/-! ## The words and the entry frame condition -/

/-- **The runtime words the start path touches** at `n0 = k0 = 0`: the
counters `scc_rt_pinned_next`, `scc_rt_stack_next`, `scc_rt_stack_lock`,
`scc_rt_stack_free_n`; the TCB's header at `scc_rt_pinned`; its six fields
from `scc_rt_pinned + 8` (the limit word `limA` the second). -/
def hello1Words : List (BitVec 64) :=
  [6291472#64, 6291488#64, 6291496#64, 6291504#64, 134217728#64,
    134217736#64, 134217744#64, 134217752#64, 134217760#64, 134217768#64, 134217776#64]

/-- **The entry frame condition**: every word of `hello1Words` unmapped in
the thread's private memory. -/
def hello1F (m : MachineData) : Prop := ∀ a ∈ hello1Words, Mem.loadInt m.dmem a 8 = none

theorem hello1Words_entry_ok : hello1Words.all (clearOf Scc.Sem.Entry.linux.stack) = true := by decide +kernel

theorem hello1Words_pool_ok : hello1Words.all (clearOf hello1Λ.stackPool) = true := by decide +kernel

/-- **The words are clear of the entry stack** (`Entry.linux.stack`). -/
theorem hello1Words_entry : ∀ a ∈ hello1Words,
    a.toNat + 8 ≤ Scc.Sem.Entry.linux.stack.lo ∨
      Scc.Sem.Entry.linux.stack.lo + Scc.Sem.Entry.linux.stack.size ≤ a.toNat :=
  fun a ha => clearOf_iff.mp (List.all_eq_true.mp hello1Words_entry_ok a ha)

/-- **The words are clear of the stack pool** (`hello1Λ.stackPool`). -/
theorem hello1Words_pool : ∀ a ∈ hello1Words,
    a.toNat + 8 ≤ hello1Λ.stackPool.lo ∨ hello1Λ.stackPool.lo + hello1Λ.stackPool.size ≤ a.toNat :=
  fun a ha => clearOf_iff.mp (List.all_eq_true.mp hello1Words_pool_ok a ha)

/-- The word `a` is mapped in the loaded kernel state for reading and
writing, its bytes in `data` or `pinned`. -/
noncomputable def mappedB (a : BitVec 64) : Bool :=
  Scc.Sem.Kernel.mapped (K0 hello1Λ) true ⟨a, 8⟩ && Scc.Sem.Kernel.mapped (K0 hello1Λ) false ⟨a, 8⟩ &&
    (List.range 8).all fun i =>
      decide (hello1Λ.data.contains (a.toNat + i)) || decide (hello1Λ.pinned.contains (a.toNat + i))

theorem hello1Words_mappedB : hello1Words.all mappedB = true := by decide +kernel

/-- **The words are mapped** in the loaded kernel state, for reading and
writing, and shared (in `data` or `pinned`). -/
theorem hello1Words_mapped {a : BitVec 64} (ha : a ∈ hello1Words) :
    Scc.Sem.Kernel.mapped (K0 hello1Λ) true ⟨a, 8⟩ = true ∧ Scc.Sem.Kernel.mapped (K0 hello1Λ) false ⟨a, 8⟩ = true ∧
      ∀ i < 8, hello1Λ.data.contains (a.toNat + i) ∨ hello1Λ.pinned.contains (a.toNat + i) := by
  have h := List.all_eq_true.mp hello1Words_mappedB a ha
  simp only [mappedB, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

end Spike.Lib.A64.Flow.Hello1.Mem
