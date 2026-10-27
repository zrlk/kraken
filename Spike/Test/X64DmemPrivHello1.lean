/-
**`privInv_load` at `hello1.w`** (x86-64; a non-vacuity regression of
`Spike/Lib/X64DmemPriv.lean`): the invariant `PrivInv` holds when
`hello1Cells` is loaded at its static link `hello1Λ` with the Linux entry,
for any symbol table and initial memory, and so along every run of the
canonical machine; so no thread of any reachable configuration maps a
byte of `hello1Λ`'s heap or static image (`PrivKeys.not_mem`), and none
loads a word of them (`PrivKeys.wordsNone`).

Both premises are discharged: `WideSt` from `hello1_wide`
(`wideSt_threadAt`), `Entry.linux.clear hello1Λ` by kernel decision.
-/
import Spike.Lib.X64DmemPrivPlace
import Spike.Lib.X64Hello1Code

namespace Spike.Test.X64DmemPrivHello1

open Kraken Kraken.Promising Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64 Spike.Lib.DmemPriv
  Spike.Lib.X64DmemPriv SccCode

/-- The Linux entry is clear of `hello1Λ`. -/
theorem hello1_clear : Entry.linux.clear hello1Λ = true := by decide +kernel

/-- **`PrivInv` at `hello1`'s load.** -/
theorem hello1_privInv_load (n : Nat) (syms : List (String × Nat)) (mem : List (Loc × Val)) :
    PrivInv abi WideSt hello1Λ Entry.linux (loadProg (kernel n) Entry.linux hello1Λ hello1Cells syms mem) :=
  privInv_load (wideSt_threadAt hello1_wide _ _ _) hello1_clear

/-- **Along every run from `hello1`'s load**, no thread maps a byte of the
heap or the static image. -/
theorem hello1_not_mem {n : Nat} {μ : Marks} (syms : List (String × Nat)) (mem : List (Loc × Val))
    {tr : List Ev} {c : (machine (kernel n)).Cfg}
    (h : (machine (kernel n)).Run μ (loadProg (kernel n) Entry.linux hello1Λ hello1Cells syms mem) tr c)
    {tid : Nat} {t : Thread Kraken.Promising.X64.isa} (ht : c.1.threads[tid]? = some t) {a : BitVec 64}
    (ha : hello1Λ.heap.contains a.toNat ∨ hello1Λ.data.contains a.toNat) : a ∉ abi.dmem t.st :=
  ((privInv_run (hello1_privInv_load n syms mem) h).dmemPriv tid t ht).not_mem hello1Λ_wf hello1_clear ha

/-- **Along every run from `hello1`'s load**, no thread's memory loads a
word of the heap or the static image: the frames' `WordsNone` of
`Spike/Lib/X64Hello1SetupPriv.lean` (`hwn`). -/
theorem hello1_wordsNone {n : Nat} {μ : Marks} (syms : List (String × Nat)) (mem : List (Loc × Val))
    {tr : List Ev} {c : (machine (kernel n)).Cfg}
    (h : (machine (kernel n)).Run μ (loadProg (kernel n) Entry.linux hello1Λ hello1Cells syms mem) tr c)
    {tid : Nat} {t : Thread Kraken.Promising.X64.isa} (ht : c.1.threads[tid]? = some t) :
    WordsNone hello1Λ (abi.dmem t.st) :=
  wordsNone_run_of_wide (mem := mem) hello1_wide hello1Λ_wf hello1_clear h ht

end Spike.Test.X64DmemPrivHello1
