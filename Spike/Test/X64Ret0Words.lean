import Spike.Test.X64Ret0PlaceOK
import Spike.Lib.X64Ret0Mem

/-!
# A8 against the hand runtime words of `ret0.w` on x86-64

The runtime's data words of `ret0.w` from its placement check
(`ret0_placeOK`, component A8, `Scc/Cert/Rt/RtWordsX64.lean`), at the hand
statements of `Spike/Lib/X64Ret0Mem.lean`: the six labels in the canonical
loader's thread (`ret0_pinA` …) and the words' side conditions
(`ret0Words_entry`, `ret0Words_pool`, `ret0Words_mapped`), each re-derived by
an extraction lemma; the only decisions are of the addresses `Rt.X64.rtA`
on the link. A module of its own: the hand file's imports stay out of the
placement test's.

x86-64 has no `RuntimeLayout` record yet (AArch64's is
`Spike/Lib/Rt/A64Layout.lean`, built from the placement check by
`Spike/Lib/Rt/A64LayoutOfPlaceOK.lean`); these checks stand in for its
oracle.
-/

namespace Scc.Cert.PlaceOK.X64.Test

open Kraken Kraken.Promising.X64 SccCode
open Spike.Lib.X64.Flow.Ret0 (pinA pnA stacksA nextA lockA freeNA)
open Spike.Lib.X64.Flow.Ret0.Mem (labOf ret0Exe ret0Words)
open Spike.Lib.X64Consumer (K0)

/-- `ret0`'s runtime word `x`'s address, as A8 decides it on the link. -/
abbrev ret0A (x : String) : BitVec 64 := Rt.X64.rtA ret0Λ ret0Cells ret0Secs x

/-- **A8 at `ret0`**: a runtime word at its label in the loaded thread. -/
theorem ret0_lab {x : String} (hx : x ∈ Rt.X64.rtNames) : (labOf ret0Exe x).toBitVec = ret0A x := by
  have h := lab_link_of_placeOK ret0Imms ret0_placeOK hx Scc.Sem.Entry.linux
  dsimp only [Config.canonical] at h; exact h

/-- **A8 at `ret0`**: the words' side conditions. -/
theorem ret0_wordsOk :
    Rt.X64.wordsOk ret0Λ (ret0A "scc_rt_pinned") (ret0A "scc_rt_pinned_next") (ret0A "scc_rt_stacks")
      (ret0A "scc_rt_stack_next") (ret0A "scc_rt_stack_lock") (ret0A "scc_rt_stack_free_n") = true := by
  have h := Rt.X64.wordsOk_of_rtWordsOk (rtWordsOk_link_of_placeOK ret0Imms ret0_placeOK)
  dsimp only [Config.canonical] at h; exact h

/-! ## The labels: `ret0_pinA` … -/

example : pinA (labOf ret0Exe) = 134217728#64 := (ret0_lab (by decide)).trans (by decide +kernel)
example : pnA (labOf ret0Exe) = 6291472#64 := (ret0_lab (by decide)).trans (by decide +kernel)
example : stacksA (labOf ret0Exe) = 268435456#64 := (ret0_lab (by decide)).trans (by decide +kernel)
example : nextA (labOf ret0Exe) = 6291488#64 := (ret0_lab (by decide)).trans (by decide +kernel)
example : lockA (labOf ret0Exe) = 6291496#64 := (ret0_lab (by decide)).trans (by decide +kernel)
example : freeNA (labOf ret0Exe) = 6291504#64 := (ret0_lab (by decide)).trans (by decide +kernel)

/-! ## The words: `ret0Words_entry`, `ret0Words_pool`, `ret0Words_mapped` -/

/-- The words of A8 at `ret0` are the hand list. -/
theorem ret0_rtWords :
    Rt.X64.rtWords (ret0A "scc_rt_pinned") (ret0A "scc_rt_pinned_next") (ret0A "scc_rt_stack_next")
      (ret0A "scc_rt_stack_lock") (ret0A "scc_rt_stack_free_n") = ret0Words := by decide +kernel

example : ∀ a ∈ ret0Words,
    a.toNat + 8 ≤ Scc.Sem.Entry.linux.stack.lo ∨
      Scc.Sem.Entry.linux.stack.lo + Scc.Sem.Entry.linux.stack.size ≤ a.toNat := by
  rw [← ret0_rtWords]; exact Rt.X64.words_entry_of_wordsOk ret0_wordsOk

example : ∀ a ∈ ret0Words,
    a.toNat + 8 ≤ ret0Λ.stackPool.lo ∨ ret0Λ.stackPool.lo + ret0Λ.stackPool.size ≤ a.toNat := by
  rw [← ret0_rtWords]; exact Rt.X64.words_pool_of_wordsOk ret0_wordsOk

example {a : BitVec 64} (ha : a ∈ ret0Words) :
    Scc.Sem.Kernel.mapped (K0 ret0Λ) true ⟨a, 8⟩ = true ∧ Scc.Sem.Kernel.mapped (K0 ret0Λ) false ⟨a, 8⟩ = true ∧
      ∀ i < 8, ret0Λ.data.contains (a.toNat + i) ∨ ret0Λ.pinned.contains (a.toNat + i) := by
  rw [← ret0_rtWords] at ha
  have hm := (Rt.X64.words_mapped_of_wordsOk ret0_wordsOk a ha).2.2
  exact ⟨Spike.Lib.X64Consumer.mapped_K0_of_mem hm, Spike.Lib.X64Consumer.mapped_K0_of_mem hm, hm⟩

end Scc.Cert.PlaceOK.X64.Test
