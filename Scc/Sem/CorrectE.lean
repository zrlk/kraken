/-
**Correctness at every admissible initial stack** (the release statement's
entry quantifier).

`Correct` (`Scc/Sem/Correct.lean`) is stated at one target, and the
canonical targets (`Scc.Sem.A64.canonical`, `Scc.Sem.X64.canonical`) fix
the entry state to `Entry.linux`, the oracle's fixed stack. The release
statement quantifies over it instead: `CorrectE` (per ISA,
`Scc/Sem/CorrectEA64.lean`, `Scc/Sem/CorrectEX64.lean`) is `Correct` at
`target (kernel n) E` for every entry state `E` that `Entry.Ok` admits for
the layout:

- `E.clear Λ`: the initial stack lies in the address space and is
  disjoint from every region of `Λ` and from `Λ.rodata` (the loaders
  refuse a layout failing it);
- `E.sp % 16 = 0`: the initial stack pointer is 16-aligned;
- `65536 ≤ E.stack.size`: at least 64 KiB of initial stack;
- `E.sp < 2 ^ 63`: the stack pointer is a user address.

The four conjuncts are fixed constants, not a computed need of the program.
Trusted (release note): Linux starts a static executable with its stack
pointer 16-aligned and below `2 ^ 63`, with at least 64 KiB of mapped zero
bytes below it, disjoint from the code, `.rodata` and the data regions; so
its entry state satisfies `Entry.Ok`. `Entry.Ok` admits any stack inside
`2 ^ 64` disjoint from the code, `.rodata` and the data regions, above or
below them. That the quantifier is inhabited is a separate, proved fact: a
layout ending at or below `2 ^ 32` admits the witness `⟨⟨2 ^ 32, 65536⟩⟩`
(`Entry.ok_witness`).
-/
import Scc.Sem.Target

namespace Scc.Sem

/-- **An admissible initial stack for `Λ`**: clear of the layout, its
stack pointer 16-aligned and a user address, with at least 64 KiB. -/
def Entry.Ok (E : Entry) (Λ : Layout) : Prop :=
  E.clear Λ = true ∧ E.sp % 16 = 0 ∧ 65536 ≤ E.stack.size ∧ E.sp < 2 ^ 63

instance (E : Entry) (Λ : Layout) : Decidable (E.Ok Λ) := by
  unfold Entry.Ok; infer_instance

/-- **The witness entry state**: a layout whose regions and `.rodata` all end
at or below `2 ^ 32` admits the 64 KiB stack at `2 ^ 32`. -/
theorem Entry.ok_witness {Λ : Layout} (h : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32) :
    Entry.Ok ⟨⟨2 ^ 32, 65536⟩⟩ Λ := by
  refine ⟨?_, by decide, by decide, by decide⟩
  simp only [Entry.clear, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true]
  exact ⟨by omega, fun r hr => Or.inl (h r hr)⟩

end Scc.Sem
