/-
**The x64 instruction forms a WeakCore lowering may emit, as one decidable
predicate.**

Kraken has no x64 counterpart of AArch64's `Program.WCLowerable`
(`Kraken/Promising/Lower/Lowerable.lean`): none of its clauses 1–5 has an x64
instance (every locked RMW is `acqRel`, the x64 adapter passes
`noRet = false`, there is no RCpc load, a locked `cmpxchg16b` is one 16-byte
event), and clause 6 is not encoded for x64. This module states the x64
conventions a lowering must follow, on Kraken's x64 syntax, for `scc`'s x64
output; it lives in `Scc`, not in Kraken.

1. **L (locked RMW).** A WeakCore RMW lowers to a locked x64 RMW: no unlocked
   `xadd`, `cmpxchg` or `cmpxchg16b` with a memory destination (unlocked, they
   are a separate load and store to the memory model, not one atomic step).
   `xchg` with a memory operand is locked whether or not the prefix is
   written, and the `lockBin`/`lockUn` forms are locked by construction, so
   they are allowed.
2. **N (no non-temporal stores).** No `movnti`: it is a weakly ordered store
   (ordered only by fences, locked instructions and per-location coherence),
   weaker than any store WeakCore has.

Everything else is allowed (ALU, `div`/`idiv`/`cqo`/`popcnt`, branches,
calls, plain loads and stores of any width, the `%fs:` moves `movfs` (a plain
load or store), `syscall` and `ud2` (halts with no memory event), `nop`,
`mfence`/`lfence`/`sfence`, the AVX moves); labels and byte arrays are
lowerable. None of these is an RMW.

**Obligation S (sub-word stores to owned cells), not checked here.** The
x64 emitter writes 8- and 16-bit values with `movb`/`movw` to memory
(AArch64's clause 6 forbids the analogous `strb`/`strh`). That is sound only
under the hypothesis, named here for the later simulation proof,

  `SubWordOwned`: every 8- or 16-bit memory write of the program targets a
  cell that no other thread writes,

which is the same ownership invariant the AArch64 emitter's lane stores rely
on (WeakCore's only sub-word store is a lane store into the writer's own
buffer, `WeakCore/SubWord.lean`). It is a property of the lowering, not of
the instruction syntax, so it is not a clause of the decidable predicate.

The predicates are `Bool` functions with `= true`, so
`ProgramWCLowerable p` is decided by `decide +kernel` on a concrete program
(`Scc/Emit/X64Test.lean`, and the certificates of `Scc/Cert/`).
-/
import Kraken.X64.Syntax

namespace Scc.Emit.X64

/-- An operation a WeakCore lowering may emit (clauses L and N). -/
def opWCLowerableB {w : _root_.Width} : Operation w → Bool
  -- (L) an RMW with a memory destination is locked
  | .xadd lock (.mem _) _ => lock
  | .cmpxchg lock (.mem _) _ => lock
  -- (N) no non-temporal store
  | .movnti .. => false
  | _ => true

/-- A vector or 16-byte operation a WeakCore lowering may emit (clause L). -/
def avxOpWCLowerableB {w : AvxWidth} : AvxOperation w → Bool
  | .cmpxchg16b lock _ => lock
  | _ => true

/-- **`instrWCLowerableB i`: `i` is a form a WeakCore lowering may emit on
x64** (clauses L and N of the module docstring). -/
def instrWCLowerableB : Instr → Bool
  | .regular _ _ op => opWCLowerableB op
  | .avx _ _ op => avxOpWCLowerableB op

/-- A cell's lowerability: an instruction's; labels and byte arrays are
lowerable. -/
def directiveWCLowerableB : Directive → Bool
  | .instr i => instrWCLowerableB i
  | _ => true

/-- **WeakCore-lowerable x64 cell.** -/
def DirectiveWCLowerable (d : Directive) : Prop := directiveWCLowerableB d = true

instance (d : Directive) : Decidable (DirectiveWCLowerable d) :=
  inferInstanceAs (Decidable (_ = true))

/-- **WeakCore-lowerable x64 program**: every cell is (clauses L and N;
obligation S is separate, see the module docstring). -/
def ProgramWCLowerable (p : Program) : Prop := ∀ d ∈ p, DirectiveWCLowerable d

instance (p : Program) : Decidable (ProgramWCLowerable p) :=
  inferInstanceAs (Decidable (∀ d ∈ p, DirectiveWCLowerable d))

theorem programWCLowerable_append {p q : Program} :
    ProgramWCLowerable (p ++ q) ↔ ProgramWCLowerable p ∧ ProgramWCLowerable q := by
  simp only [ProgramWCLowerable, List.mem_append]
  exact ⟨fun h => ⟨fun d hd => h d (.inl hd), fun d hd => h d (.inr hd)⟩,
    fun h d hd => hd.elim (h.1 d) (h.2 d)⟩

private def mem0 : AddrExpr := { base := some (.reg .rcx), idx := none }
private def rax : _root_.Reg .W64 := .low .rax .W64

-- The clauses accept and reject what they say.
example : DirectiveWCLowerable (.instr (.regular .W64 .W64 (.xadd true (.mem mem0) rax))) := by
  decide +kernel
example : ¬ DirectiveWCLowerable (.instr (.regular .W64 .W64 (.xadd false (.mem mem0) rax))) := by
  decide +kernel
example : DirectiveWCLowerable (.instr (.regular .W64 .W64 (.xadd false (.reg rax) rax))) := by
  decide +kernel
example : ¬ DirectiveWCLowerable (.instr (.regular .W64 .W64 (.cmpxchg false (.mem mem0) rax))) := by
  decide +kernel
example : DirectiveWCLowerable (.instr (.regular .W64 .W64 (.xchg rax (.mem mem0)))) := by
  decide +kernel
example : ¬ DirectiveWCLowerable (.instr (.regular .W64 .W64 (.movnti mem0 rax))) := by
  decide +kernel
example : ¬ DirectiveWCLowerable (.instr (.avx .W64 .W128 (.cmpxchg16b false mem0))) := by
  decide +kernel
example : ProgramWCLowerable [.label "f", .instr (.regular .W64 .W64 .mfence),
    .instr (.regular .W64 .W8 (.mov (.mem mem0) (.regOrMem (.reg (.low .rax .W8)))))] := by
  decide +kernel

end Scc.Emit.X64
