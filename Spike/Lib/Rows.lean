/-
**The nodes outside a program's blocks** (ISA-generic data): the rows a
per-node instance (`correctA64`) needs beyond the blocks of `scc --code`'s
tables, as `Spike/Gen/genrows_a64.py` emits them.

A row is one instruction that no block covers, with its function, its
place (a label and the number of instructions after it, as for a block:
`Scc.Cert.Rt.A64.Grp`), its kind and whether its function is the runtime's.
The kind says which node lemma or `Out` row the instance uses there:

- `label`: an address of a label into a register (`adrp`, `add :lo12:`);
- `system`: a system-register move or a `nop` (no memory, no event);
- `fence`: a barrier (`dmb`: no memory access, no event; it moves the
  thread's views);
- `site`: the `nop` at a resource-transfer site (the take or release site);
- `switch`: a stack switch (`sp` written from a register of unknown
  offset);
- `svc`: a system call;
- `flags`: a register operation with undefined flags (x64's shifts by `%cl`,
  `imul`, logical operations; a finite choice of successors);
- `dead`: an instruction no run reaches (x64's `ud2`);
- `load`, `store`, `rmw`: one memory access not off `sp` (a runtime word, or
  a source cell in a compiled function).

Nothing here depends on the shape of the consumer's node obligations; the
instance maps each kind to its row. The module imports no ISA (the x64 and
AArch64 syntaxes cannot be imported together).
-/
namespace Spike.Lib.Rows

/-- The kind of an instruction outside the blocks. -/
inductive RowK where
  | label
  | system
  | fence
  | site
  | switch
  | svc
  | flags
  | dead
  | load
  | store
  | rmw
  deriving DecidableEq, Repr

/-- **A row**: an instruction outside the blocks, at `k` instructions after
the label `l`, in the function `fn`; `rt` when the function is the
runtime's. -/
structure Row where
  fn : String
  l : String
  k : Nat
  kind : RowK
  rt : Bool
  deriving DecidableEq, Repr

end Spike.Lib.Rows
