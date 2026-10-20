/-
**The value invariant with successful plain stores**.
ISA-neutral; the companion of `MemVals.lean`, whose core (`MemVals`,
`MemVals.read`, `memVals_write`, `ValInvAt`) it reuses unchanged.

`MemVals.ValX` asks the write condition of *every* answer of a store,
`b = false` included. The machine never answers a non-exclusive store with
`b = false` (`runTree`'s failure branch is guarded by `xcl`), and the
environment that AArch64's per-thread runs use, `SharedEnv.inv S G`, only
answers a non-exclusive store with success (`inv_step_store`), as
`A64NoFaultD`'s address runs (`AddrSafeA`, `EvTree.AllLeavesA`) do. So the
AArch64 link of the value invariant needs the store clause guarded by the
same condition:

- `ValXA L V P t`: `ValX` with the store continuation asked only at
  `b = true ∨ xcl = true` (`ValX.toValXA`: every `ValX` tree is `ValXA`);
- **`runTree_valXA`**, `stepOne_valXA`, `threadNP_valXA`, `certWrite_valXA`:
  `runTree_valX` and its consequences, the store case reading the failure
  branch off `xcl`;
- **`Reachable.valInvA`**, **`faultFree_of_valInvA`**: `Reachable.valInv`
  and `faultFree_of_valInv` for `ValXA`, promises included.

Nothing here is stronger than the machine: a `ValXA` tree is unconstrained
exactly at the answers `runTree` never produces.

The content of this module (`ValXA`, `ValX.toValXA`, `ValXA.mono`,
`runTree_valXA`, …, `faultFree_of_valInvA`) moved, same names, to the
ISA-neutral `EnvG/MemValsGen.lean`, whose lemmas are now the generic forms
and `MemVals.lean`'s `ValX` lemmas their instances. This module forwards
to both.
-/
import Kraken.Promising.SLR.EnvG.MemVals
import Kraken.Promising.SLR.EnvG.MemValsGen
