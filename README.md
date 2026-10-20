# Kraken

## X64 model scope

The x64 model is intended for verifying sequential software
that performs computations using common registers and memory.
Operating-systems and concurrency features currently out of scope.

Included
- 64-bit mode, including 32-bit and smaller operations available in this mode
- All 64-bit registers and [partial-register access](https://en.wikipedia.org/wiki/X86#Structure)
- Status flags
- Memory access, including avoidance of faults
- ADX, BMI, BMI2, and similar extensions
- Assembler features: labels, arithmetic on immediates, rodata

Excluded
- Handling of most exceptions and faults
- Virtual memory
- Segment registers
- MSRs
- Other execution modes, such as 32-bit and 16-bit modes
- Mutable globals (bss and data)

### Incidental extensions to x64

While the model is centrally a subset of x64, we work with assembly, and
we do not seek to model [which assembly programs are encodable](https://godbolt.org/z/Mb5YzbxMG),
and instead give semantics to some instructions that cannot be assembled.
For example, a `mov` from memory to memory is interpreted in the obvious way,
even though an assembler would reject it.
(We do model restrictions on operands where they simplify the semantics,
e.g. entirely ruling out a memory operand in a particular position 
to make its evaluation infallible).
However, if code proven against our semantics assembles for a real x64 target,
we want to be sure that it will satisfy the proven specification.
Thus incidental extensions to x64 must not clash with actual features of x64,
or undefined behavior in x64 (e.g. bswap r16).

More guidance on reviewing semantics is in [CONTRIBUTING.md](CONTRIBUTING.md).

## Weak memory (multi-threaded) model

`Kraken/Promising/` is an ISA-generic operational weak-memory model after
Promising-ARM/RISC-V (Pulte et al., PLDI 2019): a global timestamped memory,
per-thread views, promises with certification. A thread is Kraken's
single-threaded interpreter, unchanged; shared memory is left out of a
thread's `dmem`, so every shared access reaches the model as the
`nonmem_*`/`sync_*`/`rmw`/`fence` effect the ISA emits for unmapped memory.
Two architecture profiles: `Arch.armv8` (the paper's model, with herd7's
conventions for pick dependencies and `CAS`) and `Arch.tso` (x86-TSO as an
instance of the same rules).

`krakenlitmus_aarch64` and `krakenlitmus_x64` run herd7 `.litmus` tests and
print herd's report; `Kraken/Litmus/litmus_tests.py` compares state sets with
herd7's; see [Kraken/Litmus/README.md](Kraken/Litmus/README.md) for worked
examples and [Kraken/Litmus/INTERACTIVE.md](Kraken/Litmus/INTERACTIVE.md)
for a tutorial on the interactive stepper. The catalogue and generated corpora agree with herd7 master on every
test (`Kraken/Litmus/KNOWN_GAPS.md`). The single-threaded model and proofs are
untouched by this layer: the only observable change to sequential semantics
is that `STXR`/`STLXR` may fail spuriously, as the architecture allows.

## Third-party material

`Kraken/Litmus/corpus/` contains litmus tests from the
[diy toolsuite / herdtools7](https://github.com/herd/herdtools7) by Jade
Alglave and Luc Maranget, copyright INRIA and the authors, distributed under
the CeCILL-B license; see
[Kraken/Litmus/corpus/README.md](Kraken/Litmus/corpus/README.md) and
[LICENSE-herdtools7.txt](Kraken/Litmus/corpus/LICENSE-herdtools7.txt).
Kraken's own code is under the MIT license ([LICENSE](LICENSE)).
