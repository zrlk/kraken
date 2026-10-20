# x86_64 vector litmus tests (hand-argued)

Written for Kraken; not from herdtools7. herd7 has no vector support: the
master build used as oracle elsewhere (7.58+1, rev `9574394`) rejects
`movdqa`, `movups` and `cmpxchg16b` and the `xmm` registers with a syntax
error, and its x86 parser cannot read 128-bit literals. So each test's
expected output is the hand-written `<test>.litmus.hand` (herd's report
format), argued below; `litmus_tests.py` uses a `.hand` file when there is
no `.herd` one.

    python3 Kraken/Litmus/litmus_tests.py --isa x64 Kraken/Litmus/corpus/x86_64-vector

A 16-byte value prints as one unsigned number, the low 8 bytes in the low
64 bits: the record `{1,1}` (low word, high word) is
`0x10000000000000001` = 18446744073709551617, `{2,2}` is
`0x20000000000000002` = 36893488147419103234.

## `MP16+movdqa`: never torn

`rec` is `__int128`, one 16-byte location. P0 stores `{1,1}`, then `{2,2}`,
each with one aligned `movdqa`; P1 loads `rec` once with `movdqa`. On
processors with AVX an aligned 16-byte `movdqa` access is single-copy
atomic (SDM Vol. 3A, "Guaranteed Atomic Operations"), so the load returns
the initial record or one of the two stores: 3 states, and the condition
(a torn record) is `Never` true.

## `MP16+movups`: torn reads observable

The same with `movups` on both sides. `movups` is not guaranteed atomic;
Kraken models it as two 8-byte accesses in address order, low word first,
so the record is two 8-byte words,
`uint64_t rec[2]` (a 16-byte location would make the pieces mixed-size).
Under TSO the writer's stores reach memory in order W1.lo, W1.hi, W2.lo,
W2.hi; the reader reads lo, then hi. If R.lo follows i of the four writes
and R.hi follows j ≥ i, it reads lo version ⌈i/2⌉ and hi version ⌊j/2⌋:
(lo, hi) ∈ {(0,0), (0,1), (0,2), (1,0), (1,1), (1,2), (2,1), (2,2)}, 8
states (`xmm2` = hi·2⁶⁴ + lo), five of them torn: `Sometimes`.
`locations [rec;]` prints the final record, `{2,2}` in every state.
