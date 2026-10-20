# `CASP` on FEAT_LSE2: tests outside the regression run

    python3 Kraken/Litmus/litmus_tests.py --lse2 Kraken/Litmus/corpus/lowering/aarch64/lse2/open

These tests check the lowering table's `casPair -> casp*` row against
hardware. The `.litmus.lse2` oracles are hardware (Arm ARM) oracles. Kraken
is **weaker than hardware** on both. It is never stricter. Today's result:
0 match, 2 mismatch (Kraken weaker).

The two `__int128` tests that were here (`MP+caspal-i128+ldp`,
`CoWW+stp+caspal-i128`) match their oracles under `--lse2` since `isaLSE2`
performs a `CASP` of `X` registers on a 16-aligned declared 16-byte location
as one 16-byte `rmw`; they are now in the regression run (`../`). The table
below keeps their rows for the record.

## What the Arm ARM says

Arm ARM DDI 0487G.a, §B2.2.1 "Requirements for single-copy atomicity",
last item of the list of single-copy-atomic accesses:

> The reads and writes of the two words or two double-words accessed by CASP
> instructions are single-copy atomic at the size of the two words or
> double-words.

- **No alignment or FEAT_LSE2 condition.** The sentence is in the base list,
  not under "Changes to single-copy atomicity in Armv8.4", which is where
  the FEAT_LSE2 `LDP`/`STP` rule is. So an `X`-register `CASP` is one
  128-bit single-copy-atomic read and, on success, one 128-bit write, with
  or without FEAT_LSE2.
- **Alignment still matters for whether the access happens at all.**
  §B2.5.2 "Alignment of data accesses", atomic instructions: "If FEAT_LSE2
  is not implemented, these instructions generate an Alignment fault if the
  address being accessed is not aligned to the size of the data structure
  being accessed". That is 16 bytes for an `X` pair. With FEAT_LSE2, an
  unaligned access that lies within an aligned 16-byte quantity is
  performed, and "Where memory access is performed, then it is single-copy
  atomic".
- In every test here the pair is 16-aligned.

## What herd and Kraken do

- **herd 7.58** treats `CASP`'s halves as two accesses, combined with `>>|`
  (`AArch64Sem.ml`). They are not single-copy atomic as a pair, and the two
  reads (and the two writes) are unordered. See `../../../../KNOWN_GAPS.md`,
  "`CASP`".
- **Kraken** (`isa`) follows herd: `caspTree` (`Kraken/Promising/AArch64.lean`,
  `Lower/EventsA64.lean` "`exec_casp`: `caspTree`, two RMWs in one tree")
  emits two 8-byte `rmw` events, both orders of the halves explored.
  - Under `isaLSE2` an `LDP`/`STP` of a 16-byte declared location is one
    16-byte event (`exec_ldp_lse2`/`exec_stp_lse2`), and so is an `X`-register
    `CASP` there (`toEvCASP`, `exec_casp16`), a Kraken modelling choice
    gated on `isaLSE2` so that `isa` stays herd-faithful.
  - Under `isa` a `CASP` on that location is a mixed-size access, which
    Kraken rejects.
  - On two 8-byte locations (`uint64_t t[2]`), `CASP` and `LDP` are both
    two accesses.

| Test | Hardware oracle (`.lse2`) | herd 7.58 | Kraken `-lse2` (and without), before the one-event `CASP` |
|---|---|---|---|
| `MP+caspal-i128+ldp`: `CASPAL (0,0)->(1,2)` on `__int128 x` vs `LDP x` | Never: `(0,0)`, `(1,2)` (both accesses 16-byte single-copy atomic) | `-variant mixed`: Sometimes, 4 states (torn `(1,0)`, `(0,2)`) | **Unsupported**: "mixed-size access: 8 bytes at …, declared 16 bytes" |
| `CoWW+stp+caspal-i128`: `STP (1,1)` vs `CASPAL (0,0)->(2,2)` on `__int128 x` | Never: `CASPAL` reads `(0,0)` (succeeds, then the `STP` overwrites) or `(1,1)` (fails). Final `x = (1,1)` either way. | no result (warning "mask 64 bit value … with s128 mask") | **Unsupported** (mixed size) |
| `MP+caspal-arr+ldp`: `CASPAL (0,0)->(1,2)` on `uint64_t t[2]` vs `LDP t` | Never: `(0,0)`, `(1,2)` (the aligned 16-byte `LDP` is single-copy atomic under FEAT_LSE2 whatever the declarations say; `CASP` is too) | Sometimes, 4 states | Sometimes, 4 states (`(0,0)`, `(0,2)`, `(1,0)`, `(1,2)`): **superset** of the hardware states |
| `MP+caspal-arr+caspal-rd`: the same, but the reader is a failing `CASPAL` (comparand `(5,5)`) used as a 16-byte read | Never: `(0,0)`, `(1,2)` (both `CASP`s 128-bit atomic; no `LDP` involved) | Sometimes, 4 states | Sometimes, 4 states: **superset**. This isolates `CASP`'s own pair atomicity: the torn read comes from the two-event `CASP`, not from the `LDP`. |

In the regression run `../CAS+caspal-arr+casal` (`CASPAL` on `t[0..1]` vs
`CASAL` on `t[0]`) **matches** the hardware oracle. Exactly one of the two
succeeds, because each half's RMW is atomic on its own 8-byte location. Two
`CASP`s, or a `CASP` and a single-word RMW, therefore exclude each other in
Kraken as on hardware. What Kraken lacks is the **128-bit read**: a reader
can see one half of a `CASP` without the other.

## Consequences for the lowering table

- **`casPair` and LSE2 `ldp`/`stp` share a cell under `isaLSE2`** when it
  is declared as one 16-byte location (otherwise `isaLSE2` keeps two
  accesses, `../../../../aarch64-pairs/lse2/MP+stp+ldp-arr`): both are single
  16-byte events there. If it is declared as two 8-byte words, `CASP` runs,
  but every pair read can be torn.
- Kraken's two-event `CASP` is **sound** (weaker than hardware; every
  hardware outcome is a Kraken outcome in the two array tests). It cannot
  prove a property that relies on a `CASP` pair being read atomically.
- The one-event 16-byte `CASP` on a 16-byte location under `isaLSE2` turned
  the two `-i128` tests into supported, matching ones. If the array tests
  were re-declared `__int128` they would then match the hardware oracle.
