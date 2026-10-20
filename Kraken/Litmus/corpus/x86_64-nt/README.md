# x86_64 non-temporal stores (`movnti`)

A regression corpus for Kraken's weak non-temporal stores. It
contains:

- the 95 tests of the model-fidelity sweep's x86_64 families
  (`../sweep/gen.sh`) that use diy's `NT` annotation (`movnti`), and
- 12 hand-written tests in `hand/`: `MP+nt-{sfence,mfence,lfence,xchg}+po`,
  `MP+nt-sfence-nt+po`, `SB+nt-{mfences,sfences}`, `2+2W+nt-sfences`,
  `Co{WW,WR,RR}+nt` and `movntiq` (the 64-bit form).

[gen.sh](gen.sh) regenerates everything (herdtools7 master is needed: herd7
7.58 from opam does not know the `NT` annotation; see
[ORACLE.txt](ORACLE.txt)). To run it:

    lake build krakenlitmus_x64
    python3 Kraken/Litmus/litmus_tests.py --isa x64 Kraken/Litmus/corpus/x86_64-nt Kraken/Litmus/corpus/x86_64-nt/hand

Expected result: `107 match, 0 mismatch, 0 unsupported, of 107; 59 compared
with an SDM oracle (weaker than herd)`, in about 5 s of CPU time.

## Semantics (Intel SDM)

`movnti m32/m64, r32/r64` is a store with the usual dependencies. The SDM
(vol. 3A §8.2.2 and §11.3.1, and the MOVNTI entry) makes non-temporal stores
*weakly ordered*: they may be reordered with other stores to different
locations, in both directions. Like every store, they are not reordered with
older loads. Same-location stores stay in order (coherence). `sfence`,
`mfence` and locked instructions order them; `lfence` does not.

In Kraken this is `StoreKind.nt`, which `Arch.tso` keeps (`Arch.ntStore`;
under ARMv8 it is a plain store):

- a non-temporal store raises `Views.vwOldNT`, not `vwOld`, so a later
  release store does not wait for it;
- its pre-view includes the earlier reads (`vrOld`, `vrOldNR`) but not the
  earlier writes;
- `fence .st` (`sfence`), `fence .sy` (`mfence`, and the fences around a
  locked RMW) and `fence .stAll` fold `vwOldNT` in;
- `lfence` and `sfence` still order nothing against later reads (KNOWN_GAPS).

## Oracles

herd7 treats `movnti` as an ordinary TSO store, so on these tests it is
stronger than the SDM. Where they differ, `<test>.litmus.sdm` holds the
outcome set of [sdm_model.py](sdm_model.py), a small operational reading of
the SDM written independently of Kraken. It has a FIFO store buffer for
ordinary stores and an unordered write-combining buffer for non-temporal
ones, keeps same-location stores in order, and models `sfence` epochs,
`mfence`/locked drains and store forwarding. On the 277 non-NT tests of the
sweep it agrees with herd except on the 34 known `lfence`/`sfence`
write-to-read tests (`../sweep/README.md`). `litmus_tests.py` prefers a
`.sdm` oracle over `.herd`, but only after checking that it contains every
herd state: the SDM may only add outcomes.

The 59 Kraken-weaker tests, each forbidden by herd (`Never`) and allowed by
the SDM and Kraken (`Sometimes`):

| Tests | Why the SDM allows the outcome |
|---|---|
| `MP+{ponant,pontna}+{po,lfence,sfence,mfence}` (8), `MP-xchg+{ponant,pontna}+*` (12) | The writer's two stores (one of them non-temporal) are unordered; nothing on the reader's side helps. |
| `S+*` (12), `R+*` (8) | Same: the writer's W→W pair is unordered. |
| `2+2W+*` (17) | At least one thread's W→W pair has a non-temporal store and no `sfence`/`mfence`/locked instruction. |
| `hand/MP+nt-lfence+po` | `lfence` does not order stores. |
| `hand/SB+nt-sfences` | `sfence` does not order a store before a later load. |

(`ponant` and `pontna` are diy's po edges ordinary→NT and NT→ordinary.) The
other 48 tests, including `MP+nt-{sfence,mfence,xchg}+po`,
`MP+nt-sfence-nt+po`, `2+2W+nt-sfences` and the coherence tests, agree with
herd.
