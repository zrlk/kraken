# Model-fidelity sweep

[gen.sh](gen.sh) generates a broad diycross7 sweep (AArch64 and x86_64:
the standard shapes × fences, annotations, dependencies, atomics and
exclusives) into a directory given on the command line, with herd7's output
on each test. It is **not run by `litmus_tests.py`** and its tests are not
checked in: it is a tool for finding model disagreements, each of which
becomes its own task.

    Kraken/Litmus/corpus/sweep/gen.sh <herdtools7 install/bin> <scratch dir>
    for d in <scratch dir>/aarch64/*/; do python3 Kraken/Litmus/litmus_tests.py "$d"; done
    for d in <scratch dir>/x86_64/*/;  do python3 Kraken/Litmus/litmus_tests.py --isa x64 "$d"; done

## First run (herd7 7.58+1, rev 9574394)

3617 AArch64 tests and 372 x86_64 tests; Kraken took about 6 CPU minutes
in total. x86_64: 243 agree, 34 mismatch, 95 unsupported.

| Family | Tests | Mismatches | Direction | Cause |
|---|---|---|---|---|
| AArch64 `*-amo` (the `LxSx`/`LxSxAL` tests) | 480 | 80 | none (same states) | herd's `Loop Ok`/`Loop No` pseudo-state for the exclusive retry loop; every other state agrees. `litmus_tests.py` now drops the pseudo-state (`../README.md`): re-run (herd7 7.58 from opam), the five `*-amo` families give 480 match, 0 mismatch (80 marked `(herd Loop)`) |
| AArch64, all other families | 3137 | 0 | | |
| x86_64 with `lfence`/`sfence` between a write and a later read (SB, R, RWC, SB+rfi) | | 34 | Kraken weaker | herd's `x86tso-mixed.cat` closes `lob` under composition, so `W; po; [F]; po; R` orders the pair for *any* fence event. Kraken (a design decision) orders nothing with `lfence`/`sfence` against a later read, as the SDM says (KNOWN_GAPS) |
| x86_64 `movnti` (diy's `NT` annotation) | 95 | 95 unsupported (with weak non-temporal stores: 38 agree, 57 Kraken weaker) | Kraken weaker | Kraken has weak SDM non-temporal stores, while herd treats `movnti` as a TSO store. These tests are now the regression corpus `../x86_64-nt/`, with SDM oracles for the 57 |

herd master does not parse x86 vector moves (`movdqa`/`movups` with `%xmm`
operands are a syntax error), so the sweep has none.
