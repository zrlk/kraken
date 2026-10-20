# Generated litmus corpus

Litmus families produced by `diycross7` from [gen.sh](gen.sh) (cycle shapes
with alternatives at each per-thread edge: barriers, dependencies,
release/acquire annotations), with herd7's output on each test as the
oracle (`*.litmus.herd`, `Time`/`Hash` lines removed). The generator and
herd7 revision are in [ORACLE.txt](ORACLE.txt); the tools are from
herdtools7 (CeCILL-B, see `../corpus/README.md`).

    python3 Kraken/Litmus/litmus_tests.py Kraken/Litmus/generated/aarch64
    python3 Kraken/Litmus/litmus_tests.py --isa x64 Kraken/Litmus/generated/x86_64
