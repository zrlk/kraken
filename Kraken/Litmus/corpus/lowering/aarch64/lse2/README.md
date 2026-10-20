# Lowering-table FEAT_LSE2 tests (hand-argued oracles)

    python3 Kraken/Litmus/litmus_tests.py --lse2 Kraken/Litmus/corpus/lowering/aarch64/lse2

The `casPair`, `ldp`/`stp` row of the lowering table on AArch64 `isaLSE2`,
combined with the table's other orderings (`stlr`/`ldar`/`ldapr`,
`dmb ishst`/`dmb ish`, `casl`/`casa`/`casal`). As in
`../../../aarch64-pairs/lse2/` (same argument style), `--lse2` passes `-lse2`
to `krakenlitmus_aarch64` and compares with `<test>.litmus.lse2`. herd7 does
not model FEAT_LSE2: its `LDP`/`STP` are always two accesses. So these
oracles are argued by hand from the Arm ARM (DDI 0487G.a), not produced by
herd. Without `-lse2` every `__int128` test here is unsupported (an 8-byte
half of a 16-byte location is mixed-size).

The base rule (B2.2.1, "Changes to single-copy atomicity in Armv8.4") says:
"If FEAT_LSE2 is implemented, LDP, LDNP, and STP instructions that load or
store two 64-bit registers are single-copy atomic when … the overall memory
access is aligned to 16 bytes" (to Normal WB memory). Each test's 16-byte
location `x` (`__int128`) is 16-aligned. So each `STP`/`LDP` of `x` is **one**
access: a read returns the initial `(0,0)` or the written `(1,2)` / `(1,1)`,
never half of each. The ordering arguments are the ordinary ARMv8 ones for a
single-copy-atomic access, the same as herd's for a single-register access in
the matching non-pair test of `../` (e.g. `MP+popl+poap` Never,
`MP+popl+po` Sometimes):

| Test | Oracle | Argument |
|---|---|---|
| `MP+stp-i128+popl+poap-ldp` | Never, 3 states | `STLR` flag orders the `STP` before it; `LDAR` orders the `LDP` after it. So flag = 1 implies `x = (1,2)`. The `LDP` is one read, so it is never torn. |
| `MP+stp-i128+popl+poqp-ldp` | Never, 3 | The same with `LDAPR`. RCpc only relaxes an `LDAPR` against an *earlier* `STLR` of the same thread; here the `LDAPR` still orders the later `LDP`. |
| `MP+stp-i128+popl+addr-ldp` | Never, 3 | The `LDP`'s address depends on the flag read (`EOR`/`ADD`). An address dependency orders the read (dob). |
| `MP+stp-i128+dmb.ishst+poap-ldp` | Never, 3 | `DMB ISHST` orders the `STP` before the flag `STR` (W→W). |
| `MP+stp-i128+dmb.ishst+addr-ldp` | Never, 3 | `DMB ISHST` writer, address-dependent reader. |
| `MP+stp-i128+casl+poqp-ldp` | Never, 3 | Flag set by `CASL` 0→1. Its write is a release (orders the `STP`); `LDAPR` reader. |
| `MP+stp-i128+popl+casa-ldp` | Never, 3 | Reader `CASA` 1→2 on the flag (fails on 0). `CASA`'s read is an acquire whether or not it succeeds, so the later `LDP` is ordered after it. The flag value read is the comparand register. |
| `MP+stp-i128+popl+po-ldp` | Sometimes, 4 | Control: plain `LDR` flag then `LDP`, unordered. flag = 1 with `x = (0,0)` is allowed, but still no torn state. |
| `MP+stp-i128+po+po-ldp` | Sometimes, 4 | Control: plain on both sides. |
| `SB+stp-ldp-i128+dmb.ishs` | Never, 3 | SB with `STP; DMB ISH; LDP`. The full barrier forbids both loads reading the initial value. No torn reads. |
| `LB+ldp-stp-i128` | Sometimes, 4 | LB with `LDP` then `STP` of the other location, both plain. ARMv8 allows LB, so both loads may read 1. No torn reads. |
| `MP+caspal-i128+ldp` | Never, 2 | `CASPAL (0,0)->(1,2)` on `__int128 x` against an `LDP` of `x`. Arm ARM B2.2.1: `CASP`'s accesses are single-copy atomic at 128 bits, and so is the aligned `LDP`, so the reader sees `(0,0)` or `(1,2)`, never a torn value. Kraken's `isaLSE2` performs this `CASP` as one 16-byte `rmw` (`toEvCASP`). |
| `CoWW+stp+caspal-i128` | Never, 2 | `STP (1,1)` against `CASPAL (0,0)->(2,2)` on `__int128 x`. The `CASPAL` reads a whole value: `(0,0)` (it succeeds, and the `STP` is coherence-after its write, since nothing intervenes between an RMW's read and write) or `(1,1)` (it fails). Final `x = (1,1)` either way. |
| `CAS+caspal-arr+casal` | Never, 2 | `CASPAL (0,0)->(1,2)` on `uint64_t t[2]` against `CASAL 0->3` on `t[0]`. Arm ARM B2.2.1 (CASP 128-bit single-copy atomic; see `open/README.md`): exactly one of them succeeds. Either `CASPAL` wins (`t = {1,2}`, and `CASAL` fails reading 1) or `CASAL` wins (`t = {3,0}`, and `CASPAL` fails reading `(3,0)`). Kraken's `CASP` (two `rmw` events, herd's reading) gives the same two states here, because each half's RMW is atomic on its own location. |

`open/` holds the `CASP` tests where Kraken is weaker than FEAT_LSE2 hardware
(see its README); they are outside the regression run.
