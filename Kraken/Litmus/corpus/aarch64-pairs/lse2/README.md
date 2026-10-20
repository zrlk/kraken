# FEAT_LSE2 tests (hand-argued oracles)

Run with `python3 Kraken/Litmus/litmus_tests.py --lse2 Kraken/Litmus/corpus/aarch64-pairs/lse2`.
This passes `-lse2` to `krakenlitmus_aarch64`, which selects
`Kraken.Promising.AArch64.isaLSE2`, and compares the result with
`<test>.litmus.lse2`.

FEAT_LSE2 (Armv8.4) makes an `LDP`/`STP` of two `X` registers single-copy
atomic when its 16-byte access is 16-byte aligned (to Normal memory). herd7
does not model this; its `LDP`/`STP` are always two accesses. So these oracles
are argued by hand, not produced by herd. They model FEAT_LSE2 hardware, not
herd's AArch64 model. No regression corpus uses `-lse2`.

| Test | Oracle | Argument |
|---|---|---|
| `MP+stp+ldp-i128` | Never: states `(0,0)`, `(1,2)` | The `STP` and the `LDP` of the 16-byte location `x` are one access each, so the `LDP` reads either the initial value or the `STP`'s, never half of each. herd without FEAT_LSE2 says Sometimes (four states). |
| `CoRR+stp-i128` | Never: the 6 states with `X2 ≤ X6` in coherence order `0 < 1 < 2` | Each `STP` is one write and each `LDP` one read of `x`, so CoRR coherence applies to whole values. This matches herd's verdict for two-access `STP`, where per-half coherence gives the same states. |
| `MP+stp+ldp-arr` | Sometimes: all four states | Control. The halves are two 8-byte array elements, not one 16-byte location, so `isaLSE2` keeps two accesses, as herd does. That is weaker than FEAT_LSE2 hardware, where an aligned `STP` is atomic whatever the test declares, so this test is not hardware-exact. Weaker is sound: Kraken's locations are footprints, and a 16-byte access across two 8-byte locations would be a mixed-size access. |

Without `-lse2`, the first two tests are unsupported: an 8-byte half of the
declared 16-byte location `x` is a mixed-size access.
