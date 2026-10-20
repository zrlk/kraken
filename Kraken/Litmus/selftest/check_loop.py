#!/usr/bin/env python3
"""Self-test of `litmus_tests.py`'s handling of herd's `Loop` pseudo-state.

Usage:
  Kraken/Litmus/selftest/check_loop.py

Runs `litmus_tests.py -v` on `selftest/loop/` (needs `krakenlitmus_aarch64`)
and checks its rows. Each test there is corpus test A184 (an `LDXR`/`STXR`
retry loop; Kraken's only final state is `[x]=2`) with a `.herd` oracle that
carries herd's `Loop Ok` line. The `.litmus` files are
`corpus/aarch64-instructions/A184.litmus` (herdtools7, CeCILL-B: see
`corpus/README.md`) with only the test name changed; `LoopMatch.litmus.herd`
is A184's herd output, renamed, the other two oracles are doctored:

- `LoopMatch`: herd's real oracle (`[x]=2`, `Always`): must match.
- `LoopWrongState`: doctored, real state `[x]=3`: must be a mismatch that
  reports `kraken-only: [x]=2` and `herd-only: [x]=3`.
- `LoopMissingState`: doctored, real states `[x]=1`, `[x]=2` and verdict
  `Sometimes`: must be a mismatch that reports `herd-only: [x]=1`.

So dropping the pseudo-state does not hide a real-state mismatch. Exit
status is non-zero on a failed check.
"""
import pathlib
import re
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
SCRIPT = HERE.parent / "litmus_tests.py"

EXPECT = {
    "LoopMatch.litmus": ("match", ["(herd Loop)"]),
    "LoopWrongState.litmus": ("MISMATCH", ["(herd Loop)", "kraken-only: [x]=2", "herd-only: [x]=3"]),
    "LoopMissingState.litmus": ("MISMATCH", ["(herd Loop)", "herd Sometimes / kraken Always", "herd-only: [x]=1"]),
}


def main():
    proc = subprocess.run([sys.executable, str(SCRIPT), "-v", str(HERE / "loop")],
                          capture_output=True, text=True)
    print(proc.stdout, end="")
    rows = {}
    for line in proc.stdout.split("\n"):
        m = re.match(r"^(\S+)\s+(\S+\.litmus)\s*(.*)$", line)
        if m:
            rows[m.group(2)] = (m.group(1), m.group(3))
    failed = 0
    for name, (status, needles) in EXPECT.items():
        got = rows.get(name)
        if got is None:
            print(f"FAIL {name}: no row")
            failed += 1
            continue
        if got[0] != status or any(n not in got[1] for n in needles):
            print(f"FAIL {name}: expected {status} with {needles}, got {got[0]} {got[1]!r}")
            failed += 1
    if "1 match, 2 mismatch, 0 unsupported, of 3; 3 compared without herd's Loop pseudo-state" not in proc.stdout:
        print("FAIL summary line")
        failed += 1
    if proc.returncode != 1:
        print(f"FAIL exit status {proc.returncode} (expected 1: there are mismatches)")
        failed += 1
    print("check_loop: " + ("OK" if not failed else f"{failed} check(s) failed"))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
