#!/usr/bin/env bash
# Drift check of the generated program data and certificates: every
# committed file regen_a64.sh / regen_x64.sh writes for the per-node
# instances (`ret0`, and `hello1`'s negative certificate) is what a fresh
# regeneration from the current scc writes, and each copied program under
# Spike/Gen/ equals its original under Scc/Test/ (regen_*.sh checks that
# first).
#
# Usage: Spike/Gen/drift.sh
# Exit status 0 when every check is clean, 1 when any file is stale (the
# fresh files are under .lake/spike-gen/; rerun the named regen command
# without --check to update), 2 on a usage error. `scc` is built first
# (`lake` from `$LAKE`).
set -u

if [ $# -ne 0 ]; then echo "usage: $0" >&2; exit 2; fi
cd "$(dirname "$0")/../.."

st=0
run() {
  echo "== $*"
  if ! env "$@"; then st=1; fi
}

run bash Spike/Gen/regen_a64.sh ret0 A64Ret0 --check
run bash Spike/Gen/regen_x64.sh ret0 X64Ret0 --check
run CERT_FAILS=11 bash Spike/Gen/regen_a64.sh hello1 A64Hello1 --check
run CERT_FAILS=11 bash Spike/Gen/regen_x64.sh hello1 X64Hello1 --check

if [ "$st" = 0 ]; then echo "drift: clean"; else echo "drift: STALE (see above)"; fi
exit "$st"
