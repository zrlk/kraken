#!/usr/bin/env bash
# Drift check of the generated program data and certificates: every
# committed file regen_a64.sh / regen_x64.sh writes for the per-node
# instances (`ret0`, and `hello1`'s negative certificate) and the zero-frame
# x64 certificate (`frame0`) is what a fresh
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
# The zero-frame x64 program (`Spike/Test/Frame0LinkedX64.lean`): its
# certificate and the text its ELF fixture is linked from.
frame0() {
  local T=.lake/spike-gen/frame0.x64 st=0
  mkdir -p "$T"
  "${LAKE:-lake}" build scc >/dev/null || return 1
  .lake/build/bin/scc --arch x64 -o "$T/frame0.s" --cert "$T/cert.lean" Spike/Gen/frame0.w >/dev/null || return 1
  for k in "cert.lean:Spike/Test/Cert/X64Frame0Cert.lean" "frame0.s:Scc/Test/elf/frame0x64/frame0.s"; do
    if ! cmp -s "$T/${k%%:*}" "${k#*:}"; then echo "STALE ${k#*:} (fresh: $T/${k%%:*})"; st=1; fi
  done
  [ "$st" = 0 ] && echo "up to date: Spike/Test/Cert/X64Frame0Cert.lean, Scc/Test/elf/frame0x64/frame0.s"
  return "$st"
}
echo "== frame0"
if ! frame0; then st=1; fi

if [ "$st" = 0 ]; then echo "drift: clean"; else echo "drift: STALE (see above)"; fi
exit "$st"
