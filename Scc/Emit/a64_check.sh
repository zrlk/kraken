#!/usr/bin/env bash
# Assemble, link and run the IR-level AArch64 test programs of scc, then the
# WeakCore test programs (`Scc/Test/run.sh --arch arm`).
#
# Usage: Scc/Emit/a64_check.sh [out-dir] [runs]
#
# Writes the emitted test programs of Scc/Emit/A64Test.lean as .s files
# (through a generated driver run with `lake env lean --run`), assembles each with llvm-mc (FEAT_LSE, LSE2),
# links it with clang/lld as a static freestanding binary, and, when
# qemu-aarch64 is installed, runs it under `qemu-aarch64 -cpu max` and compares
# stdout and the exit code with the expectations below. Programs with threads
# are run `runs` times (default 50) to catch nondeterministic failures.
# Set LAKE to the lake to use (default: lake).
set -u
root=$(cd "$(dirname "$0")/../.." && pwd)
out=${1:-$root/.lake/scc-a64}
runs=${2:-50}
lake=${LAKE:-lake}
cd "$root" || exit 2

# name|expected stdout (printf format)|expected exit code|runs (1 or "many");
# an empty exit code means assemble and link only.
expect=(
  'hello_ir|Hello, world\n|0|1'
  'allops_ir|||'
  'checks_ir|ok\n|0|1'
  'overflow_ir||101|1'
  'stack_ir||101|1'
  'threads_ir|child\nmain\n|0|many'

)

mkdir -p "$out"
printf 'import Scc.Emit.A64Test\ndef main (args : List String) : IO UInt32 :=\n  Scc.Emit.A64.Test.writeAll args\n' \
  >"$out/driver.lean"
"$lake" build Scc.Emit.A64Test >/dev/null || { echo "FAIL: build"; exit 1; }
"$lake" env lean --run "$out/driver.lean" "$out" || { echo "FAIL: emit"; exit 1; }

fail=0
for e in "${expect[@]}"; do
  IFS='|' read -r name stdout code n <<<"$e"
  s="$out/$name.s"
  if ! llvm-mc-19 -triple=aarch64 -mattr=+lse,+lse2 -filetype=obj -o "$out/$name.o" "$s"; then
    echo "FAIL: $name: llvm-mc"; fail=1; continue
  fi
  if ! clang --target=aarch64-linux-gnu -march=armv8.4-a -nostdlib -static -fuse-ld=lld \
      -o "$out/$name" "$s"; then
    echo "FAIL: $name: link"; fail=1; continue
  fi
  if [ -z "$code" ] || ! command -v qemu-aarch64 >/dev/null; then
    echo "ok:   $name (assembled and linked)"; continue
  fi
  want=$(printf "$stdout"; echo x)
  count=1; [ "$n" = many ] && count=$runs
  bad=0
  for ((i = 0; i < count; i++)); do
    got=$(qemu-aarch64 -cpu max "$out/$name" 2>"$out/$name.err"; rc=$?; echo x; echo "$rc" >"$out/$name.rc")
    rc=$(cat "$out/$name.rc")
    if [ "$got" != "$want" ] || [ "$rc" != "$code" ]; then
      bad=$((bad + 1))
      [ $bad -eq 1 ] && echo "  $name run $i: exit $rc, stdout: $(printf %q "${got%x}")"
    fi
  done
  if [ $bad -eq 0 ]; then
    echo "ok:   $name ($count run(s), exit $code)"
  else
    echo "FAIL: $name: $bad of $count run(s) differ"; fail=1
  fi
done
# The WeakCore test programs of Scc/Test, compiled with `scc --arch arm`.
LAKE="$lake" "$root/Scc/Test/run.sh" --arch arm || fail=1
exit $fail
