#!/usr/bin/env bash
# Block data: `scc --blocks` on every test program.
#
# Usage: Scc/Test/blocks.sh [--check]
#
# Every test program scc compiles (Scc/Test/*.w), for x64 and AArch64, is
# compiled with `--blocks` and `--code`.  The block data must be
# written, the coverage statistics must be JSON, every block must have its
# address comment (`, at L + off`), on x64 every block's size list must
# have one entry per instruction, and on AArch64 the placement data
# (`.place.lean`) must be written.  With `--check`, every code check
# (`--code`, a few seconds and 2.5 GB each on AArch64, under a minute on
# x64) and AArch64 placement data file is
# checked by Lean (`lake env lean`, `lake` from `$LAKE`).  Outputs go to .lake/scc-blocks/; failing programs
# are listed.
set -u

CHECK=0
case "${1:-}" in
  --check) CHECK=1; shift ;;
esac
if [ $# -gt 0 ]; then echo "usage: $0 [--check]" >&2; exit 2; fi
LAKE=${LAKE:-lake}
cd "$(dirname "$0")/../.."
SCC=.lake/build/bin/scc
W=.lake/scc-blocks
mkdir -p "$W"
pass=0; fail=0
for w in Scc/Test/*.w; do
  n=$(basename "$w" .w)
  for a in x64 arm; do
    o="$W/$n.$a"
    "$SCC" --arch "$a" -o "$o.s" "$w" >/dev/null 2>&1 || continue  # not a program scc compiles
    code=(--code "$o.code.lean")
    if ! "$SCC" --arch "$a" -o "$o.s" --blocks "$o.lean" "${code[@]}" "$w" >/dev/null 2>"$o.err"; then
      echo "FAIL $n $a: scc --blocks failed ($o.err)"; fail=$((fail + 1)); continue
    fi
    if [ "$CHECK" = 1 ] && ! "$LAKE" env lean "$o.code.lean" >"$o.code.out" 2>&1; then
      echo "FAIL $n $a: $o.code.lean does not check ($o.code.out)"; fail=$((fail + 1)); continue
    fi
    if [ "$a" = arm ] && [ ! -s "$o.place.lean" ]; then
      echo "FAIL $n $a: no placement data $o.place.lean"; fail=$((fail + 1)); continue
    fi
    if [ "$a" = arm ] && [ "$CHECK" = 1 ] && ! "$LAKE" env lean "$o.place.lean" >"$o.place.out" 2>&1; then
      echo "FAIL $n $a: $o.place.lean does not check ($o.place.out)"; fail=$((fail + 1)); continue
    fi
    if python3 - "$a" "$o.lean" "$o.lean.json" <<'EOF'
import json, re, sys
arch, lean, stats = sys.argv[1:]
json.load(open(stats))
text = open(lean).read()
cmds = [c.strip() for c in text.split("\n\n") if c.strip()]
if not cmds: sys.exit("no blocks")
for c in cmds:
    head, body = c.split("\n", 1)
    if not re.fullmatch(r"-- \S+, listing lines \d+–\d+, at \S+ \+ \d+", head):
        sys.exit(f"bad comment: {head}")
    if arch == "x64":
        m = re.fullmatch(r'block_spec .*? \(parse\("(.*)"\)\)\.zip \[([\d, ]*)\]', body, re.S)
        if not m: sys.exit(f"no size list: {head}")
        if len(m.group(1).split("\n")) != len(m.group(2).split(",")):
            sys.exit(f"size list length: {head}")
EOF
    then pass=$((pass + 1))
    else echo "FAIL $n $a: $o.lean"; fail=$((fail + 1))
    fi
  done
done
echo "blocks.sh: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
