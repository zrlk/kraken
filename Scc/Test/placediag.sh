#!/usr/bin/env bash
# Which component of `placeOK` fails on a certificate's output: a diagnostic
# for a certificate that does not check, not a proof.
#
# Usage: Scc/Test/placediag.sh --arch x64|arm CERT
#
# CERT is a file `scc --cert` wrote (`Scc.Cert.Gen.render`). The script keeps
# it up to the placement decisions (the source, `asm`, `prog`, `prog_src`,
# `out` and `placeCfg`), appends an evaluation of
# `Scc.Cert.PlaceOK.Checks.firstFail` on `out` at `placeCfg`, and runs that
# with `lake env lean` (`lake` from `$LAKE`, default `lake`) in the Kraken
# package. It prints `aN` for the first failing component AN, `none` when
# every component holds (the certificate fails elsewhere), and exits 2 when
# the file cannot be evaluated. The answer is untrusted: `scc --cert-fails N`
# writes the certificate of that failure, which the kernel decides.
set -u
if [ $# -ne 3 ] || [ "$1" != --arch ]; then echo "usage: $0 --arch x64|arm CERT" >&2; exit 2; fi
case "$2" in
  x64) NS=Scc.Cert.PlaceOK.X64 ;;
  arm) NS=Scc.Cert.PlaceOK.A64 ;;
  *) echo "unknown arch $2" >&2; exit 2 ;;
esac
CERT=$3
LAKE=${LAKE:-lake}
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
DIAG="${CERT%.lean}.diag.lean"
# The certificate up to `outLit` (its literal and the decisions are not needed),
# without its theorems (with their doc comments): the evaluation reads only
# the definitions, and the kernel's decisions (`lowerable`, `sizes_ok`, ...)
# are most of the prefix's time and memory (on x64 up to 4 GB RssAnon).
if ! grep -q '^/-- `out` as a literal' "$CERT"; then echo "$CERT: no placement part" >&2; exit 2; fi
sed '/^\/-- `out` as a literal/,$d' "$CERT" | awk '
  function flush() { if (nd) printf "%s", doc; doc = ""; nd = 0 }
  skip && /^[ \t]/ { next }
  { skip = 0 }
  /^theorem / { doc = ""; nd = 0; skip = 1; next }
  indoc { doc = doc $0 "\n"; if ($0 ~ /-\/[ \t]*$/) indoc = 0; next }
  /^\/--/ { flush(); doc = $0 "\n"; nd = 1; if ($0 !~ /-\/[ \t]*$/) indoc = 1; next }
  { flush(); print }
  END { flush() }' >"$DIAG"
cat >>"$DIAG" <<EOF
#eval IO.println (match Scc.Cert.PlaceOK.Checks.firstFail ($NS.checks placeCfg) ($NS.tablesOf placeCfg) out with
  | some n => s!"placediag: a{n}"
  | none => "placediag: none")

end SccCertificate
EOF
ABS=$(cd "$(dirname "$DIAG")" && pwd)/$(basename "$DIAG")
out=$(cd "$ROOT" && "$LAKE" env lean "$ABS" 2>&1)
r=$(printf '%s\n' "$out" | sed -n 's/^placediag: //p' | head -n 1)
if [ -z "$r" ]; then printf '%s\n' "$out" | head -c 2000 >&2; exit 2; fi
echo "$r"
