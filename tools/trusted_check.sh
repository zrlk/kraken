#!/usr/bin/env bash
# Trusted-file check: which files under the trusted filter differ from a pinned list.
#
# Usage:
#   tools/trusted_check.sh REV [LIST]     compare REV with LIST (default tools/trusted_paths.md5)
#   tools/trusted_check.sh --write REV    print the list for REV (to regenerate LIST)
#
# The trusted filter selects every tracked file whose path matches TRUSTED_RE
# (below), every file under Scc/Test/elf/, and every file whose basename is in
# TRUSTED_NAMES. These are the files a reviewer must read when they change: the
# Kraken semantics, the certificate generator and the runtime certificates, the
# source and target semantics, the trusted shell drivers (certify, elf, a64link,
# run) and the ELF fixtures.
#
# LIST holds one line per file, `md5  path` (md5 of the file's contents at the
# pinned revision), sorted by path. The comparison prints
#   ADDED <path>      under the filter at REV, not in LIST
#   REMOVED <path>    in LIST, not at REV
#   CHANGED <path>    contents differ
# then a summary: per top-level directory the number of trusted files and of
# differences, and for Kraken/ the differences per second-level directory.
# Exit status: 0 when REV matches LIST exactly, 1 otherwise, 2 on usage errors.
#
# Release use: the gate runs `tools/trusted_check.sh HEAD`; any line other
# than the summary must be reviewed, and LIST is then regenerated with
# --write at the new release commit and committed with it.
set -u
ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT" || exit 2
WRITE=0
if [ "${1:-}" = --write ]; then WRITE=1; shift; fi
REV=${1:-}
[ -n "$REV" ] || { sed -n '2,8p' "$0" >&2; exit 2; }
LIST=${2:-$ROOT/tools/trusted_paths.md5}
git rev-parse --verify -q "$REV^{tree}" > /dev/null || { echo "trusted_check: unknown revision $REV" >&2; exit 2; }
[ "$WRITE" = 1 ] || [ -f "$LIST" ] || { echo "trusted_check: no list $LIST" >&2; exit 2; }

TRUSTED_RE='Scc/Cert/Gen|Cli.lean|^Main|certify|Scc/Cert/Spawn|Scc/Sem|a64link|elf.sh|^Kraken/|Scc/Cert/Rt/|Frontend|CertTest|Scc/Test/Rt|Spike/Test/Cert|Cert/Link.lean|LinkImage|Maps[A-Za-z0-9]*[.]lean|Scc/Config|Lower/Spec|OutStage(X64|A64)[.]lean'
TRUSTED_NAMES='HelloLinkedX64.lean ElfTest.lean run.sh'
export TRUSTED_RE TRUSTED_NAMES

python3 - "$WRITE" "$REV" "$LIST" <<'EOF'
import collections, hashlib, os, re, subprocess, sys

write, rev, listfile = sys.argv[1] == "1", sys.argv[2], sys.argv[3]
pat = re.compile(os.environ["TRUSTED_RE"])
names = set(os.environ["TRUSTED_NAMES"].split())

def trusted(path):
    return bool(pat.search(path)) or path.startswith("Scc/Test/elf/") or path.rsplit("/", 1)[-1] in names

out = subprocess.run(["git", "ls-tree", "-r", "-z", rev], capture_output=True, check=True).stdout
blobs = {}
for rec in out.split(b"\0"):
    if not rec:
        continue
    meta, path = rec.split(b"\t", 1)
    kind, sha = meta.split()[1:3]
    path = path.decode()
    if kind == b"blob" and trusted(path):
        blobs[path] = sha.decode()

cat = subprocess.Popen(["git", "cat-file", "--batch"], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
md5 = {}
for path in sorted(blobs):
    cat.stdin.write((blobs[path] + "\n").encode())
    cat.stdin.flush()
    size = int(cat.stdout.readline().split()[2])
    md5[path] = hashlib.md5(cat.stdout.read(size + 1)[:size]).hexdigest()
cat.stdin.close()
cat.wait()

if write:
    for path in sorted(md5):
        print(f"{md5[path]}  {path}")
    sys.exit(0)

pinned = {}
with open(listfile) as f:
    for line in f:
        line = line.rstrip("\n")
        if line:
            h, path = line.split("  ", 1)
            pinned[path] = h

diffs = []
for path in sorted(set(md5) | set(pinned)):
    if path not in pinned:
        diffs.append(("ADDED", path))
    elif path not in md5:
        diffs.append(("REMOVED", path))
    elif md5[path] != pinned[path]:
        diffs.append(("CHANGED", path))
for kind, path in diffs:
    print(f"{kind} {path}")

def top(path, depth):
    parts = path.split("/")
    return "/".join(parts[:depth]) + ("/" if len(parts) > depth else "")

files = collections.Counter(top(p, 1) for p in md5)
ndiff = collections.Counter(top(p, 1) for _, p in diffs)
print(f"trusted_check: {rev}: {len(md5)} trusted files, {len(pinned)} pinned, "
      f"{len(diffs)} differences (" + ", ".join(
          f"{k} {sum(1 for d in diffs if d[0] == k)}" for k in ("ADDED", "REMOVED", "CHANGED")) + ")")
for d in sorted(set(files) | set(ndiff)):
    print(f"  {d:<24} {files[d]:>5} files, {ndiff[d]} differ")
def kdir(path):  # Kraken/<dir>/, or Kraken/* for the files directly under Kraken/
    d = top(path, 2)
    return d if d.endswith("/") else "Kraken/*"

kfiles = collections.Counter(kdir(p) for p in md5 if p.startswith("Kraken/"))
kdiff = collections.Counter(kdir(p) for _, p in diffs if p.startswith("Kraken/"))
if kfiles or kdiff:
    print("  Kraken/ by directory:")
    for d in sorted(set(kfiles) | set(kdiff)):
        print(f"    {d:<32} {kfiles[d]:>5} files, {kdiff[d]} differ")
sys.exit(1 if diffs else 0)
EOF
