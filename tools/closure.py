#!/usr/bin/env python3
"""Import closure of Lean modules at a git revision, from real `import` lines only.

Usage:
  tools/closure.py REV ROOT...                  print the closure's files, sorted
  tools/closure.py --changed A B ROOT...        print the closure's files that differ
                                                between revisions A and B
  tools/closure.py --certify [--changed A B]    the roots are the certify roots (below)

A module `X.Y.Z` is the file `X/Y/Z.lean` at the revision. Modules not in
the repository (`Lean`, `Std`, ...) are left out of the closure. Only the
file header counts: `import` commands (optionally `public`, `meta` or
`private`) before the first other command, after an optional `module` or
`prelude` and any comments. So an `import` inside a string literal or a
docstring further down (for instance the certificate templates in
Scc/Cert/Blocks.lean) is never followed.

With --changed, the closure is the union of the closures at A and at B; a
file is listed when its contents differ between A and B, or when it exists
at one revision only. The exit status is 1 when anything is listed, else 0.

This is the closure half of the carry-over rule for certify/certify_test
results between two release candidates: identical scc binaries, and no
changed `.lean` file in the closure of the certify roots (`--certify`).
"""
import subprocess
import sys

# The modules certify.sh builds and imports to state its theorems: the
# end-to-end theorems, the compiler theorems, and the registry's final
# theorem modules (hello1, wake, hello on both ISAs).
CERTIFY_ROOTS = [
    "Scc.Cert.E2EX64", "Scc.Cert.E2EA64",
    "Spike.Lib.LowerX64.Correct1", "Spike.Lib.LowerA64.Correct1",
    "Spike.Test.X64Hello1FinalC", "Spike.Test.A64Hello1FinalCA",
    "Spike.Test.WakeLinkedX64Root", "Spike.Test.WakeLinkedA64Root",
    "Spike.Test.HelloLinkedX64Root", "Spike.Test.HelloLinkedA64Root",
]


class Repo:
    """Blob reads at one revision through one `git cat-file --batch`."""

    def __init__(self, rev):
        self.rev = rev
        out = subprocess.run(["git", "ls-tree", "-r", rev], capture_output=True, text=True, check=True).stdout
        self.blob = {}
        for line in out.splitlines():
            meta, path = line.split("\t", 1)
            self.blob[path] = meta.split()[2]
        self.cat = subprocess.Popen(["git", "cat-file", "--batch"], stdin=subprocess.PIPE, stdout=subprocess.PIPE)

    def read(self, path):
        self.cat.stdin.write((self.blob[path] + "\n").encode())
        self.cat.stdin.flush()
        size = int(self.cat.stdout.readline().split()[2])
        data = self.cat.stdout.read(size + 1)[:size]
        return data.decode("utf-8", errors="replace")


def header_imports(text):
    """The modules imported by the header of a Lean file."""
    i, n, mods = 0, len(text), []
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j + 1
        elif text.startswith("/-", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if text.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif text.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
        else:
            j = i
            while j < n and not text[j].isspace():
                j += 1
            word = text[i:j]
            if word in ("module", "prelude", "public", "meta", "private"):
                i = j
            elif word == "import":
                # exactly one module name per `import` command (`import all M` allowed)
                i = j
                while True:
                    while i < n and text[i].isspace():
                        i += 1
                    k = i
                    while k < n and not text[k].isspace():
                        k += 1
                    name = text[i:k]
                    i = k
                    if name != "all":
                        break
                if name:
                    mods.append(name)
            else:
                break
    return mods


def closure(repo, roots):
    seen, stack = set(), list(roots)
    while stack:
        m = stack.pop()
        path = m.replace(".", "/") + ".lean"
        if path in seen or path not in repo.blob:
            continue
        seen.add(path)
        stack.extend(header_imports(repo.read(path)))
    return seen


def main(argv):
    changed, certify = None, False
    args = list(argv)
    if args and args[0] == "--certify":
        certify, args = True, args[1:]
    if args and args[0] == "--changed":
        if len(args) < 3:
            print(__doc__, file=sys.stderr)
            return 2
        changed, args = (args[1], args[2]), args[3:]
    if args and args[0] == "--certify":
        certify, args = True, args[1:]
    if changed is None:
        if not args:
            print(__doc__, file=sys.stderr)
            return 2
        rev, args = args[0], args[1:]
    roots = args + (CERTIFY_ROOTS if certify else [])
    if not roots:
        print("closure.py: no root modules", file=sys.stderr)
        return 2
    if changed is None:
        repo = Repo(rev)
        missing = [m for m in roots if m.replace(".", "/") + ".lean" not in repo.blob]
        for m in missing:
            print(f"closure.py: root {m} is not a file at {rev}", file=sys.stderr)
        for p in sorted(closure(repo, roots)):
            print(p)
        return 2 if missing else 0
    a, b = Repo(changed[0]), Repo(changed[1])
    files = closure(a, roots) | closure(b, roots)
    diff = sorted(p for p in files if a.blob.get(p) != b.blob.get(p))
    for p in diff:
        print(p)
    print(f"closure.py: {len(files)} files in the closure, {len(diff)} changed between {changed[0]} and {changed[1]}",
          file=sys.stderr)
    return 1 if diff else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
